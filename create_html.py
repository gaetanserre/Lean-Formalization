import os

# List all directories in the current directory
PROJECTS_NAME = os.listdir()
print_blue = lambda s: print("\033[94m" + s + "\033[0m")

for project in PROJECTS_NAME:
    current_dir = os.getcwd()
    if os.path.isdir(project) and not project.startswith("."):
        print_blue(f"Current Lean project: {project}")
        os.chdir(project)
        project = project.replace("-", "")
        # Get path to all Lean files
        for file in os.listdir(project):
            if file.endswith(".lean"):
                lean_file = os.path.join(project, file)
                # Call Alectryon on each Lean file
                os.system(
                    f"alectryon --frontend lean4 {lean_file} --lake lakefile.lean --webpage-style windowed --output-directory html"
                )
    os.chdir(current_dir)
