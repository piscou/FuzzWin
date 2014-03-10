#include "fuzzwin.h"
#include <qfiledialog>
#include <qmessagebox>

FUZZWIN_GUI::FUZZWIN_GUI(QWidget *parent) : 
    QMainWindow(parent),
    env(QProcessEnvironment::systemEnvironment())
{
    this->setupUi(this);
    QStringList columnNames;
    columnNames << "Nom" << "Fautes" << "autre";
    GUI_listOfInputs->setHeaderLabels(columnNames);
    QTreeWidgetItem *firstInput = new QTreeWidgetItem(columnNames);
    GUI_listOfInputs->addTopLevelItem(firstInput);

}

FUZZWIN_GUI::~FUZZWIN_GUI() {}


void FUZZWIN_GUI::initialize()
{
    // initialisation des boutons

    // pour PIN : variable d'environnement "PIN_ROOT"
    QString pinPath = env.value("PIN_ROOT");
    
    // si la variable n'est pas présente : PIN_NON_OK
    if (pinPath.isEmpty()) this->setButtonError(GUI_selectPinButton);
    else
    {
        // test de la présence des fichiers indispensables pour PIN
        this->isPinPresent = this->checkPinPath(pinPath);
        if (this->isPinPresent) 
        {
            this->sendToLogWindow("Répertoire de PIN : OK");
            this->setButtonOk(GUI_selectPinButton);
        } 
        else this->setButtonError(GUI_selectPinButton);
    }

    // pour Z3 : variable d'environnement "Z3_ROOT"
    QString z3Path = env.value("Z3_ROOT");
    
    // si la variable n'est pas présente : Z3_NON_OK
    if (z3Path.isEmpty()) this->setButtonError(GUI_selectZ3Button);
    else
    {
        // test de la présence des fichiers indispensables pour Z3
        this->isZ3Present = this->checkZ3Path(z3Path);
        if (this->isZ3Present) 
        {
            this->sendToLogWindow("Répertoire de Z3 : OK");
            this->setButtonOk(GUI_selectZ3Button);
        } 
        else this->setButtonError(GUI_selectZ3Button);
    }
}

bool FUZZWIN_GUI::checkPinPath(QString &path)
{
    bool result = true; // on considere que tout est ok à priori

    // ajout du séparateur, si non présent
    if (!(path.endsWith('/') || path.endsWith('\\')))
    {
        path.append(QDir::separator());
    }

    // modules 32 bits 
    QString pin_X86       = path + "ia32\\bin\\pin.exe";
    QString pin_X86_VmDll = path + "ia32\\bin\\pinvm.dll";

    // modules 64 bits
    QString pin_X64       = path + "intel64\\bin\\pin.exe";
    QString pin_X64_VmDll = path + "intel64\\bin\\pinvm.dll";

    // test de la présence des fichiers adéquats
    if (!QFile::exists(pin_X86))
    {
        result = false;
        this->sendToLogWindow("exécutable PIN 32bits absent");
    }
    if (!QFile::exists(pin_X86_VmDll))
    {
        result = false;
        this->sendToLogWindow("librairie PIN_VM 32bits absente");
    }

    // OS 64 bits : présence obligatoire des modules 64bits
    if (pGlobals->osType >= BEGIN_HOST_64BITS) 
    {
        if (!QFile::exists(pin_X64))
        {
            result = false;
            this->sendToLogWindow("exécutable PIN 64bits absent");
        }
        if (!QFile::exists(pin_X64_VmDll))
        {
            result = false;
            this->sendToLogWindow("librairie PIN_VM 64bits absente");
        }
    }
    
    return (result);
}

bool FUZZWIN_GUI::checkZ3Path(QString &path)
{
    bool result = true; // on considere que tout est ok à priori

    // ajout du séparateur, si non présent
    if (!(path.endsWith('/') || path.endsWith('\\'))) path.append(QDir::separator());
    
    // chemin vers Z3
    QString z3Path = path + "bin\\z3.exe";
    
    // test de la présence de Z3
    if (!QFile::exists(z3Path))
    {
        result = false;
        this->sendToLogWindow("solveur Z3 absent");
    }
    
    return (result);
}

void FUZZWIN_GUI::sendToLogWindow(const QString &msg)
{
    QTime thisTime = QDateTime::currentDateTime().time();
    QString fullMsg(thisTime.toString("[HH:mm:ss:zzz] : ") + msg + "\n");
    this->GUI_logWindow->insertPlainText(fullMsg);
}

void FUZZWIN_GUI::setButtonOk(QPushButton *b)
{
    b->setStyleSheet("background-color:rgb(100,255,100)");
}

void FUZZWIN_GUI::setButtonError(QPushButton *b)
{
    b->setStyleSheet("background-color:rgb(255,50,20)");
}


void FUZZWIN_GUI::on_GUI_selectPinButton_clicked()
{
    // récupération du dossier où se trouve PIN
    QString pinPath = QFileDialog::getExistingDirectory(this, 
        "Sélection du répertoire de PIN",
        QDir::currentPath(),
        QFileDialog::ShowDirsOnly);

    // test de la présence des fichiers indispensables pour PIN
    this->isPinPresent = this->checkPinPath(pinPath);
    if (this->isPinPresent) 
    {
        this->sendToLogWindow("Répertoire de PIN : OK");
        this->setButtonOk(GUI_selectPinButton);
    } 
    else this->setButtonError(GUI_selectPinButton);
}

void FUZZWIN_GUI::on_GUI_selectZ3Button_clicked()
{
    QString z3Path = QFileDialog::getExistingDirectory(this, 
        "Sélection du répertoire de Z3",
        QDir::currentPath(),
        QFileDialog::ShowDirsOnly);

    // test de la présence des fichiers indispensables pour Z3
    this->isZ3Present = this->checkZ3Path(z3Path);
    if (this->isZ3Present) 
    {
        this->sendToLogWindow("Répertoire de Z3 : OK");
        this->setButtonOk(GUI_selectZ3Button);
    } 
    else this->setButtonError(GUI_selectZ3Button);
}

void FUZZWIN_GUI::on_GUI_selectInitialInputButton_clicked()
{
    QString filename = QFileDialog::getOpenFileName(this, 
        "Sélection de l'entrée initiale",
        QDir::currentPath());

    if (filename.isEmpty()) this->setButtonOk(GUI_selectInitialInputButton);
    else 
    {
        GUI_initialInput->setText(filename);
        this->setButtonError(GUI_selectInitialInputButton);
    }
}

void FUZZWIN_GUI::on_GUI_selectTargetButton_clicked()
{
    QString filename = QFileDialog::getOpenFileName(this, 
        "Sélection de l'exécutable cible",
        QDir::currentPath(),
        "Exécutables (*.exe)");

    if (filename.isEmpty()) this->setButtonError(GUI_selectTargetButton);
    else 
    {
        // conversion QString -> encodage local (avec prise en charge des accents..)
        std::string filenameLocal(filename.toLocal8Bit().constData());

        switch (getKindOfExecutable(filenameLocal))
        {
        case SCS_64BIT_BINARY:
            if (pGlobals->osType < BEGIN_HOST_64BITS)
            {
                this->sendToLogWindow("Exécutable 64 bits non supporté sur OS 32bits");
                this->setButtonError(GUI_selectTargetButton);
            }
            else 
            {
                this->sendToLogWindow("Exécutable 64 bits sélectionné");
                GUI_targetPath->setText(filename);
            }
            break;

        case SCS_32BIT_BINARY:
            this->sendToLogWindow("Exécutable 32bits sélectionné");
            this->setButtonOk(GUI_selectTargetButton);
            GUI_targetPath->setText(filename);
            break;

        default:
            this->sendToLogWindow("Fichier cible incompatible");
            this->setButtonError(GUI_selectTargetButton);
            break;
        }
    }
}

void FUZZWIN_GUI::on_GUI_selectResultsDirButton_clicked()
{
    QString dirPath = QFileDialog::getExistingDirectory(this, 
        "Sélection du répertoire de résultats",
        QDir::currentPath(),
        QFileDialog::ShowDirsOnly);

    if (dirPath.isEmpty()) return;
    else
    {
        QDir resultsDir(dirPath);
        if (resultsDir.exists())
        {
            QMessageBox::StandardButton result = QMessageBox::question(
                this, "Confirmation de l'utilisation du dossier",
                "Le répertoire suivant existe déjà.\n"
                + dirPath + "\n"
                "Voulez-vous effacer son contenu avant exécution ?",
                QMessageBox::Ok | QMessageBox::No | QMessageBox::Abort,
                QMessageBox::No);
            
            // Abandon => aucun changement
            if      (QMessageBox::Abort == result) return;
            // OK => effacement du dossier
            else if (QMessageBox::Ok    == result)
            {
                QDir directory(dirPath);
                bool isSuccess = directory.removeRecursively(); // nouveauté Qt 5.0
                isSuccess &= directory.mkpath("."); 

                if (isSuccess) // tout s'est bien passé
                {
                    this->sendToLogWindow("Effacement du dossier de résultats -> Ok");
                    this->setButtonOk(GUI_selectResultsDirButton);
                    GUI_resultsDir->setText(dirPath);
                    
                }
                else
                {
                    this->sendToLogWindow("Effacement du dossier de résultats -> Erreur");
                    this->setButtonError(GUI_selectResultsDirButton);
                    GUI_resultsDir->clear();
                }

            }
            // No => dossier inchangé
            else
            {
                this->sendToLogWindow("Dossier de résultats sélectionné (pas d'effacement)");
                this->setButtonOk(GUI_selectResultsDirButton);
                GUI_resultsDir->setText(dirPath);
            }
        }
    }
}
