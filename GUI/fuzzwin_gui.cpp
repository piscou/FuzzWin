#include "fuzzwin_gui.h"

/****** CLASSE GUI *********/

FUZZWIN_GUI::FUZZWIN_GUI() : QMainWindow(nullptr),
    _env(QProcessEnvironment::systemEnvironment()),           // environnement de l'application
    _fixedSizePolicy(QSizePolicy::Fixed, QSizePolicy::Fixed), // hauteur et largeur fixes
    _startButtonStatus(STATUS_START)   // Bouton "Start" initialisé avec le texte "Start"
{  
    /***********************************/
    /***** INITIALISATION DE LA GUI ****/
    /***********************************/

    // création du widget central
    _centralWidget = new QWidget(this);
    _centralWidget->setSizePolicy(_fixedSizePolicy);

    // création des groupes d'objets et du menu
    initGroupConfiguration();
    initGroupSession();
    initGroupOptions();
    initButtons();
    initGroupResultats();
    initLines();

    // positionnement des objets sur une grille H=6, V=4
    _gCentralLayout = new QGridLayout(_centralWidget);
    _gCentralLayout->setContentsMargins(11, 11, 11, 11);
    _gCentralLayout->addWidget(_groupConfiguration, 0, 0, 1, 2);
    _gCentralLayout->addWidget(_groupSession,       1, 0, 1, 2);
    _gCentralLayout->addWidget(_groupOptions,       2, 0, 1, 2);

    _gCentralLayout->addWidget(_startButton,        3, 0, 1, 1);
    _gCentralLayout->addWidget(_stopButton,         4, 0, 1, 1);
    _gCentralLayout->addWidget(_quitButton,         3, 1, 1, 1);
    _gCentralLayout->addWidget(_aboutButton,        4, 1, 1, 1);

    _gCentralLayout->addWidget(_Vline,          0, 2, 6, 1);    
    _gCentralLayout->addWidget(_groupResultats, 0, 3, 6, 1);

    // affectation à la fenetre et redimension
    this->setCentralWidget(_centralWidget);
    this->resize(800, 500);

    // connexion signaux/slots
    this->connectSignalsToSlots();
}

int FUZZWIN_GUI::testConfig()
{
    // test de la compatibilité de l'OS
    _osType = getNativeArchitecture();
    if (HOST_UNKNOWN == _osType)
    {
        QMessageBox::critical(nullptr, "Erreur", "OS non supporté", QMessageBox::Close);
        return (EXIT_FAILURE);
    }

    // test de la présence des DLL du pintool
    QString exePath = QApplication::applicationDirPath();
    _pintool_X86    = QDir::toNativeSeparators(exePath + "/../pintool/fuzzwinX86.dll");
    if (!QFile::exists(_pintool_X86))
    {
        QMessageBox::critical(nullptr, "Erreur", "pintool FuzzWin 32bits absent");
        return (EXIT_FAILURE);
    }

    // pintool 64bits si besoin (mode 64 bits)
    if (_osType >= BEGIN_HOST_64BITS) 
    {
        _pintool_X64 = QDir::toNativeSeparators(exePath + "/../pintool/fuzzwinX64.dll");
        if (!QFile::exists(_pintool_X64))
        {
            QMessageBox::critical(nullptr, "Erreur", "pintool FuzzWin 64bits absent");
            return (EXIT_FAILURE);
        }
    }

    // présence "normale" de PIN = via variable d'environnement "PIN_ROOT"
    QString pinPath = _env.value("PIN_ROOT");
    
    // si la variable est renseignée : test de la présence des fichiers de PIN
    if (! pinPath.isEmpty())  checkPinPath(pinPath);

    // présence "normale" de Z3 = via variable d'environnement "Z3_ROOT"
    QString z3Path = _env.value("Z3_ROOT"); 
    
    // si la variable est renseignée : test de la présence des fichiers de Z3
    if (! z3Path.isEmpty()) checkZ3Path(z3Path);

    return (EXIT_SUCCESS);
}

void FUZZWIN_GUI::initGroupConfiguration()
{
    _groupConfiguration = new QGroupBox("Configuration", _centralWidget);
    _groupConfiguration->setSizePolicy(_fixedSizePolicy);

    _selectPin = new FuzzwinButton(_groupConfiguration, "Dossier de PIN");
    _selectZ3  = new FuzzwinButton(_groupConfiguration, "Dossier de Z3");

    _hLayout1 = new QHBoxLayout(_groupConfiguration);
    _hLayout1->addWidget(_selectPin);
    _hLayout1->addWidget(_selectZ3);
}

void FUZZWIN_GUI::initGroupSession() 
{
    _groupSession = new QGroupBox("Session", _centralWidget);
    _groupSession->setSizePolicy(_fixedSizePolicy);
    
    _selectInitialInput = new FuzzwinButton(_groupSession, "Entrée initiale");
    _selectTarget       = new FuzzwinButton(_groupSession, "Exécutable cible");
    _selectResultsDir   = new FuzzwinButton(_groupSession, "Dossier de résultats");

    _vLayout1 = new QVBoxLayout(_groupSession);
    _vLayout1->setContentsMargins(11, 11, 11, 11);
    _vLayout1->addWidget(_selectInitialInput);
    _vLayout1->addWidget(_selectTarget);
    _vLayout1->addWidget(_selectResultsDir);
}
   
void FUZZWIN_GUI::initGroupOptions()
{
    _groupOptions = new QGroupBox("Options", _centralWidget);
    _groupOptions->setSizePolicy(_fixedSizePolicy);

    _scoreEnabled          = new QCheckBox("Calcul du Score",               _groupOptions);
    _bytesToTaintEnabled   = new QCheckBox("Octets à marquer",              _groupOptions);
    _maxConstraintsEnabled = new QCheckBox("Nombre maximal de contraintes", _groupOptions);
    _maxTimeEnabled        = new QCheckBox("Temps maximal",                 _groupOptions);    
    _verboseEnabled        = new QCheckBox("Mode verbeux",                  _groupOptions);
    _keepfilesEnabled      = new QCheckBox("Garder fichiers temporaires",   _groupOptions);
    _traceOnlyEnabled      = new QCheckBox("Trace seulement",               _groupOptions); 
    _timeStampEnabled      = new QCheckBox("Horodatage des logs",           _groupOptions);
    _hashFilesEnabled      = new QCheckBox("Hash des entrées générées",     _groupOptions);
    
    _logAsmEnabled         = new QCheckBox("Log de déssasemblage", _groupOptions); 
    _logTaintEnabled       = new QCheckBox("Log de marquage",      _groupOptions);
    _maxConstraints        = new QSpinBox(_groupOptions);
    _maxTime               = new QTimeEdit(_groupOptions);
    _listOfBytesToTaint    = new QLineEdit(_groupOptions);

    _maxConstraints->setEnabled(false);     // tant que la case n'est pas cochée
    _maxTime->setEnabled(false);            // tant que la case n'est pas cochée
    _listOfBytesToTaint->setEnabled(false); // tant que la case n'est pas cochée

    _gLayout1 = new QGridLayout(_groupOptions);
    _gLayout1->setContentsMargins(11, 11, 11, 11);
    _gLayout1->addWidget(_scoreEnabled,          0, 0, 1, 1);   
    _gLayout1->addWidget(_maxConstraintsEnabled, 1, 0, 1, 1);
    _gLayout1->addWidget(_maxConstraints,        2, 0, 1, 1);
    _gLayout1->addWidget(_maxTimeEnabled,        3, 0, 1, 1);
    _gLayout1->addWidget(_maxTime,               4, 0, 1, 1);
    _gLayout1->addWidget(_bytesToTaintEnabled,   5, 0, 1, 1);
    _gLayout1->addWidget(_listOfBytesToTaint,    6, 0, 1, 1);
    _gLayout1->addWidget(_logAsmEnabled,         7, 0, 1, 1);
    _gLayout1->addWidget(_logTaintEnabled,       8, 0, 1, 1);
    _gLayout1->addWidget(_verboseEnabled,        9, 0, 1, 1);    
    _gLayout1->addWidget(_keepfilesEnabled,      10, 0, 1, 1);
    _gLayout1->addWidget(_traceOnlyEnabled,      11, 0, 1, 1);
    _gLayout1->addWidget(_timeStampEnabled,      12, 0, 1, 1);
    _gLayout1->addWidget(_hashFilesEnabled,      13, 0, 1, 1);
}
    
void FUZZWIN_GUI::initGroupResultats()
{
    _groupResultats = new QGroupBox("Résultats", _centralWidget);

    _labelInitialInput = new QLabel("Entrée initiale",_groupResultats);
    _labelInitialInput->setSizePolicy(_fixedSizePolicy);
    _initialInput      = new InitialInputLineEdit(_groupResultats);
    _initialInput->setSizePolicy(QSizePolicy::MinimumExpanding, QSizePolicy::Fixed);
    _initialInput->setAcceptDrops(true);
    _initialInput->setDragEnabled(true);

    _labelTargetPath = new QLabel("Exécutable cible", _groupResultats);
    _labelTargetPath->setSizePolicy(_fixedSizePolicy);
    _targetPath      = new TargetPathLineEdit(_groupResultats);
    _targetPath->setSizePolicy(QSizePolicy::MinimumExpanding, QSizePolicy::Fixed);
    _targetPath->setAcceptDrops(true);
    _targetPath->setDragEnabled(true);

    _labelResultsDir  = new QLabel("Dossier de résultats", _groupResultats);
    _labelResultsDir->setSizePolicy(_fixedSizePolicy);
    _resultsDir       = new ResultsDirLineEdit(_groupResultats);
    _resultsDir->setSizePolicy(QSizePolicy::MinimumExpanding, QSizePolicy::Fixed);
    _resultsDir->setAcceptDrops(true);
    _resultsDir->setDragEnabled(true);
    
    _Tabs = new QTabWidget(_groupResultats);

    _logTab    = new QWidget();
    _logWindow = new QTextEdit(_logTab);
    // changement de la police => davantage "console"
    _logWindow->setFont(QFont("Lucida console", 8));
    _logWindow->setReadOnly(true);
    _hLayout2  = new QHBoxLayout(_logTab);
    _hLayout2->setContentsMargins(11, 11, 11, 11);
    _hLayout2->addWidget(_logWindow);
    _logWindow->setAcceptDrops(false);

    _entriesTab = new QWidget();    
    
    _inputsView = new QTreeView(_entriesTab);
    _inputsView->setFont(QFont("MS Shell Dlg", 8));
    _inputsView->setUniformRowHeights(true); // permet d'optimiser l'affichage
    _inputsView->setSortingEnabled(true);
    _inputsView->setAcceptDrops(false); 
    _inputsView->setIndentation(3); 
    _inputsView->setDragDropMode(QAbstractItemView::NoDragDrop);
    _inputsView->setEditTriggers(QAbstractItemView::NoEditTriggers);
    
    
    QStringList headerLabels;
    headerLabels << "Entrée" << "Contraintes marquées" << "Contraintes inversées" << "Code erreur";
    _inputsModel = new TreeModel(headerLabels, _entriesTab);
    _inputsView->setModel(_inputsModel);
    _inputsView->header()->setStretchLastSection(false); // pas d'étirement de la dernière colonne
    for (int i = 0 ; i < _inputsModel->columnCount() ; ++i)
    {
        _inputsView->resizeColumnToContents(i);
    }

    /// TEST POUR LA PARTIE MODELE/VUE
#if 0
    QList<int> firstInputData;
    firstInputData << 0 << 55 << 44 << 1;

    // nouvelle ligne
    _inputsModel->insertRow(0);
    QModelIndex modelIndex = _inputsModel->index(0, 0);
    _inputsModel->setData(modelIndex, "input0");

    QModelIndexList a = _inputsModel->match(_inputsModel->index(0, 0),Qt::DisplayRole, "input1", 1, Qt::MatchRecursive);
    QModelIndexList b = _inputsModel->match(_inputsModel->index(0, 0),Qt::DisplayRole, "input0", 1, Qt::MatchRecursive);

    // essai ligne fille
    _inputsModel->insertRows(0, 1, _inputsModel->index(0, 0));
    QModelIndex childIndex = _inputsModel->index(0, 0, _inputsModel->index(0, 0));
    for (int column = 0 ; column < 4 ; ++column)
    {
        int value = firstInputData.at(column);
        QModelIndex columnIndex = _inputsModel->index(0, column, _inputsModel->index(0, 0));
        _inputsModel->setData(columnIndex, QVariant(value));
    }
#endif

    _labelFaultsFound = new QLabel("Nombre de fautes trouvées", _groupResultats);
    _faultsFound      = new QSpinBox(_groupResultats);
    _faultsFound->setReadOnly(true);
    _faultsFound->setAlignment(Qt::AlignRight|Qt::AlignTrailing|Qt::AlignVCenter);
    _faultsFound->setButtonSymbols(QAbstractSpinBox::NoButtons);    
    _faultsFound->setSizePolicy(_fixedSizePolicy);

    _saveLogButton = new QPushButton("Sauvegarder Log");
    _saveLogButton->setSizePolicy(_fixedSizePolicy);
    _saveLogButton->setMinimumWidth(150);

    _saveConfigButton = new QPushButton("Sauvegarder configuration");
    _saveConfigButton->setSizePolicy(_fixedSizePolicy);
    _saveConfigButton->setMinimumWidth(150);

    _vLayout2     = new QVBoxLayout(_entriesTab);
    _vLayout2->setContentsMargins(11, 11, 11, 11);
    _vLayout2->addWidget(_inputsView);

    _Tabs->addTab(_logTab,     "Log");
    _Tabs->addTab(_entriesTab, "Entrées");    
    _Tabs->setCurrentIndex(0);

    _gLayout2 = new QGridLayout(_groupResultats);
    _gLayout2->setContentsMargins(11, 11, 11, 11);    

    _gLayout2->addWidget(_labelInitialInput, 0, 0, 1, 1);
    _gLayout2->addWidget(_initialInput,      0, 1, 1, 3);

    _gLayout2->addWidget(_labelTargetPath,   1, 0, 1, 1);
    _gLayout2->addWidget(_targetPath,        1, 1, 1, 3);    

    _gLayout2->addWidget(_labelResultsDir,   2, 0, 1, 1);
    _gLayout2->addWidget(_resultsDir,        2, 1, 1, 3);
    
    _gLayout2->addWidget(_Tabs,              3, 0, 1, 4); 
    
    _gLayout2->addWidget(_labelFaultsFound,  4, 0, 1, 1);
    _gLayout2->addWidget(_faultsFound,       4, 1, 1, 1);
    _gLayout2->addWidget(_saveLogButton,     4, 2, 1, 1, Qt::AlignCenter);
    _gLayout2->addWidget(_saveConfigButton,  4, 3, 1, 1, Qt::AlignCenter);
}
    
void FUZZWIN_GUI::initButtons()
{
    _startButton       = new QPushButton("Démarrer",       _centralWidget);
    _stopButton        = new QPushButton("Arreter",        _centralWidget);
    _quitButton        = new QPushButton("Quitter",        _centralWidget); 
    _aboutButton       = new QPushButton("A propos...",    _centralWidget);

    _startButton->setMinimumWidth(100);
    _stopButton->setMinimumWidth(100);
    _quitButton->setMinimumWidth(100);
    _aboutButton->setMinimumWidth(100);  

    _startButton->setSizePolicy(_fixedSizePolicy);
    _stopButton->setSizePolicy(_fixedSizePolicy);
    _quitButton->setSizePolicy(_fixedSizePolicy);
    _aboutButton->setSizePolicy(_fixedSizePolicy);

    // boutons désactivés à la construction
    _startButton->setEnabled(false);   
    _stopButton->setEnabled(false);
}

void FUZZWIN_GUI::initLines()
{    
    _Vline = new QFrame(_centralWidget);
    _Vline->setFrameShape(QFrame::VLine);
    _Vline->setFrameShadow(QFrame::Sunken);
}

void FUZZWIN_GUI::connectSignalsToSlots()
{
    // cases à cocher qui activent des champs
    connect(_bytesToTaintEnabled,   SIGNAL(clicked(bool)), _listOfBytesToTaint, SLOT(setEnabled(bool)));
    connect(_maxConstraintsEnabled, SIGNAL(clicked(bool)), _maxConstraints,     SLOT(setEnabled(bool)));
    connect(_maxTimeEnabled,        SIGNAL(clicked(bool)), _maxTime,            SLOT(setEnabled(bool)));
    
    // bouton quitter => confirmation avant de le faire
    connect(_quitButton, SIGNAL(clicked(bool)), this, SLOT(quitFuzzwin()));
    
    // boutons de sélection de la GUI pour PIN, Z3 et les données de session
    connect(_selectPin,          SIGNAL(clicked()),  this, SLOT(selectPin_clicked()));
    connect(_selectZ3,           SIGNAL(clicked()),  this, SLOT(selectZ3_clicked()));
    connect(_selectInitialInput, SIGNAL(clicked()),  this, SLOT(selectInitialInput_clicked()));
    connect(_selectTarget,       SIGNAL(clicked()),  this, SLOT(selectTarget_clicked()));
    connect(_selectResultsDir,   SIGNAL(clicked()),  this, SLOT(selectResultsDir_clicked()));
   
    // signal de modification de status d'un bouton => vérifier l'ensemble
    connect(_selectPin,          SIGNAL(buttonStatusChanged()),  this, SLOT(testButtons()));
    connect(_selectZ3,           SIGNAL(buttonStatusChanged()),  this, SLOT(testButtons()));
    connect(_selectInitialInput, SIGNAL(buttonStatusChanged()),  this, SLOT(testButtons()));
    connect(_selectTarget,       SIGNAL(buttonStatusChanged()),  this, SLOT(testButtons()));
    connect(_selectResultsDir,   SIGNAL(buttonStatusChanged()),  this, SLOT(testButtons()));

    // signaux émis par le drop de fichiers sur les lignes de texte
    connect(_targetPath,    SIGNAL(newTargetDropped(QString)),   this,   SLOT(checkKindOfExe(QString)));
    connect(_resultsDir,    SIGNAL(newDirDropped   (QString)),   this,   SLOT(checkDir(QString)));
    connect(_initialInput,  SIGNAL(conformData()),  _selectInitialInput, SLOT(setButtonOk()));
    
    // autoscroll de la fenetre de log
    connect(_logWindow,     SIGNAL(textChanged()), this,   SLOT(autoScrollLogWindow()));
    // sauvegarde des logs
    connect(_saveLogButton,    SIGNAL (clicked()), this, SLOT(saveLog_clicked()));
    connect(_saveConfigButton, SIGNAL (clicked()), this, SLOT(saveConfig_clicked()));

    // bouton Go/resume (traitement selon le texte du bouton)
    connect(_startButton,  SIGNAL(clicked()), this, SLOT(start_clicked()));    
    connect(_stopButton,   SIGNAL(clicked()), this, SLOT(stop_clicked()));
}

void FUZZWIN_GUI::closeEvent(QCloseEvent *e)
{
    // comme si on cliquait sur le bouton
    this->quitFuzzwin();
    // si la fonction revient ici, c'est qu'il y a eu abandon => ignorer l'event
    e->ignore();
}

void FUZZWIN_GUI::log(const QString &msg)
{
    // s'assurer que le curseur est bien à la dernière ligne avant insertion...
    _logWindow->moveCursor(QTextCursor::End);
    _logWindow->insertHtml(msg);
}

void FUZZWIN_GUI::selectPin_clicked()
{
    // récupération du dossier où se trouve PIN
    QString pinPath = QFileDialog::getExistingDirectory(this, 
        "Sélection du répertoire de PIN",
        QDir::currentPath(),
        QFileDialog::ShowDirsOnly);

    if (pinPath.isNull()) return;   // bouton "cancel" sélectionné

    // test de la présence des fichiers indispensables pour PIN
    checkPinPath(pinPath);
}

void FUZZWIN_GUI::selectZ3_clicked()
{
    QString z3Path = QFileDialog::getExistingDirectory(this, 
        "Sélection du répertoire de Z3",
        QDir::currentPath(),
        QFileDialog::ShowDirsOnly);

    if (z3Path.isNull()) return;    // bouton "cancel" sélectionné
    
    checkZ3Path(z3Path);
}

void FUZZWIN_GUI::selectInitialInput_clicked()
{
    QString filename = QFileDialog::getOpenFileName(this, 
        "Sélection de l'entrée initiale",
        QDir::currentPath());

    // si non Null => bouton Ok choisi, donc traiter
    if (!filename.isNull()) 
    {
        _initialInput->setText(filename);
        _initialInput->setCursorPosition(0);
        _selectInitialInput->setButtonOk();
    }
}

void FUZZWIN_GUI::selectTarget_clicked()
{
    QString filename = QFileDialog::getOpenFileName(this, 
        "Sélection de l'exécutable cible",
        QDir::currentPath(),
        "Exécutables (*.exe)");

    // si non Null => bouton Ok choisi, donc traiter
    if (!filename.isNull()) checkKindOfExe(filename);
}

void FUZZWIN_GUI::selectResultsDir_clicked()
{
    QString dirPath = QFileDialog::getExistingDirectory(this, 
        "Sélection du répertoire de résultats",
        QDir::currentPath(),
        QFileDialog::ShowDirsOnly);

    // chaine nulle => annulation de la boite de dialogue, sinon traitement
    if (!dirPath.isNull()) checkDir(dirPath); 
}

void FUZZWIN_GUI::quitFuzzwin()
{
    QMessageBox::StandardButton result = QMessageBox::warning(this,
        "Confirmation", "Voulez vous vraiment quitter ?",
        QMessageBox::Yes | QMessageBox::Abort, QMessageBox::Abort);

    if (QMessageBox::Yes == result) QApplication::quit();
}

void FUZZWIN_GUI::testButtons()
{
    // si tout est au vert => activer bouton, sinon désactiver
    bool globalStatus = _selectPin->getStatus() 
                      & _selectZ3->getStatus() 
                      & _selectInitialInput->getStatus()
                      & _selectTarget->getStatus()
                      & _selectResultsDir->getStatus();
    
    _startButton->setEnabled(globalStatus);
}

void FUZZWIN_GUI::start_clicked()
{ 
    /*************************************************/ 
    /*  "GO" -->>--> "PAUSE" -->>-> "RESUME" ->>-+   */
    /*                  |                        |   */
    /*                  +----------<<<-----------+   */
    /*************************************************/

    switch (_startButtonStatus) // état actuel du bouton
    {
    case STATUS_START:     
        this->startSession();           // démarrage de l'algorithme
        _stopButton->setEnabled(true);  // activer le bouton "Stop"
        // changement du status du bouton "start" -> "pause", et activation du bouton "stop"
        _startButton->setText("Pause");
        _startButtonStatus = STATUS_PAUSE;
        _stopButton->setEnabled(true);
        break;
    case STATUS_PAUSE:  
        emit pauseAlgorithm();          // envoyer un message de pause à l'algo.     
        // désactiver les boutons tant que l'algorithme n'a pas été mis en pause
        _startButton->setDisabled(true);
        _stopButton->setDisabled(true);
        break;
    case STATUS_RESUME: 
        // relance de l'algorithme
        emit launchAlgorithm();          // envoyer un message de pause à l'algo. 
        // session reprise => afficher le texte "pause" et fixer le status associé
        _startButton->setText("Pause");
        _startButtonStatus = STATUS_PAUSE;
        break;
    }
}

void FUZZWIN_GUI::startSession()
{
    /*********************************/
    /** ARGUMENTS POUR L'ALGORITHME **/
    /*********************************/

    // revérifier que le dossier de résultats est bien vide
    // surtout utile lorsqu'on démarre une nouvelle session juste apres la précédente
    QString resultsDir = _resultsDir->text();
    this->checkDir(resultsDir);

    // nouvelle structure pour les arguments
    ArgumentsForAlgorithm args;
    ZeroMemory(&args, sizeof(args));

    args._resultsDir     = std::string(qPrintable(QDir::toNativeSeparators(_resultsDir->text())));
    args._firstInputPath = std::string(qPrintable(QDir::toNativeSeparators(_initialInput->text())));
    args._targetPath     = std::string(qPrintable(QDir::toNativeSeparators(_targetPath->text())));
    args._z3Path         = std::string(qPrintable(QDir::toNativeSeparators(_z3Path))); 

    // récupération des options pour l'algorithme  
    args._computeScore   = _scoreEnabled->isChecked();
    args._verbose        = _verboseEnabled->isChecked();
    args._keepFiles      = _keepfilesEnabled->isChecked();
    args._timeStamp      = _timeStampEnabled->isChecked();
    args._hashFiles      = _hashFilesEnabled->isChecked();
    args._traceOnly      = _traceOnlyEnabled->isChecked();

    // récupération des options pour le pintool
    // options de ligne de commande pour le pintool en mode "marquage"
    std::string cmdLineOptions("-option taint"); 
    cmdLineOptions += " -os " + std::to_string(_osType);
    
    if (_maxConstraintsEnabled->isChecked())
    {
        cmdLineOptions += " -maxconstraints " + std::to_string(_maxConstraints->value());
    }
    if (_maxTimeEnabled->isChecked())
    {
        args._maxExecutionTime = (60 * _maxTime->time().minute()) + _maxTime->time().second();
        cmdLineOptions += " -maxtime " + std::to_string(args._maxExecutionTime);
    }
    if (_bytesToTaintEnabled->isChecked())
    {
         cmdLineOptions += " -range " + std::string(qPrintable(_listOfBytesToTaint->text()));
    }

    if (_logAsmEnabled->isChecked())   cmdLineOptions += " -logasm" ;
    if (_logTaintEnabled->isChecked()) cmdLineOptions += " -logtaint" ;

    
    /*****************************************************************/
    /** CREATION DE L'ALGORITHME ET AFFECTATION A UN NOUVEAU THREAD **/
    /*****************************************************************/
    _pFuzzwinThread = new QThread;  

    // création de l'objet "algorithme" et finalisation de l'algo
    _pFuzzwinAlgo = new FuzzwinAlgorithm_GUI(_osType, &args);
    
    // création des outils internes et externes et dernieres initialisations
    int result = _pFuzzwinAlgo->finalizeInitialization(
        std::string(qPrintable(_pinPath_X86)),
        std::string(qPrintable(_pinPath_X64)),
        std::string(qPrintable(_pintool_X86)),
        std::string(qPrintable(_pintool_X64)),
        cmdLineOptions);

    if (EXIT_FAILURE == result)
    { 
        delete (_pFuzzwinThread);
        delete (_pFuzzwinAlgo);
        return;
    }

    // affectation de l'algo au thread
    _pFuzzwinAlgo->moveToThread(_pFuzzwinThread);
    // connections des signaux et slots
    this->connectGUIToAlgo();

    // C'EST PARTI MON KIKI : démarrage du thread, et signel de lancement envoyé à l'algorithme
    _pFuzzwinThread->start();
    emit launchAlgorithm();
}

void FUZZWIN_GUI::connectGUIToAlgo()
{
    // connection des signaux/slots entre la GUI et l'algorithme
    
    // SENS GUI->ALGO
    connect(this, SIGNAL(launchAlgorithm()), _pFuzzwinAlgo, SLOT(wrapStartFromGui()));
    connect(this, SIGNAL(pauseAlgorithm()),  _pFuzzwinAlgo, SLOT(wrapPauseFromGui()), Qt::DirectConnection);
    connect(this, SIGNAL(stopAlgorithm()),   _pFuzzwinAlgo, SLOT(wrapStopFromGui()),  Qt::DirectConnection);
   
    // SENS ALGO->GUI
    connect(_pFuzzwinAlgo, SIGNAL(sendToGui(QString)),      this,     SLOT(log(QString)),    Qt::QueuedConnection);
    connect(_pFuzzwinAlgo, SIGNAL(sendAlgorithmFinished()), this,     SLOT(algoFinished()),  Qt::QueuedConnection);
    connect(_pFuzzwinAlgo, SIGNAL(sendTraceOnlyFinished()), this,     SLOT(algoTraceOnlyFinished()),  Qt::QueuedConnection);
    
    connect(_pFuzzwinAlgo, SIGNAL(pauseIsEffective()),      this,     SLOT(sessionPaused()), Qt::QueuedConnection);
    connect(_pFuzzwinAlgo, SIGNAL(setFaultsFound(int)), _faultsFound, SLOT(setValue(int)),   Qt::QueuedConnection);
    
    // SIGNZL FIN DE THREAD
    connect(_pFuzzwinThread, SIGNAL(finished()), _pFuzzwinAlgo, SLOT(deleteLater()));
}

// slot appelé par un signal de l'algorithme, lorsque celui-ci a été mis en pause
void FUZZWIN_GUI::sessionPaused()
{
    // session mise en pause => afficher le texte "Resume" et fixer le status associé
    _startButton->setText("Resume");
    _startButtonStatus = STATUS_RESUME;
    // activer les boutons
    _startButton->setEnabled(true);
    _stopButton->setEnabled(true);
}

void FUZZWIN_GUI::stop_clicked()
{
    emit stopAlgorithm();
    
    // activer le bouton "Go", et désactiver le "Stop"
    _startButton->setEnabled(true);
    _startButton->setText("Démarrer");
    _startButtonStatus = STATUS_START;
    _stopButton->setDisabled(true);
     
    _pFuzzwinThread->terminate();
    _pFuzzwinThread->wait();

    delete (_pFuzzwinThread);
}

void FUZZWIN_GUI::saveLog_clicked()
{
    QString filter = "*.log";
    // sauvegarde du contenu du widget '_logWindow' dans un fichier
    QString filename = QFileDialog::getSaveFileName(this, 
        "Sélection du nom de fichier", 
        QDir::currentPath(), 
        "Fichier de log (*.log)", 
        &filter);

    if (filename.isNull()) return;  // bouton 'annuler' 

    QFile logFile(filename);
    if (!logFile.open(QIODevice::WriteOnly | QIODevice::Text))   return; // erreur d'ouverture

    QTextStream out(&logFile);
    out << _logWindow->toPlainText();
    logFile.close();
}

void FUZZWIN_GUI::saveConfig_clicked()
{
    // TEST POUR LA PARTIE HEXVIEW
#if 0
    QHexView *test = new QHexView;
    QFile *file = new QFile(_pintool_X86);
    file->open(QIODevice::ReadOnly);
        
    test->setData(file);
    test->show();
#endif
    
}

void FUZZWIN_GUI::checkKindOfExe(const QString &path)
{
    // conversion QString -> encodage local 
    std::string filenameLocal(qPrintable(path));

    switch (getKindOfExecutable(filenameLocal))
    {
    case SCS_64BIT_BINARY:
        if (_osType < BEGIN_HOST_64BITS)
        {
            log(TEXTRED("Exécutable 64 bits non supporté sur OS 32bits") + LINEFEED);
            _selectTarget->setButtonError();
        }
        else 
        {
            log(TEXTGREEN("Exécutable 64 bits sélectionné") + LINEFEED);
            _selectTarget->setButtonOk();
            _targetPath->setText(path);
        }
        break;

    case SCS_32BIT_BINARY:
        log(TEXTGREEN("Exécutable 32bits sélectionné") + LINEFEED);
        _selectTarget->setButtonOk();
        _targetPath->setText(path);
        break;

    default:
        log(TEXTRED("Exécutable cible incompatible") + LINEFEED);
        _selectTarget->setButtonError();
        break;
    }
    _targetPath->setCursorPosition(0);
}

void FUZZWIN_GUI::checkPinPath(QString path)
{
    bool goodNess = true; // on considere que tout est ok à priori. 1 seul false et c'est rouge

    // ajout du séparateur, si non présent
    if (!(path.endsWith('/') || path.endsWith('\\')))
    {
        path.append(QDir::separator());
    }

    // modules 32 bits 
    _pinPath_X86          = QDir::toNativeSeparators(path + "ia32/bin/pin.exe");
    QString pin_X86_VmDll = QDir::toNativeSeparators(path + "ia32/bin/pinvm.dll");

    // test de la présence des fichiers adéquats
    if (!QFile::exists(_pinPath_X86))
    {
        this->log(TEXTRED("exécutable PIN 32bits absent") + LINEFEED);

        goodNess &= false;
    }
    if (!QFile::exists(pin_X86_VmDll))
    {
        this->log(TEXTRED("librairie PIN_VM 32bits absente") + LINEFEED);
        goodNess &= false;
    }

    // OS 64 bits : présence obligatoire des modules 64bits
    if (_osType >= BEGIN_HOST_64BITS) 
    {
        // modules 64 bits
        _pinPath_X64          = QDir::toNativeSeparators(path + "intel64/bin/pin.exe");
        QString pin_X64_VmDll = QDir::toNativeSeparators(path + "intel64/bin/pinvm.dll");
    
        if (!QFile::exists(_pinPath_X64))
        {
            log(TEXTRED("exécutable PIN 64bits absent") + LINEFEED);
            goodNess &= false;
        }
        if (!QFile::exists(pin_X64_VmDll))
        {
            log(TEXTRED("librairie PIN_VM 64bits absente") + LINEFEED);
            goodNess &= false;
        }
    }
    // si tout est bon (aucun 'false' rencontré) => bouton au vert
    // sinon bouton au rouge
    if (goodNess) 
    {
        log(TEXTGREEN("Répertoire de PIN : OK") + LINEFEED);
        _selectPin->setButtonOk();
    }
    else  _selectPin->setButtonError();
}

void FUZZWIN_GUI::checkZ3Path(QString path)
{
    // ajout du séparateur, si non présent
    if (!(path.endsWith('/') || path.endsWith('\\'))) path.append(QDir::separator());
    
    // chemin vers l'exécutable Z3
    path += "bin/z3.exe";
    
    // test de son existence
    if (QFile::exists(path))
    {
        log(TEXTGREEN("Répertoire de Z3 : OK") + LINEFEED);
        _z3Path = path;
        _selectZ3->setButtonOk();
    }
    else
    {
        log(TEXTRED("solveur Z3 absent") + LINEFEED);
        _selectZ3->setButtonError();
    } 
}

void FUZZWIN_GUI::updateInputView(CInput input)
{
   // QStringList data;
    //data << QString("%1").arg(input.getBound()) << input.getFileInfo().fileName();
//    QTreeWidgetItem *newInput = new QTreeWidgetItem(_listOfInputs, data);
  //  _listOfInputs->update();
}

void FUZZWIN_GUI::checkDir(const QString &path)
{
    QDir resultsDir(path);

    // demander confirmation d'effacement du contenu si non vide
    if (resultsDir.entryInfoList(QDir::NoDotAndDotDot|QDir::AllEntries).count() != 0)
    {
        QMessageBox::StandardButton result = QMessageBox::question(
            this, "Confirmer l'effacement du dossier ?",
            "Le répertoire suivant existe déjà : " + path + "\n"
            "Voulez-vous effacer son contenu avant exécution ?",
            QMessageBox::Ok | QMessageBox::No | QMessageBox::Abort,
            QMessageBox::No);
            
        // Abandon => aucun changement
        if      (QMessageBox::Abort == result) return ;
        // OK => effacement du dossier
        else if (QMessageBox::Ok    == result)
        {
            bool isSuccess = resultsDir.removeRecursively(); // nouveauté Qt 5.0
            isSuccess &= resultsDir.mkpath("."); 

            if (isSuccess) // tout s'est bien passé
            {
                log(TIMESTAMP + "Effacement du dossier de résultats -> Ok" + LINEFEED);
                _selectResultsDir->setButtonOk();
                _resultsDir->setText(path);     
            }
            else
            {
                log(TIMESTAMP + TEXTRED("Effacement du dossier de résultats -> Erreur") + LINEFEED);
                _selectResultsDir->setButtonError();
                _resultsDir->clear();
            }
        }
        // No => dossier inchangé
        else
        {
            log("Dossier de résultats sélectionné (pas d'effacement)");
            _selectResultsDir->setButtonOk();
            _resultsDir->setText(path);

        }
    }
    // dossier existant et vide
    else
    {
         log("Dossier de résultats sélectionné (vide)" + LINEFEED);
        _selectResultsDir->setButtonOk();
        _resultsDir->setText(path);
    }
    _resultsDir->setCursorPosition(0);
}

void FUZZWIN_GUI::algoFinished()
{
    int nbFautes = _faultsFound->value();
    if (!_faultsFound->value())
    {
        QMessageBox::information(this, "Fin de l'opération", "Aucune faute trouvée", QMessageBox::Ok);
    }
    else
    {
        QMessageBox::critical(this, "Fin de l'opération", 
            QString("%1 faute(s) trouvée(s)").arg(nbFautes), QMessageBox::Ok);
    }
    // arret de l'eventloop du thread
    _pFuzzwinThread->quit();
    _pFuzzwinThread->wait();   
    delete (_pFuzzwinThread);   

    // préparation pour une nouvelle session
    _startButton->setEnabled(true);
    _startButton->setText("Démarrer");
    _startButtonStatus = STATUS_START;
    _stopButton->setDisabled(true);
}

void FUZZWIN_GUI::algoTraceOnlyFinished()
{
    // arret de l'eventloop du thread
    _pFuzzwinThread->quit();
    _pFuzzwinThread->wait();   
    delete (_pFuzzwinThread);   

    // préparation pour une nouvelle session
    _startButton->setEnabled(true);
    _startButton->setText("Démarrer");
    _startButtonStatus = STATUS_START;
    _stopButton->setDisabled(true);
}

void FUZZWIN_GUI::autoScrollLogWindow()
{
    _logWindow->verticalScrollBar()->setValue(_logWindow->verticalScrollBar()->maximum());
}
