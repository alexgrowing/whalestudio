import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteLevelRecharacterisedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TrueTau

variable {D : D7} (E : NExpTied D)
  (τ' : ∀ i : D.ntw.Tw, ℕ → Bool → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)

abbrev Cond (D : D7) (i : D.ntw.Tw) (j k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) : Type :=
  PLift (1 ≤ j ∧ j ≤ D.R.m ∧ NX.AdmTw D i k Q ψ)

abbrev mtAt (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) :
    NX.MtVReal D i j b k Q ψ E.sgnT (E.Wt i j b) (E.rhoW i j b) (E.tauG i j b) :=
  E.mtV i j b k Q ψ c.down.1 c.down.2.1 c.down.2.2

def chiAt (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) :
    (mtAt E i j b k Q ψ c).J →* (NX.Kk D i k)ˣ :=
  (GlobalTheory.T.exists_definiteLevel_recharacterised D i j b k Q ψ E.sgnT (E.Wt i j b) (E.rhoW i j b) (E.tauG i j b) (τ' i j b) (mtAt E i j b k Q ψ c)).choose

abbrev Sp (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) : Type :=
  ↥(NX.TypeSpF D.host.E D.R.nV (NX.Kk D i k) (mtAt E i j b k Q ψ c).ρ (mtAt E i j b k Q ψ c).J (chiAt E τ' i j b k Q ψ c))

theorem fdSp (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (c : Cond D i j k Q ψ) :
    FiniteDimensional (NX.Kk D i k) (Sp E τ' i j b k Q ψ c) :=
  GlobalTheory.LevForms.typeSpF_finiteDimensional D.host.E D.R.nV (NX.Kk D i k) _ _ _
    (GlobalTheory.T.exists_definiteLevel_recharacterised D i j b k Q ψ E.sgnT (E.Wt i j b) (E.rhoW i j b) (E.tauG i j b) (τ' i j b)
      (mtAt E i j b k Q ψ c)).choose_spec.1

def MtN (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) : Type :=
  (c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c

section Inst

variable (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ)

instance acgMtN : AddCommGroup (MtN E τ' i j b k Q ψ) :=
  inferInstanceAs (AddCommGroup ((c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c))

instance modKMtN : Module (FractionRing (D.ntw.Ok i k)) (MtN E τ' i j b k Q ψ) :=
  inferInstanceAs (Module (NX.Kk D i k) ((c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c))

instance modOMtN : Module (D.ntw.Ok i k) (MtN E τ' i j b k Q ψ) :=
  Module.compHom (MtN E τ' i j b k Q ψ) (algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)))

instance towMtN : IsScalarTower (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)) (MtN E τ' i j b k Q ψ) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance fdMtN : FiniteDimensional (FractionRing (D.ntw.Ok i k)) (MtN E τ' i j b k Q ψ) := by
  haveI := fdSp E τ' i j b k Q ψ
  haveI : Subsingleton (Cond D i j k Q ψ) := ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩
  haveI : Finite (Cond D i j k Q ψ) := Finite.of_subsingleton
  exact (Module.Finite.pi : Module.Finite (NX.Kk D i k) ((c : Cond D i j k Q ψ) → Sp E τ' i j b k Q ψ c))

def evalN (c : Cond D i j k Q ψ) : MtN E τ' i j b k Q ψ ≃ₗ[NX.Kk D i k] Sp E τ' i j b k Q ψ c where
  toFun f := f c
  invFun x := fun _ => x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := funext fun c' => by cases c; cases c'; rfl
  right_inv _ := rfl

end Inst

section AnyExport

variable (ex : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw)
  (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (nth' : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw ex)

abbrev twX : TwNew D := ⟨D.ntw, ex, h0, nth', D.ntwbr, D.ntwbr_ind⟩

theorem gVal_twX (hps : ∀ (i : D.ntw.Tw) (b : Bool) (u : G0g D.nd), NX.psiUTot D i b u = NX.psiUTot (twX ex h0 nth').toD7 i b u)
    (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) :
    NX.gVal D i k b kv s red τ x = NX.gVal (twX ex h0 nth').toD7 i k b kv s red τ x := by
  unfold NX.gVal
  rw [hps]
  rfl

def realN (hps : ∀ (i : D.ntw.Tw) (b : Bool) (u : G0g D.nd), NX.psiUTot D i b u = NX.psiUTot (twX ex h0 nth').toD7 i b u)
    (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ)
    (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [mW : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀)
    (τ τ₁ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) (χ' : M.J →* (NX.Kk D i k)ˣ)
    (hχ : (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ₁ kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1))
    (r : ex.MtV i j b k Q ψ ≃ₗ[NX.Kk D i k] NX.TypeSpF D.host.E D.R.nV (NX.Kk D i k) M.ρ M.J χ') :
    @NX.MtVReal (twX ex h0 nth').toD7 i j b k Q ψ e W₀ _ mW ρ₀ τ₁ :=
  @NX.MtVReal.mk (twX ex h0 nth').toD7 i j b k Q ψ e W₀ _ mW ρ₀ τ₁ M.W M.acg M.mod M.fd M.ρ M.irr M.alg M.bc M.J χ' hχ.1 hχ.2.1
    M.QP M.QP_sub M.QP_cover M.QP_nconj M.DP M.DP_sub M.DP_cover M.DP_nconj M.sp M.sp_w M.redG M.J_mem
    (fun κ h => by
      have h1 := hχ.2.2 κ h
      simp only [gVal_twX ex h0 nth' hps] at h1
      exact h1) r

end AnyExport

section Generic

variable (Mt : ∀ (i : D.ntw.Tw) (_ : ℕ) (_ : Bool) (k : ℕ) (_ : Finset (PlE D.host))
    (_ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), Type)
  [∀ i j b k Q ψ, AddCommGroup (Mt i j b k Q ψ)] [∀ i j b k Q ψ, Module (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)]
  [∀ i j b k Q ψ, Module (D.ntw.Ok i k) (Mt i j b k Q ψ)]
  [∀ i j b k Q ψ, IsScalarTower (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)]
  [∀ i j b k Q ψ, FiniteDimensional (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)]

def exN : NExp D.R D.host D.what₂ D.LL0 D.nd D.ntw :=
  { D.nexp with
    delU := fun i Q M => GlobalTheory.GalChar.delU D.host D.ntw.cc (D.ntw.l i) Q M
    delU_unr := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).1
    delU_l := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.1
    delU_anti := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.1
    delU_open := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.1
    delU_res := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.1
    delU_conj := fun i => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.2.2.1
    MtV := Mt
    acgMt := fun _ _ _ _ _ _ => inferInstance
    modMtK := fun _ _ _ _ _ _ => inferInstance
    modMtO := fun _ _ _ _ _ _ => inferInstance
    towMt := fun _ _ _ _ _ _ => inferInstance
    fdMt := fun _ _ _ _ _ _ => inferInstance
    MtLat := fun i j b k Q ψ =>
      Submodule.span (D.ntw.Ok i k) (Set.range (Module.finBasis (FractionRing (D.ntw.Ok i k)) (Mt i j b k Q ψ)))
    MtLat_fg := fun _ _ _ _ _ _ => Submodule.fg_span (Set.finite_range _)
    MtLat_span := fun i j b k Q ψ => by rw [Submodule.span_span_of_tower, (Module.finBasis _ _).span_eq]
    thP := fun _ _ _ _ _ _ => 0 }

def thN : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw (exN Mt) := { D.nth with }

variable (nth' : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw (exN Mt))

abbrev twN : TwNew D := twX (exN Mt) D.nStage_trivialCharacter_coeff_eq nth'

theorem twN_univ : GlobalTheory.UnivChar.IsUnivChar (twN Mt nth').toD7.nexp := fun _ _ _ => rfl

theorem twN_psi : ∀ (i : D.ntw.Tw) (b : Bool) (u : G0g D.nd), NX.psiUTot D i b u = NX.psiUTot (twN Mt nth').toD7 i b u := fun _ _ _ => rfl

set_option maxHeartbeats 4000000 in

def expN (hτ : ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) →
      ((E.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        ((τ' i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)))
    (r : ∀ i j b k Q ψ (c : Cond D i j k Q ψ), Mt i j b k Q ψ ≃ₗ[NX.Kk D i k] Sp E τ' i j b k Q ψ c) :
    NExpTied (twN Mt nth').toD7 :=
  { E with
    acgWt := E.acgWt
    modWt := E.modWt
    fdWt := E.fdWt
    delU_cont := fun i Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host D.ntw.cc (D.ntw.l i)).2.2.2.1 Q M
    delU_ine := fun i Q M hQ P hP =>
      GlobalTheory.UnivCharIne.delU_ine (twN Mt nth').toD7 (twN_univ Mt nth') i Q M hQ P hP
    tauG := τ'
    tau_galois_first_character := fun i j b kv x u h1 h2 hl hu => (hτ i j b kv x h1 h2 hl).symm.trans (E.tau_galois_first_character i j b kv x u h1 h2 hl hu)
    mtV := fun i j b k Q ψ h1 h2 h =>
      @realN D (exN Mt) D.nStage_trivialCharacter_coeff_eq nth' (twN_psi Mt nth') i j b k Q ψ E.sgnT (E.Wt i j b) (E.acgWt i j b) (E.modWt i j b) (E.rhoW i j b)
        (E.tauG i j b) (τ' i j b) (mtAt E i j b k Q ψ ⟨⟨h1, h2, h⟩⟩) (chiAt E τ' i j b k Q ψ ⟨⟨h1, h2, h⟩⟩)
        (@GlobalTheory.T.exists_definiteLevel_recharacterised D i j b k Q ψ E.sgnT (E.Wt i j b) (E.acgWt i j b) (E.modWt i j b) (E.rhoW i j b) (E.tauG i j b) (τ' i j b)
          (mtAt E i j b k Q ψ ⟨⟨h1, h2, h⟩⟩)).choose_spec
        (r i j b k Q ψ ⟨⟨h1, h2, h⟩⟩) }

set_option maxHeartbeats 4000000 in

def sideN {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ)
    (hτ : ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) →
      ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        ((τ' i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)))
    (r : ∀ i j b k Q ψ (c : Cond D i j k Q ψ), Mt i j b k Q ψ ≃ₗ[NX.Kk D i k] Sp Bs.exp τ' i j b k Q ψ c) :
    SideB (twN Mt nth').toD7 ((twN Mt nth').cf cf) ((twN Mt nth').row Rw) low Pq ((twN Mt nth').rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp := expN Bs.exp τ' Mt nth' hτ r
    pq := fun i j b k Q ψ hj hj' hA => Bs.pq i j b k Q ψ hj hj' hA }

theorem twN_noOff (h : GlobalTheory.HeightCounting.SerCopy.NoOff D) : GlobalTheory.HeightCounting.SerCopy.NoOff (twN Mt nth').toD7 := fun i j b hn => h i j b hn

end Generic

theorem exists_trueTau : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ) (τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ), (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∃ N : TwNew D, N.tw = D.ntw ∧ (GlobalTheory.HeightCounting.SerCopy.NoOff D → GlobalTheory.HeightCounting.SerCopy.NoOff N.toD7) ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧ ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  intro D cf Rw low Pq S hL eig θ Bs τ hτ
  let τ' : ∀ i : D.ntw.Tw, ℕ → Bool → ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ :=
    fun i j b kv => (Units.map (GlobalTheory.SeriesTie.sideEmb D.ntw i b).toMonoidHom).comp (τ j kv)
  exact ⟨twN (MtN Bs.exp τ') (thN _), rfl, twN_noOff _ _, twN_univ _ _, sideN τ' _ _ Bs hτ (evalN Bs.exp τ'), τ,
    fun _ _ _ _ _ _ _ => rfl⟩

end GlobalTheory.TrueTau
