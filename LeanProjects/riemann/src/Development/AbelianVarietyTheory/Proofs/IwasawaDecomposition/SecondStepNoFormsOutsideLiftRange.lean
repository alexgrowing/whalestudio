import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.HeightCounting.CutOff

section Generic

def cut (p : Prop) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Submodule R M where
  carrier := {x | ¬ p → x = 0}
  add_mem' := fun {a b} ha hb h => by rw [ha h, hb h, add_zero]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c x hx h => by rw [hx h, smul_zero]

variable {p : Prop} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem cut_subsingleton (h : ¬ p) : Subsingleton ↥(cut p R M) := ⟨fun a b => Subtype.ext ((a.2 h).trans (b.2 h).symm)⟩

def cutEnd (p : Prop) (f : Module.End R M) : Module.End R ↥(cut p R M) :=
  f.restrict (p := cut p R M) (q := cut p R M) fun x hx h => by rw [hx h, map_zero]

theorem cutEnd_one : cutEnd p (1 : Module.End R M) = 1 := LinearMap.ext fun _ => rfl

theorem cutEnd_mul (f g : Module.End R M) : cutEnd p (f * g) = cutEnd p f * cutEnd p g := LinearMap.ext fun _ => rfl

def cutAct (p : Prop) {G : Type} [Group G] (ρ : G →* (M ≃ₗ[R] M)) : G →* (↥(cut p R M) ≃ₗ[R] ↥(cut p R M)) where
  toFun g := LinearEquiv.ofLinear (cutEnd p (ρ g).toLinearMap) (cutEnd p (ρ g).symm.toLinearMap)
    (LinearMap.ext fun x => Subtype.ext ((ρ g).apply_symm_apply x)) (LinearMap.ext fun x => Subtype.ext ((ρ g).symm_apply_apply x))
  map_one' := LinearEquiv.ext fun x => Subtype.ext (by
    change ρ 1 x = x
    rw [map_one]; rfl)
  map_mul' g h := LinearEquiv.ext fun x => Subtype.ext (by
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul]; rfl)

def cutTop (h : p) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : ↥(cut p R M) ≃ₗ[R] M where
  toFun x := x.1
  invFun x := ⟨x, fun hn => absurd h hn⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem cut_free [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M] : Module.Free R ↥(cut p R M) := by
  by_cases h : p
  · exact Module.Free.of_equiv (cutTop h R M).symm
  · haveI := cut_subsingleton (R := R) (M := M) h
    infer_instance

theorem cut_finite [Module.Finite R M] : Module.Finite R ↥(cut p R M) := by
  by_cases h : p
  · exact Module.Finite.equiv (cutTop h R M).symm
  · haveI := cut_subsingleton (R := R) (M := M) h
    infer_instance

theorem cut_split [IsDomain R] [Module.Free R M] [Module.Finite R M] [Module.Free R ↥(cut p R M)] [Module.Finite R ↥(cut p R M)]
    {K : Type} [CommRing K] (φ : R →+* K) (f : Module.End R M)
    (hf : ∃ s : Multiset K, (LinearMap.charpoly f).map φ = (s.map fun a => Polynomial.X - Polynomial.C a).prod) :
    ∃ s : Multiset K, (LinearMap.charpoly (cutEnd p f)).map φ = (s.map fun a => Polynomial.X - Polynomial.C a).prod := by
  by_cases h : p
  · have e : (cutTop h R M).conj (cutEnd p f) = f := LinearMap.ext fun _ => rfl
    rw [← LinearEquiv.charpoly_conj (cutTop h R M), e]
    exact hf
  · haveI := cut_subsingleton (R := R) (M := M) h
    refine ⟨0, ?_⟩
    have h1 : LinearMap.charpoly (cutEnd p f) = 1 := by
      rw [← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
      exact Module.finrank_zero_of_subsingleton
    rw [h1]; simp

theorem cut_span (h : p) {K : Type} [CommRing K] [Algebra R K] (T : Set (K ⊗[R] M)) (T' : Set (K ⊗[R] ↥(cut p R M)))
    (hT : Submodule.span K T = ⊤)
    (hh : ∀ x ∈ T, ∀ y, (∀ (f : Module.End R M) (a : K), f.baseChange K x = a • x → (cutEnd p f).baseChange K y = a • y) → y ∈ T') :
    Submodule.span K T' = ⊤ := by
  let e : K ⊗[R] M ≃ₗ[K] K ⊗[R] ↥(cut p R M) := LinearEquiv.baseChange R K _ _ (cutTop h R M).symm
  have he : ∀ (f : Module.End R M) x, (cutEnd p f).baseChange K (e x) = e (f.baseChange K x) := fun f x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [eq_top_iff, ← e.range, ← Submodule.map_top, ← hT, Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hh x hx _ fun f a hf => by
    change (cutEnd p f).baseChange K (e x) = a • e x
    rw [he, hf, map_smul]

theorem cut_lift {G : Type} [Group G] (ρ : G →* (M ≃ₗ[R] M)) (a : MonoidAlgebra R G) (x : ↥(cut p R M)) :
    ((MonoidAlgebra.lift R (Module.End R ↥(cut p R M)) G
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (cutAct p ρ)) a x : ↥(cut p R M)) : M) =
    MonoidAlgebra.lift R (Module.End R M) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) a x := by
  induction a using MonoidAlgebra.induction_on with
  | of g => rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]; rfl
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul, hf]

variable {K : Type} [CommRing K] [Algebra R K] {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def cutVal (p : Prop) (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K] (V : Type) [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] : ↥(cut p K V) →ₗ[R] V where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cutEmb (p : Prop) (K : Type) [CommRing K] [Algebra R K] {V : Type} [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] (f : M →ₗ[R] V) : ↥(cut p R M) →ₗ[R] ↥(cut p K V) where
  toFun x := ⟨f x.1, fun h => by rw [x.2 h, map_zero]⟩
  map_add' x y := Subtype.ext (map_add f x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul f c x.1)

theorem cutEmb_inj {f : M →ₗ[R] V} (hf : Function.Injective f) : Function.Injective (cutEmb p K f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem cut_comap_span (S : Set V) (h0 : (0 : V) ∈ S) :
    (Submodule.span R S).comap (cutVal p R K V) = Submodule.span R (Subtype.val ⁻¹' S : Set ↥(cut p K V)) := by
  by_cases h : p
  · exact (Submodule.span_preimage_eq (f := cutVal p R K V) ⟨0, h0⟩ fun x _ => ⟨⟨x, fun hn => absurd h hn⟩, rfl⟩).symm
  · haveI := cut_subsingleton (R := K) (M := V) h
    exact Subsingleton.elim _ _

theorem cut_span_top (S : Set M) (h0 : (0 : M) ∈ S) (hS : Submodule.span R S = ⊤) :
    Submodule.span R (Subtype.val ⁻¹' S : Set ↥(cut p R M)) = ⊤ := by
  by_cases h : p
  · rw [← Submodule.comap_top (cut p R M).subtype, ← hS]
    exact (Submodule.span_preimage_eq (f := (cut p R M).subtype) ⟨0, h0⟩ fun x _ => ⟨⟨x, fun hn => absurd h hn⟩, rfl⟩)
  · haveI := cut_subsingleton (R := R) (M := M) h
    exact Subsingleton.elim _ _

theorem cut_range {G : Type} [Group G] (ρ : G →* (V ≃ₗ[K] V)) (a : MonoidAlgebra K G) (U : Subgroup G) (ψ : U → K)
    (f : M →ₗ[R] V) (B : Submodule R V)
    (hB : LinearMap.range f = B ⊓ ((⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - ψ u • LinearMap.id)).map
      (MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) a)).restrictScalars R) :
    LinearMap.range (cutEmb p K f) = B.comap (cutVal p R K V) ⊓
      ((⨅ u : U, LinearMap.ker ((cutAct p ρ u).toLinearMap - ψ u • LinearMap.id)).map
        (MonoidAlgebra.lift K (Module.End K ↥(cut p K V)) G
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (cutAct p ρ)) a)).restrictScalars R := by
  by_cases h : p
  · ext x
    have h1 : x ∈ LinearMap.range (cutEmb p K f) ↔ x.1 ∈ LinearMap.range f :=
      ⟨fun ⟨y, hy⟩ => ⟨y.1, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨⟨y, fun hn => absurd h hn⟩, Subtype.ext hy⟩⟩
    have h2 : ∀ y : ↥(cut p K V), y ∈ (⨅ u : U, LinearMap.ker ((cutAct p ρ u).toLinearMap - ψ u • LinearMap.id)) ↔
        y.1 ∈ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - ψ u • LinearMap.id)) := fun y => by
      rw [Submodule.mem_iInf, Submodule.mem_iInf]
      exact forall_congr' fun u => Subtype.ext_iff
    rw [h1, hB]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, fun hn => absurd h hn⟩, (h2 _).2 hy, Subtype.ext ((cut_lift ρ a _).trans e)⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨y.1, (h2 _).1 hy, (cut_lift ρ a y).symm.trans (congrArg Subtype.val e)⟩
  · haveI := cut_subsingleton (R := K) (M := V) h
    exact Subsingleton.elim _ _

end Generic

variable (D : D7)

abbrev Rg (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ D.R.m

def cutTw : NTw D.R D.host D.what₂ D.LL0 D.nd :=
  { D.ntw with
    B := fun i j b => ↥(cut (Rg D j) (D.ntw.O i) (D.ntw.B i j b))
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => cut_free
    finB := fun _ _ _ => cut_finite
    Theta := fun _ _ _ => ⊥
    ThetaPsi := fun _ _ _ _ _ _ => ⊥
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_bot _).symm
    hk := fun i j b k P => cutEnd (Rg D j) (D.ntw.hk i j b k P)
    hk_zero := fun i j b P => by rw [D.ntw.hk_zero, cutEnd_one] }

abbrev FmC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Type := ↥(cut (Rg D j) (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))

abbrev BC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Type := ↥(cut (Rg D j) (D.ntw.O i) (D.ntw.B i j b))

def actC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : G0g D.nd →* (FmC D i j b ≃ₗ[FractionRing (D.ntw.O i)] FmC D i j b) :=
  cutAct (Rg D j) (D.nexp.actG i j b)

def bsupC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (FmC D i j b) :=
  (D.nexp.Bsup i j b).comap (cutVal (Rg D j) (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))

def twPsiC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (_ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) :
    FmC D i j b →ₗ[D.ntw.O i] (D.ntw.Ok i k ⊗[D.ntw.O i] FmC D i j b) :=
  TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i k) (FmC D i j b) 1

theorem twPsiC_one (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (f : FmC D i j b) :
    twPsiC D i j b k 1 f = (1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] f := rfl

def twDelC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M : ℕ) :
    FmC D i j b →ₗ[D.ntw.O i] (FmC D i j b ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) Q M)) := 0

def thPC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) :
    D.nexp.MtV i j b k Q ψ →ₗ[D.ntw.Ok i k] (D.ntw.Ok i k ⊗[D.ntw.O i] FmC D i j b) := 0

def hkC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) : Module.End (FractionRing (D.ntw.O i)) (FmC D i j b) :=
  cutEnd (Rg D j) (D.nexp.hkF i j b k P)

def embC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : BC D i j b →ₗ[D.ntw.O i] FmC D i j b :=
  cutEmb (Rg D j) (FractionRing (D.ntw.O i)) (D.nexp.embB i j b)

theorem embC_inj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Function.Injective (embC D i j b) := cutEmb_inj (D.nexp.embB_inj i j b)

def eHC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (D.ntw.O i)) (FmC D i j b) :=
  cutEnd (Rg D j) (D.nexp.eH i j b)

theorem eHC_idem (i : D.ntw.Tw) (j : ℕ) (b : Bool) : eHC D i j b * eHC D i j b = eHC D i j b :=
  (cutEnd_mul _ _).symm.trans (congrArg (cutEnd (Rg D j)) (D.nexp.eH_idem i j b))

def cutEx : NExp D.R D.host D.what₂ D.LL0 D.nd (cutTw D) :=
  { Fm := FmC D
    acgFm := fun (i : D.ntw.Tw) j b => (inferInstance : AddCommGroup (FmC D i j b))
    modFmK := fun (i : D.ntw.Tw) j b => (inferInstance : Module (FractionRing (D.ntw.O i)) (FmC D i j b))
    modFmO := fun (i : D.ntw.Tw) j b => (inferInstance : Module (D.ntw.O i) (FmC D i j b))
    towFm := fun (i : D.ntw.Tw) j b => (inferInstance : IsScalarTower (D.ntw.O i) (FractionRing (D.ntw.O i)) (FmC D i j b))
    fdFm := fun (i : D.ntw.Tw) j b => (cut_finite : Module.Finite (FractionRing (D.ntw.O i)) (FmC D i j b))
    actG := actC D
    U := D.nexp.U
    psiU := D.nexp.psiU
    eAlg := D.nexp.eAlg
    eLL0 := D.nexp.eLL0
    eAlg_def := D.nexp.eAlg_def
    eAlg_idem := D.nexp.eAlg_idem
    eAlg_central := D.nexp.eAlg_central
    Bsup := bsupC D
    Dat := fun _ _ _ => Empty
    th := fun _ _ _ d => d.elim
    lev := fun _ _ _ d => d.elim
    thPsi := fun _ _ _ _ _ _ d => d.elim
    thPsi_one := fun _ _ _ _ d => d.elim
    thU := fun _ _ _ _ _ d => d.elim
    twPsi := twPsiC D
    twPsi_one := twPsiC_one D
    twDel := twDelC D
    delU := D.nexp.delU
    delU_unr := D.nexp.delU_unr
    delU_l := D.nexp.delU_l
    delU_anti := D.nexp.delU_anti
    delU_open := D.nexp.delU_open
    delU_res := D.nexp.delU_res
    delU_conj := D.nexp.delU_conj
    MtV := D.nexp.MtV
    acgMt := D.nexp.acgMt
    modMtK := D.nexp.modMtK
    modMtO := D.nexp.modMtO
    towMt := D.nexp.towMt
    fdMt := D.nexp.fdMt
    MtLat := D.nexp.MtLat
    MtLat_fg := D.nexp.MtLat_fg
    MtLat_span := D.nexp.MtLat_span
    thP := thPC D
    hkF := hkC D
    embB := embC D
    embB_inj := embC_inj D
    eH := eHC D
    eH_idem := eHC_idem D }

def valC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : FmC D i j b →+ D.nexp.Fm i j b :=
  (cut (Rg D j) (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)).subtype.toAddMonoidHom

def evC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : FmC D i j b →+ (D.nth.Pt i j → ℂ_[D.ntw.l i]) := (D.nth.ev i j b).comp (valC D i j b)

def urC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : AddSubgroup (FmC D i j b) := (D.nth.FmUr i j b).comap (valC D i j b)

theorem evC_inj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Function.Injective (evC D i j b) :=
  (D.nth.ev_inj i j b).comp Subtype.val_injective

theorem span_ur (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    Submodule.span (FractionRing (D.ntw.O i)) (urC D i j b : Set (FmC D i j b)) = ⊤ :=
  cut_span_top _ (D.nth.FmUr i j b).zero_mem (D.nth.FmUr_span i j b)

theorem bsup_ur (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    bsupC D i j b = Submodule.span (D.ntw.O i) {f : FmC D i j b | f ∈ urC D i j b ∧ ∀ y, ‖evC D i j b f y‖ ≤ 1} := by
  unfold bsupC
  rw [D.nth.Bsup_def]
  exact cut_comap_span _ ⟨(D.nth.FmUr i j b).zero_mem, fun y => by simp⟩

def cutTh : NTh D.R D.host D.what₂ D.LL0 D.nd (cutTw D) (cutEx D) :=
  { D.nth with
    ev := evC D
    ev_smul := fun i j b a f y => D.nth.ev_smul i j b a (valC D i j b f) y
    ev_inj := evC_inj D
    datPhi := fun _ _ _ d => Empty.elim d
    datP := fun _ _ _ d => Empty.elim d
    hk_ev := fun i j b k P h1 h2 h3 h4 f y => D.nth.hk_ev i j b k P h1 h2 h3 h4 (valC D i j b f) y
    FmUr := urC D
    FmUr_smul := fun i j b a f ha hf => D.nth.FmUr_smul i j b a (valC D i j b f) ha hf
    FmUr_span := span_ur D
    Bsup_def := bsup_ur D }

def cutN : TwNew D := ⟨cutTw D, cutEx D, D.nStage_trivialCharacter_coeff_eq, cutTh D, D.ntwbr, D.ntwbr_ind⟩

def cutExp (E : NExpTied D) : NExpTied (cutN D).toD7 :=
  { E with
    acgWt := E.acgWt
    modWt := E.modWt
    fdWt := E.fdWt
    thU_empty := fun _ _ _ _ d => Empty.elim d
    mtV := fun i j b k Q ψ hj hj' hA =>
      letI : AddCommGroup (E.Wt i j b) := E.acgWt i j b
      letI : Module (FractionRing ((cutN D).toD7.ntw.O i)) (E.Wt i j b) := E.modWt i j b
      { E.mtV i j b k Q ψ hj hj' hA with } }

theorem cut_sigSpan (h : D.ntw.SigSpan) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule.span (FractionRing (D.ntw.O i))
      {x : TensorProduct (D.ntw.O i) (FractionRing (D.ntw.O i)) (BC D i j b) | ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧
        D.ntw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
          ((cutEnd (Rg D j) (D.ntw.hk i j b k P)).baseChange (FractionRing (D.ntw.O i))) x =
            algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) • x} = ⊤ :=
  cut_span (p := Rg D j) ⟨h1, h2⟩ _ _ (h i j b h1 h2) fun _ ⟨s, e1, e2, hs⟩ _ hy =>
    ⟨s, e1, e2, fun k P a1 a2 a3 a4 => hy _ _ (hs k P a1 a2 a3 a4)⟩

theorem cut_hkSplit {F : TwFrameC D} {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (P : PlE D.host) (hP : P ∉ D.ntw.S0 i) :
    haveI : Module.Free (D.ntw.O i) (BC D i j b) := cut_free
    haveI : Module.Finite (D.ntw.O i) (BC D i j b) := cut_finite
    ∃ s : Multiset (FractionRing (D.ntw.O i)),
      (LinearMap.charpoly (cutEnd (Rg D j) (D.ntw.hk i j b k P))).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))) =
        (s.map fun a => Polynomial.X - Polynomial.C a).prod :=
  haveI : Module.Free (D.ntw.O i) (BC D i j b) := cut_free
  haveI : Module.Finite (D.ntw.O i) (BC D i j b) := cut_finite
  cut_split _ _ (T.hk_split i j b k P hP)

theorem cut_bRange {F : TwFrameC D} {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    LinearMap.range (embC D i j b) = bsupC D i j b ⊓
      ((⨅ u : D.nexp.U, LinearMap.ker ((actC D i j b u).toLinearMap -
        ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • LinearMap.id)).map
        (MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (FmC D i j b)) (G0g D.nd)
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (actC D i j b)) (D.nexp.eAlg i b))).restrictScalars
            (D.ntw.O i) :=
  cut_range (p := Rg D j) (D.nexp.actG i j b) (D.nexp.eAlg i b) D.nexp.U
    (fun u => ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i))) (D.nexp.embB i j b)
    (D.nexp.Bsup i j b) (T.B_range i j b)

def topC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hj : 1 ≤ j) (hj' : j ≤ D.R.m) :
    FmC D i j b ≃ₗ[FractionRing (D.ntw.O i)] D.nexp.Fm i j b :=
  cutTop (p := Rg D j) ⟨hj, hj'⟩ (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)

variable (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
  (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
  (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
  (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)

def eFC (Bs : SideB D cf Rw low Pq S hL eig θ) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hj : 1 ≤ j) (hj' : j ≤ D.R.m) :
    FmC D i j b ≃ₗ[FractionRing (D.ntw.O i)] Formalism.IndefR.NX.Fm S i j b :=
  (topC D i j b hj hj').trans (Bs.eF i j b hj hj')

theorem hkEmbC (Bs : SideB D cf Rw low Pq S hL eig θ) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (x : BC D i j b)
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (a3 : P ∉ D.ntw.S0 i) (a4 : IsSplitPl D.host P) (a5 : k ≤ D.R.r) :
    embC D i j b (cutEnd (Rg D j) (D.ntw.hk i j b k P) x) = hkC D i j b k P (embC D i j b x) :=
  Subtype.ext (Bs.hk_emb i j b k P x.1 a1 a2 a3 a4 a5)

set_option maxHeartbeats 4000000 in

def cutSideB (Bs : SideB D cf Rw low Pq S hL eig θ) :
    SideB (cutN D).toD7 ((cutN D).cf cf) ((cutN D).row Rw) low Pq ((cutN D).rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with
      hk_split := cut_hkSplit D Bs.tw
      B_range := cut_bRange D Bs.tw }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp := cutExp D Bs.exp
    pq := fun i j b k Q ψ hj hj' hA => Bs.pq i j b k Q ψ hj hj' hA
    eF := eFC D cf Rw low Pq S hL eig θ Bs
    bsup := fun (i : D.ntw.Tw) j b hj hj' x => Bs.bsup i j b hj hj' (valC D i j b x)
    act := fun (i : D.ntw.Tw) j b hj hj' g x => Bs.act i j b hj hj' g (valC D i j b x)
    hkEq := fun (i : D.ntw.Tw) j b hj hj' k P x => Bs.hkEq i j b hj hj' k P (valC D i j b x)
    hk_emb := hkEmbC D cf Rw low Pq S hL eig θ Bs
    sigSpan := cut_sigSpan D Bs.sigSpan }

theorem cut_lamTie (Z : GlobalTheory.LamTie.LamDat D) (h : GlobalTheory.LamTie.IsLamTieFull D.ntw Z) : GlobalTheory.LamTie.IsLamTieFull (cutN D).tw Z := h

theorem fmC_subsingleton (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hn : ¬ (1 ≤ j ∧ j ≤ D.R.m)) : Subsingleton (FmC D i j b) :=
  cut_subsingleton hn

theorem cut_noOff : GlobalTheory.HeightCounting.SerCopy.NoOff (cutN D).toD7 := fmC_subsingleton D

end GlobalTheory.HeightCounting.CutOff

end

theorem _root_.GlobalTheory.T.secondStep_no_forms_outside_liftRange : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ GlobalTheory.HeightCounting.SerCopy.NoOff N.toD7 ∧ Nonempty (SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ) :=
  fun D cf Rw low Pq S hL eig θ Bs => ⟨GlobalTheory.HeightCounting.CutOff.cutN D, GlobalTheory.HeightCounting.CutOff.cut_lamTie D, fun i => ⟨i, rfl, rfl⟩,
    GlobalTheory.HeightCounting.CutOff.cut_noOff D, ⟨GlobalTheory.HeightCounting.CutOff.cutSideB D cf Rw low Pq S hL eig θ Bs⟩⟩
