import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExactFormsLeClosedForms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CechDR GlobalTheory.CxForm GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ContDiff

namespace GlobalTheory.PD

section Smooth

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

abbrev dF (α : A.Fld) : A.Fld := A.dExt α

abbrev smForms : Subalgebra ℂ A.Fld := A.forms

abbrev dL : smForms A →ₗ[ℂ] smForms A := A.dForms

def filAt (n p : ℕ) (m : ℤ) : Submodule ℂ (Alt n) :=
  ⨅ T ∈ {T : Finset (Fin (n + n)) | ¬ ((T.card : ℤ) = m ∧ p ≤ (T.filter (·.val < n)).card)}, LinearMap.ker ((bas n).coord T)

def smCx (p : ℕ) : Cx ℂ (smForms A) :=
  ⟨fun m => ⨅ x : A.Pt, (filAt n p m).comap ((LinearMap.proj x : A.Fld →ₗ[ℂ] Alt n) ∘ₗ (smForms A).val.toLinearMap), dL A⟩

abbrev HSm (m : ℤ) : Type := (smCx A 0).H m

def FSm (p : ℕ) (m : ℤ) : Submodule ℂ (HSm A m) :=
  (((smCx A p).Z m).submoduleOf ((smCx A 0).Z m)).map (Submodule.mkQ _)

structure FormOn (S : Set M) (α : A.Fld) : Prop where
  smooth : ∀ i T, ContDiffOn ℝ ∞ (fun v => (bas n).repr (A.loc α i v) T) ((A.e i).target ∩ (A.e i).symm ⁻¹' S)
  compat : ∀ x x' : A.Pt, x.pt ∈ S → x.pt = x'.pt → α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x')

def fnC (g : M → ℂ) : A.Fld := fun x => algebraMap ℂ _ (g x.pt)

def cint [MeasurableSpace M] (α : A.Fld) : ℂ := (A.integral α : ℂ) - Complex.I * (A.integral (Complex.I • α) : ℂ)

variable {ι : Type} [LinearOrder ι]

def Rep (S : Finset ι → Set M) (g : Finset ι → A.Fld) (α : A.Fld) : Prop :=
  ∃ y : Finset ι → A.Fld, y ∅ = 0 ∧ (∀ s, FormOn A (S s) (y s)) ∧ ∀ s, s.Nonempty → ∀ x : A.Pt, x.pt ∈ S s →
    g s x = const α s x + GlobalTheory.DI.delta y s x + (-1 : ℤ) ^ s.card • dF A (y s) x

end Smooth

section Scheme

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ)

abbrev atl [SmoothOfRelativeDimension d p] : HolAtlas (CxPts p σ) d := algAtlas p d σ

variable [IsIntegral X]

@[reducible] def ffAlg : Algebra k X.functionField :=
  ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra

variable [Algebra k X.functionField]

def IsVal [SmoothOfRelativeDimension d p] (g : DR k X.functionField → (atl p σ d).Fld) : Prop :=
  algebraMap k X.functionField = @algebraMap k X.functionField _ _ (ffAlg p) ∧
  ∀ (U : X.Opens) [Nonempty U] (J : Type) [Fintype J] (q : ℕ) (f₀ : J → Γ(X, U)) (f : J → Fin q → Γ(X, U)) (y : (atl p σ d).Pt),
    y.pt ∈ ptsIn p σ U →
    g (∑ l, X.germToFunctionField U (f₀ l) • ExteriorAlgebra.ιMulti X.functionField q
        fun j => D k X.functionField (X.germToFunctionField U (f l j))) y =
      ∑ l, ev p σ U (f₀ l) y.pt • (List.ofFn fun j => dF (atl p σ d) (fnC _ (ev p σ U (f l j))) y).prod

omit σ in

structure IsAffCover {ι : Type} (U : ι → X.Opens) (B : Finset ι → Subalgebra k X.functionField) : Prop where
  alg : algebraMap k X.functionField = @algebraMap k X.functionField _ _ (ffAlg p)
  affine : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (I.inf U)
  cover : iSup U = ⊤
  ne : ∀ I : Finset ι, genericPoint X ∈ I.inf U
  ring : ∀ I : Finset ι, I.Nonempty → ∀ y, y ∈ B I ↔ ∃ f : Γ(X, I.inf U), (X.presheaf.germ (I.inf U) (genericPoint X) (ne I)).hom f = y

end Scheme

section Compare

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem mem_filAt_iff {p : ℕ} {m : ℤ} {a : Alt n} :
    a ∈ filAt n p m ↔ ∀ T, (bas n).repr a T ≠ 0 → (T.card : ℤ) = m ∧ p ≤ holCount T := by
  simp only [filAt, Submodule.mem_iInf, LinearMap.mem_ker, Set.mem_setOf_eq, Module.Basis.coord_apply, holCount]
  exact forall_congr' fun T => not_imp_comm

theorem mem_filAt_nat {p k : ℕ} {a : Alt n} : a ∈ filAt n p k ↔ HasDeg k a ∧ a ∈ holGe n p := by
  rw [mem_filAt_iff, mem_holGe_iff]
  exact ⟨fun h => ⟨fun T hT => by exact_mod_cast (h T hT).1, fun T hT => (h T hT).2⟩,
    fun h T hT => ⟨by exact_mod_cast h.1 T hT, h.2 T hT⟩⟩

variable {A}

theorem mem_smCx_C {p : ℕ} {m : ℤ} {α : smForms A} : α ∈ (smCx A p).C m ↔ ∀ x, α.1 x ∈ filAt n p m := by
  simp only [smCx, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem mem_smCx_C_nat {p k : ℕ} {α : smForms A} : α ∈ (smCx A p).C k ↔ A.IsDeg k α ∧ A.TypeGe p α := by
  rw [mem_smCx_C, HolAtlas.typeGe_iff]
  simp only [mem_filAt_nat]
  exact forall_and

theorem smCx_C_neg {p : ℕ} {m : ℤ} (hm : m < 0) : (smCx A p).C m = ⊥ := by
  refine eq_bot_iff.2 fun α hα => Subtype.ext (funext fun x => (bas n).ext_elem fun T => ?_)
  by_contra h
  have := (mem_filAt_iff.1 (mem_smCx_C.1 hα x) T (by simpa using h)).1
  omega

theorem mem_smCx_Z_nat {p k : ℕ} {α : smForms A} : α ∈ (smCx A p).Z k ↔ α.1 ∈ A.closedForms k ∧ A.TypeGe p α := by
  rw [Cx.Z, Submodule.mem_inf, mem_smCx_C_nat, LinearMap.mem_ker, HolAtlas.mem_closedForms, Subtype.ext_iff]
  exact ⟨fun h => ⟨⟨α.2, h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.2.1, h.2⟩, h.1.2.2⟩⟩

theorem mem_smCx_B_nat {k : ℕ} {α : smForms A} : α ∈ (smCx A 0).B k ↔ α.1 ∈ A.exactForms k := by
  rw [Cx.B]
  cases k with
  | zero =>
    rw [smCx_C_neg (by norm_num), Submodule.map_bot, HolAtlas.exactForms_zero, Submodule.mem_bot, Submodule.mem_bot]
    exact Subtype.ext_iff
  | succ k =>
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = k by push_cast; ring, HolAtlas.mem_exactForms_succ, Submodule.mem_map]
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨η, η.2, (mem_smCx_C_nat.1 hη).1, rfl⟩
    · rintro ⟨η, hη, hk, e⟩
      exact ⟨⟨η, hη⟩, mem_smCx_C_nat.2 ⟨hk, fun _ _ _ => Nat.zero_le _⟩, Subtype.ext e.symm⟩

variable (A)

theorem isCx_smCx (p : ℕ) : (smCx A p).IsCx := by
  intro m α hα
  refine ⟨?_, (A.isDga).d_d α⟩
  rcases lt_or_ge m 0 with hm | hm
  · rw [smCx_C_neg hm, Submodule.mem_bot] at hα
    rw [hα, map_zero]
    exact zero_mem _
  · lift m to ℕ using hm
    rw [mem_smCx_C_nat] at hα
    exact (mem_smCx_C_nat (k := m + 1)).2 ⟨hα.1.dExt, hα.2.dExt⟩

def zEquiv (k : ℕ) : (smCx A 0).Z k ≃ₗ[ℂ] A.closedForms k where
  toFun α := ⟨α.1.1, (mem_smCx_Z_nat.1 α.2).1⟩
  invFun α := ⟨⟨α.1, α.2.1⟩, mem_smCx_Z_nat.2 ⟨α.2, fun _ _ _ => Nat.zero_le _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coe_zEquiv (k : ℕ) (α : (smCx A 0).Z k) : (zEquiv A k α : A.Fld) = α.1.1 := rfl

def hsmEquiv (k : ℕ) : HSm A k ≃ₗ[ℂ] A.HSm k :=
  Submodule.Quotient.equiv _ _ (zEquiv A k) (by
    ext β
    rw [Submodule.mem_map_equiv]
    exact mem_smCx_B_nat)

theorem hsmEquiv_mk (k : ℕ) (α : (smCx A 0).Z k) :
    hsmEquiv A k (Submodule.Quotient.mk α) = HolAtlas.HSm.mk A k (zEquiv A k α) := rfl

theorem mem_FSm_iff (p k : ℕ) (c : HSm A k) : c ∈ FSm A p k ↔ hsmEquiv A k c ∈ HolAtlas.HSm.fil A p k := by
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨zEquiv A k α, (mem_smCx_Z_nat.1 hα).2, rfl⟩
  · rintro ⟨β, hβ, e⟩
    refine ⟨(zEquiv A k).symm β, mem_smCx_Z_nat.2 ⟨β.2, hβ⟩, (hsmEquiv A k).injective ?_⟩
    exact e

theorem map_FSm (p k : ℕ) : (FSm A p k).map (hsmEquiv A k).toLinearMap = HolAtlas.HSm.fil A p k := by
  ext c
  rw [Submodule.mem_map_equiv, mem_FSm_iff, LinearEquiv.apply_symm_apply]

end Compare

section Basic₂

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

example : dL A 0 = 0 := map_zero _

example (m : ℤ) : Module ℂ (HSm A m) := inferInstance

example (m : ℤ) : (0 : HSm A m) ∈ FSm A 3 m := Submodule.zero_mem _

example : Module.finrank ℂ (HSm (HolAtlas.std 0) (0 : ℕ)) = 1 :=
  (hsmEquiv _ 0).finrank_eq.trans HolAtlas.HSm.finrank_std₀

example : dF (HolAtlas.std 1) HolAtlas.zFld ≠ 0 := HolAtlas.dExt_zFld_ne_zero

end Basic₂

section Inhab

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem FormOn.of_isForm {α : A.Fld} (h : A.IsForm α) (S : Set M) : FormOn A S α where
  smooth i T := (h.smooth i T).mono Set.inter_subset_left
  compat x x' _ hx := h.compat x x' hx

theorem FormOn.zero (S : Set M) : FormOn A S 0 := by
  have h := (HolAtlas.isForm_algebra M n A).1
  have h0 := ((HolAtlas.isForm_algebra M n A).2 0 1 1 h h).2.2
  rw [zero_smul] at h0
  exact FormOn.of_isForm A h0 S

example (S : Set M) : FormOn A S 1 := FormOn.of_isForm A (HolAtlas.isForm_algebra M n A).1 S

theorem isAffCover_spec (K : Type) [Field K] :
    letI := ffAlg (𝟙 (Sp K))
    IsAffCover (𝟙 (Sp K)) (fun _ : Unit => (⊤ : (Sp K).Opens)) (fun _ => ⊤) := by
  letI := ffAlg (𝟙 (Sp K))
  have hinf : ∀ I : Finset Unit, I.inf (fun _ : Unit => (⊤ : (Sp K).Opens)) = ⊤ := fun I => by simp
  refine ⟨rfl, fun I _ => ?_, ?_, fun I => ?_, fun I _ y => ?_⟩
  · rw [hinf]; exact isAffineOpen_top _
  · simp
  · rw [hinf]; trivial
  · change y ∈ (⊤ : Subalgebra K (Sp K).functionField) ↔ _
    simp only [Algebra.mem_top, true_iff]
    have key : ∀ (V : (Sp K).Opens) (hV : V = ⊤) (h : genericPoint (Sp K) ∈ V),
        Function.Surjective ((Sp K).presheaf.germ V (genericPoint (Sp K)) h).hom := by
      intro V hV h
      subst hV
      haveI : Nonempty (⊤ : (Sp K).Opens) := ⟨⟨genericPoint (Sp K), trivial⟩⟩
      have hF := functionField_isFractionRing_of_isAffineOpen (Sp K) ⊤ (isAffineOpen_top _)
      have hK : IsField Γ(Sp K, ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
      exact (IsFractionRing.surjective_iff_isField (R := Γ(Sp K, ⊤)) (K := (Sp K).functionField)).2 hK
    exact key _ (hinf I) _ y

end Inhab

end GlobalTheory.PD
