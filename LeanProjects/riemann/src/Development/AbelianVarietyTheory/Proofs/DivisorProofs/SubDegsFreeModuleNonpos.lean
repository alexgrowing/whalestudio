import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FiniteDegreeMorphisms
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveRootGeometry.QuotDeg

open GlobalTheory.QCoh (IsFiniteQC)

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]

theorem exists_deg_eq_add (hC : IsProjCurve k C) {B Q : C.Modules} [IsFiniteQC Q] (p : B ⟶ Q)
    {G : C.Modules} {i : G ⟶ B} (hi : IsCohSub i) :
    ∃ a ∈ subDegs k (kernel p), ∃ b ∈ subDegs k Q, deg k G = a + b := by
  have := hC.isNoetherian
  have := hi.mono
  have := hi.isFiniteQC
  let q : G ⟶ Q := i ≫ p
  have hKG : IsFiniteQC (kernel q) := .of_mono (kernel.ι q)
  have hm : Mono (Abelian.factorThruCoimage q) := inferInstance
  have hc : IsFiniteQC (cokernel (kernel.ι q)) := .of_mono (Abelian.factorThruCoimage q)
  let j : kernel q ⟶ kernel p := kernel.lift p (kernel.ι q ≫ i) (by
    rw [Category.assoc]; exact kernel.condition q)
  have hj : Mono j := mono_of_mono_fac (kernel.lift_ι p (kernel.ι q ≫ i) _)
  refine ⟨_, IsCohSub.deg_mem (i := j) ⟨hj, hKG⟩, _,
    IsCohSub.deg_mem (i := Abelian.factorThruCoimage q) ⟨hm, hc⟩, ?_⟩
  rw [hC.deg_cokernel]
  ring

theorem le_of_jointly_mono (hC : IsProjCurve k C) {D : C.Modules} [IsFiniteQC D] {b : ℤ}
    (hD : ∀ d ∈ subDegs k D, d ≤ b) (n : ℕ) :
    ∀ (Z : C.Modules) [IsFiniteQC Z] (ψ : Fin n → (Z ⟶ D)),
      (∀ (W : C.Modules) (g : W ⟶ Z), (∀ j, g ≫ ψ j = 0) → g = 0) →
      ∀ d ∈ subDegs k Z, d ≤ n * b := by
  have := hC.isNoetherian
  induction n with
  | zero =>
    intro Z _ ψ h
    have hZ : IsZero Z := (IsZero.iff_id_eq_zero Z).2 (h Z (𝟙 Z) fun j => j.elim0)
    rintro _ ⟨G, i, hi, rfl⟩
    have := hi.mono
    simp [deg_eq_zero_of_isZero k (hZ.of_mono i)]
  | succ n ih =>
    intro Z _ ψ h
    have : IsFiniteQC (kernel (ψ 0)) := .of_mono (kernel.ι (ψ 0))
    have hK := ih (kernel (ψ 0)) (fun j => kernel.ι (ψ 0) ≫ ψ j.succ) fun W g hg => by
      have h0 : g ≫ kernel.ι (ψ 0) = 0 := h W _ fun j => by
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [Category.assoc, kernel.condition, comp_zero]
        · rw [Category.assoc]; exact hg j
      exact (cancel_mono (kernel.ι (ψ 0))).1 (h0.trans (zero_comp).symm)
    rintro _ ⟨G, i, hi, rfl⟩
    obtain ⟨a, ha, c, hc, e⟩ := exists_deg_eq_add hC (ψ 0) hi
    rw [e]
    have := hK a ha
    have := hD c hc
    push_cast
    linarith

theorem subDegs_freeModule_nonpos (hC : IsProjCurve k C) (r : ℕ) :
    ∀ d ∈ subDegs k (QCoh.freeModule C (Fin r)), d ≤ 0 := by
  have := Abelian.hasFiniteBiproducts (C := C.Modules)
  have hO : ∀ d ∈ subDegs k (structureModule C), d ≤ 0 := by
    intro d hd
    have := (hC.isMaxSubDeg_of_rank_one (isVB_structureModule C)).2 hd
    simpa using this
  let e : QCoh.freeModule C (Fin r) ≅ ⨁ fun _ : Fin r => structureModule C :=
    (biproduct.isoCoproduct (fun _ : Fin r => structureModule C)).symm
  intro d hd
  have := le_of_jointly_mono hC hO r (QCoh.freeModule C (Fin r))
    (fun j => e.hom ≫ biproduct.π _ j) (fun W g hg => by
      have : g ≫ e.hom = 0 := biproduct.hom_ext _ _ fun j => by
        rw [Category.assoc, zero_comp]; exact hg j
      exact (cancel_mono e.hom).1 (this.trans zero_comp.symm)) d hd
  simpa using this

end GlobalTheory.CurveRootGeometry.QuotDeg

namespace GlobalTheory.CurveRootGeometry.QuotDeg

open GlobalTheory.QCoh (IsFiniteQC)
open scoped TensorProduct

variable {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]

theorem tensorAct_comm {O : Type} [CommRing O] {F F' : C.Modules} {ρ : O →+* End F}
    {ρ' : O →+* End F'} {φ : F ⟶ F'} (h : IsEquivariant ρ ρ' φ) (x : k ⊗[ℤ] O) :
    act (tensorAct k ρ) x ≫ φ = φ ≫ act (tensorAct k ρ') x := by
  induction x with
  | zero => simp only [act, map_zero]; rw [zero_comp, comp_zero]
  | tmul c a => rw [act_tensorAct_tmul, act_tensorAct_tmul, Linear.smul_comp, Linear.comp_smul, h a]
  | add x y hx hy => simp only [act, map_add] at *; rw [Preadditive.add_comp, Preadditive.comp_add, hx, hy]

theorem proj_eigenMap {O ι : Type} [CommRing O] [DecidableEq ι] {τ : ι → (O →+* k)} (hτ : IsSplitBy τ)
    {F F' : C.Modules} {ρ : O →+* End F} {ρ' : O →+* End F'} {φ : F ⟶ F'} (h : IsEquivariant ρ ρ' φ)
    (j : ι) : hτ.proj ρ j ≫ eigenMap (scal C (τ j)) h = φ ≫ hτ.proj ρ' j := by
  rw [← cancel_mono (eigenι ρ' (scal C (τ j))), Category.assoc, eigenMap_ι, ← Category.assoc,
    IsSplitBy.proj_ι, Category.assoc, IsSplitBy.proj_ι, tensorAct_comm h]

theorem epi_eigenMap {O ι : Type} [CommRing O] {τ : ι → (O →+* k)} (hτ : IsSplitBy τ)
    {F F' : C.Modules} {ρ : O →+* End F} {ρ' : O →+* End F'} {φ : F ⟶ F'} (h : IsEquivariant ρ ρ' φ)
    [Epi φ] (j : ι) : Epi (eigenMap (scal C (τ j)) h) := by
  classical
  have : Epi (hτ.proj ρ' j) := ⟨fun u v e => by
    simpa using eigenι ρ' (scal C (τ j)) ≫= e⟩
  have : Epi (hτ.proj ρ j ≫ eigenMap (scal C (τ j)) h) := by
    rw [proj_eigenMap]; infer_instance
  exact epi_of_epi (hτ.proj ρ j) _

end GlobalTheory.CurveRootGeometry.QuotDeg

namespace GlobalTheory.CurveRootGeometry.QuotDeg

open GlobalTheory.QCoh (IsFiniteQC)

theorem quot_deg : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
  ∀ (O : Type) [CommRing O], Splits O k → ∀ (F F' : C.Modules) (g g' : ℕ), IsVB F g → IsVB F' g' →
  ∀ (ρ : O →+* End F) (ρ' : O →+* End F') (φ : F ⟶ F'), IsEquivariant ρ ρ' φ → Epi φ →
    (∃ r : ℕ, Nonempty (kernel φ ≅ GlobalTheory.QCoh.freeModule C (Fin r))) →
    (∀ σ : O →+* k, deg k (eigen ρ' (scal C σ)) = deg k (eigen ρ (scal C σ))) ∧
      ∀ d ∈ subDegs k F, ∃ d' ∈ subDegs k F', d ≤ d' := by
  intro k _ _ C _ _ hC O _ hS F F' g g' hF hF' ρ ρ' φ hφ _ ⟨r, ⟨eK⟩⟩
  classical
  have hP := hC.toIsProjCurve
  have := hP.isNoetherian
  have := hF.isFiniteQC
  have := hF'.isFiniteQC
  have hK : ∀ d ∈ subDegs k (kernel φ), d ≤ 0 := by
    rw [subDegs_congr eK]; exact subDegs_freeModule_nonpos hP r
  refine ⟨fun σ => ?_, fun d ⟨G, i, hi, e⟩ => ?_⟩
  · obtain ⟨κ, _, τ, hτ⟩ := hS
    obtain ⟨j₀, rfl⟩ := hτ.exists_eq σ
    have := hτ.isFiniteQC_eigen ρ
    have := hτ.isFiniteQC_eigen ρ'
    have := fun j => epi_eigenMap hτ hφ (φ := φ) j
    have hKj : ∀ j, IsFiniteQC (kernel (eigenMap (scal C (τ j)) hφ)) := fun j =>
      .of_mono (kernel.ι (eigenMap (scal C (τ j)) hφ))
    have e₁ : ∀ j, deg k (eigen ρ (scal C (τ j))) =
        deg k (kernel (eigenMap (scal C (τ j)) hφ)) + deg k (eigen ρ' (scal C (τ j))) := fun j =>
      hP.deg_shortExact (S := ShortComplex.mk _ _ (kernel.condition (eigenMap (scal C (τ j)) hφ)))
        (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance inferInstance)
    have e₂ : ∀ j, deg k (kernel (eigenMap (scal C (τ j)) hφ)) ≤ 0 := fun j => by
      let m : kernel (eigenMap (scal C (τ j)) hφ) ⟶ kernel φ :=
        kernel.lift φ (kernel.ι _ ≫ eigenι ρ _) (by
          rw [Category.assoc, ← eigenMap_ι (scal C (τ j)) hφ, kernel.condition_assoc, zero_comp])
      have : Mono m := mono_of_mono_fac (kernel.lift_ι _ _ _)
      exact hK _ (IsCohSub.deg_mem (i := m) ⟨inferInstance, inferInstance⟩)
    have hKφ : IsFiniteQC (kernel φ) := .of_mono (kernel.ι φ)
    have e₃ : deg k F = deg k (kernel φ) + deg k F' :=
      hP.deg_shortExact (S := ShortComplex.mk _ _ (kernel.condition φ))
        (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance inferInstance)
    have e₄ : deg k (kernel φ) = 0 := by
      rw [deg_congr k eK]; exact deg_freeModule (hP.finiteCoh _) (Fin r)
    have e₅ := (hP.deg_eq_sum_eigen hτ ρ).1
    have e₆ := (hP.deg_eq_sum_eigen hτ ρ').1
    have e₇ : ∑ j, deg k (kernel (eigenMap (scal C (τ j)) hφ)) = 0 := by
      have : ∑ j, deg k (eigen ρ (scal C (τ j))) =
          ∑ j, deg k (kernel (eigenMap (scal C (τ j)) hφ)) + ∑ j, deg k (eigen ρ' (scal C (τ j))) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => e₁ j
      omega
    have e₈ := (Finset.sum_eq_zero_iff_of_nonpos fun j _ => e₂ j).1 e₇ j₀ (Finset.mem_univ _)
    rw [e₁ j₀, e₈, zero_add]
  · obtain ⟨a, ha, b, hb, e'⟩ := exists_deg_eq_add hP φ hi
    refine ⟨b, hb, ?_⟩
    have := hK a ha
    omega

end GlobalTheory.CurveRootGeometry.QuotDeg
