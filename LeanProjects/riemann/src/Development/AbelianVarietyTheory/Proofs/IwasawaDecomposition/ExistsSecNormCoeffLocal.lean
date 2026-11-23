import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffMapOfIsPushoutStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffInDomainMulStatement
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

noncomputable section

namespace GlobalTheory.NormalDescent

open TopologicalSpace Opposite GlobalTheory.LBGerm GlobalTheory.FiniteAmple

theorem injective_res_of_isAffineOpen {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)]
    (h : W ≤ V) {x : X} (hx : x ∈ W) : Function.Injective (X.presheaf.map (homOfLE h).op).hom := by
  have hxV : x ∈ V := h hx
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hinj : Function.Injective (X.presheaf.germ V x hxV).hom :=
    IsLocalization.injective (M := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl) (S := X.presheaf.stalk x)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  intro a b e
  apply hinj
  rw [← X.presheaf.germ_res (homOfLE h) x hx]
  simp only [CommRingCat.comp_apply, e]

theorem exists_sec_normCoeff_local : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {M : LB X}, M.IsLB → ∀ t : (M.pull f).Sec, ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      ∃ (V : X.Opens) (hV : IsAffineOpen V) (_ : IsDomain Γ(X, V)) (_ : IsIntegrallyClosed Γ(X, V))
        (τ : Γ(Y, f ⁻¹ᵁ V)), x ∈ V ∧ (∀ y : Y, f y ∈ V → (y ∈ nonzeroLocus t ↔ y ∈ Y.basicOpen τ)) ∧
        ∀ (k : ℕ) (z : X), z ∈ V →
          (z ∈ nonzeroLocus (u k) ↔ z ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k)) := by
  intro X Y f _ _ _ M hM t
  let α : Type := {p : X.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2 ∧ IsIrreducible (p.1 : Set X)}
  have nd : ∀ a : α, IsDomain Γ(X, a.1.1) ∧ IsIntegrallyClosed Γ(X, a.1.1) := fun a =>
    GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible a.2.2.2
  have cov : ∀ x : X, ∃ a : α, x ∈ a.1.1 := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hM x
    have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (irreducibleComponent_mem_irreducibleComponents x)
    obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := M.U i ⊓ ⟨_, hC⟩) (x := x)
      ⟨hi, mem_irreducibleComponent⟩
    have hle : V ≤ M.U i ⊓ ⟨_, hC⟩ := hle
    exact ⟨⟨(V, i), hV, hle.trans inf_le_left, ⟨⟨x, hx⟩,
      (isIrreducible_irreducibleComponent (x := x)).2.open_subset V.isOpen fun q hq => (hle hq).2⟩⟩, hx⟩
  have le : ∀ a : α, f ⁻¹ᵁ a.1.1 ≤ (M.pull f).U fun _ => a.1.2 := fun a y hy => mem_pull.2 (a.2.2.1 hy)
  let τ : ∀ a : α, Γ(Y, f ⁻¹ᵁ a.1.1) := fun a => resG Y (le a) (t.f fun _ => a.1.2)
  let c : ∀ (k : ℕ) (a : α), Γ(X, a.1.1) := fun k a =>
    haveI := (nd a).1
    normCoeff (f.app a.1.1).hom (f.finite_app _ a.2.1) (τ a) k
  have key : ∀ k (x : X) (a b : α), x ∈ a.1.1 → x ∈ b.1.1 → gs (𝟙 X) x _ (c k a) =
      (gm (𝟙 X) x (M.U a.1.2 ⊓ M.U b.1.2) (M.g a.1.2 b.1.2)).val ^ k * gs (𝟙 X) x _ (c k b) := by
    intro k x a b ha hb
    obtain ⟨W, hW, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := a.1.1 ⊓ b.1.1) (x := x) ⟨ha, hb⟩
    have hle : W ≤ a.1.1 ⊓ b.1.1 := hle
    have la : W ≤ a.1.1 := hle.trans inf_le_left
    have lb : W ≤ b.1.1 := hle.trans inf_le_right
    have lg : W ≤ M.U a.1.2 ⊓ M.U b.1.2 := le_inf (la.trans a.2.2.1) (lb.trans b.2.2.1)
    have hWi : IsIrreducible (W : Set X) := ⟨⟨x, hx⟩, a.2.2.2.2.open_subset W.isOpen la⟩
    obtain ⟨_, _⟩ := GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWi
    obtain ⟨_, _⟩ := nd a
    obtain ⟨_, _⟩ := nd b
    have ea := GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout _ _ _ _ (isPushout_app f a.2.1 hW la) (injective_res_of_isAffineOpen a.2.1 la hx)
      (f.finite_app _ a.2.1) (f.finite_app _ hW) (τ a) k
    have eb := GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout _ _ _ _ (isPushout_app f b.2.1 hW lb) (injective_res_of_isAffineOpen b.2.1 lb hx)
      (f.finite_app _ b.2.1) (f.finite_app _ hW) (τ b) k
    have eτ : resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ a.1.1 from fun _ hy => la hy) (τ a) =
        (f.app W).hom (resG X lg (M.g a.1.2 b.1.2).val) *
          resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ b.1.1 from fun _ hy => lb hy) (τ b) := fn_ext fun y hy => by
      have hy' : (𝟙 Y ≫ f) y ∈ W := hy
      rw [gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y (le a) (la hy),
        gs_res (𝟙 Y) y (le b) (lb hy), gs_pull (𝟙 Y) f y W hy, gs_res (𝟙 Y ≫ f) y _ hy',
        gs_unit (𝟙 Y ≫ f) y _ (lg hy'),
        ← gm_pull_g M f (𝟙 Y) y (fun _ => a.1.2) (fun _ => b.1.2) (le a (la hy)) (le b (lb hy))]
      exact gs_compat t (𝟙 Y) y (le a (la hy)) (le b (lb hy))
    have e : resG X la (c k a) = resG X lg (M.g a.1.2 b.1.2).val ^ k * resG X lb (c k b) :=
      ea.trans ((congrArg (fun z => normCoeff (f.app W).hom (f.finite_app _ hW) z k) eτ).trans
        ((GlobalTheory.T.reversedCharpolyCoeffInDomain_mul _ _ _ _ k).trans (congrArg (_ * ·) eb.symm)))
    have e' := congrArg (gs (𝟙 X) x W) e
    rwa [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit _ x _ (lg hx)] at e'
  choose u hu using fun k => exists_sec_of_refinement (isLB_lbPow hM k) (fun a : α => a.1.1)
    (fun a _ => a.1.2) (fun a x hx => mem_powChart.2 (a.2.2.1 hx)) cov (c k) fun x a b ha hb => by
      rw [gm_lbPow_g k (𝟙 X) x _ _ (mem_powChart.2 (a.2.2.1 ha)) (mem_powChart.2 (b.2.2.1 hb)),
        Units.val_pow_eq_pow_val]
      exact key k x a b ha hb
  refine ⟨u, fun x => ?_⟩
  obtain ⟨a, ha⟩ := cov x
  refine ⟨a.1.1, a.2.1, (nd a).1, (nd a).2, τ a, ha, fun y hy => ?_, fun k z hz => ?_⟩
  · have hy : y ∈ f ⁻¹ᵁ a.1.1 := hy
    rw [mem_nonzeroLocus_iff_isUnit t (le a hy), ← gs_res (𝟙 Y) y (le a) hy]
    exact isUnit_gs_iff (𝟙 Y) y _ hy _
  · have hJ : z ∈ (lbPow M k).U fun _ => a.1.2 := mem_powChart.2 (a.2.2.1 hz)
    rw [mem_nonzeroLocus_iff_isUnit (u k) hJ, hu k z _ a hJ hz, Units.isUnit_units_mul]
    exact isUnit_gs_iff (𝟙 X) z _ hz _

end GlobalTheory.NormalDescent
