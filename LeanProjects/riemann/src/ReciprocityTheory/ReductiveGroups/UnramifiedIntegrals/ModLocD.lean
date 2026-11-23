import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic

noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_of_ratRoot {Ω M : Type*} [Field Ω] [IsAlgClosed Ω] [Field M] (e : Ω →+* M)
    (f₀ : ℚ →+* Ω) (f : ℚ →+* M) {p : Polynomial ℚ} (hp : p ≠ 0) {y : M}
    (hy : p.eval₂ f y = 0) : ∃ a : Ω, e a = y := by
  have hP : p.map f₀ ≠ 0 := (Polynomial.map_ne_zero_iff f₀.injective).2 hp
  have hr : ((p.map f₀).map e).roots = (p.map f₀).roots.map e :=
    (IsAlgClosed.splits _).roots_map e
  have hf : e.comp f₀ = f := Subsingleton.elim _ _
  have hmem : y ∈ ((p.map f₀).map e).roots := by
    rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff e.injective).2 hP), Polynomial.map_map, hf,
      Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hy
  rw [hr, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem exists_e_eq {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (r : PadicAlgCl l →+* PadicAlgCl l) (x : Om d) : ∃ y : Om d, e y = r (e x) := by
  obtain ⟨p, hp, hpx⟩ := Om_isAlgebraic d x
  have : IsAlgClosed (Om d) := (inferInstance : IsAlgClosure (KQ d) (Om d)).isAlgClosed
  let f₀ : ℚ →+* Om d := algebraMap ℚ (Om d)
  have h0 : p.eval₂ f₀ x = 0 := by
    apply (algebraMap (Om d) ℂ).injective
    rw [Polynomial.hom_eval₂, map_zero]
    have : (algebraMap (Om d) ℂ).comp f₀ = algebraMap ℚ ℂ := Subsingleton.elim _ _
    rw [this]
    exact hpx
  refine exists_of_ratRoot e f₀ ((r.comp e).comp f₀) hp ?_
  have := congrArg (r.comp e) h0
  rw [Polynomial.hom_eval₂, map_zero] at this
  exact this

theorem norm_lt_of_res {l : ℕ} [Fact l.Prime] {r : PadicAlgCl l → PadicAlgCl l}
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) {z : PadicAlgCl l} (hz : ‖z‖ < 1) : ‖r z‖ < 1 := by
  have h := PadicAlgCl.isNonarchimedean l (r z - z) z
  rw [sub_add_cancel] at h
  exact lt_of_le_of_lt h (max_lt (hr z hz.le) hz)

theorem norm_le_of_res {l : ℕ} [Fact l.Prime] {r : PadicAlgCl l → PadicAlgCl l}
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : ‖r z‖ ≤ 1 := by
  have h := PadicAlgCl.isNonarchimedean l (r z - z) z
  rw [sub_add_cancel] at h
  exact le_trans h (max_le (hr z hz).le hz)

theorem norm_le_iff_of_res {l : ℕ} [Fact l.Prime] (r : PadicAlgCl l →+* PadicAlgCl l)
    (hr : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖r z - z‖ < 1) (z : PadicAlgCl l) : ‖r z‖ ≤ 1 ↔ ‖z‖ ≤ 1 := by
  refine ⟨fun h => ?_, fun h => norm_le_of_res hr h⟩
  by_contra hz
  push Not at hz
  have h1 : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have h2 := norm_lt_of_res hr h1
  rw [map_inv₀, norm_inv] at h2
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    linarith
  have h3 : 0 < ‖r z‖ := norm_pos_iff.2 ((map_ne_zero r).2 hz0)
  have h4 : 1 ≤ ‖r z‖⁻¹ := (one_le_inv₀ h3).2 h
  linarith

theorem fix_KQ {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (k : KQ d) : ρ (e (algebraMap (KQ d) (Om d) k)) = e (algebraMap (KQ d) (Om d) k) := by
  let φ₁ : KQ d →ₐ[ℚ] PadicAlgCl l := (e.comp (algebraMap (KQ d) (Om d))).toRatAlgHom
  let φ₂ : KQ d →ₐ[ℚ] PadicAlgCl l :=
    ((ρ : PadicAlgCl l →+* PadicAlgCl l).comp (e.comp (algebraMap (KQ d) (Om d)))).toRatAlgHom
  have h : φ₂ = φ₁ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (s := {sqD d}) rfl ?_
    intro x hx
    have hx' : x = sqD d := hx
    subst hx'
    have hm : e (algebraMap (KQ d) (Om d) (sqK d)) ∈
        IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))} :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    exact ρ.commutes ⟨_, hm⟩
  exact DFunLike.congr_fun h k

theorem locLift {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (e : Om d →+* PadicAlgCl l)
    (he : ∀ x : Om d, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = ι (x : ℂ))
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (hρ : ∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) :
    ∃ σ : Om d ≃ₐ[KQ d] Om d, InertiaEl (Aio d l ι) σ ∧ ∀ x : Om d, e (σ x) = ρ (e x) := by
  have hinj : Function.Injective e := e.injective
  choose g hg using exists_e_eq e (ρ : PadicAlgCl l →+* PadicAlgCl l)
  choose g' hg' using exists_e_eq e (ρ.symm : PadicAlgCl l →+* PadicAlgCl l)
  have hg1 : ∀ x, e (g x) = ρ (e x) := hg
  have hg2 : ∀ x, e (g' x) = ρ.symm (e x) := hg'
  let σ : Om d ≃ₐ[KQ d] Om d :=
    { toFun := g
      invFun := g'
      left_inv := fun x => hinj (by rw [hg2, hg1, AlgEquiv.symm_apply_apply])
      right_inv := fun x => hinj (by rw [hg1, hg2, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => hinj (by rw [hg1, map_mul, map_mul, map_mul, hg1, hg1])
      map_add' := fun x y => hinj (by rw [hg1, map_add, map_add, map_add, hg1, hg1])
      commutes' := fun k => hinj (by rw [hg1, fix_KQ]) }
  have hσ : ∀ x, e (σ x) = ρ (e x) := hg1
  have hn : ∀ x : Om d, ‖ι (x : ℂ)‖ = ‖e x‖ := fun x => by
    rw [← he, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  have hiff : ∀ x : Om d, σ x ∈ Aio d l ι ↔ x ∈ Aio d l ι := fun x => by
    rw [mem_Aio, mem_Aio, hn, hn, hσ]
    exact norm_le_iff_of_res (ρ : PadicAlgCl l →+* PadicAlgCl l) hρ (e x)
  refine ⟨σ, ⟨?_, ?_⟩, hσ⟩
  · show σ • Aio d l ι = Aio d l ι
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hiff]
    have : σ (σ⁻¹ • x) = x := σ.apply_symm_apply x
    rw [this]
  · intro x hx
    rw [mem_nonunits_Aio]
    rw [hn, map_sub, hσ]
    exact hρ _ (by rw [← hn]; exact (mem_Aio ι x).1 hx)

end ReciprocityTheory.ChartRestriction.L1
