import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchForm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreB

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section ProdSub

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

def prodSub (V₁ : Submodule ℂ M₁) (V₂ : Submodule ℂ M₂) : Submodule ℂ (WithLp 2 (M₁ × M₂)) :=
  (V₁.prod V₂).comap (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

theorem mem_prodSub {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂} {x : WithLp 2 (M₁ × M₂)} :
    x ∈ prodSub V₁ V₂ ↔ prFst x ∈ V₁ ∧ prSnd x ∈ V₂ := Iff.rfl

theorem finiteDimensional_prodSub {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂} (h₁ : FiniteDimensional ℂ V₁)
    (h₂ : FiniteDimensional ℂ V₂) : FiniteDimensional ℂ (prodSub V₁ V₂) := by
  have h₁' : V₁.FG := Module.Finite.iff_fg.mp h₁
  have h₂' : V₂.FG := Module.Finite.iff_fg.mp h₂
  refine Module.Finite.iff_fg.mpr ?_
  unfold prodSub
  first
    | (rw [Submodule.comap_equiv_eq_map_symm]; exact (h₁'.prod h₂').map _)
    | (have heq : Submodule.comap (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap (V₁.prod V₂) =
          Submodule.map (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm.toLinearMap (V₁.prod V₂) := by
         ext x
         simp only [Submodule.mem_comap, Submodule.mem_map]
         constructor
         · intro hx
           exact ⟨_, hx, by simp⟩
         · rintro ⟨y, hy, rfl⟩
           simpa using hy
       rw [heq]
       exact (h₁'.prod h₂').map _)

theorem prodSub_kStable {ε : Fin n → Bool} {E₁ : Fin n → Fin n → Module.End ℂ M₁}
    {E₂ : Fin n → Fin n → Module.End ℂ M₂} {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂}
    (h₁ : IsKStableSub ε E₁ V₁) (h₂ : IsKStableSub ε E₂ V₂) :
    IsKStableSub ε (prodE E₁ E₂) (prodSub V₁ V₂) := fun a b hab v hv =>
  mem_prodSub.2 ⟨h₁ a b hab _ (mem_prodSub.1 hv).1, h₂ a b hab _ (mem_prodSub.1 hv).2⟩

end ProdSub

theorem casimir_mem_genSub {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    {V : Submodule ℂ M} {w : M} (hw : w ∈ V) : casimir E w ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf]
  rintro T ⟨hVT, hT⟩
  show (∑ a, ∑ b, E a b * E b a) w ∈ T
  first
    | (rw [LinearMap.sum_apply]
       refine Submodule.sum_mem _ fun a _ => ?_
       rw [LinearMap.sum_apply]
       exact Submodule.sum_mem _ fun b _ => hT a b _ (hT b a _ (hVT hw)))
    | (simp only [LinearMap.coeFn_sum, Finset.sum_apply]
       exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hT a b _ (hT b a _ (hVT hw)))

theorem casimir_eq_casVal_of_model {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {M₁ : Type*} [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁] {E₁ : Fin n → Fin n → Module.End ℂ M₁}
    (hE₁ : IsGlRep E₁) (hU₁ : IsInfUnitary ε E₁) {V₁ : Submodule ℂ M₁}
    (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E₁ V₁ 1,
      IsKHWVec ε E₁ (lowK ε lam - root a b) w → w = 0)
    {M₂ : Type*} [NormedAddCommGroup M₂] [InnerProductSpace ℂ M₂] {E₂ : Fin n → Fin n → Module.End ℂ M₂}
    (hE₂ : IsGlRep E₂) (hU₂ : IsInfUnitary ε E₂) {V₂ : Submodule ℂ M₂}
    (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v) :
    ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v := by
  obtain ⟨hfd₁, hks₁, hirr₁, w₁, hw₁m, hw₁0, hw₁K⟩ := hV₁
  obtain ⟨hfd₂, hks₂, -, w₂, hw₂m, hw₂0, hw₂K⟩ := hV₂

  set y : WithLp 2 (M₁ × M₂) := (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm (w₁, w₂) with hydef
  have hy1 : prFst y = w₁ := by simp [hydef, prFst]
  have hy2 : prSnd y = w₂ := by simp [hydef, prSnd]
  have hE := isGlRep_prod hE₁ hE₂
  have hU := isInfUnitary_prod hU₁ hU₂
  have hyK : IsKHWVec ε (prodE E₁ E₂) (lowK ε lam) y := by
    refine ⟨fun a => prod_ext ?_ ?_, fun a b hab hε => prod_ext ?_ ?_⟩
    · rw [prFst_prodE, map_smul, hy1, hw₁K.1 a]
    · rw [prSnd_prodE, map_smul, hy2, hw₂K.1 a]
    · rw [prFst_prodE, hy1, hw₁K.2 a b hab hε, map_zero]
    · rw [prSnd_prodE, hy2, hw₂K.2 a b hab hε, map_zero]
  have hy0 : y ≠ 0 := fun h => hw₁0 (by rw [← hy1, h, map_zero])
  have hSle : kLowSpan ε (prodE E₁ E₂) y ≤ prodSub V₁ V₂ :=
    kLowSpan_le (prodSub_kStable hks₁ hks₂) (mem_prodSub.2 ⟨hy1 ▸ hw₁m, hy2 ▸ hw₂m⟩)
  haveI := finiteDimensional_prodSub hfd₁ hfd₂
  have hfin : FiniteDimensional ℂ (kLowSpan ε (prodE E₁ E₂) y) := Submodule.finiteDimensional_of_le hSle
  have hS := kLowSpan_kIrrHW hE hU hyK hy0 hfin

  have hNoS : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε (prodE E₁ E₂) (kLowSpan ε (prodE E₁ E₂) y) 1,
      IsKHWVec ε (prodE E₁ E₂) (lowK ε lam - root a b) w → w = 0 := by
    intro a b hab hne w hw hwK
    have h1 := hNo a b hab hne _
      (layer_map_le prFst (fun a b x => prFst_prodE a b x) (fun x hx => (mem_prodSub.1 (hSle hx)).1) 1 w hw)
      (khw_map prFst (fun a b x => prFst_prodE a b x) hwK)
    have h2 := no_of_casimir hE₂ hU₂ hc₂ hgap a b hab hne _
      (layer_map_le prSnd (fun a b x => prSnd_prodE a b x) (fun x hx => (mem_prodSub.1 (hSle hx)).2) 1 w hw)
      (khw_map prSnd (fun a b x => prSnd_prodE a b x) hwK)
    exact prod_ext (by rw [h1, map_zero]) (by rw [h2, map_zero])
  have hcomm : ∀ a b x, casimir (prodE E₁ E₂) (prodE E₁ E₂ a b x) =
      prodE E₁ E₂ a b (casimir (prodE E₁ E₂) x) :=
    fun a b x => congrArg (fun T : Module.End ℂ (WithLp 2 (M₁ × M₂)) => T x) (casimir_comm hE a b)
  have hcK := khw_map (casimir (prodE E₁ E₂)) hcomm hyK
  have hcS := khw_lowK_mem_of_no hE hU hS hNoS hgap
    (casimir_mem_genSub (prodE E₁ E₂) (self_mem_kLowSpan y)) hcK
  obtain ⟨c, hc⟩ := kLowSpan_line hE hU hyK hy0 hcS hcK.1

  have h2 : casimir E₂ w₂ = c • w₂ := by
    have := casimir_map (E := prodE E₁ E₂) (E' := E₂) prSnd (fun a b x => prSnd_prodE a b x) y
    rw [hc, map_smul, hy2] at this
    exact this.symm
  have hcv : (casVal lam : ℂ) = c := smul_left_injective ℂ hw₂0 ((hc₂ w₂ hw₂m).symm.trans h2)
  have h1 : casimir E₁ w₁ = (casVal lam : ℂ) • w₁ := by
    have := casimir_map (E := prodE E₁ E₂) (E' := E₁) prFst (fun a b x => prFst_prodE a b x) y
    rw [hc, map_smul, hy1, ← hcv] at this
    exact this.symm

  have kerI : ∀ v, v ∈ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1) ↔
      casimir E₁ v = (casVal lam : ℂ) • v := fun v => by
    rw [LinearMap.mem_ker]
    show casimir E₁ v - (casVal lam : ℂ) • v = 0 ↔ _
    exact sub_eq_zero
  have hcomm₁ : ∀ a b x, casimir E₁ (E₁ a b x) = E₁ a b (casimir E₁ x) :=
    fun a b x => congrArg (fun T : Module.End ℂ M₁ => T x) (casimir_comm hE₁ a b)
  have hst : IsKStableSub ε E₁ (V₁ ⊓ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1)) := by
    intro a b hab v hv
    refine ⟨hks₁ a b hab v hv.1, (kerI _).2 ?_⟩
    rw [hcomm₁, (kerI v).1 hv.2, map_smul]
  rcases hirr₁ _ inf_le_left hst with h | h
  · exfalso
    have hw : w₁ ∈ V₁ ⊓ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1) := ⟨hw₁m, (kerI w₁).2 h1⟩
    rw [h] at hw
    exact hw₁0 ((Submodule.mem_bot ℂ).1 hw)
  · intro v hv
    have hv' : v ∈ V₁ ⊓ LinearMap.ker (casimir E₁ - (casVal lam : ℂ) • 1) := by rw [h]; exact hv
    exact (kerI v).1 hv'.2

end ReciprocityTheory.ChartRestriction.DS
