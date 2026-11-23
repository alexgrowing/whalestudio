import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfCoinv

section Abstract

variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}

theorem exists_sum_eq_zero (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) {m : M}
    (hm : m ∈ Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g}) :
    ∃ (ι : Type) (s : Finset ι) (y : ι → G), (∀ i, y i ∈ Y) ∧ (∃ i ∈ s, y i = 0) ∧ ∑ i ∈ s, ρ (y i) m = 0 := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨u, hu, g, hg, rfl⟩ := hm
    obtain ⟨k, hk, h⟩ := hsm u hu g hg
    refine ⟨ℕ, Finset.range k, fun j => j • u, fun j => Y.nsmul_mem hu j,
      ⟨0, Finset.mem_range.2 hk, zero_smul _ _⟩, ?_⟩
    have e : ∀ j : ℕ, ρ (j • u) (ρ u g - g) = ρ ((j + 1) • u) g - ρ (j • u) g := fun j => by
      rw [map_sub, hadd _ (Y.nsmul_mem hu j) _ hu, succ_nsmul]
    simp only [e]
    rw [Finset.sum_range_sub (fun j : ℕ => ρ (j • u) g), h, zero_smul, h0, sub_self]
  | zero => exact ⟨Unit, Finset.univ, fun _ => 0, fun _ => Y.zero_mem, ⟨(), Finset.mem_univ _, rfl⟩, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := ha
    obtain ⟨κ, t, z, hz, ⟨j, hj, hj0⟩, h'⟩ := hb
    refine ⟨ι × κ, s ×ˢ t, fun p => y p.1 + z p.2, fun p => Y.add_mem (hy _) (hz _),
      ⟨(i, j), Finset.mem_product.2 ⟨hi, hj⟩, by simp only [hi0, hj0, add_zero]⟩, ?_⟩
    simp only [map_add, Finset.sum_add_distrib]
    have e1 : ∑ p ∈ s ×ˢ t, ρ (y p.1 + z p.2) a = 0 := by
      rw [Finset.sum_product_right]
      refine Finset.sum_eq_zero fun q _ => ?_
      have : ∀ p, ρ (y p + z q) a = ρ (z q) (ρ (y p) a) := fun p => by rw [hadd _ (hz _) _ (hy _), add_comm]
      simp only [this]
      rw [← map_sum, h, map_zero]
    have e2 : ∑ p ∈ s ×ˢ t, ρ (y p.1 + z p.2) b = 0 := by
      rw [Finset.sum_product]
      refine Finset.sum_eq_zero fun p _ => ?_
      have : ∀ q, ρ (y p + z q) b = ρ (y p) (ρ (z q) b) := fun q => by rw [hadd _ (hy _) _ (hz _)]
      simp only [this]
      rw [← map_sum, h', map_zero]
    rw [e1, e2, add_zero]
  | smul c a _ ha =>
    obtain ⟨ι, s, y, hy, hi, h⟩ := ha
    refine ⟨ι, s, y, hy, hi, ?_⟩
    simp only [map_smul]
    rw [← Finset.smul_sum, h, smul_zero]

theorem exists_separating {B : G → G → ℂ} (hcomm : ∀ u y f, ρ u (ρ y f) = B u y • ρ y (ρ u f)) {f₀ : M} (hf : f₀ ≠ 0)
    (hd : ∀ y ∈ Y, ρ y f₀ = f₀ ∨ ∃ u, ρ u f₀ = f₀ ∧ B u y ≠ 1) {ι : Type} (s : Finset ι) {y : ι → G}
    (hy : ∀ i, y i ∈ Y) : ∃ P : M →ₗ[ℂ] M, P f₀ ≠ 0 ∧ ∀ i ∈ s, ρ (y i) f₀ = f₀ ∨ P (ρ (y i) f₀) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨LinearMap.id, hf, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | insert j s _ ih =>
    obtain ⟨P, hP, h⟩ := ih
    rcases hd _ (hy j) with h1 | ⟨u, hu, hB⟩
    · exact ⟨P, hP, fun i hi => (Finset.mem_insert.1 hi).elim (fun e => Or.inl (e ▸ h1)) (h i)⟩
    · refine ⟨P ∘ₗ (ρ u - B u (y j) • LinearMap.id), ?_, fun i hi => ?_⟩
      · have : (ρ u - B u (y j) • (LinearMap.id : M →ₗ[ℂ] M)) f₀ = (1 - B u (y j)) • f₀ := by
          rw [LinearMap.sub_apply, hu, sub_smul, one_smul]; rfl
        rw [LinearMap.comp_apply, this, map_smul]
        exact smul_ne_zero (sub_ne_zero.2 hB.symm) hP
      · have : (ρ u - B u (y j) • (LinearMap.id : M →ₗ[ℂ] M)) (ρ (y i) f₀) =
            (B u (y i) - B u (y j)) • ρ (y i) f₀ := by
          rw [LinearMap.sub_apply, hcomm, hu, sub_smul]; rfl
        rw [LinearMap.comp_apply, this, map_smul]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Or.inr (by rw [sub_self, zero_smul])
        · exact (h i hi).imp_right fun e => by rw [e, smul_zero]

theorem exists_form {B : G → G → ℂ} (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f)
    (hcomm : ∀ u y f, ρ u (ρ y f) = B u y • ρ y (ρ u f)) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) {f₀ : M} (hf : f₀ ≠ 0)
    (hd : ∀ y ∈ Y, ρ y f₀ = f₀ ∨ ∃ u, ρ u f₀ = f₀ ∧ B u y ≠ 1) :
    ∃ ℓ : M →ₗ[ℂ] ℂ, (∀ u ∈ Y, ∀ g ∈ Θ, ℓ (ρ u g) = ℓ g) ∧ ℓ f₀ ≠ 0 := by
  classical
  have hn : f₀ ∉ Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g} := fun hm => by
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := exists_sum_eq_zero hadd h0 hsm hm
    obtain ⟨P, hP, hs⟩ := exists_separating hcomm hf hd s hy
    have e : ∑ j ∈ s, P (ρ (y j) f₀) = ∑ j ∈ s with ρ (y j) f₀ = f₀, P f₀ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j hj => ?_
      split_ifs with h1
      · rw [h1]
      · exact (hs j hj).resolve_left h1
    rw [← map_sum, h, map_zero, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at e
    refine smul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, ?_⟩)) hP e.symm
    exact Finset.mem_filter.2 ⟨hi, by rw [hi0, h0]⟩
  obtain ⟨ℓ, h1, h2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  refine ⟨ℓ, fun u hu g hg => ?_, h1⟩
  have : ℓ (ρ u g - g) ∈ (⊥ : Submodule ℂ ℂ) :=
    h2 ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, hu, g, hg, rfl⟩)
  rwa [Submodule.mem_bot, map_sub, sub_eq_zero] at this

end Abstract

open GlobalTheory.PlaceModel

theorem exists_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (e : AE D), IsSplitIdem D e → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0 := by
  intro D ψ hψ S T e hs
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hcs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hcs S) (hcs T) _ _
    (isSelfDualC_latFrame S) (isSelfDualC_latFrame T)
  obtain ⟨hth, hvac, -⟩ := hf 1
  simp only [one_mul] at hth hvac
  have hs' := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  obtain ⟨he, hec, v, ε, hε, heq⟩ := id hs
  have he' : cA D e * cA D e = cA D e := hs'.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (isSelfDualC_latFrame S)
    (isSelfDualC_latFrame T)).1
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.LatVac.cA_cA, hec]
  obtain ⟨ℓ, h1, h2⟩ := exists_form (Y := half S T (cA D e)) (ρ := heisL S T ψ)
    (B := fun x y => ψ (symplO S T x y)) (Θ := {g | IsThetaFunO ψ S T g}) (heisL_half S T ψ c2)
    (GlobalTheory.SplitScalar.heisO_zero ψ S T) (heisL_comm S T ψ) (fun u hu g hg => by
      obtain ⟨U, hU, h⟩ := hg.level
      obtain ⟨k, hk, hkU⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem U hU (infPart_half hε heε' hu)
      exact ⟨k, hk, h _ hkU (infPart_half hε heε' ((half S T (cA D e)).nsmul_mem hu k))⟩) f0 (fun y hy => by
      by_cases h : ∀ u ∈ (latO S T (latFrame S) (latFrame T) fun w => w = v) ⊓ half S T e, ψ (symplO S T u y) = 1
      · have := mem_of_dual hε hdual he' heε' (by rwa [GlobalTheory.LatVac.cA_cA]) y hy fun u hu => by
          rw [GlobalTheory.LatVac.cA_cA] at hu
          rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
        exact Or.inl (hvac.2 _ hs' y (latO_le_top _ this.1) ((isHalf_iff S T).2 hy))
      · push_neg at h
        obtain ⟨u, hu, h⟩ := h
        exact Or.inr ⟨u, hvac.2 _ hs u (latO_le_top _ hu.1) ((isHalf_iff S T).2 hu.2), h⟩)
  exact ⟨ℓ, fun u hu g hg => h1 u ((isHalf_iff S T).1 hu) g hg, f, hth, h2⟩

end GlobalTheory.HalfCoinv

end
