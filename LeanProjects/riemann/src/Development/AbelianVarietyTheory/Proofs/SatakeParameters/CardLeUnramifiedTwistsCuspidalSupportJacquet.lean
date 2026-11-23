import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalJacquetSubquotientAtMostOneNonemptyBlockStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetRankOneCentralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleGl1IsoDetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.JacSuppCount

open GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel in

theorem eq_mul_unrChar_of_eq_on_units : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ ω : kˣ →* ℂˣ), (∀ u : kˣ, ValuativeRel.valuation k (u : k) = 1 → ω u = χ u) → ∃ α : ℂˣ, ω = χ * GlobalTheory.SmGL.unrChar k α := by
  intro k _ _ _ _ χ ω h
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x h0, hx⟩
  have hu : IsUnram (χ⁻¹ * ω) := fun u hu => by
    simp [h u hu]
  refine ⟨(χ⁻¹ * ω) ϖ, ?_⟩
  rw [← eq_unrChar hu hϖ]
  ext u
  simp

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.ProdSupport Matrix ValuativeRel TensorProduct in

theorem scalar_mem_KO_of_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : Type) [Fintype m] [DecidableEq m] {z : kˣ} (hz : ValuativeRel.valuation k (z : k) = 1) :
    GeneralLinearGroup.scalar m z ∈ KO k m := by
  have hz' : ValuativeRel.valuation k ((z⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hz, inv_one]
  have h1 : (z : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hz.le
  have h2 : ((z⁻¹ : kˣ) : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hz'.le
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · by_cases h : i = j
    · subst h; simpa [GeneralLinearGroup.scalar] using h1
    · simp [GeneralLinearGroup.scalar, h, zero_mem]
  · rw [← map_inv]
    by_cases h : i = j
    · subst h; simpa [GeneralLinearGroup.scalar] using h2
    · simp [GeneralLinearGroup.scalar, h, zero_mem]

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.ProdSupport Matrix ValuativeRel TensorProduct in

theorem card_le_ncard_unrTwist : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s s' : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (d' : Fin s' → ℕ) (e : (Σ j, Fin (d' j)) ≃ Fin n) (A : Finset (Fin s')) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) → (∀ j ∈ A, d' j = 1) → x ≠ 0 → (∀ j ∈ A, ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (d' j)), GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → A.card ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  intro _ hG k _ _ _ _ n s s' χ π d σ d' e A x hχ hcs hA hx hact
  obtain ⟨-, hσ, e₀, hsub⟩ := hcs
  obtain ⟨Y, _, _, τ, y, hτ, hτs, hy, hτy⟩ := GlobalTheory.T.irreducible_subquotient_eigenvector _ _ (jac e π.π) x hx
  have hτP : IsSubquotient τ (jac e (multiProd e₀ fun a => (σ a).π)) :=
    hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e (isSmooth_parInd _ _) hsub)
  obtain ⟨b, f, g, t, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e₀ e
    (fun a => (σ a).smooth) (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ hτP

  have hcolj : ∀ j ∈ A, ∃ i, b.1 i j = 1 ∧ ∀ i', i' ≠ i → b.1 i' j = 0 := by
    intro j hj
    have hsum : ∑ i, b.1 i j = 1 := by simpa [hA j hj] using b.2.2 j
    obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => b.1 i j) (Finset.mem_univ i)
    have h0 : ∑ i' ∈ Finset.univ.erase i, b.1 i' j = 0 := by simp only at hsplit; omega
    refine ⟨i, by simp only at hsplit; omega, fun i' hi' => ?_⟩
    exact Finset.sum_eq_zero_iff.1 h0 i' (Finset.mem_erase.2 ⟨hi', Finset.mem_univ i'⟩)
  rcases A.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp
  haveI : Nonempty (Fin s) := ⟨(hcolj j₀ hj₀).choose⟩
  choose! ι hι1 hι0 using hcolj

  have hrow1 : ∀ i j j', 0 < b.1 i j → 0 < b.1 i j' → j = j' := fun i =>
    GlobalTheory.T.cuspidal_jacquet_subquotient_at_most_one_nonempty_block k (d i) _ (σ i).π s' (b.1 i) (f i) _ (fun j => (t i j).ρ) (hσ i).2.2
      (fun j => Model.nontrivial_of_isIrreducible (t i j).irr) (hrow i)

  have hd1 : ∀ j ∈ A, d (ι j) = 1 := by
    intro j hj
    have h := b.2.1 (ι j)
    rw [Fintype.card_fin, Finset.sum_eq_single j (fun j' _ hj' => by
      by_contra hne
      exact hj' (hrow1 _ _ _ (Nat.pos_of_ne_zero hne) (by rw [hι1 j hj]; exact one_pos)))
      (by simp), hι1 j hj] at h
    exact h.symm
  have hinj : Set.InjOn ι (A : Set (Fin s')) := by
    intro j hj j' hj' h
    refine hrow1 (ι j) j j' (by rw [hι1 j hj]; exact one_pos) ?_
    rw [h, hι1 j' hj']; exact one_pos

  have hmem : ∀ j ∈ A, ι j ∈ {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv
      (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
    intro j hj
    set i := ι j with hi
    obtain ⟨ω, -, hω⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar (σ i).smooth (σ i).irr

    have hT : ∀ (z : kˣ) (v : ⨂[ℂ] j', (t i j').V),
        piTensor (fun j' => (t i j').ρ) (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b.1 i j)) z)) v =
          (ω z : ℂ) • v := fun z v =>
      Model.scalar_of_isSubquotient (hrow i) (GlobalTheory.T.jacquet_rank_one_central k (d i) _ (σ i).π ω s' (b.1 i) (f i) j (hd1 j hj)
        (hι1 j hj) hω z) v
    have hωt : HasCentralChar (t i j).ρ ω := by
      obtain ⟨ω', -, hω'⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar (t i j).smooth (t i j).irr
      have := nontrivial_piTensor _ fun j' => Model.nontrivial_of_isIrreducible (t i j').irr
      obtain ⟨v, hv⟩ := exists_ne (0 : ⨂[ℂ] j', (t i j').V)
      have : ω' = ω := MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hv
        ((piTensor_mulSingle (fun j' => (t i j').ρ) j _ _ (hω' z) v).symm.trans (hT z v)))
      exact this ▸ hω'
    have hz : ∀ i', i' ≠ i → IsEmpty (Fin (b.1 i' j)) := fun i' h' => by
      rw [hι0 j hj i' h']; infer_instance
    have hcen := hasCentralChar_multiProd (g j) (fun i' => (t i' j).ρ) i hz hωt
    have hωχ : ∀ u : kˣ, ValuativeRel.valuation k (u : k) = 1 → ω u = χ u := by
      intro u hu
      have h1 := Model.scalar_of_isSubquotient hcol
        (piTensor_mulSingle (fun j => multiProd (g j) fun i => (t i j).ρ) j _ _ (hcen u)) y
      have h2 := hτy _ _ (hact j hj _ (scalar_mem_KO_of_val (Fin (d' j)) hu))
      rw [det_scalar_one (hA j hj)] at h2
      exact Units.ext (smul_left_injective ℂ hy (h1.symm.trans h2))
    obtain ⟨α, hα⟩ := eq_mul_unrChar_of_eq_on_units k χ ω hωχ
    exact ⟨hd1 j hj, α, hα ▸ GlobalTheory.T.irreducible_gl1_iso_det k (d i) _ (σ i).π ω (hd1 j hj) (σ i).irr hω⟩
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn ι hmem hinj (Set.toFinite _)

end GlobalTheory.JacSuppCount
