import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingTensorFiltrationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPiece

theorem subsingleton_tmul {O N M : Type} [CommRing O] [AddCommGroup N] [Module O N] [AddCommGroup M] [Module O M]
    [Subsingleton M] (y : N ⊗[O] M) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

set_option maxHeartbeats 1000000 in
theorem main : ∀ {O A G : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing G] [Algebra O G] [Module.Flat O G]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m) (u v : ℕ)
    {M : Fin m → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)] {M' : Type} [AddCommGroup M']
    (θ : ∀ i : Fin m, u ≤ (i : ℕ) → (i : ℕ) < v → (G ≃ₗ[O] M i))
    (h0 : ∀ i : Fin m, ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → Subsingleton (M i))
    (π : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G)) →+ M'),
    Function.Surjective π →
    (∀ x, π x = 0 ↔ x.1 ∈ (pdP γ v).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G))) →
    ∀ f : ∀ i, S.N i → M i → M', (∀ i n, f i n 0 = 0) →
    (∀ (i : Fin m) n x (hu : u ≤ (i : ℕ)) (hv : (i : ℕ) < v) hx, f i n (θ i hu hv x) = π ⟨S.ν i n ⊗ₜ x, hx⟩) →
    Tens O f := by
  intro O A G _ _ _ _ _ _ I γ m S u v M _ _ M' _ θ h0 π hπ hker f hf0 hf
  classical
  obtain ⟨g₀, hs, hm⟩ := GlobalTheory.T.graded_splitting_tensor_filtration (Γ := G) γ m S
  let t : ∀ i : Fin m, S.N i ⊗[O] M i →+ S.N i ⊗[O] G := fun i =>
    if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then
      ((LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm : S.N i ⊗[O] M i ≃ₗ[O] S.N i ⊗[O] G).toLinearMap.toAddMonoidHom
    else 0
  have t_act : ∀ (i : Fin m) (h : u ≤ (i : ℕ) ∧ (i : ℕ) < v) (a : S.N i ⊗[O] G),
      t i (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) a) = a := by
    intro i h a
    simp only [t, dif_pos h]
    exact (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm_apply_apply a
  have t_inact : ∀ (i : Fin m), ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → t i = 0 := by
    intro i h
    simp only [t, dif_neg h]
  let T : (∀ i, S.N i ⊗[O] M i) →+ (∀ i, S.N i ⊗[O] G) :=
    { toFun := fun w i => t i (w i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  have T_apply : ∀ w i, T w i = t i (w i) := fun _ _ => rfl
  have hT : ∀ w, g₀ (T w) ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
    intro w
    refine (hm u _).2 fun i hi => ?_
    rw [T_apply, t_inact i (by omega)]
    rfl
  let φ : (∀ i, S.N i ⊗[O] M i) →+ M' :=
    { toFun := fun w => π ⟨g₀ (T w), hT w⟩
      map_zero' := by
        have : (⟨g₀ (T 0), hT 0⟩ : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add]
        exact congrArg π (Subtype.ext (by simp)) }
  have φ_apply : ∀ w, φ w = π ⟨g₀ (T w), hT w⟩ := fun _ => rfl
  have inj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun w hw => ?_
    rw [φ_apply] at hw
    have h1 := (hm v _).1 ((hker _).1 hw)
    funext i
    by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
    · have h2 := h1 i h.2
      rw [T_apply] at h2
      obtain ⟨a, ha⟩ := (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).surjective (w i)
      rw [← ha, t_act i h] at h2
      rw [← ha, h2, map_zero]
      rfl
    · haveI := h0 i h
      exact subsingleton_tmul _
  have surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨z, hz⟩ := g₀.surjective x.1
    have hzu := (hm u z).1 (by rw [hz]; exact x.2)
    let w : ∀ i, S.N i ⊗[O] M i := fun i =>
      if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) (z i) else 0
    refine ⟨w, ?_⟩
    rw [φ_apply, ← sub_eq_zero, ← map_sub, hker]
    have : ((⟨g₀ (T w), hT w⟩ - x : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) : A ⊗[O] G)
        = g₀ (T w - z) := by
      rw [map_sub, hz]
      rfl
    rw [this, hm]
    intro i hi
    rw [Pi.sub_apply, T_apply, sub_eq_zero]
    by_cases h : u ≤ (i : ℕ)
    · have h' : u ≤ (i : ℕ) ∧ (i : ℕ) < v := ⟨h, hi⟩
      simp only [w, dif_pos h']
      exact t_act i h' _
    · rw [t_inact i (by omega), hzu i (by omega)]
      rfl
  refine ⟨AddEquiv.ofBijective φ ⟨inj, surj⟩, fun i n x => ?_⟩
  rw [AddEquiv.ofBijective_apply]
  by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
  · obtain ⟨y, rfl⟩ := (θ i h.1 h.2).surjective x
    have hTs : T (Pi.single i (n ⊗ₜ[O] θ i h.1 h.2 y)) = Pi.single i (n ⊗ₜ[O] y) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [T_apply, Pi.single_eq_same, Pi.single_eq_same]
        exact t_act j h (n ⊗ₜ[O] y)
      · rw [T_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
    have hx : S.ν i n ⊗ₜ[O] y ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
      rw [← hs, ← hTs]
      exact hT _
    rw [hf i n y h.1 h.2 hx, φ_apply]
    exact congrArg π (Subtype.ext (by simp only [hTs, hs]))
  · haveI := h0 i h
    rw [Subsingleton.elim x 0, TensorProduct.tmul_zero, Pi.single_zero, map_zero, hf0]

end GlobalTheory.CompanionTheory.GrPiece
