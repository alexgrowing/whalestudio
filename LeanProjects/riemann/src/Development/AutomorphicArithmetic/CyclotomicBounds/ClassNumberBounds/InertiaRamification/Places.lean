import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Decomp
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

omit [NeZero N] in
private theorem mem_ker_toUnitHom_iff (ψ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    u ∈ (MulChar.toUnitHom ψ).ker ↔ ψ (u : ZMod N) = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_eq_one, MulChar.coe_toUnitHom]

omit [NeZero N] in
private theorem charKer_le_ker {X : Subgroup (DirichletCharacter ℂ N)}
    {ψ : DirichletCharacter ℂ N} (h : ψ ∈ X) : charKer X ≤ (MulChar.toUnitHom ψ).ker :=
  iInf₂_le (f := fun (φ : DirichletCharacter ℂ N) (_ : φ ∈ X) => (MulChar.toUnitHom φ).ker) ψ h

omit [NeZero N] in
private theorem neg_one_notMem_ker {ψ : DirichletCharacter ℂ N} (o : ψ.Odd) :
    (-1 : (ZMod N)ˣ) ∉ (MulChar.toUnitHom ψ).ker := by
  rw [mem_ker_toUnitHom_iff]
  have h : ψ (-1) = -1 := o
  simp only [Units.val_neg, Units.val_one, h]
  norm_num

omit [NeZero N] in
private theorem not_conjIn_of_trivial {X : Subgroup (DirichletCharacter ℂ N)}
    {ψ : DirichletCharacter ℂ N} (h : ψ ∈ X) (o : ψ.Odd) {D : Subgroup (ZMod N)ˣ}
    (hD : ∀ u ∈ D, ψ (u : ZMod N) = 1) :
    D ⊔ charKer X ≤ (MulChar.toUnitHom ψ).ker ∧ ¬ ConjIn X D := by
  have hle : D ⊔ charKer X ≤ (MulChar.toUnitHom ψ).ker :=
    sup_le (fun u hu => (mem_ker_toUnitHom_iff ψ u).2 (hD u hu)) (charKer_le_ker h)
  exact ⟨hle, fun hc => neg_one_notMem_ker o (hle hc)⟩

theorem split_of_splitsFor (X : Subgroup (DirichletCharacter ℂ N)) {ch : DirichletCharacter ℂ N}
    (hch : ch ∈ X) (hodd : ch.Odd) (hs : SplitsFor l ch) :
    decompUnits N l ⊔ charKer X ≤ (MulChar.toUnitHom ch).ker ∧ ¬ ConjIn X (decompUnits N l) ∧
      numPlaces l X = 2 * numPlaces l (evenPart X) ∧
      ∀ σ τ : (ZMod N)ˣ, σ⁻¹ * τ ∈ decompUnits N l ⊔ charKer X →
        ch (σ : ZMod N) = ch (τ : ZMod N) := by
  obtain ⟨hle, hc⟩ := not_conjIn_of_trivial hch hodd ((splitsFor_iff l ch).2.1 hs)
  refine ⟨hle, hc, (conjIn_iff l X).1.2 hc, fun σ τ h => ?_⟩
  have h1 := (mem_ker_toUnitHom_iff ch _).1 (hle h)
  have h2 : (τ : ZMod N) = σ * ((σ⁻¹ * τ : (ZMod N)ˣ) : ZMod N) := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [h2, map_mul, h1, mul_one]

end KStar.Ram
