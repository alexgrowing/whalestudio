import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutFaithfullyFlat
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecMul

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (f : T' ⟶ T)
    (x : T ⟶ A) (n : ℕ) : f ≫ x ^ n = (f ≫ x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, comp_mul, ih]

end GlobalTheory.SecMul

namespace GlobalTheory

theorem sec_mul_diff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D)
    (s s' s'' : RootFn A D), IsSec n b x s → IsSec n b y s' → IsSec n b (x * y) s'' → ∃! e : D,
    ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → s'' D' φ (z * w) - s D' φ z - s' D' φ w = φ e := by
  intro R _ A _ _ n hR b hb D _ _ x y s s' s'' hs hs' hs''
  have hroot : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (p : Pt A D) (z : Pt A E), z ^ n = spOver φ ≫ p →
      (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ p := by
    intro E _ _ E' _ _ φ ψ p z hz
    rw [← SecMul.comp_pow_pt, hz, ← Category.assoc, spOver_comp]
  have hmul : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z w : Pt A E), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → (z * w) ^ n = spOver φ ≫ (x * y) := by
    intro E _ _ φ z w hz hw
    rw [mul_pow, hz, hw, comp_mul]
  have hinv : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z z' w w' : Pt A E),
      z ^ n = spOver φ ≫ x → z' ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y → w' ^ n = spOver φ ≫ y →
      s'' E φ (z' * w') - s E φ z' - s' E φ w' = s'' E φ (z * w) - s E φ z - s' E φ w := by
    intro E _ _ φ z z' w w' hz hz' hw hw'
    obtain ⟨t, rfl⟩ : ∃ t, z' = z * t := ⟨z⁻¹ * z', (mul_inv_cancel_left z z').symm⟩
    obtain ⟨u, rfl⟩ : ∃ u, w' = w * u := ⟨w⁻¹ * w', (mul_inv_cancel_left w w').symm⟩
    have ht : t ^ n = 1 := by rw [mul_pow, hz] at hz'; exact mul_eq_left.mp hz'
    have hu : u ^ n = 1 := by rw [mul_pow, hw] at hw'; exact mul_eq_left.mp hw'
    rw [_root_.mul_mul_mul_comm, hs''.2 E φ _ _ (hmul E φ z w hz hw) (by rw [mul_pow, ht, hu, _root_.one_mul]),
      hb.2 E t u ht hu, hs.2 E φ z t hz ht, hs'.2 E φ w u hw hu]
    ring
  have hnat : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (z w : Pt A E), z ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y →
      s'' E' (ψ.comp φ) (spOver ψ ≫ z * spOver ψ ≫ w) - s E' (ψ.comp φ) (spOver ψ ≫ z) -
        s' E' (ψ.comp φ) (spOver ψ ≫ w) = ψ (s'' E φ (z * w) - s E φ z - s' E φ w) := by
    intro E _ _ E' _ _ φ ψ z w hz hw
    rw [← comp_mul, hs''.1 E E' φ ψ _ (hmul E φ z w hz hw), hs.1 E E' φ ψ z hz, hs'.1 E E' φ ψ w hw,
      map_sub, map_sub]
  obtain ⟨D2, _, _, ψ, z0, w0, hf, hz0, hw0⟩ : ∃ (D2 : Type) (_ : CommRing D2) (_ : Algebra R D2)
      (ψ : D →ₐ[R] D2) (z0 w0 : Pt A D2), (ψ : D →+* D2).FaithfullyFlat ∧ z0 ^ n = spOver ψ ≫ x ∧
      w0 ^ n = spOver ψ ≫ y := by
    obtain ⟨D1, _, _, ψ1, z1, hf1, hz1⟩ := hR D x
    obtain ⟨D2, _, _, ψ2, w2, hf2, hw2⟩ := hR D1 (spOver ψ1 ≫ y)
    refine ⟨D2, inferInstance, inferInstance, ψ2.comp ψ1, spOver ψ2 ≫ z1, w2,
      ringHom_faithfullyFlat_comp hf1 hf2, hroot D1 D2 ψ1 ψ2 x z1 hz1, ?_⟩
    rw [hw2, ← Category.assoc, spOver_comp]
  have hinjψ : Function.Injective ψ := RingHom.FaithfullyFlat.injective hf
  obtain ⟨e, he, -⟩ := ff_descent_pairs R D D2 ψ hf
    (s'' D2 ψ (z0 * w0) - s D2 ψ z0 - s' D2 ψ w0) (fun E _ _ α β hαβ ↦ by
      rw [← hnat D2 E ψ α z0 w0 hz0 hw0, ← hnat D2 E ψ β z0 w0 hz0 hw0]
      have h1 := hroot D2 E ψ α x z0 hz0
      have h2 := hroot D2 E ψ α y w0 hw0
      rw [hαβ] at h1 h2 ⊢
      exact hinv E (β.comp ψ) _ _ _ _ (hroot D2 E ψ β x z0 hz0) h1 (hroot D2 E ψ β y w0 hw0) h2)
  refine ⟨e, fun E _ _ φ z w hz hw ↦ ?_, fun e' he' ↦ hinjψ ((he' D2 ψ z0 w0 hz0 hw0).symm.trans he.symm)⟩
  obtain ⟨E', _, _, ψ', φ', hf', hcomm⟩ := exists_pushout_faithfullyFlat R D D2 E ψ φ hf
  apply RingHom.FaithfullyFlat.injective hf'
  have hR2 : ψ' (φ e) = s'' E' (φ'.comp ψ) (spOver φ' ≫ z0 * spOver φ' ≫ w0) - s E' (φ'.comp ψ) (spOver φ' ≫ z0) -
      s' E' (φ'.comp ψ) (spOver φ' ≫ w0) := by
    rw [hnat D2 E' ψ φ' z0 w0 hz0 hw0, ← he]
    change (ψ'.comp φ) e = (φ'.comp ψ) e
    rw [hcomm]
  change ψ' (s'' E φ (z * w) - s E φ z - s' E φ w) = ψ' (φ e)
  rw [← hnat E E' φ ψ' z w hz hw, hR2]
  have h1 := hroot E E' φ ψ' x z hz
  have h2 := hroot E E' φ ψ' y w hw
  rw [hcomm] at h1 h2 ⊢
  exact hinv E' (φ'.comp ψ) _ _ _ _ (hroot D2 E' ψ φ' x z0 hz0) h1 (hroot D2 E' ψ φ' y w0 hw0) h2

end GlobalTheory
