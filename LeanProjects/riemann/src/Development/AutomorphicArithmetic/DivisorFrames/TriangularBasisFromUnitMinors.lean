import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

private theorem minor_snoc_expand {K : Type} [CommRing K] {n g k : ℕ} (a : Fin n → Fin g → K) (hk : k < n)
    (s : Fin k → Fin g) : ∃ t : Fin n → K, t ⟨k, hk⟩ = minor a hk.le s ∧ (∀ l : Fin n, k < l.1 → t l = 0) ∧
      ∀ j, minor a (Nat.succ_le_of_lt hk) (Fin.snoc (α := fun _ => Fin g) s j) = ∑ l, t l * a l j := by
  have hk' : k + 1 ≤ n := Nat.succ_le_of_lt hk
  let c : Fin (k + 1) → K := fun l => (-1) ^ ((l : ℕ) + k) *
    (Matrix.of fun (p q : Fin k) => a (Fin.castLE hk' (l.succAbove p)) (s q)).det
  refine ⟨fun l => if h : l.1 < k + 1 then c ⟨l.1, h⟩ else 0, ?_, fun l hl => dif_neg (by omega), fun j => ?_⟩
  · have h1 : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
    simp only [Nat.lt_succ_self, dif_pos, c, h1, Fin.val_last, Fin.succAbove_last, minor]
    rw [← two_mul, pow_mul, neg_one_sq, one_pow, _root_.one_mul]
    rfl
  · rw [minor, Matrix.det_succ_column _ (Fin.last k)]
    refine Finset.sum_of_injOn (Fin.castLE hk') (Fin.castLE_injective hk').injOn (by simp) (fun l _ hl => ?_)
      (fun l _ => ?_)
    · beta_reduce
      rw [dif_neg, zero_mul]
      intro hc
      exact hl ⟨⟨l, hc⟩, by simp, rfl⟩
    · have h2 : (Fin.castLE hk' l).1 < k + 1 := l.2
      beta_reduce
      rw [dif_pos h2]
      simp only [c, Matrix.of_apply, Fin.snoc_last, Fin.val_last, Fin.val_castLE, Fin.eta, Fin.succAbove_last]
      rw [mul_right_comm]
      congr 3
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.snoc_castSucc]

theorem UpperTheory.triangular_basis_from_unit_minors :
    ∀ (A K : Type) [CommRing A] [CommRing K] (ι : A →+* K), Function.Injective ι → ∀ (n g : ℕ) (a : Fin n → Fin g → K), (∀ (k : ℕ) (hk : k ≤ n) (s : Fin k → Fin g), ∃ c : A, ι c = minor a hk s) → (∀ (k : ℕ) (hk : k ≤ n), ∃ (s : Fin k → Fin g) (c : Aˣ), ι c = minor a hk s) → ∃ (v : Fin n → Fin g → A) (T : Fin n → Fin n → K), (∀ i, T i i = 1) ∧ (∀ i l, i < l → T i l = 0) ∧ (∀ i, (fun j => ι (v i j)) = ∑ l, T i l • a l) ∧ ∃ s, IsUnit (minor v le_rfl s) := by
  intro A K _ _ ι hι n g a h1 h2
  have key : ∀ i : Fin n, ∃ (w : Fin g → A) (t : Fin n → K), t i = 1 ∧ (∀ l, i < l → t l = 0) ∧
      (fun j => ι (w j)) = ∑ l, t l • a l := by
    intro i
    obtain ⟨s, u, hu⟩ := h2 i.1 i.2.le
    obtain ⟨t, ht1, ht2, ht3⟩ := minor_snoc_expand a i.2 s
    choose c hc using fun j => h1 _ (Nat.succ_le_of_lt i.2) (Fin.snoc (α := fun _ => Fin g) s j)
    refine ⟨fun j => (u⁻¹ : Aˣ) * c j, fun l => ι (u⁻¹ : Aˣ) * t l, ?_, fun l hl => ?_, ?_⟩
    · have : t i = ι u := ht1.trans hu.symm
      simp only [this]
      rw [← map_mul, Units.inv_mul, map_one]
    · simp only [ht2 l hl, mul_zero]
    · funext j
      simp only [map_mul, hc, ht3, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, _root_.mul_assoc]
  choose v T hT1 hT2 hT3 using key
  refine ⟨v, T, hT1, hT2, hT3, ?_⟩
  obtain ⟨s, u, hu⟩ := h2 n le_rfl
  refine ⟨s, u, hι ?_⟩
  rw [hu, GlobalTheory.LineNorm.Chart.map_minor, GlobalTheory.LineNorm.Chart.minor_tri a _ T hT2 hT3]
  simp only [hT1, Finset.prod_const_one, _root_.one_mul]
