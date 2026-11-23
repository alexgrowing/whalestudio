import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionIffShiftedProductsKillComaximaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section
namespace GlobalTheory.UPel.HT.LieLin
open Matrix

theorem ringHom_mapMatrix_algebraMap_scalar {B T : Type} [CommRing B] [CommRing T] (f : B →+* T) {n : ℕ} (x : B) :
    f.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap T (Matrix (Fin n) (Fin n) T) (f x) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

theorem list_prod_matrixActionAfterRingHom_sub_apply {O T : Type} [CommRing O] [CommRing T] {n : ℕ} {B : Type} [CommRing B]
    (M : O →+* Matrix (Fin n) (Fin n) B) (f : B →+* T) {a : ℕ} (c : Fin a → O) (τ : Fin a → (O →+* T))
    (v : Fin n → T) :
    (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))).prod v =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).prod *ᵥ v := by
  have h : (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))) =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).map
        (Matrix.toLinAlgEquiv' (R := T) (n := Fin n)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, map_sub, AlgEquiv.commutes]
    rfl
  rw [h, ← map_list_prod]
  rfl

theorem lieMod_matAct_iff_lieIdeal_le_ker : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (T : Type) [CommRing T] (f : B →+* T),
    LieMod (matAct M f) D.ω (f (βB b.ρ)) (fun i => (f.comp βB).comp (b.t i)) ↔ lieIdeal b βB M ≤ RingHom.ker f := by
  intro p _ D R _ b B _ βB n M T _ f
  set g : R →+* T := f.comp βB with hg
  set τ : Fin D.a → (𝓞 D.F →+* T) := fun i => g.comp (b.t i) with hτ
  set ρ' : T := g b.ρ with hρ'
  set Nh : 𝓞 D.F →+* Matrix (Fin n) (Fin n) T := f.mapMatrix.comp M with hNh
  let Am : T →+* Matrix (Fin n) (Fin n) T := algebraMap T (Matrix (Fin n) (Fin n) T)
  set P : (Fin D.a → 𝓞 D.F) → Matrix (Fin n) (Fin n) T :=
    fun c => (List.ofFn fun i => (M (c i)).map f - Am (τ i (c i))).prod with hP
  set Q : Matrix (Fin n) (Fin n) T := Nh D.ω - Am (g ((D.tr : R) - b.ρ)) with hQ

  have hmap : ∀ c, f.mapMatrix (lieMat b βB M c) = P c * Q := by
    intro c
    rw [lieMat, map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2; funext i; rw [Function.comp_apply, map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
    · rw [map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
  have hdec : ∀ v, (∃ w : Fin D.a → (Fin n → T), (∀ i, w i ∈ eigSub (matAct M f) (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c, P c *ᵥ v = 0 := by
    intro v
    have hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤ := by
      intro i j hij
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      convert h using 3
      funext x
      simp [hτ]
    rw [GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal (𝓞 D.F) T (Fin n → T) (matAct M f) D.a τ hcomax v]
    simp only [list_prod_matrixActionAfterRingHom_sub_apply, hP]
    rfl

  have hω : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : ρ' * ρ' - (D.tr : T) * ρ' + (D.nm : T) = 0 := by
    have := congrArg g b.ρ_root
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    rw [hρ']; linear_combination this
  have hquad : (Nh D.ω - Am ρ') * Q = 0 := by
    have hX : Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) = 0 := by
      have := congrArg Nh hω
      simpa [map_intCast] using this
    have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']
    rw [hQ, hs]
    calc (Nh D.ω - Am ρ') * (Nh D.ω - Am ((D.tr : T) - ρ'))
        = Nh D.ω * Nh D.ω - Am (ρ' + ((D.tr : T) - ρ')) * Nh D.ω + Am (ρ' * ((D.tr : T) - ρ')) := by
          rw [map_add, map_mul, sub_mul, mul_sub, mul_sub, add_mul, ← Algebra.commutes ((D.tr : T) - ρ') (Nh D.ω)]
          abel
      _ = Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) := by
          congr 2
          · congr 2; ring
          · congr 1; linear_combination -hρ
      _ = 0 := hX
  have hAm : ∀ (x : T) (v : Fin n → T), Am x *ᵥ v = x • v := by
    intro x v
    simp only [Am, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hact : ∀ v, matAct M f D.ω v = Nh D.ω *ᵥ v := fun v => rfl
  have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']

  have hu : IsUnit (ρ' - ((D.tr : T) - ρ')) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = 4 * D.nm - D.tr ^ 2 := ⟨(4 * D.nm - D.tr ^ 2).toNat,
      Int.toNat_of_nonneg (by have := D.disc_neg; omega)⟩
    have hkp : k.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro hd
      apply D.disc_p
      have : (p : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.2 hd
      rw [hk] at this
      have h2 : D.tr ^ 2 - 4 * D.nm = -(4 * D.nm - D.tr ^ 2) := by ring
      rw [h2]; exact (dvd_neg).2 this
    have hkT : IsUnit (k : T) := by
      have := (b.unit k hkp).map g
      simpa using this
    have hsq : (ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ')) = -(k : T) := by
      have : ((k : ℤ) : T) = ((4 * D.nm - D.tr ^ 2 : ℤ) : T) := by rw [hk]
      push_cast at this
      rw [this]; linear_combination 4 * hρ
    have : IsUnit ((ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ'))) := by
      rw [hsq]; exact hkT.neg
    exact isUnit_of_mul_isUnit_left this
  constructor
  · intro hL
    rw [lieIdeal, Ideal.span_le]
    rintro x ⟨c, i, j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have he : f (lieMat b βB M c i j) = ((P c * Q) *ᵥ Pi.single j 1) i := by
      rw [Matrix.mulVec_single_one, ← hmap]
      rfl
    rw [he, ← Matrix.mulVec_mulVec]
    set w := Q *ᵥ Pi.single j 1 with hw
    have hwe : matAct M f D.ω w = ρ' • w := by
      have h0 : ((Nh D.ω - Am ρ') * Q) *ᵥ Pi.single j 1 = 0 := by rw [hquad, Matrix.zero_mulVec]
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hAm, sub_eq_zero] at h0
      rw [hact, ← hw] at *
      exact h0
    obtain ⟨w', hw'⟩ := hL w hwe
    have := (hdec w).1 ⟨w', hw'⟩ c
    rw [this]; rfl
  · intro hI v hv
    apply (hdec v).2
    intro c
    have hz : P c * Q = 0 := by
      ext i j
      have := hI (Ideal.subset_span ⟨c, i, j, rfl⟩)
      rw [RingHom.mem_ker] at this
      rw [← hmap]
      simpa using this
    have hQv : Q *ᵥ v = (ρ' - ((D.tr : T) - ρ')) • v := by
      rw [hQ, Matrix.sub_mulVec, hAm, ← hact, hv, hs]
      change ρ' • v - ((D.tr : T) - ρ') • v = _
      rw [← sub_smul]
    have h1 : (ρ' - ((D.tr : T) - ρ')) • (P c *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]
    exact (hu.smul_eq_zero).1 h1

end GlobalTheory.UPel.HT.LieLin
