import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoisoCount

open Matrix

theorem vecMul_eq_zero_of_rows_li {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : LinearIndependent K (fun i => X i)) (y : m → K)
    (hy : y ᵥ* X = 0) : y = 0 := by
  rw [Fintype.linearIndependent_iff] at h
  funext i; exact h y (by rw [← vecMul_eq_sum]; exact hy) i

theorem rows_li_of_vecMul {K : Type*} [Field K] {m n : Type*} [Fintype m]
    (X : Matrix m n K) (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) :
    LinearIndependent K (fun i => X i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [h g (by rw [vecMul_eq_sum]; exact hg)]; rfl

theorem det_gram_ne_zero {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] (X : Matrix m n K)
    (h : ∀ y : m → K, y ᵥ* X = 0 → y = 0) : (X * Xᵀ).det ≠ 0 := by
  intro hd
  obtain ⟨y, hy0, hy⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hd
  apply hy0; apply h
  apply dotProduct_self_eq_zero.1
  have : (y ᵥ* X) ⬝ᵥ (y ᵥ* X) = y ⬝ᵥ (X *ᵥ (y ᵥ* X)) := by rw [dotProduct_mulVec]
  rw [this, ← vecMul_transpose, vecMul_vecMul, hy, dotProduct_zero]

theorem gram_map {K : Type*} [CommRing K] {m n : Type*} [Fintype n] (Z : Matrix m n ℤ) :
    Z.map (Int.cast : ℤ → K) * (Z.map (Int.cast : ℤ → K))ᵀ = (Z * Zᵀ).map (Int.cast : ℤ → K) := by
  ext i j; simp [Matrix.mul_apply]

theorem det_map_intCast {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℤ) : (Z.map (Int.cast : ℤ → K)).det = (Z.det : K) := by
  have := RingHom.map_det (Int.castRingHom K) Z
  simpa using this.symm

theorem rank_bound {r r₀ : ℕ} (P : Matrix (Fin r₀) (Fin r₀) ℤ)
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ x ∈ S, P.map (Int.cast : ℤ → ZMod N) *ᵥ x = 0) :
    r + (P.map (Int.cast : ℤ → ℝ)).rank ≤ 2 * r₀ := by
  classical
  set Pr := P.map (Int.cast : ℤ → ℝ) with hPr
  obtain ⟨κ, c, hc, hsp, hli⟩ := exists_linearIndependent' ℝ (fun k => Pr k)
  haveI : Finite κ := Finite.of_injective c hc
  letI : Fintype κ := Fintype.ofFinite κ
  have hρ : Pr.rank = Nat.card κ := by
    rw [Matrix.rank_eq_finrank_span_row, Nat.card_eq_fintype_card, ← finrank_span_eq_card hli, hsp]; rfl
  set R : Matrix κ (Fin r₀) ℤ := P.submatrix c id with hR
  have hRr : ∀ y : κ → ℝ, y ᵥ* R.map (Int.cast : ℤ → ℝ) = 0 → y = 0 :=
    vecMul_eq_zero_of_rows_li _ hli
  have hd0 : (R * Rᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero _ hRr
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  set d := (R * Rᵀ).det
  set N := d.natAbs + 1 with hN
  have hN2 : 2 ≤ N := by have := Int.natAbs_pos.2 hd0; omega
  haveI : NeZero N := ⟨by omega⟩
  have hu : IsUnit (d : ZMod N) := by
    have h1 : ((d.natAbs : ℕ) : ZMod N) = -1 := by
      have : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
      rw [hN] at this; push_cast at this; exact eq_neg_of_add_eq_zero_left this
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast, h1]; exact isUnit_one.neg
    · rw [h, Int.cast_neg, Int.cast_natCast, h1, neg_neg]; exact isUnit_one
  obtain ⟨S, hcard, hSk⟩ := hS N (by omega)
  set RN := R.map (Int.cast : ℤ → ZMod N) with hRN
  let f : (Fin r₀ → ZMod N) →+ (κ → ZMod N) := RN.mulVecLin.toAddMonoidHom
  have hsurj : Function.Surjective f := by
    intro z
    have hG : IsUnit (RN * RNᵀ).det := by rw [hRN, gram_map, det_map_intCast]; exact hu
    refine ⟨RNᵀ *ᵥ ((RN * RNᵀ)⁻¹ *ᵥ z), ?_⟩
    show RN *ᵥ (RNᵀ *ᵥ _) = z
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, one_mulVec]
  have hkc : Nat.card f.ker * N ^ Nat.card κ = N ^ r₀ := by
    have h1 := f.ker.card_mul_index
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top,
      Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin r₀),
      Fintype.card_fin] at h1
    exact h1
  have hsub : S ⊆ (f.ker : Set (Fin r₀ → ZMod N)) := by
    intro x hx
    show RN *ᵥ x = 0
    funext k
    have := congrFun (hSk x hx) (c k)
    exact this
  have hle : Nat.card S ≤ Nat.card f.ker := Nat.card_mono (Set.toFinite _) hsub
  have key : N ^ r * N ^ Nat.card κ ≤ N ^ r₀ * N ^ r₀ := by
    rw [← hcard, ← hkc, _root_.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hle)
  rw [← pow_add, ← pow_add] at key
  have := (Nat.pow_le_pow_iff_right hN2).1 key
  rw [hρ]; omega

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem ker_le_span {r r₀ : ℕ} (Mr : Matrix (Fin r) (Fin r) ℝ) (Ar : Matrix (Fin r₀) (Fin r) ℝ)
    (hM : IsUnit Mr.det) (hA : LinearIndependent ℝ (fun i => Ar i))
    (hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀) :
    LinearMap.ker (Ar * Mrᵀ).mulVecLin ≤ Submodule.span ℝ (Set.range fun i => Ar i) := by
  set T := (Ar * Mrᵀ).mulVecLin
  set E := Arᵀ.mulVecLin
  have hE : Function.Injective E := by
    intro x y hxy
    have : (x - y) ᵥ* Ar = 0 := by
      rw [sub_vecMul, ← mulVec_transpose, ← mulVec_transpose]; exact sub_eq_zero.2 hxy
    exact sub_eq_zero.1 (vecMul_eq_zero_of_rows_li _ hA _ this)
  have hrE : LinearMap.range E = Submodule.span ℝ (Set.range fun i => Ar i) := by
    rw [Matrix.range_mulVecLin]; rfl
  have hAr : Ar.rank = r₀ := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℝ (Submodule.span ℝ (Set.range fun i => Ar i)) = r₀
    rw [finrank_span_eq_card hA, Fintype.card_fin]
  have hT : Module.finrank ℝ (LinearMap.range T) = r₀ := by
    change (Ar * Mrᵀ).rank = r₀
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by rwa [Matrix.det_transpose]), hAr]
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 := LinearMap.finrank_range_add_finrank_ker (T ∘ₗ E)
  have hQ : Module.finrank ℝ (LinearMap.range (T ∘ₗ E)) = (Ar * Mrᵀ * Arᵀ).rank := by
    rw [Matrix.rank, Matrix.mulVecLin_mul]
  have hmap : Submodule.map E (LinearMap.ker (T ∘ₗ E)) = LinearMap.range E ⊓ LinearMap.ker T := by
    rw [LinearMap.ker_comp, Submodule.map_comap_eq]
  have h3 : Module.finrank ℝ (LinearMap.range E ⊓ LinearMap.ker T : Submodule ℝ (Fin r → ℝ)) =
      Module.finrank ℝ (LinearMap.ker (T ∘ₗ E)) := by
    rw [← hmap]; exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective E hE _)).symm
  rw [Module.finrank_fin_fun] at h1 h2
  have heq := Submodule.eq_of_le_of_finrank_le
    (inf_le_right : LinearMap.range E ⊓ LinearMap.ker T ≤ LinearMap.ker T) (by omega)
  rw [← hrE, ← heq]; exact inf_le_left

theorem gramQ {r r₀ : ℕ} (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ) :
    (Matrix.of fun i j => (A i j : ℝ)) * (M.map (Int.cast : ℤ → ℝ))ᵀ * (Matrix.of fun i j => (A i j : ℝ))ᵀ
      = (Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k).map (Int.cast : ℤ → ℝ) := by
  ext i k
  simp [Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CoisoCount

namespace GlobalTheory.CoisoCount

open Matrix

theorem coisotropic_of_torsion_count (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ)
    (A : Fin r₀ → Fin r → ℤ) (hM : M.det ≠ 0)
    (hA : LinearIndependent ℚ (fun i j => (A i j : ℚ)))
    (hS : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧
      ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i))
    (v : Fin r → ℝ)
    (hv : ∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) :
    v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  classical
  set Ar : Matrix (Fin r₀) (Fin r) ℝ := Matrix.of fun i j => (A i j : ℝ) with hAr
  set Mr := M.map (Int.cast : ℤ → ℝ) with hMr
  set P : Matrix (Fin r₀) (Fin r₀) ℤ := Matrix.of fun k i => A i ⬝ᵥ M *ᵥ A k with hP
  have hAz : ((Matrix.of A) * (Matrix.of A)ᵀ).det ≠ 0 := by
    intro h0
    apply det_gram_ne_zero ((Matrix.of A).map (Int.cast : ℤ → ℚ))
      (vecMul_eq_zero_of_rows_li ((Matrix.of A).map (Int.cast : ℤ → ℚ)) hA)
    rw [gram_map, det_map_intCast, h0, Int.cast_zero]
  have hArli : LinearIndependent ℝ (fun i => Ar i) := by
    apply rows_li_of_vecMul
    intro y hy
    have hdet : (Ar * Arᵀ).det ≠ 0 := by
      have : Ar = (Matrix.of A).map (Int.cast : ℤ → ℝ) := rfl
      rw [this, gram_map, det_map_intCast]; exact_mod_cast hAz
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    rw [← vecMul_vecMul, hy, zero_vecMul]
  have hMu : IsUnit Mr.det := by
    rw [hMr, det_map_intCast]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hM)
  have hρ : r + (Ar * Mrᵀ * Arᵀ).rank ≤ 2 * r₀ := by
    rw [hAr, hMr, gramQ]
    apply rank_bound P
    intro N hN
    haveI : NeZero N := ⟨hN.ne'⟩
    obtain ⟨S, hc, hS'⟩ := hS N hN
    refine ⟨S, hc, fun x hx => ?_⟩
    funext k
    set a : Fin r₀ → ℤ := fun i => ((x i).val : ℤ) with ha_def
    have ha : (fun j => (a j : ZMod N)) = x := by funext j; simp only [a]; rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdv := hS' a (Pi.single k 1) (by rw [ha]; exact hx)
    have hsum : (∑ i, (Pi.single k (1 : ℤ) : Fin r₀ → ℤ) i • A i) = A k := by
      simp [Pi.single_apply]
    rw [hsum] at hdv
    have hvs : ∑ i, a i • A i = a ᵥ* Matrix.of A := (vecMul_eq_sum _ _).symm
    have hz : (∑ i, a i • A i) ⬝ᵥ M *ᵥ A k = (P *ᵥ a) k := by
      rw [hvs, ← dotProduct_mulVec, dotProduct_comm]; rfl
    rw [hz] at hdv
    have hcast := RingHom.map_mulVec (Int.castRingHom (ZMod N)) P a k
    have e1 : (((P *ᵥ a) k : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdv
    simp only [Int.coe_castRingHom, e1] at hcast
    have h2 : (Int.cast ∘ a : Fin r₀ → ZMod N) = x := ha
    rw [h2] at hcast
    exact hcast.symm
  have hker : v ∈ LinearMap.ker (Ar * Mrᵀ).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    rw [← mulVec_mulVec, mulVec_transpose]
    have := hv i
    rw [dotProduct_mulVec, dotProduct_comm] at this
    exact this
  exact ker_le_span Mr Ar hMu hArli hρ hker

end GlobalTheory.CoisoCount
