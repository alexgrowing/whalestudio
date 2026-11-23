import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledMatrixMemRationalLattice

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceDatum

open GlobalTheory.PlaceModel

theorem isUnit_add_sum_idem {R ι : Type} [CommRing R] (hR : ∀ n : ℕ, 0 < n → IsUnit (n : R)) (p : ι → R) (s : Finset ι) :
    (∀ i ∈ s, p i * p i = p i) → ∀ n : ℕ, 0 < n → IsUnit ((n : R) + ∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ n hn; simpa using hR n hn
  | insert a s ha ih =>
    intro h n hn
    have h' := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨u, hu⟩ := (h' n hn).exists_right_inv
    obtain ⟨v, hv⟩ := (h' (n + 1) n.succ_pos).exists_right_inv
    have hp := h a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha]
    refine IsUnit.of_mul_eq_one ((1 - p a) * u + p a * v) ?_
    push_cast at hv
    linear_combination (1 - p a) * hu + p a * hv + (v - u) * hp

theorem eq_zero_of_sum_idem {R ι : Type} [CommRing R] (hR : ∀ n : ℕ, 0 < n → IsUnit (n : R)) (p : ι → R) (s : Finset ι)
    (h : ∀ i ∈ s, p i * p i = p i) (h0 : ∑ i ∈ s, p i = 0) {i : ι} (hi : i ∈ s) : p i = 0 := by
  classical
  have hu := isUnit_add_sum_idem hR p (s.erase i) (fun j hj => h j (Finset.mem_of_mem_erase hj)) 1 one_pos
  rw [← Finset.add_sum_erase s p hi] at h0
  refine (hu.mul_left_eq_zero).1 ?_
  push_cast
  linear_combination p i * h0 - h i hi

variable {D : D7}

theorem isUnit_natCast (n : ℕ) (hn : 0 < n) : IsUnit (n : AE D) := by
  rw [← map_natCast (incA D)]
  exact (Ne.isUnit (Nat.cast_ne_zero.2 hn.ne')).map _

theorem placeIdem_eq {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨β, rfl, k1, k0⟩ := h'
  congr 1
  refine RestrictedProduct.ext _ _ fun w => ?_
  by_cases hw : w = v
  · subst hw; exact h1.trans k1.symm
  · exact (h0 w hw).trans (k0 w hw).symm

theorem placeIdem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero _) ?_
  change α * β = 0
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV D.host.F w (α * β) = evalV D.host.F w 0
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · subst hw; rw [k0 w hv, mul_zero]
  · rw [h0 w hw, zero_mul]

theorem cross_eq_zero {R ι : Type} [CommRing R] (hR : ∀ n : ℕ, 0 < n → IsUnit (n : R)) (c : R →+* R) (p : ι → R)
    (s : Finset ι) (h : ∀ i ∈ s, p i * p i = p i) (hc : (∑ i ∈ s, p i) * c (∑ i ∈ s, p i) = 0) :
    ∀ i ∈ s, ∀ j ∈ s, p i * c (p j) = 0 := by
  intro i hi j hj
  rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product'] at hc
  refine eq_zero_of_sum_idem hR (fun q : ι × ι => p q.1 * c (p q.2)) _ (fun q hq => ?_) hc
    (i := (i, j)) (Finset.mem_product.2 ⟨hi, hj⟩)
  rw [mul_mul_mul_comm, ← map_mul, h _ (Finset.mem_product.1 hq).1, h _ (Finset.mem_product.1 hq).2]

theorem sum_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i ∈ s, p i * p i = p i)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0) : (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => h0 i hi j hj hji) (fun h => absurd hi h), h i hi]

theorem idempotent_eq_of_orthogonal_decomp {R : Type} [CommRing R] {a a' b b' : R} (a1 : a * a = a) (a2 : a * a' = 0) (b1 : b * b = b)
    (b2 : b * b' = 0) (h : a + a' = b + b') (h1 : a * b' = 0) (h2 : b * a' = 0) : a = b := by
  linear_combination (a + b) * h - a1 - a2 + h1 + b1 + b2 - h2

theorem idempotent_mul_eq_zero_of_orthogonal {R : Type} [CommRing R] {a a' b b' : R} (a1 : a * a = a) (a2 : a * a' = 0) (b1 : b * b = b)
    (b2 : b * b' = 0) (h : (a + a') * (b + b') = 0) : a * b = 0 := by
  have hi : a * (a + a') = a := by linear_combination a1 + a2
  have hj : b * (b + b') = b := by linear_combination b1 + b2
  rw [← hi, ← hj, mul_mul_mul_comm, h, mul_zero]

theorem idemAt_mul {a b : AE D} {i j : Formalism.L2.DIV.Pl D.host.E} (ha : Formalism.L2.NTheta.IsIdemAt a i)
    (hb : Formalism.L2.NTheta.IsIdemAt b j) (h1 : a * cA D b = 0) (h2 : b * cA D a = 0) (hji : j ≠ i) : a * b = 0 := by
  obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, a4⟩ := ha
  obtain ⟨⟨b1, b2, v', ε', hε', b3⟩, b4⟩ := hb
  by_cases hv : v = v'
  · rw [← hv] at hε'
    have : a = b := idempotent_eq_of_orthogonal_decomp a1 a2 b1 b2 (a3.trans (placeIdem_eq hε hε' ▸ b3.symm)) h1 h2
    refine absurd (HeightOneSpectrum.ext (Ideal.ext fun x => ?_)) hji
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [a4 x hx, b4 x hx, this]
  · refine idempotent_mul_eq_zero_of_orthogonal a1 a2 b1 b2 ?_
    rw [a3, b3, ← RingHom.map_mul, placeIdem_mul hε hε' hv, RingHom.map_zero]

theorem idemSum_mul_self {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) : e * e = e := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    cross_eq_zero (R := AE D) isUnit_natCast (cA D) es P h1 hc
  have h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    idemAt_mul (hes i hi) (hes j hj) (hcross i hi j hj) (hcross j hj i hi) hji
  exact sum_idem (R := AE D) es P h1 h2

theorem map_sum_eq_zero {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι)
    (h : ∀ i ∈ s, f (p i) = 0) : f (∑ i ∈ s, p i) = 0 := by
  rw [map_sum]; exact Finset.sum_eq_zero h

theorem infPart_idemSum {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) : infPart D e = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  refine map_sum_eq_zero (infPart D) es P fun i hi => ?_
  obtain ⟨⟨a1, a2, v, ε, ⟨β, rfl, -⟩, a3⟩, -⟩ := hes i hi
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have hi' : es i * (es i + cA D (es i)) = es i := by rw [mul_add, a1, a2, add_zero]
  rw [← hi', a3, RingHom.map_mul, h0, mul_zero]

theorem infPart_cA {e : AE D} (h : infPart D e = 0) : infPart D (cA D e) = 0 := by
  have key : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
    | tmul a x => rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]
  rw [key, h, RingHom.map_zero]

theorem mem_waveSpan {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G} (h : IsBichar χ)
    (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (Φ : G → ℂ) (h1 : ∀ t, Φ t ≠ 0 → t ∈ X) (k : ℕ) (hk : 0 < k) (h2 : ∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t)
    (h3 : ∀ t, Φ t ≠ 0 → k • t ∈ L) : Φ ∈ waveSpan χ X Y L := by
  obtain ⟨R, hR, hR'⟩ := hfin k hk
  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : G => k • t) ⁻¹' R2).Finite := hR2.preimage (tf k hk).injOn
  refine mem_of_finite_cosets (K := L.map (nsmulAddMonoidHom k))
    (ind_nsmul_mem h hL hL' hLL' hX (dX k hk) (dY k hk) R hR hR') hP.toFinset Φ h1 ?_ fun t ht => ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact h2 u hu
  · obtain ⟨r, hr, u, hu, e⟩ := hR2' _ (h3 t ht)
    refine ⟨t - k • u, hP.mem_toFinset.2 ?_, k • u, ⟨u, hu, rfl⟩, by abel⟩
    change k • (t - k • u) ∈ R2
    rwa [smul_sub, e, smul_smul, add_sub_cancel_right]

variable {S T : HSp D}

theorem infPart_of_half {e : AE D} (h : infPart D e = 0) {u : WO S T} (hu : IsHalf e u) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, ← hu i j, RingHom.map_mul, h, zero_mul]
  rfl

theorem placeModel_unique_of_dual (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁)
    (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₂) {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) :
    T₁ Φ = T₂ Φ := by
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e)) (Λ ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e Λ
    have s1 : IsSBHalf e Λ fun t => ψ (symplO S T t y) * halfInd e Λ t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e Λ t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := h₁.vac
    have v2 := h₂.vac
    rw [one_smul] at v1 v2
    rw [e1, h₁.trans _ s1 x ((isHalf_iff S T).2 hx), h₂.trans _ s1 x ((isHalf_iff S T).2 hx),
      h₁.modul _ s0 y ((isHalf_iff S T).2 hy), h₂.modul _ s0 y ((isHalf_iff S T).2 hy), v1, v2]
  | zero => rw [LinearMap.map_zero, LinearMap.map_zero]
  | add f g _ _ hf hg => rw [LinearMap.map_add, LinearMap.map_add, hf, hg]
  | smul c f _ hf => rw [LinearMap.map_smul, LinearMap.map_smul, hf]

theorem exists_common_den {A ι : Type} [CommRing A] [Finite ι] (R : Subring A) {p : ι → A → Prop}
    (h : ∀ i, ∃ N : ℕ, 0 < N ∧ ∀ z, p i z → (N : A) * z ∈ R) : ∃ N : ℕ, 0 < N ∧ ∀ i z, p i z → (N : A) * z ∈ R := by
  classical
  have := Fintype.ofFinite ι
  choose N hN h using h
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i z hz => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem R _) (h i z hz)

theorem exists_den_matrix {A : Type} [CommRing A] (R : Subring A) (hA : ∀ z : A, ∃ N : ℕ, 0 < N ∧ (N : A) * z ∈ R)
    {a b : Type} [Finite a] [Finite b] (P : Matrix a b A) : ∃ N : ℕ, 0 < N ∧ ∀ i j, (N : A) * P i j ∈ R := by
  obtain ⟨N, hN, h⟩ := exists_common_den R (p := fun (q : a × b) z => z = P q.1 q.2) fun q => by
    obtain ⟨N, hN, h⟩ := hA (P q.1 q.2)
    exact ⟨N, hN, fun z hz => hz ▸ h⟩
  exact ⟨N, hN, fun i j => h (i, j) _ rfl⟩

theorem exists_den_mul {A : Type} [CommRing A] (R : Subring A) (hA : ∀ z : A, ∃ N : ℕ, 0 < N ∧ (N : A) * z ∈ R)
    {a b c d : Type} [Finite a] [Fintype b] [Fintype c] [Finite d] (P : Matrix a b A) (Q : Matrix c d A) :
    ∃ N : ℕ, 0 < N ∧ ∀ (M : ℕ) (X : Matrix b c A), (∀ i j, (M : A) * X i j ∈ R) →
      ∀ i j, ((N * M : ℕ) : A) * (P * X * Q) i j ∈ R := by
  obtain ⟨N₁, h₁, hP⟩ := exists_den_matrix R hA P
  obtain ⟨N₂, h₂, hQ⟩ := exists_den_matrix R hA Q
  refine ⟨N₁ * N₂, Nat.mul_pos h₁ h₂, fun M X hX i j => ?_⟩
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine sum_mem fun k _ => sum_mem fun l _ => ?_
  convert mul_mem (mul_mem (hP i l) (hX l k)) (hQ k j) using 1
  push_cast
  ring

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_mem_int {b : E} (hb : b ∈ Formalism.UG.intOE E) {α : Af F} (hα : α ∈ Formalism.UG.intAd F) :
    b ⊗ₜ[F] α ∈ Formalism.L2.Herm.intAf F E := by
  have h1 : b ⊗ₜ[F] (1 : Af F) ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inl ⟨⟨b, hb⟩, rfl⟩)
  have h2 : (1 : E) ⊗ₜ[F] α ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
  simpa using mul_mem h1 h2

theorem natCast_mul_tmul (N : ℕ) (b : E) (α : Af F) :
    (N : E ⊗[F] Af F) * (b ⊗ₜ[F] α) = ((N : E) * b) ⊗ₜ[F] α := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.smul_tmul']

theorem exists_den_adele (z : E ⊗[F] Af F) : ∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * z ∈ Formalism.L2.Herm.intAf F E := by
  have hadd : ∀ x y : E ⊗[F] Af F, (∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * x ∈ Formalism.L2.Herm.intAf F E) →
      (∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * y ∈ Formalism.L2.Herm.intAf F E) →
      ∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * (x + y) ∈ Formalism.L2.Herm.intAf F E := by
    rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
    convert add_mem (mul_mem (natCast_mem _ M) hx) (mul_mem (natCast_mem _ N) hy) using 1
    push_cast
    ring
  have hp : ∀ (b : E) (α : Af F), α ∈ Formalism.UG.intAd F →
      ∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * (b ⊗ₜ[F] α) ∈ Formalism.L2.Herm.intAf F E := fun b α hα => by
    obtain ⟨d, hd, h⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E b
    exact ⟨d, hd, by rw [natCast_mul_tmul]; exact tmul_mem_int h hα⟩
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y hx hy => exact hadd _ _ hx hy
  | tmul b α =>
    obtain ⟨x, β, hβ, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos α
    rw [one_smul, TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    exact hadd _ _ (hp _ _ (one_mem _)) (hp _ _ hβ)

theorem comm_symm_mem {r : E ⊗[F] Af F} (hr : r ∈ Formalism.L2.Herm.intAf F E) :
    (Algebra.TensorProduct.comm F (Af F) E).symm r ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  induction hr using Subring.closure_induction with
  | mem r hr =>
    rcases hr with ⟨⟨b, hb⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
    · exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F hb
    · exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F hβ ⟨1, map_one _⟩
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact GlobalTheory.AdIdem.mul_mem_hat F E ha hb

theorem exists_den_fg {M : Type} [AddCommGroup M] [Module (𝓞 E) M] {Λ : Submodule (𝓞 E) M} (h : Λ.FG)
    (φ : M →ₗ[𝓞 E] E) : ∃ N : ℕ, 0 < N ∧ ∀ z, (∃ x ∈ Λ, z = φ x) → (N : E) * z ∈ Formalism.UG.intOE E := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨N, hN, h⟩ := exists_common_den (Formalism.UG.intOE E) (p := fun (q : s) z => z = φ q) fun q => by
    obtain ⟨N, hN, h⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E (φ q)
    exact ⟨N, hN, fun z hz => hz ▸ h⟩
  refine ⟨N, hN, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h ⟨x, hx⟩ _ rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, mul_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, Algebra.smul_def, mul_left_comm]
    exact mul_mem ⟨c, rfl⟩ hx

theorem exists_den_fg_pi {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : Λ.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, ∀ i, (N : E) * x i ∈ Formalism.UG.intOE E := by
  obtain ⟨N, hN, h⟩ := exists_common_den (Formalism.UG.intOE E) fun i : Fin n => exists_den_fg h (LinearMap.proj i)
  exact ⟨N, hN, fun x hx i => h i _ ⟨x, hx, rfl⟩⟩

theorem star_mem_intOE [StarRing E] {x : E} (hx : x ∈ Formalism.UG.intOE E) : star x ∈ Formalism.UG.intOE E := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨⟨_, IsIntegral.map (starRingEnd E).toIntAlgHom b.2⟩, rfl⟩

theorem resS_natCast_absNorm (PP : Formalism.L2.DIV.Pl E) :
    ((Ideal.absNorm PP.asIdeal : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.absNorm_mem _

theorem resS_add (PP : Formalism.L2.DIV.Pl E) {x y z : E ⊗[F] Af F} (hx : x ∈ Formalism.L2.Herm.intAf F E)
    (hy : y ∈ Formalism.L2.Herm.intAf F E) (hz : z ∈ Formalism.L2.Herm.intAf F E)
    (h : y = x + (Ideal.absNorm PP.asIdeal : ℕ) * z) :
    Formalism.L2.DIV.resS F PP ⟨y, hy⟩ = Formalism.L2.DIV.resS F PP ⟨x, hx⟩ := by
  have e : (⟨y, hy⟩ : Formalism.L2.Herm.intAf F E) = ⟨x, hx⟩ + (Ideal.absNorm PP.asIdeal : ℕ) * ⟨z, hz⟩ := Subtype.ext h
  rw [e, map_add, map_mul, map_natCast, resS_natCast_absNorm, zero_mul, add_zero]

end General

theorem finPart_mem_of_toEAf {w : AE D} (hw : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    finPart D w ∈ intAE D := by
  have h : intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
    unfold intAE GlobalTheory.AdLat.hat1
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, rfl⟩
      exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
      exact ⟨a, ha, x, rfl⟩
  rw [h, ← (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm_apply_apply (finPart D w)]
  exact comm_symm_mem hw

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_den_latRat (hS : ΛS.FG) (hT : ΛT.FG) : ∃ M : ℕ, 0 < M ∧
    ∀ X ∈ GlobalTheory.LatVac.latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)),
      ∀ i j, (M : D.host.E) * X i j ∈ Formalism.UG.intOE D.host.E := by
  obtain ⟨N₁, h₁, k₁⟩ := exists_den_fg (Λ := (D.host.AA : Submodule (𝓞 D.host.E) D.host.E))
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _) LinearMap.id
  obtain ⟨N₂, h₂, k₂⟩ := exists_den_fg_pi hT
  obtain ⟨N₃, h₃, k₃⟩ := exists_den_fg_pi hS
  obtain ⟨N₄, h₄, k₄⟩ := exists_den_matrix (Formalism.UG.intOE D.host.E) (GlobalTheory.AdIdem.exists_nat_mul_integral _) S.gram
  refine ⟨N₁ * N₂ * N₃ * N₄, by positivity, fun X hX i j => ?_⟩
  induction hX using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
    simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Finset.mul_sum]
    refine sum_mem fun k _ => ?_
    convert mul_mem (mul_mem (mul_mem (k₁ a ⟨a, ha, rfl⟩) (k₂ t ht i)) (star_mem_intOE (k₃ s hs k))) (k₄ k j) using 1
    rw [star_mul', star_natCast]
    push_cast
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_apply, mul_neg]; exact neg_mem hx

theorem exists_den_latO (hS : ΛS.FG) (hT : ΛT.FG) : ∃ M : ℕ, 0 < M ∧
    ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, (M : EAf D) * toEAf D (u i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨M, hM, h⟩ := exists_den_latRat hS hT
  refine ⟨M, hM, fun u hu i j => ?_⟩
  refine GlobalTheory.LatVac.latO_induction
    (p := fun u => (M : EAf D) * toEAf D (u i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ?_ ?_ ?_ ?_ hu
  · intro α hα X hX
    change (M : EAf D) * (X i j ⊗ₜ[D.host.F] α) ∈ _
    rw [natCast_mul_tmul]
    exact tmul_mem_int (h X hX i j) hα
  · rw [Matrix.zero_apply, RingHom.map_zero, mul_zero]; exact zero_mem _
  · intro x y hx hy; rw [Matrix.add_apply, RingHom.map_add, mul_add]; exact add_mem hx hy
  · intro x hx; rw [Matrix.neg_apply, RingHom.map_neg, mul_neg]; exact neg_mem hx

theorem mul_pair_one {w : AE D} (hw : infPart D w = 0) :
    w * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = w := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, RingHom.map_mul, hw, zero_mul, sub_zero]
  · rw [RingHom.map_sub, RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, ← Algebra.TensorProduct.one_def, mul_one, sub_self]

theorem exists_nsmul_mem_latO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) :
    ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
      (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
      K • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  classical
  choose N hN h using fun p : Fin T.rank × Fin S.rank =>
    GlobalTheory.LatVacFull.latRat_full D S T ΛS ΛT hS hT (Matrix.single p.1 p.2 1)
  refine ⟨∏ p, N p, Finset.prod_pos fun p _ => hN p, fun t ht hi => ?_⟩
  rw [Matrix.matrix_eq_sum_single t, ← Finset.sum_product', ← Finset.sum_nsmul]
  refine sum_mem fun p _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ p), mul_nsmul']
  refine nsmul_mem ?_ _
  convert GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_mem_of_toEAf (hi p.1 p.2)) _
    (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (h p)) using 1
  ext i j
  change N p • Matrix.single p.1 p.2 (t p.1 p.2) i j =
    t p.1 p.2 * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (N p • Matrix.single p.1 p.2 (1 : D.host.E) i j))
  rw [TensorProduct.tmul_smul, nsmul_eq_mul, nsmul_eq_mul, mul_left_comm, Matrix.single_apply, Matrix.single_apply]
  split_ifs
  · rw [mul_pair_one (congrFun (congrFun ht p.1) p.2)]
  · rw [TensorProduct.tmul_zero, mul_zero, mul_zero, mul_zero]

theorem exists_nsmul_mem_latO' (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (t : WO S T) (ht : t.map (infPart D) = 0) : ∃ k : ℕ, 0 < k ∧
      k • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨K, hK, h⟩ := exists_nsmul_mem_latO hS hT
  obtain ⟨N, hN, h'⟩ := exists_den_matrix (Formalism.L2.Herm.intAf D.host.F D.host.E) exists_den_adele (t.map (toEAf D))
  refine ⟨N * K, Nat.mul_pos hN hK, ?_⟩
  rw [mul_nsmul]
  refine h _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · change infPart D (N • t i j) = 0
    rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (t i j) = 0 from congrFun (congrFun ht i) j, mul_zero]
  · change toEAf D (N • t i j) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact h' i j

theorem exists_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {e : AE D} (he : e * e = e) (hinf : infPart D e = 0) {f₀ Φ : WO S T → ℂ}
    (hex : ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    (hΦ : IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ) :
    ∃ f, IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f := by
  obtain ⟨Tm, hTm⟩ := hex
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  refine ⟨Tm Φ, ⟨Tm, hTm⟩, fun T' hT' => placeModel_unique_of_dual ψ _ (fun u hu y hy => ?_) (fun x hx h => ?_)
    (fun k hk => ?_) (fun y hy => ?_) hTm hT' hΦ⟩
  · exact (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  · refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  · exact exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))

theorem redM_add {a b : ℕ} (PP : Formalism.L2.DIV.Pl D.host.E) (X Y Z : Matrix (Fin b) (Fin a) (EAf D)) (hX : IsIntM X)
    (hZ : IsIntM Z) (h : ∀ i j, Y i j = X i j + (Ideal.absNorm PP.asIdeal : ℕ) * Z i j) : redM PP Y = redM PP X := by
  funext i j
  have hY : Y i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h]; exact add_mem (hX i j) (mul_mem (natCast_mem _ _) (hZ i j))
  have e : redM PP X i j = Formalism.L2.DIV.resS D.host.F PP ⟨X i j, hX i j⟩ := dif_pos (hX i j)
  exact (dif_pos hY).trans ((resS_add PP (hX i j) hY (hZ i j) (h i j)).trans e.symm)

open Classical in

theorem isSBHalf_of_red {a b : ℕ} (e : AE D) (Λ : AddSubgroup (WO S T)) (fr : WO S T → Matrix (Fin b) (Fin a) (EAf D))
    (hadd : ∀ (x u : WO S T) (k : ℕ) i j, fr (x + k • u) i j = fr x i j + k * fr u i j)
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, ∀ i j, (M : EAf D) * fr u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t, IsHalf e t → IsIntM (fr t) → K • t ∈ Λ)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ω : (∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) → ℂ)
    (hω : ∀ y y', (∀ PP ∈ P, y PP = y' PP) → ω y = ω y') :
    IsSBHalf e Λ fun x => if IsHalf e x ∧ IsIntM (fr x) then ω (fun PP => redM PP (fr x)) else 0 := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  have hN : 0 < ∏ PP ∈ P, Ideal.absNorm PP.asIdeal := Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨fun t ht => ?_, K * ((∏ PP ∈ P, Ideal.absNorm PP.asIdeal) * M), by positivity, fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · have hi : ∀ i j, ((K * ((∏ PP ∈ P, Ideal.absNorm PP.asIdeal) * M) : ℕ) : EAf D) * fr u i j ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => by
      rw [← mul_assoc, Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) (hB u hu i j)
    have h1 : IsHalf e (t + (K * ((∏ PP ∈ P, Ideal.absNorm PP.asIdeal) * M)) • u) ↔ IsHalf e t := by
      rw [isHalf_iff, isHalf_iff]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((isHalf_iff S T).1 hh) _)
    have h2 : IsIntM (fr (t + (K * ((∏ PP ∈ P, Ideal.absNorm PP.asIdeal) * M)) • u)) ↔ IsIntM (fr t) := by
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [hadd]
      exact add_mem_cancel_right (hi i j)
    by_cases ht : IsHalf e t ∧ IsIntM (fr t)
    · simp only [if_pos ht, if_pos (And.intro (h1.2 ht.1) (h2.2 ht.2))]
      refine hω _ _ fun PP hPP => redM_add PP _ _
        (fun i j => ((K * (∏ PP ∈ P.erase PP, Ideal.absNorm PP.asIdeal) : ℕ) : EAf D) * ((M : EAf D) * fr u i j))
        ht.2 (fun i j => mul_mem (natCast_mem _ _) (hB u hu i j)) fun i j => ?_
      rw [hadd, ← Finset.mul_prod_erase P _ hPP]
      simp only [Nat.cast_mul]
      ring
    · simp only [if_neg ht, if_neg fun h : _ ∧ _ => ht ⟨h1.1 h.1, h2.1 h.2⟩]
  · have h : IsHalf e t ∧ IsIntM (fr t) := by
      by_contra h
      exact ht (if_neg h)
    rw [mul_nsmul]
    exact nsmul_mem (hC t h.1 h.2) _

theorem omegaQ_congr {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) (h : ∀ PP ∈ Q, y PP = y' PP) :
    omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
  have hiff : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
      ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det :=
    forall₂_congr fun PP hPP => by rw [h PP hPP]
  unfold omegaQ
  by_cases hy : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dif_pos hy, dif_pos (hiff.1 hy)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    congr 3
    exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 PP.2])
  · rw [dif_neg hy, dif_neg fun h' => hy (hiff.2 h')]

open Classical in

def omegaTop {a : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (A : Prop) (z : ∀ PP : ↥L.Pg, Matrix (Fin a) (Fin a) (Formalism.L2.DIV.kP PP.1)) : ℂ :=
  if h : A ∧
      ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
        (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = z PP) ∧
        (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H then
    ((L.P.chi ⟨fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (h.2.choose PP), h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ PP : ↥L.Pg, ∏ c ∈ Finset.range L.s,
        ((L.cg (c + 1) PP.1 (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (c + 1) (h.2.choose PP)) : ℂˣ) : ℂ)) *
      ∏ PP : ↥L.Pg, (((χj PP.1 (Matrix.GeneralLinearGroup.det (h.2.choose PP))) : ℂˣ) : ℂ)⁻¹
  else 0

theorem omegaG_congr {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) (h : ∀ PP ∈ L.Pg, y PP = y' PP) :
    omegaG L χj y = omegaG L χj y' := by
  have e : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP),
      omegaG L χj y = omegaTop L χj (∀ PP ∈ L.Pg, LowZero a (y PP)) fun PP => topL a (y PP.1) := fun y => by
    unfold omegaG omegaTop
    congr
  rw [e, e, propext (forall₂_congr fun PP hPP => by rw [h PP hPP] :
    (∀ PP ∈ L.Pg, LowZero a (y PP)) ↔ ∀ PP ∈ L.Pg, LowZero a (y' PP))]
  congr 1
  funext PP
  rw [h PP.1 PP.2]

theorem frMapO_add (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x u : WO S T) (k : ℕ)
    (i : Fin T.rank) (j : Fin S.rank) :
    frMapO S T βS βT (x + k • u) i j = frMapO S T βS βT x i j + k * frMapO S T βS βT u i j := by
  have : ∀ a b, toEAf D ((x + k • u) a b) = toEAf D (x a b) + k * toEAf D (u a b) := fun a b => by
    change toEAf D (x a b + k • u a b) = _
    rw [nsmul_eq_mul, RingHom.map_add, RingHom.map_mul, map_natCast]
  simp only [frMapO, Matrix.mul_apply, Matrix.map_apply, this, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_den_frMapO (hS : ΛS.FG) (hT : ΛT.FG) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    ∃ M : ℕ, 0 < M ∧
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ∀ i j, (M : EAf D) * frMapO S T βS βT u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨M, hM, h⟩ := exists_den_latO hS hT
  obtain ⟨N, hN, h'⟩ := exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E) exists_den_adele (βT⁻¹).val βS.val
  exact ⟨N * M, Nat.mul_pos hN hM, fun u hu => h' M (u.map (toEAf D)) (h u hu)⟩

theorem exists_nsmul_of_frMapO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 → IsIntM (frMapO S T βS βT t) →
      K • t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨K, hK, h⟩ := exists_nsmul_mem_latO hS hT
  obtain ⟨N, hN, h'⟩ := exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E) exists_den_adele βT.val (βS⁻¹).val
  refine ⟨N * K, Nat.mul_pos hN hK, fun t ht hi => ?_⟩
  rw [mul_nsmul]
  refine h _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · change infPart D (N • t i j) = 0
    rw [nsmul_eq_mul, RingHom.map_mul, show infPart D (t i j) = 0 from congrFun (congrFun ht i) j, mul_zero]
  · change toEAf D (N • t i j) ∈ _
    rw [nsmul_eq_mul, RingHom.map_mul, map_natCast]
    have := h' 1 (frMapO S T βS βT t) (fun i j => by rw [Nat.cast_one, one_mul]; exact hi i j) i j
    rwa [mul_one, frMapO, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this

end GlobalTheory.PlaceDatum

end
