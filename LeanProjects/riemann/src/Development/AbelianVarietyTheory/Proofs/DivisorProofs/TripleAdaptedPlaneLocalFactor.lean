import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity

noncomputable section

namespace GlobalTheory.LeviLine

open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

def sf (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ (J *ᵥ fun i => c (v i))

def levi (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (t s : R) : Matrix (Fin n) (Fin n) R :=
  1 + (t - 1) • vecMulVec x (J *ᵥ fun i => c (y i)) - (s - 1) • vecMulVec y (J *ᵥ fun i => c (x i))

variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

theorem sf_add_left (u w v : Fin n → R) : sf c J (u + w) v = sf c J u v + sf c J w v := by
  simp [sf, add_dotProduct]

theorem sf_sub_left (u w v : Fin n → R) : sf c J (u - w) v = sf c J u v - sf c J w v := by
  simp [sf, sub_dotProduct]

theorem sf_smul_left (r : R) (u v : Fin n → R) : sf c J (r • u) v = r * sf c J u v := by
  simp [sf, smul_dotProduct]

theorem sf_add_right (u v w : Fin n → R) : sf c J u (v + w) = sf c J u v + sf c J u w := by
  simp only [sf, Pi.add_apply, map_add]
  rw [show (fun i => c (v i) + c (w i)) = (fun i => c (v i)) + fun i => c (w i) from rfl, mulVec_add, dotProduct_add]

theorem sf_sub_right (u v w : Fin n → R) : sf c J u (v - w) = sf c J u v - sf c J u w := by
  simp only [sf, Pi.sub_apply, map_sub]
  rw [show (fun i => c (v i) - c (w i)) = (fun i => c (v i)) - fun i => c (w i) from rfl, mulVec_sub, dotProduct_sub]

theorem sf_smul_right (r : R) (u v : Fin n → R) : sf c J u (r • v) = c r * sf c J u v := by
  simp only [sf, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => c r * c (v i)) = c r • fun i => c (v i) from rfl, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem vecMulVec_mulVec' (x a z : Fin n → R) : vecMulVec x a *ᵥ z = (a ⬝ᵥ z) • x := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem levi_mulVec (x y : Fin n → R) (t s : R) (z : Fin n → R) :
    levi c J x y t s *ᵥ z = z + ((t - 1) * sf c J z y) • x - ((s - 1) * sf c J z x) • y := by
  simp only [levi, add_mulVec, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec', smul_smul, sf,
    dotProduct_comm z]

theorem sf_skew (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (u v : Fin n → R) :
    sf c J u v = -c (sf c J v u) := by
  simp only [sf, dotProduct, mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem ext_form {A B : Matrix (Fin n) (Fin n) R} (h : ∀ u v : Fin n → R, u ⬝ᵥ A *ᵥ v = u ⬝ᵥ B *ᵥ v) : A = B := by
  ext i j
  simpa [mulVec_single_one, single_one_dotProduct] using h (Pi.single i 1) (Pi.single j 1)

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ u : Fin n → R, A *ᵥ u = B *ᵥ u) : A = B :=
  ext_form fun u v => by rw [h]

variable {c J}

theorem levi_unitary (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) {x y : Fin n → R}
    (hxx : sf c J x x = 0) (hyy : sf c J y y = 0) (hxy : sf c J x y = 1) {t s : R} (hts : t * c s = 1) (hst : s * c t = 1) :
    (levi c J x y t s)ᵀ * J * (levi c J x y t s).map c = J := by
  have hyx : sf c J y x = -1 := by rw [sf_skew c J hc hJ, hxy, map_one]
  refine ext_form fun u v => ?_
  set v' : Fin n → R := fun i => c (v i) with hv'
  have hv : v = fun i => c (v' i) := funext fun i => (hc (v i)).symm
  have key : (levi c J x y t s).map c *ᵥ v = fun i => c ((levi c J x y t s *ᵥ v') i) := by
    ext i
    rw [RingHom.map_mulVec, hv]
    rfl
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, key]
  change sf c J (levi c J x y t s *ᵥ u) (levi c J x y t s *ᵥ v') = u ⬝ᵥ J *ᵥ v
  rw [hv]
  change _ = sf c J u v'
  rw [levi_mulVec, levi_mulVec]
  simp only [sf_add_left, sf_sub_left, sf_smul_left, sf_add_right, sf_sub_right, sf_smul_right, map_mul, map_sub, map_one,
    hxx, hyy, hxy, hyx]
  rw [sf_skew c J hc hJ x v', sf_skew c J hc hJ y v']
  linear_combination (sf c J u x * c (sf c J v' y)) * hst - (sf c J u y * c (sf c J v' x)) * hts

theorem levi_one (x y : Fin n → R) : levi c J x y 1 1 = 1 := by simp [levi]

theorem levi_mul (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) {x y : Fin n → R}
    (hxx : sf c J x x = 0) (hyy : sf c J y y = 0) (hxy : sf c J x y = 1) (t s t' s' : R) :
    levi c J x y t s * levi c J x y t' s' = levi c J x y (t * t') (s * s') := by
  have hyx : sf c J y x = -1 := by rw [sf_skew c J hc hJ, hxy, map_one]
  refine ext_mulVec fun u => ?_
  rw [← mulVec_mulVec, levi_mulVec, levi_mulVec, levi_mulVec]
  simp only [sf_add_left, sf_sub_left, sf_smul_left, hxx, hyy, hxy, hyx]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem levi_mulVec_of_orth (x y : Fin n → R) (t s : R) {z : Fin n → R} (hx : sf c J z x = 0) (hy : sf c J z y = 0) :
    levi c J x y t s *ᵥ z = z := by
  rw [levi_mulVec, hx, hy]
  simp

end GlobalTheory.LeviLine

namespace GlobalTheory.LeviLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open Matrix

theorem ext_mulVec_single {R : Type} [CommRing R] {m k : ℕ} {A B : Matrix (Fin m) (Fin k) R}
    (h : ∀ j, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) : A = B := by
  ext i j
  simpa [mulVec_single_one] using congrFun (h j) i

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigma_invol h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR]

theorem sf_inc (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → E) :
    sf (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom (incM F J) (incV F u) (incV F v) = inclR (F := F) (AF F) (form σ J u v) := by
  have h1 : (fun i => (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom (incV F v i)) = fun i => inclR (F := F) (AF F) (σ (v i)) :=
    funext fun i => cA_inclR σ (v i)
  have h2 : (incM F J *ᵥ fun i => inclR (F := F) (AF F) (σ (v i))) =
      fun i => inclR (F := F) (AF F) ((J *ᵥ fun i => σ (v i)) i) :=
    funext fun i => (RingHom.map_mulVec _ _ _ _).symm
  simp only [sf, h1, h2, form]
  rw [RingHom.map_dotProduct]
  rfl

end GlobalTheory.LeviLine

namespace GlobalTheory.LeviLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open Matrix

theorem exists_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d₁) (H' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∃ (t : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)ˣ) (m : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), GlobalTheory.ThK.IsLevi (W₁ := W₁) H' t 1 m ∧ 1 < (GlobalTheory.Doubling.absE F E t : ℝ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH
  have hcm := hT.base.cm
  set c : AE F E →+* AE F E := (cA σ : AE F E →ₐ[AF F] AE F E).toRingHom with hcdef
  have hc : ∀ r, c (c r) = r := cA_invol hcm
  have hJ : ∀ i j, c (incM F G.W.J j i) = -incM F G.W.J i j := by
    intro i j
    change cA σ (inclR (F := F) (AF F) (G.W.J j i)) = -inclR (F := F) (AF F) (G.W.J i j)
    rw [cA_inclR, hT.geo.hW.skew i j, map_neg]
  have hxx : sf c (incM F G.W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [sf_inc, hH.xx, map_zero]
  have hyy : sf c (incM F G.W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [sf_inc, hH.yy, map_zero]
  have hxy : sf c (incM F G.W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [sf_inc, hH.xy, map_one]
  have hyx : sf c (incM F G.W.J) (incV F H'.y) (incV F H'.x) = -1 := by rw [sf_skew c _ hc hJ, hxy, map_one]
  set t : (AE F E)ˣ := (GlobalTheory.Eis.Conv.halfE F E)⁻¹ with htdef
  have hts : (t : AE F E) * c (c (↑t⁻¹ : AE F E)) = 1 := by rw [hc, Units.mul_inv]
  have hst : c (↑t⁻¹ : AE F E) * c (t : AE F E) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hts' : (↑t⁻¹ : AE F E) * c (c (t : AE F E)) = 1 := by rw [hc, Units.inv_mul]
  have hst' : c (t : AE F E) * c (↑t⁻¹ : AE F E) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  let L := levi c (incM F G.W.J) (incV F H'.x) (incV F H'.y)
  let g : GL (Fin (a + a')) (AE F E) :=
    ⟨L t (c ↑t⁻¹), L ↑t⁻¹ (c t), by
      rw [levi_mul hc hJ hxx hyy hxy, Units.mul_inv, ← map_mul, Units.inv_mul, map_one, levi_one],
      by rw [levi_mul hc hJ hxx hyy hxy, Units.inv_mul, ← map_mul, Units.mul_inv, map_one, levi_one]⟩
  have hg : g ∈ UG (cA σ) (incM F G.W.J) := levi_unitary hc hJ hxx hyy hxy hts hst
  refine ⟨t, ⟨g, hg⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · change L t (c ↑t⁻¹) *ᵥ incV F H'.x = _
    rw [levi_mulVec, hxx, hxy]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) *ᵥ incV F H'.y = c ↑t⁻¹ • incV F H'.y
    rw [levi_mulVec, hyy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change L t (c ↑t⁻¹) * incM F H'.ι = incM F H'.ι * (1 : Matrix (Fin d₁) (Fin d₁) (AE F E))
    rw [Matrix.mul_one]
    refine ext_mulVec_single fun k => ?_
    have hcol : incM F H'.ι *ᵥ Pi.single k 1 = incV F (H'.ι *ᵥ Pi.single k 1) := by
      ext i
      simp [mulVec_single_one, incM, incV]
    rw [← mulVec_mulVec, hcol]
    exact levi_mulVec_of_orth _ _ _ _ (by rw [sf_inc, (hH.orth _).1, map_zero]) (by rw [sf_inc, (hH.orth _).2, map_zero])
  · have h1 := GlobalTheory.Eis.Conv.absE_halfE F E σ hcm
    have h2 : absE F E t * absE F E (GlobalTheory.Eis.Conv.halfE F E) = 1 := by
      rw [← map_mul, htdef, inv_mul_cancel, map_one]
    rw [h1] at h2
    have h3 : absE F E t = (4 : ℝ≥0) ^ Fintype.card (InfinitePlace F) := by
      rw [← mul_one (absE F E t), ← inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (4 : ℝ≥0) ≠ 0)), ← mul_assoc, h2, one_mul]
    rw [h3]
    have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    push_cast
    exact one_lt_pow₀ (by norm_num) hpos.ne'

end GlobalTheory.LeviLine

end
