import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviPlane

variable {R : Type} [CommRing R] (c : R →+* R) {n : ℕ}

def fm (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

def lev (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) : Matrix (Fin n) (Fin n) R :=
  1 + (s - 1) • Matrix.vecMulVec X (J *ᵥ fun i => c (Y i)) - (r - 1) • Matrix.vecMulVec Y (J *ᵥ fun i => c (X i))

theorem lev_mulVec (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) (w : Fin n → R) :
    lev c J X Y s r *ᵥ w = w + ((s - 1) * fm c J w Y) • X - ((r - 1) * fm c J w X) • Y := by
  ext i
  simp only [lev, fm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm w]
  ring

theorem fm_skew (hc : ∀ x, c (c x) = x) (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = -J i j)
    (p q : Fin n → R) : fm c J p q = -c (fm c J q p) := by
  simp only [fm, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

variable {c}

theorem fm_add_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u + u') v = fm c J u v + fm c J u' v := by
  simp [fm, add_dotProduct]

theorem fm_sub_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u - u') v = fm c J u v - fm c J u' v := by
  simp [fm, sub_dotProduct]

theorem fm_smul_left (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J (a • u) v = a * fm c J u v := by
  simp [fm, smul_dotProduct]

theorem fm_add_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v + v') = fm c J u v + fm c J u v' := by
  have : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_add, dotProduct_add]

theorem fm_sub_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v - v') = fm c J u v - fm c J u v' := by
  have : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_sub, dotProduct_sub]

theorem fm_smul_right (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J u (a • v) = c a * fm c J u v := by
  have : (fun i => c ((a • v) i)) = c a • fun i => c (v i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem entry (J M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Mᵀ * J * M.map c) i j = fm c J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [fm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
variable {R : Type} [CommRing R] {c : R →+* R} {n : ℕ}

section Plane
variable (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
  (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1)
include hc hJ hxx hyy hxy

theorem fm_yx : fm c J Y X = -1 := by rw [fm_skew c hc J hJ, hxy, map_one]

theorem lev_mul (s r s' r' : R) : lev c J X Y s r * lev c J X Y s' r' = lev c J X Y (s * s') (r * r') := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have key : ∀ w, (lev c J X Y s r * lev c J X Y s' r') *ᵥ w = lev c J X Y (s * s') (r * r') *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, lev_mulVec, lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, hxx, hyy, hxy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem lev_one : lev c J X Y 1 1 = 1 := by simp [lev]

theorem lev_unitary (s r : R) (hsr : s * c r = 1) :
    (lev c J X Y s r)ᵀ * J * (lev c J X Y s r).map c = J := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have hrs : r * c s = 1 := by
    have := congrArg c hsr; rw [map_mul, hc, map_one] at this; rw [mul_comm]; exact this
  have key : ∀ u v, fm c J (lev c J X Y s r *ᵥ u) (lev c J X Y s r *ᵥ v) = fm c J u v := by
    intro u v
    rw [lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, fm_add_right, fm_sub_right, fm_smul_right, hxx, hyy, hxy, hyx]
    rw [fm_skew c hc J hJ X v, fm_skew c hc J hJ Y v]
    simp only [map_mul, map_sub, map_one, map_neg]
    linear_combination (-(fm c J u Y * c (fm c J v X))) * hsr + (fm c J u X * c (fm c J v Y)) * hrs
  ext i j
  rw [entry, key]
  have h1 := entry (c := c) J 1 i j
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one,
    Matrix.one_mulVec] at h1
  exact h1.symm

end Plane

theorem lev_X {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} (hxx : fm c J X X = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ X = s • X := by
  rw [lev_mulVec, hxx, hxy]; ext i; simp; ring

theorem lev_Y (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
    (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ Y = r • Y := by
  rw [lev_mulVec, hyy, fm_yx hc hJ hxx hyy hxy]; ext i; simp; ring

theorem lev_mul_ι {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} {k : ℕ} (ι : Matrix (Fin n) (Fin k) R)
    (hι : ∀ j, fm c J (fun i => ι i j) X = 0 ∧ fm c J (fun i => ι i j) Y = 0) (s r : R) :
    lev c J X Y s r * ι = ι := by
  ext i j
  have h := congrFun (lev_mulVec c J X Y s r (fun i => ι i j)) i
  rw [(hι j).1, (hι j).2] at h
  simp only [mul_zero, zero_smul, add_zero, sub_zero] at h
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct] using h

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, Algebra.TensorProduct.map_tmul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cAr_inclR (σ : E →ₐ[F] E) (e : E) :
    (cA σ).toRingHom (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := cA_inclR σ e

theorem fm_inc (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    fm (cA σ).toRingHom (incM F J) (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by
  simp only [fm, form, incV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
    AlgHom.coe_toRingHom, cAr_inclR, cA_inclR]

end GlobalTheory.LeviPlane

open GlobalTheory.LeviPlane in

theorem GlobalTheory.LeviPlane.levi_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ t : (AE F E)ˣ, ∃ m : UA σ G.W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH t
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hσ := sigma_invol hT.base.cm
  have hc : ∀ x, c (c x) = x := fun x => cA_invol hσ x
  have hJ : ∀ i j, c (incM F G.W.J j i) = -incM F G.W.J i j := by
    intro i j
    simp only [hcdef, incM, Matrix.map_apply, cAr_inclR, hT.geo.hW.skew, map_neg]
  have hxx : fm c (incM F G.W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fm_inc, hH.xx, map_zero]
  have hyy : fm c (incM F G.W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fm_inc, hH.yy, map_zero]
  have hxy : fm c (incM F G.W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fm_inc, hH.xy, map_one]
  have hι : ∀ j, fm c (incM F G.W.J) (fun i => incM F H'.ι i j) (incV F H'.x) = 0 ∧
      fm c (incM F G.W.J) (fun i => incM F H'.ι i j) (incV F H'.y) = 0 := by
    intro j
    have hcol : (fun i => incM F H'.ι i j) = incV F (H'.ι *ᵥ Pi.single j 1) := by
      ext i; simp [incV, incM, Matrix.mulVec_single_one]
    rw [hcol, fm_inc, fm_inc, (hH.orth _).1, (hH.orth _).2, map_zero]; exact ⟨rfl, rfl⟩
  let L : AE F E → AE F E → Matrix (Fin (a + a')) (Fin (a + a')) (AE F E) :=
    fun s r => lev c (incM F G.W.J) (incV F H'.x) (incV F H'.y) s r
  have hmul : ∀ s r s' r', L s r * L s' r' = L (s * s') (r * r') := fun s r s' r' =>
    lev_mul hc hJ hxx hyy hxy s r s' r'
  have h1 : L 1 1 = 1 := lev_one hc hJ hxx hyy hxy
  let g : GL (Fin (a + a')) (AE F E) :=
    ⟨L (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)), L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)),
      by rw [hmul, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, h1],
      by rw [hmul, ← map_mul, Units.inv_mul, Units.mul_inv, map_one, h1]⟩
  have hg : g ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J) := by
    show (L _ _)ᵀ * incM F G.W.J * (L _ _).map (cA σ) = incM F G.W.J
    have := lev_unitary hc hJ hxx hyy hxy (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E))
      (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_invol hσ, Units.mul_inv])
    exact this
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
  · exact lev_X hxx hxy _ _
  · exact lev_Y hc hJ hxx hyy hxy _ _
  · have : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [this, Matrix.mul_one]
    exact lev_mul_ι _ hι _ _
