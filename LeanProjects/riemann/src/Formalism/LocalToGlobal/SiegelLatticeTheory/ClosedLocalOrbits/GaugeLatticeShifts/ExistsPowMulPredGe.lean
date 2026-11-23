import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacLocOfHpk
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

section Lin

variable {n : ℕ} (ε : Fin n → Bool)

theorem exists_dualVec {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → ℂ) (hu : LinearIndependent ℂ u)
    (t : ι → ℂ) : ∃ v, ∀ i, hJ ε (u i) v = t i := by
  let A : Matrix (Fin n) ι ℂ := Matrix.of fun p i => u i p
  have hA : ∀ c : ι → ℂ, A *ᵥ c = ∑ i, c i • u i := by
    intro c
    ext p
    simp only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinj : Function.Injective A.mulVec := by
    intro c d hcd
    have h0 : ∑ i, (c - d) i • u i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [← hA, ← hA]
      exact sub_eq_zero.2 hcd
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h0 i)
  have hpd := Matrix.PosDef.conjTranspose_mul_self A hinj
  have hdet : IsUnit (Aᴴ * A).det := (Matrix.isUnit_iff_isUnit_det _).1 hpd.isUnit
  refine ⟨Formalism.REAL.Jm ε *ᵥ (A *ᵥ ((Aᴴ * A)⁻¹ *ᵥ t)), fun i => ?_⟩
  have key : ∀ w : Fin n → ℂ, star (u i) ⬝ᵥ w = (Aᴴ *ᵥ w) i := by
    intro w
    simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, A, Matrix.of_apply, Pi.star_apply]
  unfold hJ
  rw [Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, Matrix.one_mulVec, key, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem goodPos_of_dual {r : ℕ} (e f : Fin r → Fin n → ℂ) (z z'' : Fin n → ℂ) (hee : ∀ a b, hJ ε (e a) (e b) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hez'' : ∀ a, hJ ε (e a) z'' = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) (hfz : ∀ b, hJ ε z (f b) = 0)
    (hfz'' : ∀ b, hJ ε z'' (f b) = 0) : GoodPos ε e z z'' := by
  set g : Fin r → Fin n → ℂ := fun b => f b - ∑ c, ((1 / 2 : ℂ) * hJ ε (f c) (f b)) • e c with hg
  have hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0 := by
    intro a b
    rw [UnitaryIsometries.hJ_conj, hef]
    split_ifs <;> simp
  refine ⟨g, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩⟩
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hee, mul_zero, Finset.sum_const_zero, sub_zero, hef]
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_right, UnitaryIsometries.hJ_sum_left, hee, hfe, mul_zero,
      Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, UnitaryIsometries.hJ_sum_left]
    simp only [hef, ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_mul]
    rw [← UnitaryIsometries.hJ_conj ε (f a) (f b)]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_left, hez, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [UnitaryIsometries.hJ_conj, hfz, map_zero]
  · rw [hg]
    simp only [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_left, hez'', mul_zero, Finset.sum_const_zero, sub_zero]
    rw [UnitaryIsometries.hJ_conj, hfz'', map_zero]

def eiL (x v : Fin n → ℂ) (q : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun w := w + hJ ε x w • v - (hJ ε v w + q * hJ ε x w) • x
  map_add' w w' := by
    simp only [UnitaryIsometries.hJ_add_right, mul_add, add_smul]
    abel
  map_smul' a w := by
    simp only [UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_sub, smul_add, smul_smul]
    congr 2
    ring_nf

def ei (x v : Fin n → ℂ) (q : ℂ) : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (eiL ε x v q)

theorem ei_apply (x v : Fin n → ℂ) (q : ℂ) (w : Fin n → ℂ) :
    ei ε x v q *ᵥ w = w + hJ ε x w • v - (hJ ε v w + q * hJ ε x w) • x := by
  rw [ei, LinearMap.toMatrix'_mulVec]
  rfl

theorem ei_isIsom (x v : Fin n → ℂ) (q : ℂ) (hxx : hJ ε x x = 0) (hxv : hJ ε x v = 0)
    (hq : q + conj q = hJ ε v v) : UnitaryIsometries.IsIsom ε (ei ε x v q) := by
  intro w w'
  have hvx : hJ ε v x = 0 := by rw [UnitaryIsometries.hJ_conj, hxv, map_zero]
  rw [ei_apply, ei_apply]
  simp only [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_sub_right,
    UnitaryIsometries.hJ_smul_right, map_add, map_mul, hxx, hxv, hvx]
  rw [UnitaryIsometries.hJ_conj ε w v, UnitaryIsometries.hJ_conj ε w x]
  linear_combination (-(conj (hJ ε x w) * hJ ε x w')) * hq

end Lin

section Frame

variable {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ}

theorem hJ_comb_left (d : Fin r → ℂ) (y : Fin n → ℂ) (h : ∀ a, hJ ε (e a) y = 0) :
    hJ ε (∑ a, d a • e a) y = 0 := by
  rw [UnitaryIsometries.hJ_sum_left]
  simp [h]

theorem hJ_comb_right (d : Fin r → ℂ) (y : Fin n → ℂ) (h : ∀ a, hJ ε y (e a) = 0) :
    hJ ε y (∑ a, d a • e a) = 0 := by
  rw [UnitaryIsometries.hJ_sum_right]
  simp [h]

theorem z_not_mem_span (hF : FrameLoc ε k e z z' T T') : z ∉ Submodule.span ℂ (Set.range e) := by
  intro hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  have h0 : hJ ε z z = hJ ε (∑ a, c a • e a) z := by rw [hc]
  have h1 : (-(T : ℂ)) = 0 := by rw [← hF.zz, h0, hJ_comb_left c z hF.ez]
  exact hF.T_pos.ne' (Complex.ofReal_eq_zero.1 (neg_eq_zero.1 h1))

theorem goodPos_shift (hF : FrameLoc ε k e z z' T T') :
    ∃ d : Fin r → ℂ, GoodPos ε e z (z' + ∑ a, d a • e a) := by
  have hLI : LinearIndependent ℂ (fam e z) := by
    unfold fam
    exact linearIndependent_finSnoc.2 ⟨hF.e_li, z_not_mem_span hF⟩
  by_cases hc : z' ∈ Submodule.span ℂ (Set.range (fam e z))
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hc
    refine ⟨fun a => -c (Fin.castSucc a), ?_⟩
    have hz'' : z' + ∑ a, (-c (Fin.castSucc a)) • e a = c (Fin.last r) • z := by
      rw [← hc, Fin.sum_univ_castSucc]
      simp only [fam, Fin.snoc_castSucc, Fin.snoc_last, neg_smul, Finset.sum_neg_distrib]
      abel
    rw [hz'']
    have hd := fun b : Fin r => exists_dualVec ε (fam e z) hLI (fun i => if i = Fin.castSucc b then 1 else 0)
    choose f hf using hd
    refine goodPos_of_dual ε e f z _ hF.ee hF.ez (fun a => ?_) (fun a b => ?_) (fun b => ?_) (fun b => ?_)
    · rw [UnitaryIsometries.hJ_smul_right, hF.ez, mul_zero]
    · have h1 := hf b (Fin.castSucc a)
      simp only [fam, Fin.snoc_castSucc] at h1
      rw [h1]
      simp only [Fin.castSucc_inj]
    · have h1 := hf b (Fin.last r)
      simp only [fam, Fin.snoc_last] at h1
      rw [h1, if_neg (Fin.castSucc_lt_last b).ne']
    · have h1 := hf b (Fin.last r)
      simp only [fam, Fin.snoc_last] at h1
      rw [UnitaryIsometries.hJ_smul_left, h1, if_neg (Fin.castSucc_lt_last b).ne', mul_zero]
  · refine ⟨0, ?_⟩
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    have hLI2 : LinearIndependent ℂ (Fin.snoc (α := fun _ => Fin n → ℂ) (fam e z) z') :=
      linearIndependent_finSnoc.2 ⟨hLI, hc⟩
    have hd := fun b : Fin r => exists_dualVec ε (Fin.snoc (α := fun _ => Fin n → ℂ) (fam e z) z') hLI2
      (fun i => if i = Fin.castSucc (Fin.castSucc b) then 1 else 0)
    choose f hf using hd
    refine goodPos_of_dual ε e f z z' hF.ee hF.ez hF.ez' (fun a b => ?_) (fun b => ?_) (fun b => ?_)
    · have h1 := hf b (Fin.castSucc (Fin.castSucc a))
      simp only [fam, Fin.snoc_castSucc] at h1
      rw [h1]
      simp only [Fin.castSucc_inj]
    · have h1 := hf b (Fin.castSucc (Fin.last r))
      simp only [fam, Fin.snoc_castSucc, Fin.snoc_last] at h1
      rw [h1, if_neg]
      intro h
      exact (Fin.castSucc_lt_last b).ne' (Fin.castSucc_injective _ h)
    · have h1 := hf b (Fin.last (r + 1))
      simp only [Fin.snoc_last] at h1
      rw [h1, if_neg (Fin.castSucc_lt_last _).ne']

theorem frameLoc_shift (hF : FrameLoc ε k e z z' T T') (d : Fin r → ℂ) :
    FrameLoc ε k e z (z' + ∑ a, d a • e a) T T' := by
  have hz'e : ∀ a, hJ ε z' (e a) = 0 := fun a => by rw [UnitaryIsometries.hJ_conj, hF.ez', map_zero]
  exact
  { dim := hF.dim, k_pos := hF.k_pos, sig := hF.sig, e_li := hF.e_li, ee := hF.ee, ez := hF.ez,
    ez' := fun a => by rw [UnitaryIsometries.hJ_add_right, hF.ez', hJ_comb_right d _ (fun b => hF.ee a b), add_zero],
    zz := hF.zz,
    zz' := by
      rw [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_add_right, hF.zz', hJ_comb_right d _ hz'e,
        hJ_comb_left d _ hF.ez', hJ_comb_left d _ (fun b => hJ_comb_right d _ (fun a => hF.ee b a))]
      simp,
    T_pos := hF.T_pos, T'_pos := hF.T'_pos }

theorem exists_pow_mul_pred_ge (hF : FrameLoc ε k e z z' T T') (d : Fin r → ℂ) :
    ∃ n0 : Formalism.REAL.UJ ε, (∀ a, uMat n0 *ᵥ e a = e a) ∧ uMat n0 *ᵥ z' = z' + ∑ a, d a • e a ∧
      uMat n0 *ᵥ (∑ a, d a • e a) = ∑ a, d a • e a := by
  set x := ∑ a, d a • e a with hx
  set v : Fin n → ℂ := ((1 / T' : ℝ) : ℂ) • z' with hv
  set q : ℂ := ((-(1 / (2 * T')) : ℝ) : ℂ) with hqd
  have hxe : ∀ a, hJ ε x (e a) = 0 := fun a => hJ_comb_left d _ (fun b => hF.ee b a)
  have hxz' : hJ ε x z' = 0 := hJ_comb_left d _ hF.ez'
  have hxx : hJ ε x x = 0 := hJ_comb_left d _ (fun b => hJ_comb_right d _ (fun a => hF.ee b a))
  have hxv : hJ ε x v = 0 := by rw [hv, UnitaryIsometries.hJ_smul_right, hxz', mul_zero]
  have hvx : hJ ε v x = 0 := by rw [UnitaryIsometries.hJ_conj, hxv, map_zero]
  have hve : ∀ a, hJ ε v (e a) = 0 := fun a => by
    rw [UnitaryIsometries.hJ_conj, hv, UnitaryIsometries.hJ_smul_right, hF.ez', mul_zero, map_zero]
  have hT' : (T' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.T'_pos.ne'
  have hvz' : hJ ε v z' = -1 := by
    rw [hv, UnitaryIsometries.hJ_smul_left, Complex.conj_ofReal, hF.zz']
    push_cast
    field_simp
  have hq : q + conj q = hJ ε v v := by
    rw [hqd, hv, Complex.conj_ofReal, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, Complex.conj_ofReal, hF.zz']
    push_cast
    field_simp
    ring
  have hI := ei_isIsom ε x v q hxx hxv hq
  refine ⟨UnitaryIsometries.toUJ ε hI, fun a => ?_, ?_, ?_⟩ <;> rw [UnitaryIsometries.uMat_toUJ, ei_apply]
  · rw [hxe, hve]
    simp
  · rw [hxz', hvz']
    simp
  · rw [hxx, hvx]
    simp

theorem comb_mem_spanLt (d : Fin r → ℂ) : ∑ a, d a • e a ∈ spanLt e r :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)

theorem spanLt_le_top (a : ℕ) : spanLt e a ≤ spanLt e r :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

theorem sub_one_comb (g : Matrix (Fin n) (Fin n) ℂ) (hg : ∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1)
    (d : Fin r → ℂ) : (g - 1) *ᵥ ∑ a, d a • e a ∈ spanLt e r := by
  rw [Matrix.mulVec_sum]
  exact Submodule.sum_mem _ fun a _ => by
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (spanLt_le_top _ (hg a))

theorem sLoc_shift (d : Fin r → ℂ) : SLoc ε e (z' + ∑ a, d a • e a) = SLoc ε e z' := by
  ext g
  simp only [SLoc, Set.mem_setOf_eq, InS]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 := Submodule.sub_mem _ h2 (sub_one_comb _ h1 d)
    rwa [Matrix.mulVec_add, add_sub_cancel_right] at h3
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ h2 (sub_one_comb _ h1 d)

theorem famSc_shift (g : Formalism.REAL.UJ ε) (z'' : Fin n → ℂ) (he : ∀ a, uMat g *ᵥ e a = e a)
    (hz : uMat g *ᵥ z' = z'') (sc : ℝ) (b : Fin (r + 1)) : uMat g *ᵥ famSc sc e z' b = famSc sc e z'' b := by
  cases b using Fin.lastCases with
  | last => simp only [famSc, fam, Matrix.mulVec_smul, Fin.snoc_last, hz]
  | cast a => simp only [famSc, fam, Matrix.mulVec_smul, Fin.snoc_castSucc, he]

end Frame

theorem degRed_holds : DegRed := by
  intro hR hG n r k ε e z z' T T' sc hF hsc
  obtain ⟨d, hGP⟩ := goodPos_shift hF
  have hF'' := frameLoc_shift hF d
  obtain ⟨h'', hsec, hJ''⟩ := hG n r k ε e z (z' + ∑ a, d a • e a) T T' sc hF'' hGP hsc
  obtain ⟨n0, hn0e, hn0z, hn0x⟩ := exists_pow_mul_pred_ge hF d
  have hinv : ∀ w, uMat n0⁻¹ *ᵥ (uMat n0 *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, show uMat n0⁻¹ * uMat n0 = 1 by simp [uMat], Matrix.one_mulVec]
  have hn0i : n0⁻¹ ∈ SLoc ε e z' := by
    show InS e z' (uMat n0⁻¹)
    refine ⟨fun a => ?_, ?_⟩
    · have h1 := hinv (e a)
      rw [hn0e a] at h1
      rw [Matrix.sub_mulVec, h1, Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
    · have h1 := hinv (∑ a, d a • e a)
      rw [hn0x] at h1
      have h2 := hinv z'
      rw [hn0z, Matrix.mulVec_add, h1] at h2
      have h3 : uMat n0⁻¹ *ᵥ z' = z' - ∑ a, d a • e a := eq_sub_of_add_eq h2
      rw [Matrix.sub_mulVec, h3, Matrix.one_mulVec, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (comb_mem_spanLt d)
  have hfam : ∀ b, uMat n0 *ᵥ famSc sc e z' b = famSc sc e (z' + ∑ a, d a • e a) b :=
    famSc_shift n0 _ hn0e hn0z sc
  refine ⟨fun c => h'' c * n0, fun c hc => ?_, fun μS μS' hS hS' => ?_⟩
  · rw [← hsec c hc]
    ext a b
    show hJ ε _ (uMat (h'' c * n0) *ᵥ _) = hJ ε _ (uMat (h'' c) *ᵥ _)
    rw [show uMat (h'' c * n0) = uMat (h'' c) * uMat n0 from rfl, ← Matrix.mulVec_mulVec, hfam b]
  · have hS'' : IsHaarS (SLoc ε e (z' + ∑ a, d a • e a)) μS' := by
      rw [sLoc_shift]
      exact hS'
    obtain ⟨C, hC, hD⟩ := hJ'' μS μS' hS hS''
    refine ⟨C, hC, fun φ hφ => ?_⟩
    rw [hD φ hφ]
    refine lintegral_congr (fun c => ?_)
    congr 1
    refine lintegral_congr (fun s => ?_)
    have hRi := hR n r k ε e z' z T' T (frameLoc_swap hF) μS' hS' n0⁻¹ hn0i
    have h1 := lintegral_mul_right_of_map μS' n0⁻¹ hRi (fun x => φ (s * h'' c * x⁻¹))
    refine h1.symm.trans (lintegral_congr (fun s' => ?_))
    congr 1
    group

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
