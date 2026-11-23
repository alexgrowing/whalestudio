import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler

section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem zh_split (l : Fin (r + 2)) (hl : S.D l ≠ 0) (x y : Fin (r + 1))
    (hxy : ((x : ℕ) < l ∧ (l : ℕ) ≤ y) ∨ ((y : ℕ) < l ∧ (l : ℕ) ≤ x)) : S.Zh x y = 0 := by
  have hZ : ∀ a b : Fin (r + 1), S.Zh a b = ptEntryL S.w.blocks a b * (-1) ^ (r - (b : ℕ)) :=
    fun a b => S.relevant a b
  have hA : ∀ a : Fin (r + 1), (a : ℕ) < l → GlobalTheory.FrameBasic.sig S.w.blocks a < l := by
    intro a ha
    by_contra hc
    push_neg at hc
    apply hl
    unfold Frames.D lead
    apply Matrix.det_eq_zero_of_row_eq_zero (⟨a, ha⟩ : Fin l)
    intro j
    simp only [Matrix.submatrix_apply]
    rw [hZ]
    have hj := j.2
    have : ((Fin.castLE (Nat.lt_succ_iff.mp l.2) j : Fin (r + 1)) : ℕ) ≠
        GlobalTheory.FrameBasic.sig S.w.blocks (Fin.castLE (Nat.lt_succ_iff.mp l.2) (⟨a, ha⟩ : Fin l) : Fin (r + 1)) := by
      simp only [Fin.coe_castLE]; omega
    rw [GlobalTheory.FrameBasic.entry_zero _ _ _ this, zero_mul]
  rw [hZ]
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ (by have := hA x h1; omega), zero_mul]
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ ?_, zero_mul]
    intro he
    have h3 := hA y h1
    rw [he, GlobalTheory.FrameBasic.sig_sig] at h3
    omega

theorem m_zero [IsNonarchimedeanLocalField F] [CharZero F]
    (m m' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hm' : (∀ i j, j < i → m' i j = 0) ∧ (∀ i, m' i i = 1))
    (heq : cT L m * S.Zh * m' = S.Zh) (l : Fin (r + 2)) (hl : S.D l ≠ 0) (a b : Fin (r + 1))
    (ha : (a : ℕ) < l) (hb : (l : ℕ) ≤ b) : m a b = 0 := by
  obtain ⟨-, -, -, hU, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hU' : IsUnit S.Zh.det := hU
  have hbt : m'.BlockTriangular id := by
    intro i j hij; exact hm'.1 i j hij
  have hdet : IsUnit m'.det := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hm'.2]
  letI := Matrix.invertibleOfIsUnitDet m' hdet
  have hN : (m'⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have h1 : cT L m * S.Zh = S.Zh * m'⁻¹ := by
    calc cT L m * S.Zh = cT L m * S.Zh * m' * m'⁻¹ := by
          rw [Matrix.mul_assoc (cT L m * S.Zh) m', Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = S.Zh * m'⁻¹ := by rw [heq]
  let v : Fin (r + 1) → E := fun x => if (x : ℕ) < l then L.cj (m x b) else 0
  have hv : Matrix.vecMul v S.Zh = 0 := by
    funext y
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hy : (y : ℕ) < l
    · have h2 := congrFun (congrFun h1 b) y
      rw [Matrix.mul_apply, Matrix.mul_apply] at h2
      have h3 : ∑ z, S.Zh b z * m'⁻¹ z y = 0 := Finset.sum_eq_zero fun z _ => by
        by_cases hz : (z : ℕ) ≤ y
        · rw [zh_split S l hl b z (Or.inr ⟨by omega, hb⟩), zero_mul]
        · rw [hN (show y < z from Fin.lt_def.2 (by omega)), mul_zero]
      rw [h3] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [v, cT]
      split_ifs with hx
      · rfl
      · simp [zh_split S l hl x y (Or.inr ⟨hy, by omega⟩)]
    · refine Finset.sum_eq_zero fun x _ => ?_
      simp only [v]
      split_ifs with hx
      · rw [zh_split S l hl x y (Or.inl ⟨hx, by omega⟩), mul_zero]
      · rw [zero_mul]
  have hv0 : v = 0 := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
    (hv.trans (Matrix.zero_vecMul _).symm)
  have := congrFun hv0 a
  simp only [v, if_pos ha, Pi.zero_apply] at this
  exact (map_eq_zero_iff L.cj L.cj.injective).1 this

end Local

section Scal
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]

theorem ab_one (c : Kˣ) (n : ℕ) : algebraMap K B ((c : K) ^ n) * algebraMap K B (((c⁻¹ ^ n : Kˣ)) : K) = 1 := by
  rw [← map_mul, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow, map_one]

theorem ba_one (c : Kˣ) (n : ℕ) : algebraMap K B (((c⁻¹ ^ n : Kˣ)) : K) * algebraMap K B ((c : K) ^ n) = 1 := by
  rw [mul_comm, ab_one]

end Scal

section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

theorem f_loc (a : Fin (r + 1)) : (G.S p).f a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) •
      A.bc p (G.f a) := by
  rw [← G.f_eq p a, smul_smul, ba_one, one_smul]

theorem f'_loc (a : Fin (r + 1)) : (G.S p).f' a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) •
      A.bc p (G.f' a) := by
  rw [← G.f'_eq p a, smul_smul, ba_one, one_smul]

theorem zh_loc (a b : Fin (r + 1)) : (G.S p).Zh a b =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (b : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
      (A.loc p).ιE (G.Zh a b) := by
  show hf (A.L p) (G.S p).Hm ((G.S p).f' b) ((G.S p).f a) = _
  rw [f_loc, f'_loc, hf_smul_l, hf_smul_r, AlgEquiv.commutes, G.Hm_eq p,
    (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)]
  simp only [GFrames.Zh, Matrix.of_apply]
  ring

theorem D_ne (l : Fin (r + 2)) (h : G.D l ≠ 0) : (G.S p).D l ≠ 0 := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  set e : Fin l → Fin (r + 1) := Fin.castLE (Nat.lt_succ_iff.mp l.2) with he
  let d : Fin l → (A.loc p).Ep := fun i =>
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (e i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp)
  have hsub : (G.S p).Zh.submatrix e e =
      Matrix.diagonal d * (G.Zh.submatrix e e).map (A.loc p).ιE * Matrix.diagonal d := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, zh_loc, d]
    ring
  have hmap : ((G.Zh.submatrix e e).map (A.loc p).ιE).det = (A.loc p).ιE (G.D l) :=
    (RingHom.map_det _ _).symm
  have hD : (G.S p).D l = (∏ i, d i) * (A.loc p).ιE (G.D l) * (∏ i, d i) := by
    show ((G.S p).Zh.submatrix e e).det = _
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hmap]
  have hu : IsUnit (∏ i, d i) := by
    rw [IsUnit.prod_univ_iff]
    intro i
    exact (Units.isUnit _).map _
  rw [hD]
  intro h0
  rw [hu.mul_left_eq_zero, hu.mul_right_eq_zero] at h0
  exact h ((map_eq_zero_iff _ (A.loc p).ιE.injective).1 h0)

end Global

theorem local_pattern : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV), h ∈ (G.S p).St → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → s i j = if i = j then 1 else 0) ∧ (∀ j, h (A.bc p (G.f j)) = ∑ i, s i j • A.bc p (G.f i)) ∧ ((∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) → h ∈ (G.S p).K0 → IsIntM (A.L p) s) := by
  intro F E _ _ _ _ _ sig A r k G p h hh
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hN1, hN2, -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto (A.L p) r k (G.S p)
  obtain ⟨m, hm, hmf⟩ := hN1 h hh.1
  obtain ⟨m', hm', hmf'⟩ := hN2 h hh.2
  have heq : cT (A.L p) m * (G.S p).Zh * m' = (G.S p).Zh :=
    ((GlobalTheory.HL.FrameStab.stab_eq (A.L p) r k (G.S p)).2 m m' hm hm').2 ⟨h, hh, hmf, hmf'⟩
  refine ⟨fun i j => algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (j : ℕ))) * m i j *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp),
    ?_, ?_, ?_⟩
  · intro i j hij
    beta_reduce
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hex : ∃ l : Fin (r + 2), (i : ℕ) < l ∧ (l : ℕ) ≤ j ∧ G.D l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hij ⟨hlt, fun l h1 h2 => hc l h1 h2⟩
      obtain ⟨l, h1, h2, h3⟩ := hex
      rw [if_neg hlt.ne, m_zero (G.S p) m m' hm' heq l (D_ne G p l h3) i j h1 h2]
      simp
    · rw [if_pos rfl, hm.2, mul_one, ab_one]
    · rw [if_neg hgt.ne', hm.1 i j hgt]
      simp
  · intro j
    beta_reduce
    rw [← G.f_eq p j, map_smul, hmf j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← G.f_eq p i, smul_smul, smul_smul, mul_assoc (_ * m i j), ba_one, mul_one]
  · rintro ⟨u, hu⟩ hK i j
    have hli : LinearIndependent (A.loc p).Ep (G.S p).f :=
      (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).1.comp Sum.inl Sum.inl_injective
    have hmem : h ((G.S p).f j) ∈ Submodule.span (A.L p).O (Set.range (G.S p).f) := by
      have h1 : h • Submodule.span (A.L p).O (Set.range (G.S p).f) =
          Submodule.span (A.L p).O (Set.range (G.S p).f) := hK.1.2
      rw [← h1]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    have hb' : ∑ i, ((b i : (A.L p).O) : (A.loc p).Ep) • (G.S p).f i = h ((G.S p).f j) := by
      rw [← hb]
      exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
    have hmb : m i j = b i := by
      have := Fintype.linearIndependent_iff.1 hli (fun i => ((b i : (A.L p).O) : (A.loc p).Ep) - m i j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, hb', hmf j, sub_self])
      exact (sub_eq_zero.1 (this i)).symm
    have hO : ∀ (y : 𝒪[(A.loc p).Fp]) (n : ℕ),
        algebraMap (A.loc p).Fp (A.loc p).Ep ((y : (A.loc p).Fp) ^ n) ∈ (A.L p).O := by
      intro y n
      rw [map_pow]
      refine pow_mem (((A.L p).O_def _).2 ?_) n
      rw [show (y : (A.loc p).Fp) = algebraMap 𝒪[(A.loc p).Fp] (A.loc p).Fp y from rfl,
        ← IsScalarTower.algebraMap_apply]
      exact isIntegral_algebraMap
    have hinv : (((G.c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((u⁻¹ : (𝒪[(A.loc p).Fp])ˣ) : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
      rw [Units.val_inv_eq_inv_val, ← hu]
      symm
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun x : 𝒪[(A.loc p).Fp] => (x : (A.loc p).Fp)) (Units.inv_mul u)
    refine Subring.mul_mem _ (Subring.mul_mem _ ?_ (hmb ▸ (b i).2)) ?_
    · rw [← hu]; exact hO u _
    · rw [Units.val_pow_eq_pow_val, hinv]; exact hO _ _

end GlobalTheory.HL.LocPattern
