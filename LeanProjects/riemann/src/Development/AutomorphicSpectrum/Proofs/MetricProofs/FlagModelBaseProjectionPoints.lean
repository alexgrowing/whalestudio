import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPtsA
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorSumIdentityBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagValuationNormalizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValuationRingExtensionSpecializationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependentStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CPts

open GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sum_mapDomain_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem mConeMap_rename {Ω : Type} [Field Ω] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (g : MRing ι) : mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hb.2.2.1 n]

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap]

theorem aeval_comp_ringHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (φ ∘ x) g = φ (aeval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, Function.comp]

theorem eval_rename_block (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v f)) = eval (z ∘ v) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]

theorem rename_notMem {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    {z : (Σ k, ι' k) → ℂ} {h : MRing ι} (hn : h ∉ mCoordIdeal (z ∘ v)) : rename v h ∉ mCoordIdeal z := by
  intro hm
  have h0 : mConeMap z (rename v h) = 0 := hm
  rw [mConeMap_rename hb] at h0
  exact hn ((rename_injective κ hb.1) (by rw [h0, map_zero]))

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) (φ : Ω →+* Ω') {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : x' ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨⟨k₂, i⟩, hp⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₂ = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k₂, i⟩).symm)
    subst hk
    exact ⟨i, by simpa [Function.comp, hp] using hi'⟩
  · have h0 : mConeMap x f = 0 := hf
    have h1 : rename v f ∈ mCoordIdeal x' := by
      show mConeMap x' (rename v f) = 0
      rw [mConeMap_rename hb, hx, mConeMap_comp, h0, map_zero, map_zero]
    rw [← eval_rename_block]
    exact hz.2 _ h1

end Forms

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def regRing (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {s | ∃ v, IsValueAt y s z v}
  mul_mem' := fun ⟨v, hv⟩ ⟨w, hw⟩ => ⟨v * w, isValueAt_mul hv hw⟩
  one_mem' := ⟨1, isValueAt_one_self y z⟩
  add_mem' := fun ⟨v, hv⟩ ⟨w, hw⟩ => ⟨v + w, GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hv hw⟩
  zero_mem' := ⟨0, isValueAt_zero_self y z⟩
  neg_mem' := fun {s} ⟨v, hv⟩ => ⟨(-1 : ℤ) * v, by
    have := isValueAt_mul (isValueAt_intCast y z (-1)) hv
    simpa using this⟩

def regVal {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : regRing y z →+* ℂ where
  toFun s := valAt y s z
  map_one' := valAt_eq hz (isValueAt_one_self y z)
  map_zero' := valAt_eq hz (isValueAt_zero_self y z)
  map_mul' := fun ⟨s, v, hv⟩ ⟨t, w, hw⟩ => by
    show valAt y (s * t) z = valAt y s z * valAt y t z
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]
  map_add' := fun ⟨s, v, hv⟩ ⟨t, w, hw⟩ => by
    show valAt y (s + t) z = valAt y s z + valAt y t z
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hv hw)]

theorem regVal_apply {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (s : regRing y z) :
    regVal hz s = valAt y s z := rfl

theorem regVal_eq {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (s : regRing y z)
    {v : ℂ} (hv : IsValueAt y s z v) : regVal hz s = v := valAt_eq hz hv

theorem regVal_local {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (s : regRing y z)
    (h : regVal hz s ≠ 0) : (s : Ω)⁻¹ ∈ regRing y z := by
  obtain ⟨s, v, hv⟩ := s
  have e : regVal hz ⟨s, v, hv⟩ = v := regVal_eq hz _ hv
  rw [e] at h
  have hs : s ≠ 0 := fun h0 => h (isValueAt_zero hz (h0 ▸ hv))
  exact ⟨v⁻¹, isValueAt_inv hv hs h⟩

theorem isValueAt_ratio {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {k : K} {m c : ι k}
    (hy : y ⟨k, c⟩ ≠ 0) (hz : z ⟨k, c⟩ ≠ 0) : IsValueAt y (y ⟨k, m⟩ / y ⟨k, c⟩) z (z ⟨k, m⟩ / z ⟨k, c⟩) := by
  refine ⟨_, X ⟨k, m⟩, X ⟨k, c⟩, isMultiHomog_X_single _, isMultiHomog_X_single _, by simpa using hy, ?_,
    by simpa using hz, by simp⟩
  rw [aeval_X, aeval_X, div_mul_cancel₀ _ hy]

theorem coord_ne {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {q : Σ k, ι k}
    (h : z q ≠ 0) : y q ≠ 0 := fun h0 => h (by
  have := eval_eq_zero_of_mem_mcPts hz
    (mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_X_single (ι := ι) q) (by simpa using h0))
  simpa using this)

theorem mCoordIdeal_le {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) :
    mCoordIdeal x ≤ mCoordIdeal z := by
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x
  refine hE.le.trans (Ideal.span_le.2 fun g hg => ?_)
  obtain ⟨d, hd⟩ := hT g hg
  refine mem_mCoordIdeal_of_aeval_eq_zero z hd ?_
  have := eval_eq_zero_of_mem_mcPts hz (hE ▸ Ideal.subset_span hg : g ∈ mCoordIdeal x)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  simpa using this

theorem mem_mcPts_of_ringHom {L R : Type} [Field L] [CommRing R] (i : R →+* L) (hi : Function.Injective i)
    (ρ : R →+* ℂ) (a : (Σ k, ι k) → L) (s : (Σ k, ι k) → R) (e : K → L) (t : K → ℂ) (zt : (Σ k, ι k) → ℂ)
    (hzt : ∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) (he : ∀ k, e k ≠ 0) (ht : ∀ k, t k ≠ 0) (has : ∀ q, a q = e q.1 * i (s q))
    (hv : ∀ q, ρ (s q) = t q.1 * zt q) : zt ∈ mcPts (mCoordIdeal a) := by
  refine ⟨hzt, fun f hf => ?_⟩
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal a
  rw [hE] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd⟩ := hT g hg
    have h0 : aeval a g = 0 :=
      (GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff a hd).1 (by rw [hE]; exact Ideal.subset_span hg)
    have ha : a = fun p => e p.1 * i (s p) := funext has
    have h1 : aeval (fun p => i (s p)) g = 0 := by
      have h := GroundTheory.Heights₂.Heights.Inter.ChartNormPts.aeval_smul_homog g d hd e fun p => i (s p)
      rw [← ha, h0] at h
      have hne : (∏ k, e k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (he k)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have comp : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] (φ : R' →+* R'') (w : (Σ k, ι k) → R') (f : MRing ι),
        aeval (fun p => φ (w p)) f = φ (aeval w f) := by
      intro R' R'' _ _ φ w f
      induction f using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp => simp only [map_mul, hp, aeval_X]
    have h2 : aeval s g = 0 := hi (by rw [← comp, h1, map_zero])
    have h3 : eval (fun p => t p.1 * zt p) (map (Int.castRingHom ℂ) g) = 0 := by
      have : aeval (fun p => ρ (s p)) g = 0 := by rw [comp, h2, map_zero]
      rw [funext hv, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map] at this
      simpa using this
    rw [ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog g d hd t zt] at h3
    have hne : (∏ k, t k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)
    exact (mul_eq_zero.1 h3).resolve_left hne
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul r x _ hx => simp [smul_eq_mul, map_mul, hx]

end Reg

section Mat

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

theorem minorIJ_map (f : R →+* S) (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · rw [map_zero]

theorem minorIJ_mem {L : Type} [Field L] (P : Subring L) {A : Matrix (Fin N) (Fin N) L} (hA : ∀ a b, A a b ∈ P)
    (I J : Finset (Fin N)) : minorIJ A I J ∈ P := by
  have e : A = (Matrix.of fun a b => (⟨A a b, hA a b⟩ : P)).map P.subtype := by ext a b; rfl
  rw [e, minorIJ_map]
  exact Subtype.coe_prop _

theorem det_mem {L : Type} [Field L] (P : Subring L) {A : Matrix (Fin N) (Fin N) L} (hA : ∀ a b, A a b ∈ P) :
    A.det ∈ P := by
  have e : A = (Matrix.of fun a b => (⟨A a b, hA a b⟩ : P)).map P.subtype := by ext a b; rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Subtype.coe_prop _

theorem minorIJ_one (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp only [detFac, minorIJ_one]
  simp

theorem stepCols_nonempty {j : ℕ} (hj : j ≤ N) (i : Fin N) : (stepCols N j i).Nonempty := by
  by_cases h : (i : ℕ) + 1 ≤ j
  · refine ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
    omega
  · refine ⟨⟨0, by have := i.2; omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
    omega

theorem detFac_ne_zero {L : Type} [Field L] {j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) L}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  have hu : IsUnit T.det := hd.isUnit
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing L N j i hj).2.2.2 T T⁻¹ hT (hT.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu, detFac_one] at h
  exact left_ne_zero_of_mul_eq_one h.symm

theorem map_mul_inv_map {L : Type} [Field L] (f : L →+* S) {T : Matrix (Fin N) (Fin N) L} (hd : T.det ≠ 0)
    (X : Matrix (Fin N) (Fin N) S) : T.map f * (T⁻¹.map f * X) = X := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd.isUnit, Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.one_mul]

end Mat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

include M in

theorem blockMap_base : IsBlockMap (ι := baseIdx ι M.blk) (ι' := ι) (Subtype.val : NonPluckerBlocks M.blk → K)
    (fun q => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq] at h
    subst h
    rfl
  · rintro ⟨k, i⟩ ⟨kb, rfl⟩
    exact ⟨⟨kb, i⟩, rfl⟩

theorem base_mem {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    basePart M.blk z ∈ mcPts (mCoordIdeal M.x) :=
  comp_mem_mcPts (blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base) hz

theorem val_lift {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {s : M.Ω}
    (hs : RegAt M.x (mCoordIdeal (basePart M.blk z)) s) :
    IsValueAt y (algebraMap M.Ω Φ s) z (valAt M.x s (basePart M.blk z)) := by
  have hb := blockMap_base M
  have hzb := base_mem M hz
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hg' := isMultiHomog_rename_block hb hg
  have hh' := isMultiHomog_rename_block hb hh
  have hn' : rename _ h ∉ mCoordIdeal z := rename_notMem hb hn
  have hy : y ∘ (fun q : Σ k, baseIdx ι M.blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) = (algebraMap M.Ω Φ) ∘ M.x :=
    funext M.y_base
  have heq' : aeval y (rename (fun q : Σ k, baseIdx ι M.blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g) =
      algebraMap M.Ω Φ s * aeval y (rename (fun q : Σ k, baseIdx ι M.blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) h) := by
    rw [aeval_rename, aeval_rename, hy, aeval_comp_ringHom, aeval_comp_ringHom, heq, map_mul]
  have v1 : IsValueAt M.x s (basePart M.blk z) _ :=
    ⟨d, g, h, hg, hh, aeval_ne_zero_of_notMem hzb hh hn, heq, eval_ne_zero_of_notMem hh hn, rfl⟩
  have v2 : IsValueAt y (algebraMap M.Ω Φ s) z _ :=
    ⟨_, _, _, hg', hh', aeval_ne_zero_of_notMem hz hh' hn', heq', eval_ne_zero_of_notMem hh' hn', rfl⟩
  rw [valAt_eq hzb v1, eval_rename_block, eval_rename_block] at *
  exact v2

theorem frame_gen {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {S : Type} [CommRing S] (f : Φ →+* S)
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) {G bb : Matrix (Fin N) (Fin N) S}
    (hG : IsBlockDiag j G) (hbb : IsBlockDiag j bb) (hbt : bb.BlockTriangular id)
    (e : (F.T p.1).map (f.comp (algebraMap M.Ω Φ)) * G = (M.g p.1).map f * bb) :
    f (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) * (∏ c ∈ stepCols N j p.2, bb c c) * f (y ⟨k, m⟩) =
      f (algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) *
        ∑ I, f (algebraMap M.Ω Φ (F.u ⟨k, m⟩ I)) * minorIJ G I (stepCols N j p.2) := by
  haveI : Infinite M.Ω := Infinite.of_injective (Nat.cast : ℕ → M.Ω) Nat.cast_injective
  letI : Algebra M.Ω S := (f.comp (algebraMap M.Ω Φ)).toAlgebra
  have h1 := GlobalTheory.T.minor_sum_identity_base_change M.Ω N j (F.T p.1) _ _ (M.coef ⟨k, m⟩) (F.u ⟨k, m⟩) (stepCols N j p.2)
    (hF.2.1 p k hp m) S G hG
  have e' : (F.T p.1).map (algebraMap M.Ω S) * G = (M.g p.1).map f * bb := e
  rw [e'] at h1
  have h2 : ∀ I, minorIJ ((M.g p.1).map f * bb) I (stepCols N j p.2) =
      f (minorIJ (M.g p.1) I (stepCols N j p.2)) * ∏ c ∈ stepCols N j p.2, bb c c := fun I => by
    rw [(GlobalTheory.T.block_diagonal_minor_vanishing S N j p.2 M.j_le).2.2.1 _ bb I hbb hbt, minorIJ_map]
  simp only [h2] at h1
  have h3 : f (y ⟨k, m⟩) = ∑ I, algebraMap M.Ω S (M.coef ⟨k, m⟩ I) * f (minorIJ (M.g p.1) I (stepCols N j p.2)) := by
    rw [M.y_step p k hp m, map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul]; rfl
  have ha : algebraMap M.Ω S (detFac j p.2 (F.T p.1)) = f (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) := rfl
  rw [h3, Finset.mul_sum]
  refine Eq.trans ?_ h1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [ha]
  ring

end Flag

section Back

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem flag_nonzero {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ι k) → ℂ}
    (hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (H : M.IsFlagOf F z h) (k : K) : ∃ i, z ⟨k, i⟩ ≠ 0 := by
  by_cases hk : ∀ p, M.blk p ≠ some k
  · obtain ⟨i, hi⟩ := hzb.1 ⟨k, hk⟩
    exact ⟨i, hi⟩
  · push_neg at hk
    obtain ⟨p, hp⟩ := hk
    obtain ⟨a, ha, hz⟩ := H.2.2 p k hp
    let val := regVal hzb
    let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x (basePart M.blk z) :=
      fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
    let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x (basePart M.blk z) :=
      fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
    have rel : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
        ∑ m : ι k, val (vA I ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I = I' then 1 else 0 := fun I I' hI hI' => by
      have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
        apply Subtype.ext
        have := hF.2.2.1 p k hp I I' hI hI'
        split_ifs at this ⊢ <;> simpa [uA, vA] using this
      have e' := congrArg val e
      rw [map_sum] at e'
      simp only [map_mul] at e'
      rw [e']
      split_ifs <;> simp
    obtain ⟨m, hm, -⟩ := GlobalTheory.T.step_rows_inverse_nonzero_entry ℂ ⊤ N j p.2 (h p.1) (ι k) (fun m I => val (uA ⟨k, m⟩ I))
      (fun I m => val (vA I ⟨k, m⟩)) M.j_le (H.2.1 p.1).1 (fun _ _ => ValuationSubring.mem_top _) (H.2.1 p.1).2
      (ValuationSubring.mem_top _) (fun _ _ => ValuationSubring.mem_top _) (fun _ _ => ValuationSubring.mem_top _) rel
    refine ⟨m, ?_⟩
    rw [hz m]
    exact mul_ne_zero ha hm

theorem flag_back {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ι k) → ℂ}
    (hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (H : M.IsFlagOf F z h) : z ∈ mcPts (mCoordIdeal y) := by
  have hnz := flag_nonzero M hF hzb hG H
  let A := regRing M.x (basePart M.blk z)
  let val : A →+* ℂ := regVal hzb
  let S := MvPolynomial (UpIdx Ψ N j) Φ
  let L := FractionRing S
  let G' : Ψ → Matrix (Fin N) (Fin N) S := fun τ =>
    ((F.T τ)⁻¹.map (algebraMap M.Ω S)) * ((M.g τ).map (C : Φ →+* S) * genUp Φ N j τ)
  have indep := GlobalTheory.T.generic_flag_algebraically_independent M.Ω Φ Ψ N j M.g F.T M.g_block M.g_indep hF.1
  let iS : MvPolynomial (inertBlockIndex Ψ N j) A →+* S :=
    eval₂Hom ((algebraMap M.Ω S).comp A.subtype) fun q => G' q.1.1 q.1.2.1 q.1.2.2
  have eS : ∀ r, iS r = aeval (fun q : inertBlockIndex Ψ N j => G' q.1.1 q.1.2.1 q.1.2.2) (MvPolynomial.map A.subtype r) := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => simp [iS]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X]; simp [iS]
  have hiS : Function.Injective iS := fun a b e => by
    refine MvPolynomial.map_injective A.subtype Subtype.val_injective
      ((algebraicIndependent_iff_injective_aeval.1 indep) ?_)
    rw [← eS, ← eS, e]
  let i : MvPolynomial (inertBlockIndex Ψ N j) A →+* L := (algebraMap S L).comp iS
  have hi : Function.Injective i := (IsFractionRing.injective S L).comp hiS
  let ρ : MvPolynomial (inertBlockIndex Ψ N j) A →+* ℂ := eval₂Hom val fun q => h q.1.1 q.1.2.1 q.1.2.2
  have hGb : ∀ τ, IsBlockDiag j (G' τ) := fun τ =>
    ((((hF.1 τ).1.inv (hF.1 τ).2.isUnit)).map _).mul (((M.g_block τ).map _).mul (genUp_blockDiag τ))
  have hiG : ∀ τ, (genericBlockMatrix A N j τ).map iS = G' τ := generic_block_matrix_map iS hGb fun q => by simp [iS]
  have hρ : ∀ τ, (genericBlockMatrix A N j τ).map ρ = h τ := generic_block_matrix_map ρ (fun τ => (H.2.1 τ).1) fun q => by simp [ρ]
  let φL : Φ →+* L := (algebraMap S L).comp (C : Φ →+* S)
  have hiC : ∀ a : A, i (C a) = φL (algebraMap M.Ω Φ a) := fun a => by
    show algebraMap S L (iS (C a)) = algebraMap S L (C (algebraMap M.Ω Φ a))
    congr 1
    exact (eval₂Hom_C _ _ _).trans (MvPolynomial.algebraMap_apply ..)
  have key : ∀ k, ∃ (e : L) (t : ℂ) (sv : ι k → MvPolynomial (inertBlockIndex Ψ N j) A), e ≠ 0 ∧ t ≠ 0 ∧
      (∀ m, φL (y ⟨k, m⟩) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t * z ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some k
    · let kb : NonPluckerBlocks M.blk := ⟨k, hk⟩
      have hxc : M.x ⟨kb, F.c kb⟩ ≠ 0 := M.x_chart_ne (mCoordIdeal_le hzb) hG kb
      have hzc : basePart M.blk z ⟨kb, F.c kb⟩ = 1 := H.1 kb
      have hv : ∀ m : ι k, IsValueAt M.x (M.x ⟨kb, m⟩ / M.x ⟨kb, F.c kb⟩) (basePart M.blk z)
          (basePart M.blk z ⟨kb, m⟩ / basePart M.blk z ⟨kb, F.c kb⟩) := fun m =>
        isValueAt_ratio hxc (by rw [hzc]; exact one_ne_zero)
      refine ⟨φL (algebraMap M.Ω Φ (M.x ⟨kb, F.c kb⟩)), 1, fun m => C ⟨_, _, hv m⟩, ?_, one_ne_zero, fun m => ?_, fun m => ?_⟩
      · exact (map_ne_zero _).2 ((map_ne_zero _).2 hxc)
      · rw [hiC, ← map_mul, ← map_mul, show y ⟨k, m⟩ = algebraMap M.Ω Φ (M.x ⟨kb, m⟩) from M.y_base ⟨kb, m⟩]
        congr 2
        exact (mul_div_cancel₀ _ hxc).symm
      · have e1 : ρ (C ⟨_, _, hv m⟩) = val ⟨_, _, hv m⟩ := eval₂Hom_C _ _ _
        rw [e1, show val ⟨_, _, hv m⟩ = _ from regVal_eq hzb _ (hv m), hzc, div_one, one_mul]
        rfl
    · push_neg at hk
      obtain ⟨p, hp⟩ := hk
      obtain ⟨a, ha, hz⟩ := H.2.2 p k hp
      let uA : (Σ k, ι k) → Finset (Fin N) → A := fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
      let D : S := ∏ c ∈ stepCols N j p.2, genUp Φ N j p.1 c c
      have hD : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => by
        rw [show genUp Φ N j p.1 c c = X ⟨(p.1, c, c), le_rfl, Iff.rfl⟩ from
          genUp_apply (⟨(p.1, c, c), le_rfl, Iff.rfl⟩ : UpIdx Ψ N j)]
        exact X_ne_zero _
      have hCam : (C : Φ →+* S).comp (algebraMap M.Ω Φ) = algebraMap M.Ω S :=
        RingHom.ext fun s => (MvPolynomial.algebraMap_apply ..).symm
      have hsv : ∀ m : ι k, i (∑ I, C (uA ⟨k, m⟩ I) * minorIJ (genericBlockMatrix A N j p.1) I (stepCols N j p.2)) =
          algebraMap S L (∑ I, C (algebraMap M.Ω Φ (F.u ⟨k, m⟩ I)) * minorIJ (G' p.1) I (stepCols N j p.2)) := fun m => by
        show algebraMap S L (iS _) = _
        congr 1
        rw [map_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul, ← minorIJ_map, hiG]
        congr 1
        exact (eval₂Hom_C _ _ _).trans (MvPolynomial.algebraMap_apply ..)
      have hdet : detFac j p.2 (F.T p.1) ≠ 0 := detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2
      have hE : (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0 := Finset.prod_ne_zero_iff.2 fun k' _ =>
        zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k')
      have hdetL : φL (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) ≠ 0 := (map_ne_zero _).2 ((map_ne_zero _).2 hdet)
      have hEL : φL (algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) ≠ 0 := (map_ne_zero _).2 ((map_ne_zero _).2 hE)
      have hDL : algebraMap S L D ≠ 0 := fun e => hD (IsFractionRing.injective S L (by rw [e, map_zero]))
      refine ⟨φL (algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) /
          (φL (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) * algebraMap S L D), a⁻¹,
        fun m => ∑ I, C (uA ⟨k, m⟩ I) * minorIJ (genericBlockMatrix A N j p.1) I (stepCols N j p.2),
        div_ne_zero hEL (mul_ne_zero hdetL hDL), inv_ne_zero ha, fun m => ?_, fun m => ?_⟩
      · have rel := frame_gen M hF (C : Φ →+* S) hp m (hGb p.1) (genUp_blockDiag p.1) (genUp_upper p.1)
          (by rw [hCam]; exact map_mul_inv_map _ (hF.1 p.1).2 _)
        have rel' := congrArg (algebraMap S L) rel
        rw [map_mul, map_mul, map_mul] at rel'
        rw [hsv, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hdetL hDL)]
        refine Eq.trans ?_ (rel'.trans ?_)
        · show _ = φL _ * algebraMap S L D * φL _
          ring
        · rfl
      · rw [map_sum, hz m, inv_mul_cancel_left₀ ha]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul, ← minorIJ_map, hρ]
        congr 1
        exact eval₂Hom_C _ _ _
  choose e t sv he ht has hv using key
  have hz' : z ∈ mcPts (mCoordIdeal (fun q : Σ k, ι k => φL (y q))) :=
    mem_mcPts_of_ringHom i hi ρ _ (fun q => sv q.1 q.2) e t z hnz he ht (fun q => has q.1 q.2) fun q => hv q.1 q.2
  refine ⟨hnz, fun f hf => hz'.2 f ?_⟩
  have h0 : mConeMap y f = 0 := hf
  show mConeMap (φL ∘ y) f = 0
  rw [mConeMap_comp, h0, map_zero]

end Back

section Fwd

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem flag_fwd {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    (hc : ∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) : ∃ h, M.IsFlagOf F z h := by
  have hzb := base_mem M hz
  let am := algebraMap M.Ω Φ
  let O := regRing y z
  let v : O →+* ℂ := regVal hz
  obtain ⟨V, hOV, hpl⟩ := GlobalTheory.T.valuation_ring_extension_specialization Φ O v (regVal_local hz)
  have hO : ∀ {s}, RegAt M.x (mCoordIdeal (basePart M.blk z)) s → am s ∈ O := fun hs => ⟨_, val_lift M hz hs⟩
  let Ag : Ψ → Matrix (Fin N) (Fin N) Φ := fun τ => (F.T τ)⁻¹.map am * M.g τ
  have hinvD : ∀ τ, ((F.T τ)⁻¹.map am).det ≠ 0 := fun τ => by
    have : ((F.T τ)⁻¹.map am).det = am ((F.T τ)⁻¹.det) := (RingHom.map_det am _).symm
    rw [this]
    refine (map_ne_zero am).2 fun h0 => ?_
    have h1 := Matrix.det_nonsing_inv_mul_det (F.T τ) (hF.1 τ).2.isUnit
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hAgB : ∀ τ, IsBlockDiag j (Ag τ) := fun τ =>
    (((hF.1 τ).1.inv (hF.1 τ).2.isUnit).map am).mul (M.g_block τ)
  have hAgD : ∀ τ, (Ag τ).det ≠ 0 := fun τ => by
    rw [Matrix.det_mul]
    exact mul_ne_zero (hinvD τ) (M.isUnit_det_g τ).ne_zero
  choose b hbB hbT hbd hbV hbdet hbinv using fun τ => GlobalTheory.T.block_diag_valuation_normalization Φ V N j (Ag τ) (hAgB τ) (hAgD τ)
  let H : Ψ → Matrix (Fin N) (Fin N) Φ := fun τ => Ag τ * b τ
  have hHB : ∀ τ, IsBlockDiag j (H τ) := fun τ => (hAgB τ).mul (hbB τ)
  let wf : ∀ (p : Ψ × Fin N) (k : K), ι k → Φ := fun p k m =>
    ∑ I, am (F.u ⟨k, m⟩ I) * minorIJ (H p.1) I (stepCols N j p.2)
  have data : ∀ p, ∃ wc : Φ, wc ∈ V ∧ wc ≠ 0 ∧ wc⁻¹ ∈ V ∧ ∀ k, M.blk p = some k → ∃ c : ι k, z ⟨k, c⟩ ≠ 0 ∧
      ∀ m, ∃ r, IsValueAt y r z (z ⟨k, m⟩ / z ⟨k, c⟩) ∧ wf p k m = r * wc := by
    intro p
    cases hp : M.blk p with
    | none => exact ⟨1, V.one_mem, one_ne_zero, by simpa using V.one_mem, fun k hk => by cases hk⟩
    | some k =>
      obtain ⟨c, hzc⟩ := hz.1 k
      have hyc : y ⟨k, c⟩ ≠ 0 := coord_ne hz hzc
      have hdet : am (detFac j p.2 (F.T p.1)) ≠ 0 :=
        (map_ne_zero am).2 (detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2)
      have hE : am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0 := (map_ne_zero am).2 (Finset.prod_ne_zero_iff.2 fun k' _ =>
        zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k'))
      have hB : (∏ c ∈ stepCols N j p.2, b p.1 c c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hbd p.1 c
      have rel : ∀ m, am (detFac j p.2 (F.T p.1)) * (∏ c ∈ stepCols N j p.2, b p.1 c c) * y ⟨k, m⟩ =
          am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * wf p k m := fun m =>
        frame_gen M hF (RingHom.id Φ) hp m (hHB p.1) (hbB p.1) (hbT p.1) (by
          show (F.T p.1).map am * ((F.T p.1)⁻¹.map am * M.g p.1 * b p.1) = (M.g p.1).map (RingHom.id Φ) * b p.1
          rw [Matrix.mul_assoc ((F.T p.1)⁻¹.map am), map_mul_inv_map am (hF.1 p.1).2]
          rfl)
      obtain ⟨e, he, hw⟩ : ∃ e : Φ, e ≠ 0 ∧ ∀ m, wf p k m = e * y ⟨k, m⟩ :=
        ⟨am (detFac j p.2 (F.T p.1)) * (∏ c ∈ stepCols N j p.2, b p.1 c c) / am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k'),
          div_ne_zero (mul_ne_zero hdet hB) hE, fun m => by
            rw [div_mul_eq_mul_div, rel m, mul_div_cancel_left₀ _ hE]⟩
      obtain ⟨m₀, hm₀, hm₀i⟩ := GlobalTheory.T.step_rows_inverse_nonzero_entry Φ V N j p.2 (H p.1) (ι k) (fun m I => am (F.u ⟨k, m⟩ I))
        (fun I m => am (F.u' I ⟨k, m⟩)) M.j_le (hHB p.1) (hbV p.1) (hbdet p.1) (hbinv p.1)
        (fun I m => hOV _ (hO (hG.2.1 _ I).2)) (fun m I => hOV _ (hO (hG.2.1 _ I).1)) (fun I I' hI hI' => by
          have := congrArg am (hF.2.2.1 p k hp I I' hI hI')
          rw [map_sum] at this
          simp only [map_mul] at this
          rw [this]
          split_ifs <;> simp)
      have hwc : wf p k c ≠ 0 := by rw [hw]; exact mul_ne_zero he hyc
      have hr : ∀ m, wf p k m = y ⟨k, m⟩ / y ⟨k, c⟩ * wf p k c := fun m => by
        rw [hw, hw]
        field_simp
      refine ⟨wf p k c, ?_, hwc, ?_, fun k' hk' => ?_⟩
      · exact sum_mem fun I _ => V.mul_mem _ _ (hOV _ (hO (hG.2.1 _ I).1)) (minorIJ_mem V.toSubring (hbV p.1) I _)
      · have h1 : y ⟨k, m₀⟩ / y ⟨k, c⟩ ∈ O := ⟨_, isValueAt_ratio hyc hzc⟩
        have h2 : (wf p k c)⁻¹ = y ⟨k, m₀⟩ / y ⟨k, c⟩ * (wf p k m₀)⁻¹ := by
          have hm₀' : wf p k m₀ ≠ 0 := hm₀
          rw [hr m₀] at hm₀' ⊢
          have h3 := left_ne_zero_of_mul hm₀'
          rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
        rw [h2]
        exact V.mul_mem _ _ (hOV _ h1) hm₀i
      · obtain rfl := Option.some.inj hk'
        exact ⟨c, hzc, fun m => ⟨_, isValueAt_ratio hyc hzc, hr m⟩⟩
  choose wc hwV hw0 hwinv hdat using data
  let T : Finset Φ := (Finset.univ.image fun t : Ψ × Fin N × Fin N => H t.1 t.2.1 t.2.2) ∪
    (Finset.univ.image fun τ => (H τ).det) ∪ (Finset.univ.image wc)
  have hT1 : ∀ τ a c, H τ a c ∈ T := fun τ a c => Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.2 ⟨(τ, a, c), Finset.mem_univ _, rfl⟩))
  have hT2 : ∀ τ, (H τ).det ∈ T := fun τ => Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨τ, Finset.mem_univ _, rfl⟩))
  have hT3 : ∀ p, wc p ∈ T := fun p => Finset.mem_union_right _ (Finset.mem_image.2 ⟨p, Finset.mem_univ _, rfl⟩)
  have hTV : ∀ t ∈ T, t ∈ V := fun t ht => by
    rcases Finset.mem_union.1 ht with ht | ht
    · rcases Finset.mem_union.1 ht with ht | ht
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        exact hbV _ _ _
      · obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 ht
        exact det_mem V.toSubring (hbV τ)
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
      exact hwV p
  obtain ⟨R, hOR, ψ, hTR, hψ, hinv⟩ := hpl T hTV
  let HR : Ψ → Matrix (Fin N) (Fin N) R := fun τ => Matrix.of fun a c => ⟨H τ a c, hTR _ (hT1 τ a c)⟩
  have hHR : ∀ τ, (HR τ).map R.subtype = H τ := fun τ => by ext a c; rfl
  refine ⟨fun τ => (HR τ).map ψ, hc, fun τ => ⟨?_, ?_⟩, fun p k hp => ?_⟩
  · intro a c hac
    have h0 : HR τ a c = 0 := Subtype.ext (hHB τ a c hac)
    show ψ (HR τ a c) = 0
    rw [h0, map_zero]
  · have e1 : R.subtype (HR τ).det = (H τ).det := by rw [RingHom.map_det]; exact congrArg _ (hHR τ)
    have e2 : (HR τ).det * ⟨(H τ).det⁻¹, hinv _ (hT2 τ) (hbdet τ) (hbinv τ)⟩ = 1 := Subtype.ext (by
      show R.subtype (HR τ).det * (H τ).det⁻¹ = 1
      rw [e1, mul_inv_cancel₀ (hbdet τ)])
    have e3 := congrArg ψ e2
    rw [map_mul, map_one, RingHom.map_det] at e3
    exact left_ne_zero_of_mul_eq_one e3
  · obtain ⟨c, hzc, hm⟩ := hdat p k hp
    let wR : R := ⟨wc p, hTR _ (hT3 p)⟩
    have hβ : ψ wR ≠ 0 := by
      have e2 : wR * ⟨(wc p)⁻¹, hinv _ (hT3 p) (hw0 p) (hwinv p)⟩ = 1 := Subtype.ext (mul_inv_cancel₀ (hw0 p))
      have e3 := congrArg ψ e2
      rw [map_mul, map_one] at e3
      exact left_ne_zero_of_mul_eq_one e3
    refine ⟨z ⟨k, c⟩ / ψ wR, div_ne_zero hzc hβ, fun m => ?_⟩
    obtain ⟨r, hr, hw⟩ := hm m
    let uR : Finset (Fin N) → R := fun I => Subring.inclusion hOR ⟨am (F.u ⟨k, m⟩ I), hO (hG.2.1 _ I).1⟩
    let rR : R := Subring.inclusion hOR ⟨r, _, hr⟩
    have e1 : ∑ I, uR I * minorIJ (HR p.1) I (stepCols N j p.2) = rR * wR := Subtype.ext (by
      show R.subtype _ = r * wc p
      rw [map_sum]
      simp only [map_mul, ← minorIJ_map, hHR]
      exact hw)
    have e2 := congrArg ψ e1
    rw [map_sum] at e2
    simp only [map_mul, ← minorIJ_map] at e2
    have e3 : ∀ I, ψ (uR I) = valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) := fun I =>
      (hψ _).trans (regVal_eq hz _ (val_lift M hz (hG.2.1 _ I).1))
    have e4 : ψ rR = z ⟨k, m⟩ / z ⟨k, c⟩ := (hψ _).trans (regVal_eq hz _ hr)
    simp only [e3] at e2
    rw [e4] at e2
    show z ⟨k, m⟩ = _ * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ ((HR p.1).map ψ) I (stepCols N j p.2)
    rw [e2]
    field_simp

end Fwd

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j), (∀ z ∈ mcPts (mCoordIdeal y), basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) ∧ (∀ zb ∈ mcPts (mCoordIdeal M.x), ∃ F, M.IsFrame F ∧ M.GoodAt F (mCoordIdeal zb)) ∧ ∀ F, M.IsFrame F → ∀ z : (Σ k, ι k) → ℂ, basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) → (z ∈ mcPts (mCoordIdeal y) ↔ ∃ h, M.IsFlagOf F z h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M
  refine ⟨fun z hz => base_mem M hz, fun zb hzb => ?_, fun F hF z hzb hG hc => ⟨fun hz => flag_fwd M hF hz hG hc, fun ⟨h, H⟩ => flag_back M hF hzb hG H⟩⟩
  choose c hc using hzb.1
  exact M.frames _ (RingHom.ker_isPrime _) (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant zb c hc)
    (mCoordIdeal_le hzb)

end GlobalTheory.CompanionTheory.Ar.PB.CPts
