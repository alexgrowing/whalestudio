import Mathlib
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues

section SlopeTestRemainingChoices

theorem exists_left_inv {F : Type} [Field F] {n d : ℕ} (E : Matrix (Fin n) (Fin d) F)
    (h : Function.Injective E.mulVec) : ∃ L : Matrix (Fin d) (Fin n) F, L * E = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' E) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' E) hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' E) = 1 := by
    rw [hg]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1

theorem inj_of_left_inv {F : Type} [Field F] {n d : ℕ} {C : Matrix (Fin n) (Fin d) F}
    {L : Matrix (Fin d) (Fin n) F} (h : L * C = 1) : Function.Injective C.mulVec := by
  intro x y hxy
  have := congrArg L.mulVec hxy
  simpa [Matrix.mulVec_mulVec, h] using this

theorem map_one' {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) K).map σ = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem map_inj {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (h : Function.Injective E.mulVec) : Function.Injective (E.map σ).mulVec := by
  obtain ⟨L, hL⟩ := exists_left_inv E h
  apply inj_of_left_inv (L := L.map σ)
  rw [← Matrix.map_mul, hL, map_one']

theorem map_surj {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (P : Matrix (Fin d) (Fin n) K)
    (h : Function.Surjective P.mulVec) : Function.Surjective (P.map σ).mulVec := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  exact ⟨R.map σ, by rw [← Matrix.map_mul, hR, map_one']⟩

theorem map_conjTranspose' {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ).map σ = (E.map σ)ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
  rw [hE i a]
  rfl

theorem majAt_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec (fun i => v.embedding (y i)) := by
  have h1 : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v u =
      fun i => v.embedding (u i) := by
    intro u; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1, metOf]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

theorem emb_mulVec {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (x : Fin d → K) : (fun i => σ (E.mulVec x i)) = (E.map σ).mulVec (fun a => σ (x a)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

end SlopeTestRemainingChoices

theorem frameOfSpec : FrameOfSpec := by
  intro n A hA
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A := hA.posSemidef.nonneg
  have hs : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have hdet : IsUnit (CFC.sqrt A).det := by
    have h1 : A.det ≠ 0 := hA.det_pos.ne'
    rw [← hs, Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  have hH : (CFC.sqrt A)ᴴ = CFC.sqrt A := by
    have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  rw [metOf, frameOf, Matrix.nonsing_inv_nonsing_inv _ hdet, hH, hs]

theorem metOfSpec : MetOfSpec := by
  intro n Y hY
  have hpos : (metOf Y).PosDef := by
    apply Matrix.PosDef.conjTranspose_mul_self
    exact Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hY))
  refine ⟨hpos, ?_, (frameOfSpec n _ hpos).2⟩
  apply Matrix.inv_eq_right_inv
  rw [metOf, Matrix.mul_assoc, ← Matrix.mul_assoc Y⁻¹, Matrix.nonsing_inv_mul _ hY, Matrix.one_mul,
    ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hY, Matrix.conjTranspose_one]

theorem quotRestrPosDef : QuotRestrPosDef := by
  intro n d A hA
  refine ⟨fun P hP => ?_, fun C hC => hA.conjTranspose_mul_mul_same hC⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hP
  have hinj : Function.Injective (Pᴴ).mulVec := by
    apply inj_of_left_inv (L := Rᴴ)
    rw [← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one]
  have h1 := hA.inv.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_conjTranspose] at h1
  exact h1.inv

theorem quotEqRestrC : QuotEqRestrC := by
  intro n d A hA C P h1 h2
  have hGP : Cᴴ * A * C * P = Cᴴ * A := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Cᴴ * A), ← h2]
  have hPG : Pᴴ * (Cᴴ * A * C) = A * C := by
    have := congrArg Matrix.conjTranspose hGP
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  rw [quotMetC, restrMetC]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_assoc, hPG, Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mul, h1]

theorem stdFrameRatHerm : StdFrameRatHerm := by
  intro K _ _ _ K0 n H h1 h2
  exact ⟨h1, fun v => frameOfSpec n _ (h2 v)⟩

theorem stdFrameHermAt : StdFrameHermAt := by
  intro K _ _ v0 n H h2
  exact ⟨fun v => (frameOfSpec n _ (h2 v)).1, (frameOfSpec n _ (h2 v0)).2⟩

theorem quotFrameIsQuot : QuotFrameIsQuot := by
  intro K _ _ _ n D H h2 P hP v
  exact frameOfSpec D _ ((quotRestrPosDef n D _ (h2 v)).1 _ (map_surj _ P hP))

theorem restrFrameSpec : RestrFrameSpec := by
  intro K _ _ _ n d H h2 E hE v
  have hs := frameOfSpec d _ ((quotRestrPosDef n d _ (h2 v)).2 _ (map_inj v.embedding E hE))
  refine ⟨hs.1, hs.2, fun x y => ?_⟩
  have hm1 : metOf (restrFrame E H v) = restrMetC (E.map v.embedding) (H.map v.embedding) := hs.2
  have hm2 : metOf (stdFrame H v) = H.map v.embedding := (frameOfSpec n _ (h2 v)).2
  rw [majAt_eq, majAt_eq, hm1, hm2, emb_mulVec, emb_mulVec, restrMetC, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem map_restr {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ * H * E).map σ = restrMetC (E.map σ) (H.map σ) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose' σ E hE, restrMetC]

theorem restrFrameHermAt : RestrFrameHermAt := by
  intro K _ _ _ v0 hv0 n d H h2 E hE
  refine ⟨fun v => (restrFrameSpec K n d H h2 E hE v).1, ?_⟩
  rw [map_restr v0.embedding H E fun i a => hv0 _]
  exact (restrFrameSpec K n d H h2 E hE v0).2.1

theorem restrFrameRatHerm : RestrFrameRatHerm := by
  intro K _ _ _ K0 hcm hstar n d H h1 h2 E hE hE0
  have hmap : ∀ v : InfinitePlace K, (Eᴴ * H * E).map v.embedding =
      restrMetC (E.map v.embedding) (H.map v.embedding) :=
    fun v => map_restr v.embedding H E fun i a => hcm _ _ (hE0 i a)
  refine ⟨⟨?_, fun v => ⟨(restrFrameSpec K n d H h2 E hE v).1, ?_⟩⟩, ?_⟩
  · intro a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _
      (Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hstar _ (hE0 i a)) (h1 i j)) (hE0 j b)
  · rw [hmap v]
    exact (restrFrameSpec K n d H h2 E hE v).2.1
  · funext v
    rw [stdFrame, hmap v, restrFrame]

theorem quot_eq_restr_of {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)
    {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v.embedding).PosDef)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (hE : ∀ i a, v.embedding (star (E i a)) = starRingEnd ℂ (v.embedding (E i a)))
    (hP : IsOrthProj H E Pr) : quotFrame Pr H v = restrFrame E H v := by
  have h1 : Pr.map v.embedding * E.map v.embedding = 1 := by
    rw [← Matrix.map_mul, hP.1, map_one']
  have h2 : (E.map v.embedding)ᴴ * H.map v.embedding *
      (1 - E.map v.embedding * Pr.map v.embedding) = 0 := by
    have := congrArg (fun M => M.map v.embedding) hP.2
    simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub v.embedding), map_one',
      map_conjTranspose' v.embedding E hE] at this
    rw [this]
    exact Matrix.map_zero _ (map_zero _)
  rw [quotFrame, restrFrame, quotEqRestrC n d _ hH _ _ h1 h2]

theorem quotEqRestrAt : QuotEqRestrAt := by
  intro K _ _ _ v0 hv0 n d H hH E Pr hP
  exact quot_eq_restr_of v0 H hH E Pr (fun i a => hv0 _) hP

theorem quotEqRestrRat : QuotEqRestrRat := by
  intro K _ _ _ K0 hcm n d H hH E Pr hE hP
  funext v
  exact quot_eq_restr_of v H (hH v) E Pr (fun i a => hcm _ _ (hE i a)) hP

theorem quotFrameHermAt : QuotFrameHermAt := by
  intro K _ _ _ v0 hv0 n d H hH E Pr hP
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hinj : Function.Injective E.mulVec := inj_of_left_inv hP.1
  refine ⟨fun v => (quotFrameIsQuot K n d H hH Pr hsurj v).1, ?_⟩
  rw [quotEqRestrAt K v0 hv0 n d H (hH v0) E Pr hP]
  exact (restrFrameHermAt K v0 hv0 n d H hH E hinj).2

theorem spliceFrameSpec : SpliceFrameSpec := by
  intro K _ _ n v0 Y X
  classical
  exact ⟨by simp [spliceFrame], fun v hv => by simp [spliceFrame, hv]⟩

section Weight

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ix : Type} [Fintype Ix]

theorem weightMet_form (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (weightMet pr t X v).mulVec y =
      ∑ p, ((t p v : ℝ) : ℂ) * (star (((pr p).map v.embedding).mulVec x) ⬝ᵥ
        (metOf (X v)).mulVec (((pr p).map v.embedding).mulVec y)) := by
  rw [weightMet, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, restrMetC, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem sum_map_eq_one (pr : Ix → Matrix (Fin n) (Fin n) K) (hsum : ∑ p, pr p = 1) (σ : K →+* ℂ) :
    ∑ p, (pr p).map σ = 1 := by
  have := congrArg σ.mapMatrix hsum
  simpa [map_sum, RingHom.mapMatrix_apply] using this

theorem weightMet_posDef (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (ht : ∀ p v, 0 < t p v) (hsum : ∑ p, pr p = 1) (v : InfinitePlace K) :
    (weightMet pr t X v).PosDef := by
  have hM := (metOfSpec n _ (hX v)).1
  have hpsd : (weightMet pr t X v).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro p _
    apply Matrix.PosSemidef.smul (hM.posSemidef.conjTranspose_mul_mul_same _)
    exact_mod_cast (ht p v).le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  rw [weightMet_form]
  have ht' : ∀ p, (0 : ℂ) < ((t p v : ℝ) : ℂ) := fun p => by exact_mod_cast ht p v
  apply Finset.sum_pos'
  · intro p _
    exact mul_nonneg (ht' p).le (hM.posSemidef.dotProduct_mulVec_nonneg _)
  · by_contra hcon
    apply hx
    have h0 : ∀ p, ((pr p).map v.embedding).mulVec x = 0 := by
      intro p
      by_contra hp
      exact hcon ⟨p, Finset.mem_univ p, mul_pos (ht' p) (hM.dotProduct_mulVec_pos hp)⟩
    have h1 : x = (∑ p, (pr p).map v.embedding).mulVec x := by
      rw [sum_map_eq_one pr hsum, Matrix.one_mulVec]
    rw [h1, Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun p _ => h0 p

end Weight

theorem weightFrameSpec : WeightFrameSpec := by
  intro K _ _ _ n Ix _ pr t X hX ht hsum v
  have hs := frameOfSpec n _ (weightMet_posDef pr t X hX ht hsum v)
  refine ⟨hs.1, hs.2, fun x y => ?_⟩
  have hm : metOf (weightFrame pr t X v) = weightMet pr t X v := hs.2
  rw [majAt_eq, hm, weightMet_form]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [majAt_eq, emb_mulVec, emb_mulVec]

theorem weightFramePart : WeightFramePart := by
  intro K _ _ _ n Ix _ pr t X hX ht hsum horth v hperp p x y hx
  classical
  rw [(weightFrameSpec K n Ix pr t X hX ht hsum v).2.2 x y]
  have hq0 : ∀ q, q ≠ p → (pr q).mulVec x = 0 := by
    intro q hq
    rw [← hx, Matrix.mulVec_mulVec, horth q p hq, Matrix.zero_mulVec]
  have hz : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v 0 u = 0 := by
    intro u
    rw [majAt_eq]
    have : (fun i => v.embedding ((0 : Fin n → K) i)) = 0 := by funext i; simp
    rw [this, star_zero, zero_dotProduct]
  rw [Finset.sum_eq_single p (fun q _ hq => by rw [hq0 q hq, hz, mul_zero])
    (fun h => absurd (Finset.mem_univ p) h), hx]
  congr 1
  have hy : (fun i => v.embedding (y i)) =
      ∑ q, ((pr q).map v.embedding).mulVec (fun i => v.embedding (y i)) := by
    rw [← Matrix.sum_mulVec, sum_map_eq_one pr hsum, Matrix.one_mulVec]
  have hterm : ∀ q, q ≠ p → star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec
      (((pr q).map v.embedding).mulVec (fun i => v.embedding (y i))) = 0 := by
    intro q hq
    have := hperp p q (Ne.symm hq) x y
    rwa [hx, majAt_eq, emb_mulVec] at this
  rw [majAt_eq, majAt_eq, emb_mulVec]
  conv_rhs => rw [hy, Matrix.mulVec_sum, dotProduct_sum]
  rw [Finset.sum_eq_single p (fun q _ hq => hterm q hq) (fun h => absurd (Finset.mem_univ p) h)]

theorem majAt_congr_frame {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X X2 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (h : X v = X2 v)
    (x y : Fin n → K) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X2 v x y := by
  rw [majAt_eq, majAt_eq, h]

theorem normAt_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x =
      Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x).re := by
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.majAt]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

section Instances

variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem isCMSub_cmMax' : IsCMSub (cmMax K) := fun σ _ ha => ha σ

def sumP : Matrix (Fin 1) (Fin 2) K := Matrix.of fun _ _ => 1

def diagE : Matrix (Fin 2) (Fin 1) K := Matrix.of fun _ _ => 1

end Instances

end Formalism.L2.DIV
