import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticNinth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTransferIdealEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticEighth
import Development.WeilBound.CoreStatements.PluriharmonicCharts.LocalAnalyticSectionCoords
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap GlobalTheory.CompanionTheory.Ar.PB.CovGraph PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

section Mat

variable {R : Type} [CommRing R] {N j : ℕ}

theorem mul_transv_apply (A : Matrix (Fin N) (Fin N) R) (ca cb : Fin N) (t : R) (r c : Fin N) :
    (A * (1 + Matrix.single cb ca t)) r c = A r c + if c = ca then A r cb * t else 0 := by
  rw [mul_add, mul_one, Matrix.add_apply]
  congr 1
  split_ifs with h
  · subst h; exact Matrix.mul_single_apply_same _ _ _ _ _
  · exact Matrix.mul_single_apply_of_ne _ _ _ _ _ h _

theorem lowerUni_mul_transv {A : Matrix (Fin N) (Fin N) R} (hA : IsLowerUni A) {ca cb : Fin N}
    (hc : (cb : ℕ) = ca + 1) (t : R) : IsLowerUni (A * (1 + Matrix.single cb ca t)) := by
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  refine ⟨fun r => ?_, fun r c h => ?_⟩
  · rw [mul_transv_apply, hA.1]
    split_ifs with e
    · rw [hA.2 r cb (e ▸ hlt)]; simp
    · simp
  · rw [mul_transv_apply, hA.2 r c h]
    split_ifs with e
    · rw [hA.2 r cb (h.trans (e ▸ hlt))]; simp
    · simp

theorem minor_lowerUni {A : Matrix (Fin N) (Fin N) R} (hA : IsLowerUni A) (S : Finset (Fin N)) :
    minorIJ A S S = 1 := by
  rw [MinorCalc.minorIJ_eq_det A S S _ rfl rfl, det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => hA.1 _
  · intro x y hxy
    exact hA.2 _ _ ((S.orderEmbOfFin rfl).strictMono hxy)

theorem minor_transv {a b ca cb i : Fin N} (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) (A : Matrix (Fin N) (Fin N) R) (t : R)
    (I : Finset (Fin N)) :
    minorIJ (A * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ A I (stepCols N j i) := by
  have hu := lowerUni_mul_transv (isLowerUni_one (R := R) (N := N)) hcb t
  rw [one_mul] at hu
  rw [MinorCalc.minorIJ_mul_of_support A _ I _ ?_, minor_lowerUni hu, mul_one]
  intro k c hc hk
  have hkc : k ≠ c := fun e => hk (e ▸ hc)
  rw [Matrix.add_apply, Matrix.one_apply_ne hkc, zero_add]
  refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
  rintro ⟨rfl, rfl⟩
  apply hk
  have hi' : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
  have := b.2
  have := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, lastCol] at hc hca ⊢
  split_ifs at hc hca ⊢ <;> omega

end Mat

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

section Re

variable {L : Type} [Field L]

def ptOf (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) : (Σ k, ι k) → L := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then ψ (M.x ⟨⟨q.1, h⟩, q.2⟩)
  else ∑ I, ψ (M.coef q I) * minorIJ (G (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem ptOf_base (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L)
    (q : Σ k, baseIdx ι M.blk k) : ptOf M ψ G ⟨q.1.1, q.2⟩ = ψ (M.x q) := dif_pos q.1.2

theorem ptOf_step (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L)
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (m : ι k) :
    ptOf M ψ G ⟨k, m⟩ = ∑ I, ψ (M.coef ⟨k, m⟩ I) * minorIJ (G p.1) I (stepCols N j p.2) := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
  have e : stepOf M k h = p := M.blk_inj _ _ k (blk_stepOf M k h) hp
  show (if h : ∀ p, M.blk p ≠ some k then _ else _) = _
  rw [dif_neg h]
  simp only [e]

def IsGenLow {Ω : Type} [Field Ω] (ψ : Ω →+* L) (j : ℕ) (G : Ψ → Matrix (Fin N) (Fin N) L) : Prop :=
  (∀ τ, IsBlockDiag j (G τ) ∧ IsLowerUni (G τ)) ∧
    Function.Injective (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2)

def reModel (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) (hG : IsGenLow ψ j G) :
    FlagModel (ptOf M ψ G) Ψ N j where
  j_le := M.j_le
  Ω := M.Ω
  alg := ψ.toAlgebra
  blk := M.blk
  blk_none := M.blk_none
  blk_inj := M.blk_inj
  x := M.x
  x_ne := M.x_ne
  y_base q := ptOf_base M ψ G q
  g := G
  g_block τ := (hG.1 τ).1
  g_indep := by
    letI := ψ.toAlgebra
    exact IsGenericFlag.of_lowerUni (fun τ => (hG.1 τ).2) hG.2
  coef := M.coef
  y_step := ptOf_step M ψ G
  b := M.b
  lam := M.lam
  frames := M.frames

open GenIdeal in
theorem ideal_ptOf (M : FlagModel y Ψ N j) (ψ : M.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) (hG : IsGenLow ψ j G) :
    mCoordIdeal (ptOf M ψ G) = mCoordIdeal y := by
  obtain ⟨B, hB, hind⟩ := M.g_indep
  let ev : MvPolynomial (LowIdx Ψ N j) M.Ω →ₐ[M.Ω] Φ := aeval fun q => (M.g q.1.1 * B q.1.1) q.1.2.1 q.1.2.2
  obtain ⟨c, hc, hz⟩ := exists_scale M ev.toRingHom (algebraMap M.Ω Φ) (fun a => aeval_C _ a) M.g B M.g_block hB
    (fun q => aeval_X _ q) y M.y_base M.y_step
  obtain ⟨c', hc', hz'⟩ := exists_scale M (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2) ψ
    (fun a => eval₂Hom_C _ _ a) G (fun _ => 1) (fun τ => (hG.1 τ).1)
    (fun τ => ⟨isBlockDiag_one, blockTriangular_one, by rw [mul_one]; exact (hG.1 τ).2⟩)
    (fun q => by rw [mul_one]; exact eval₂Hom_X' _ _ q) (ptOf M ψ G) (ptOf_base M ψ G) (ptOf_step M ψ G)
  rw [mCoordIdeal_eq _ hG.2 _ _ c' hc' hz', mCoordIdeal_eq ev.toRingHom hind _ _ c hc hz]

theorem exists_genLow (M : FlagModel y Ψ N j) : ∃ G, IsGenLow (algebraMap M.Ω Φ) j (G : Ψ → Matrix (Fin N) (Fin N) Φ) := by
  obtain ⟨B, hB, hind⟩ := M.g_indep
  exact ⟨fun τ => M.g τ * B τ, fun τ => ⟨(M.g_block τ).mul (hB τ).1, (hB τ).2.2⟩, hind⟩

variable {Ω : Type} [Field Ω] {ψ : Ω →+* L} {G : Ψ → Matrix (Fin N) (Fin N) L}

theorem IsGenLow.restrict (h : IsGenLow ψ j G) {Ω₂ : Type} [Field Ω₂] (φ : Ω₂ →+* Ω) : IsGenLow (ψ.comp φ) j G := by
  refine ⟨h.1, ?_⟩
  have e : (eval₂Hom (ψ.comp φ) fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2) =
      (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2).comp (MvPolynomial.map φ) :=
    MvPolynomial.ringHom_ext (fun a => by simp) fun q => by simp
  rw [e]
  exact h.2.comp (MvPolynomial.map_injective φ φ.injective)

def flag₀ (G : Ψ → Matrix (Fin N) (Fin N) L) : Ψ → Matrix (Fin N) (Fin N) (RatFunc L) :=
  fun τ => (G τ).map (algebraMap L (RatFunc L))

def flag₁ (G : Ψ → Matrix (Fin N) (Fin N) L) (τ : Ψ) (ca cb : Fin N) : Ψ → Matrix (Fin N) (Fin N) (RatFunc L) :=
  Function.update (flag₀ G) τ (flag₀ G τ * (1 + Matrix.single cb ca RatFunc.X))

theorem IsGenLow.flag₀ (h : IsGenLow ψ j G) : IsGenLow ((algebraMap L (RatFunc L)).comp ψ) j (flag₀ G) := by
  refine ⟨fun τ => ⟨(h.1 τ).1.map _, (h.1 τ).2.map _⟩, ?_⟩
  have e : (eval₂Hom ((algebraMap L (RatFunc L)).comp ψ) fun q : LowIdx Ψ N j =>
      c_sqsys.flag₀ G q.1.1 q.1.2.1 q.1.2.2) =
      (algebraMap L (RatFunc L)).comp (eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2) :=
    MvPolynomial.ringHom_ext (fun a => by simp) fun q => by simp [c_sqsys.flag₀]
  rw [e]
  exact (algebraMap L (RatFunc L)).injective.comp h.2

theorem IsGenLow.flag₁ (h : IsGenLow ψ j G) (τ : Ψ) {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1)
    (hS : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j)) :
    IsGenLow ((algebraMap L (RatFunc L)).comp ψ) j (flag₁ G τ ca cb) := by
  refine ⟨fun τ' => ?_, ?_⟩
  · by_cases e : τ' = τ
    · subst e
      rw [c_sqsys.flag₁, Function.update_self]
      exact ⟨(h.flag₀.1 τ').1.mul (Pts.transv_block hS _), lowerUni_mul_transv (h.flag₀.1 τ').2 hc _⟩
    · rw [c_sqsys.flag₁, Function.update_of_ne e]
      exact h.flag₀.1 τ'
  · let P : LowIdx Ψ N j → Polynomial L := fun q => Polynomial.C (G q.1.1 q.1.2.1 q.1.2.2) +
      if q.1.1 = τ ∧ q.1.2.2 = ca then Polynomial.C (G q.1.1 q.1.2.1 cb) * Polynomial.X else 0
    have e : (eval₂Hom ((algebraMap L (RatFunc L)).comp ψ) fun q : LowIdx Ψ N j =>
        c_sqsys.flag₁ G τ ca cb q.1.1 q.1.2.1 q.1.2.2) =
        (algebraMap (Polynomial L) (RatFunc L)).comp (eval₂Hom (Polynomial.C.comp ψ) P) := by
      refine MvPolynomial.ringHom_ext (fun a => by simp) fun q => ?_
      simp only [eval₂Hom_X', RingHom.comp_apply, P, c_sqsys.flag₁]
      by_cases e : q.1.1 = τ
      · rw [e, Function.update_self, mul_transv_apply]
        by_cases e' : q.1.2.2 = ca <;> simp [e', c_sqsys.flag₀]
      · rw [Function.update_of_ne e]
        simp [e, c_sqsys.flag₀]
    have e2 : (Polynomial.evalRingHom 0).comp (eval₂Hom (Polynomial.C.comp ψ) P) =
        eval₂Hom ψ fun q : LowIdx Ψ N j => G q.1.1 q.1.2.1 q.1.2.2 := by
      refine MvPolynomial.ringHom_ext (fun a => by simp) fun q => ?_
      simp only [eval₂Hom_X', RingHom.comp_apply, P]
      split_ifs <;> simp
    rw [e]
    refine (IsFractionRing.injective (Polynomial L) (RatFunc L)).comp ?_
    have := h.2
    rw [← e2] at this
    exact Function.Injective.of_comp this

end Re

section Gen

variable {M : FlagModel y Ψ N j} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}

theorem wCo_v₀ (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (k₀ : K) (ca cb : Fin N) :
    M.wCo p k₀ ca cb RatFunc.X ∘ v₀ k₀ =
      ptOf M ((algebraMap Φ (RatFunc Φ)).comp (algebraMap M.Ω Φ)) (flag₀ M.g) := by
  funext ⟨k, m⟩
  show algebraMap Φ (RatFunc Φ) (y ⟨k, m⟩) = _
  by_cases hk : ∀ p, M.blk p ≠ some k
  · exact (congrArg _ (M.y_base ⟨⟨k, hk⟩, m⟩)).trans
      (ptOf_base M ((algebraMap Φ (RatFunc Φ)).comp (algebraMap M.Ω Φ)) (flag₀ M.g) ⟨⟨k, hk⟩, m⟩).symm
  · push_neg at hk
    obtain ⟨p, hp⟩ := hk
    rw [ptOf_step M _ _ p k hp, M.y_step p k hp, map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul, ← CPts.minorIJ_map]; rfl

theorem Sw.wCo_v₁ (S : Sw M τ a b k₀ ca cb) :
    M.wCo (τ, a) k₀ ca cb RatFunc.X ∘ v₁ k₀ =
      ptOf M ((algebraMap Φ (RatFunc Φ)).comp (algebraMap M.Ω Φ)) (flag₁ M.g τ ca cb) := by
  funext ⟨k, m⟩
  by_cases e : k = k₀
  · subst e
    show M.wCo (τ, a) k ca cb RatFunc.X (v₁ k ⟨k, m⟩) = _
    rw [v₁_self, ptOf_step M _ _ _ k S.hk]
    simp only [flag₁, Function.update_self]
    rfl
  · show M.wCo (τ, a) k₀ ca cb RatFunc.X (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    refine (congrFun (wCo_v₀ M (τ, a) k₀ ca cb) ⟨k, m⟩).trans ?_
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact (ptOf_base M _ _ ⟨⟨k, hk⟩, m⟩).trans (ptOf_base M _ _ ⟨⟨k, hk⟩, m⟩).symm
    · push_neg at hk
      obtain ⟨⟨τ', i⟩, hp⟩ := hk
      rw [ptOf_step M _ _ _ k hp, ptOf_step M _ _ _ k hp]
      by_cases e' : τ' = τ
      · subst e'
        have hi : i ≠ a := fun h => e (by rw [h, S.hk] at hp; exact (Option.some.inj hp).symm)
        simp only [flag₁, Function.update_self, minor_transv M.j_le S.hb S.hab S.hca S.hcb hi]
      · simp only [flag₁, Function.update_of_ne e']

end Gen

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

def reCover {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {L : Type} [Field L]
    (ψ : M'.Ω →+* L) (G : Ψ → Matrix (Fin N) (Fin N) L) (hG : IsGenLow ψ j G) : FlagCover (reModel M' ψ G hG) M where
  κ := Cv.κ
  v := Cv.v
  block := Cv.block
  φ := Cv.φ
  x_eq := Cv.x_eq
  deg_pos := Cv.deg_pos
  agree := Cv.agree

theorem transPt_eq {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) :
    ptOf M ((algebraMap M'.Ω Φ').comp Cv.φ) M'.g = transPt Cv := by
  funext ⟨k, m⟩
  by_cases hk : ∀ p, M.blk p ≠ some k
  · exact (ptOf_base M ((algebraMap M'.Ω Φ').comp Cv.φ) M'.g ⟨⟨k, hk⟩, m⟩).trans (transPt_base Cv ⟨⟨k, hk⟩, m⟩).symm
  · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
    rw [ptOf_step M _ _ p k hp, transPt_step Cv p k hp]
    rfl

theorem isValueAt_pull {L : Type} [Field L] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v)
    {w : (Σ k, ι' k) → L} {z : (Σ k, ι' k) → ℂ} {s : L} {r : ℂ} (h : IsValueAt (w ∘ v) s (z ∘ v) r) :
    IsValueAt w s z r := by
  obtain ⟨d, g, h, hg, hh, h1, h2, h3, rfl⟩ := h
  refine ⟨_, rename v g, rename v h, CPts.isMultiHomog_rename_block hv hg, CPts.isMultiHomog_rename_block hv hh,
    ?_, ?_, ?_, ?_⟩
  · rwa [aeval_rename]
  · rwa [aeval_rename, aeval_rename]
  · rwa [CPts.eval_rename_block]
  · rw [CPts.eval_rename_block, CPts.eval_rename_block]

theorem blockFnField_comp_le {L : Type} [Field L] [CharZero L] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hv : IsBlockMap κ v) (w : (Σ k, ι' k) → L) : blockFnField (w ∘ v) ≤ blockFnField w := by
  refine IntermediateField.adjoin.mono _ _ _ ?_
  rintro t ⟨p, q, h, rfl⟩
  exact ⟨v p, v q, by rw [hv.2.2.1, hv.2.2.1, h], rfl⟩

theorem val_img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {z : (Σ k, ι' k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y')) {w : (Σ k, ι k) → ℂ} (himg : IsImg Cv z w) (k : K) :
    ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
      transPt Cv ⟨k, i⟩ = e * s i ∧ IsValueAt y' (s i) z (t * w ⟨k, i⟩) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨-, g2, -⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨F', hF', hG'⟩ := h2 _ (h1 z hz)
  obtain ⟨z₁, ho₁, hnorm⟩ := FibreCount.exists_normal_base M'.blk F'.c z fun k => FibreCount.chart_ne (hG'.1 k)
  have hz₁ := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y') ho₁ hz
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [FibreCount.mCoordIdeal_eq_of_orbit (FibreCount.basePart_orbit M'.blk ho₁)]; exact hG'
  obtain ⟨h, hh⟩ := (h3 F' hF' z₁ (h1 z₁ hz₁) hG₁ hnorm).1 hz₁
  have hv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (h1 z₁ hz₁)
  obtain ⟨F, hF, hG⟩ := g2 _ hv
  obtain ⟨z₀, ho, hb, hfl⟩ := himg z₁ ho₁ F' F hF' hF hG₁ hG h hh
  obtain ⟨c, hc, ec⟩ := blocks_of_orbit ho k
  have hblk : ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
      transPt Cv ⟨k, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨k, i⟩) := by
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact GlobalTheory.T.flag_cover_base_block_value K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ ⟨k, hk⟩ hz₁ hb
    · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
      exact GlobalTheory.T.flag_cover_frames_lift_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG₁ hG hh hfl hb hp
  obtain ⟨e, s, t, he, ht, hs⟩ := hblk
  refine ⟨e, s, t * c, he, mul_ne_zero ht hc, fun i => ⟨(hs i).1, ?_⟩⟩
  rw [mul_assoc, ← ec]
  exact CovLift.isValueAt_orbit (hs i).2 (orbit_symm ho₁)

theorem ratio_mem {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) [CharZero Φ']
    (h : ∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) (k : K) (m m' : ι k) : transPt Cv ⟨k, m⟩ / transPt Cv ⟨k, m'⟩ ∈ blockFnField y' := by
  rw [GlobalTheory.T.flag_cover_block_field_eq K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv h]
  exact IntermediateField.subset_adjoin _ _ ⟨⟨.inl k, m⟩, ⟨.inl k, m'⟩, rfl, rfl⟩

theorem graph_alt {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {τ : Ψ} {a b : Fin N} {k₀ : K}
    {k₀' : K'} {ca cb : Fin N} {d : ℕ} (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2)) :
    ∃ Pt : Ideal (MRing (Sum.elim (fun o : Option K => ι (o.getD k₀)) fun o : Option K' => ι' (o.getD k₀'))),
      IsArithVar Pt (d + 2 + 1) ∧ imageZ inlV Pt = mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧
      imageZ inrV Pt = mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X) ∧
      ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        ∀ w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), RelW Cv k₀ k₀' z w → pairV w z ∈ mcPts Pt := by
  haveI : CharZero Φ' := charZero_of_injective_algebraMap (algebraMap M'.Ω Φ').injective
  haveI : CharZero (RatFunc Φ') := charZero_of_injective_algebraMap (algebraMap Φ' (RatFunc Φ')).injective
  obtain ⟨G, hG⟩ := exists_genLow M'
  have hG₀ := hG.flag₀
  have hG₁ := hG.flag₁ τ S.hcb (Pts.same_summand S.hb S.hab S.hca S.hcb)
  let ML := reModel M' _ G hG
  let MT := reModel M _ G (hG.restrict Cv.φ)
  have SL : Sw ML τ a b k₀' ca cb := ⟨S.hb, S.hab, S'.hk, S.hca, S.hcb, S.wa⟩
  have ST : Sw MT τ a b k₀ ca cb := ⟨S.hb, S.hab, S.hk, S.hca, S.hcb, S.wa⟩
  have eL := ideal_W_eq S' SL hy' (ideal_ptOf M' _ G hG)
  have eT := ideal_W_eq S ST hy (ideal_ptOf M _ G (hG.restrict Cv.φ))
  let C₀ := reCover Cv _ _ hG₀
  let C₁ := reCover Cv _ _ hG₁
  have e₀ := ideal_ptOf M' _ _ hG₀
  have e₁ := ideal_ptOf M' _ _ hG₁
  set w' := ML.wCo (τ, a) k₀' ca cb RatFunc.X with hw'
  set wT := MT.wCo (τ, a) k₀ ca cb RatFunc.X with hwT
  have l₀ : w' ∘ v₀ k₀' = ptOf M' ((algebraMap Φ' (RatFunc Φ')).comp (algebraMap M'.Ω Φ')) (flag₀ G) :=
    wCo_v₀ ML _ _ _ _
  have l₁ : w' ∘ v₁ k₀' = ptOf M' ((algebraMap Φ' (RatFunc Φ')).comp (algebraMap M'.Ω Φ')) (flag₁ G τ ca cb) :=
    SL.wCo_v₁
  have t₀ : wT ∘ v₀ k₀ = transPt C₀ := (wCo_v₀ MT (τ, a) k₀ ca cb).trans (transPt_eq C₀)
  have t₁ : wT ∘ v₁ k₀ = transPt C₁ := ST.wCo_v₁.trans (transPt_eq C₁)
  have t₀' : ∀ k m, wT ⟨some k, m⟩ = transPt C₀ ⟨k, m⟩ := fun k m => congrFun t₀ ⟨k, m⟩
  have t₁' : ∀ m, wT ⟨none, m⟩ = transPt C₁ ⟨k₀, m⟩ := fun m => by
    rw [← t₁, Function.comp, v₁_self]
  have aL : IsArithVar (mCoordIdeal w') (d + 2 + 1) := by rw [eL]; exact S'.arith hy'
  have aT : IsArithVar (mCoordIdeal wT) (d + 2 + 1) := by rw [eT]; exact S.arith hy
  have nz := fun {Kx : Type} [Fintype Kx] {ιx : Kx → Type} [∀ k, Fintype (ιx k)] (u : (Σ k, ιx k) → RatFunc Φ')
      (h : IsRelevant (mCoordIdeal u)) (k : Kx) => (show ∃ i, u ⟨k, i⟩ ≠ 0 from by
    obtain ⟨c, hc⟩ := HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant u h
    exact ⟨c k, hc k⟩)
  have hnz : ∀ kk, ∃ i, pairV wT w' ⟨kk, i⟩ ≠ 0 := by
    rintro (k | k)
    · exact nz wT aT.2.1.2.2 k
    · exact nz w' aL.2.1.2.2 k
  have r₁ : ∀ m m' : ι k₀, wT ⟨none, m⟩ / wT ⟨none, m'⟩ ∈ blockFnField w' := fun m m' => by
    rw [t₁', t₁']
    refine blockFnField_comp_le (isBlockMap_v₁ k₀') w' ?_
    rw [l₁]
    exact ratio_mem C₁ (nz _ (by rw [e₁]; exact hy'.2.1.2.2)) k₀ m m'
  have r₀ : ∀ k (m m' : ι k), wT ⟨some k, m⟩ / wT ⟨some k, m'⟩ ∈ blockFnField w' := fun k m m' => by
    rw [t₀', t₀']
    refine blockFnField_comp_le (Pts.isBlockMap_v₀ k₀') w' ?_
    rw [l₀]
    exact ratio_mem C₀ (nz _ (by rw [e₀]; exact hy'.2.1.2.2)) k m m'
  refine ⟨mCoordIdeal (pairV wT w'), ?_, by rw [imageZ_inl, eT], by rw [imageZ_inr, eL], fun z hz w hw hr => ?_⟩
  · refine HilbertSamuel.CoordArithOfFnField.proof _ _ _ _ (RatFunc Φ') w' (pairV wT w') _ ⟨Sum.inr none⟩ hnz
      (le_antisymm (blockFnField_comp_le isBlockMap_inr (pairV wT w')) ?_) aL
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨⟨k, m⟩, ⟨k', m'⟩, h, rfl⟩
    obtain rfl : k = k' := h
    rcases k with (_ | k) | k
    · exact r₁ m m'
    · exact r₀ k m m'
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨k, m⟩, ⟨k, m'⟩, rfl, rfl⟩
  · have hzL : z ∈ mcPts (mCoordIdeal w') := by rw [eL]; exact hz
    have hblk : ∀ kk, ∃ (e : RatFunc Φ') (s : Sum.elim (fun o : Option K => ι (o.getD k₀))
        (fun o : Option K' => ι' (o.getD k₀')) kk → RatFunc Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
        pairV wT w' ⟨kk, i⟩ = e * s i ∧ IsValueAt w' (s i) z (t * pairV w z ⟨kk, i⟩) := by
      rintro ((_ | k) | k)
      · obtain ⟨e, s, t, he, ht, hs⟩ := val_img C₁ (z := sndPt k₀' z) (by rw [e₁]; exact S'.snd_mem hy' hz) hr.2 k₀
        refine ⟨e, s, t, he, ht, fun i => ⟨(t₁' i).trans (hs i).1, isValueAt_pull (isBlockMap_v₁ k₀') ?_⟩⟩
        have := (hs i).2
        rw [← l₁] at this
        exact (congrArg (fun r => IsValueAt (w' ∘ v₁ k₀') (s i) (z ∘ v₁ k₀') (t * r)) (Pts.snd_self w i)).mp this
      · obtain ⟨e, s, t, he, ht, hs⟩ := val_img C₀ (z := fstPt k₀' z) (by rw [e₀]; exact fst_mem hz) hr.1 k
        refine ⟨e, s, t, he, ht, fun i => ⟨(t₀' k i).trans (hs i).1, isValueAt_pull (Pts.isBlockMap_v₀ k₀') ?_⟩⟩
        have := (hs i).2
        rw [← l₀] at this
        exact this
      · obtain ⟨c, hc⟩ := hz.1 k
        obtain ⟨hy0, hval⟩ := GlobalTheory.T.coordinate_ratio_value_at_point _ _ _ w' z k c hzL hc
        exact ⟨w' ⟨k, c⟩, fun i => w' ⟨k, i⟩ / w' ⟨k, c⟩, (z ⟨k, c⟩)⁻¹, hy0, inv_ne_zero hc,
          fun i => ⟨(mul_div_cancel₀ _ hy0).symm, hval i⟩⟩
    choose e s t he ht hs using hblk
    refine GlobalTheory.T.scaled_coordinates_value_at_point _ _ _ _ _ (pairV wT w') w' z (pairV w z) e (fun q => s q.1 q.2) t hzL ?_ he ht
      (fun q => (hs q.1 q.2).1) (fun q => (hs q.1 q.2).2)
    rintro (k | k)
    · exact hw.1 k
    · exact hz.1 k

end PositivityTheory.Xgp.c_sqsys
