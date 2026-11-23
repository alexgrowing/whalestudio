import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDim
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsC2AtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree

noncomputable section

namespace RootFieldNumerics.Sq

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp SheetDecomposition
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [CharZero Ω] [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have h : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (mConeMap y) = aeval y :=
    algHom_ext fun p => by simp [mConeMap]
  rw [← h, AlgHom.comp_apply, show mConeMap y f = 0 from hf, map_zero]

theorem valEq_of_lineIso {y : (Σ k, ι k) → Ω} (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {a b : K → ℤ} {f g : MRing ι}
    (h : IsLineIso (mCoordIdeal y) a b f g) : ValEq ℚ y a y b := by
  classical
  obtain ⟨⟨α, γ, hf, hg, hd⟩, hfP, hgP, hU⟩ := h
  have hne : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d → s ∉ mCoordIdeal y → aeval y s ≠ 0 := fun hs hP h0 =>
    hP (by rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hs, h0, map_zero, zero_mul])
  refine ⟨aeval y f / aeval y g, div_ne_zero (hne hf hfP) (hne hg hgP), fun O _ => ?_⟩
  have hex : ∀ k, ∃ c : ι k, ∀ i, O.valuation (y ⟨k, i⟩) ≤ O.valuation (y ⟨k, c⟩) := fun k => by
    obtain ⟨i, -⟩ := hy k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => O.valuation (y ⟨k, i⟩)) ⟨i, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hex
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hy k
    have := hc k i
    rw [h0, map_zero] at this
    exact hi ((Valuation.zero_iff _).1 (le_antisymm this zero_le))
  have hO : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ O := fun k i => by
    rw [← O.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (hc0 k)))]
    exact hc k i
  let w : (Σ k, ι k) → O := fun p => ⟨ratioPt y c p, hO p.1 p.2⟩
  let φ : MRing ι →+* O := eval₂Hom (Int.castRingHom O) w
  have hφ : ∀ s, (φ s : Ω) = aeval (ratioPt y c) s := fun s => by
    have : O.subtype.comp φ = (aeval (ratioPt y c) : MRing ι →ₐ[ℤ] Ω) :=
      ringHom_ext (fun r => by simp) fun p => by simp [φ, w]
    exact DFunLike.congr_fun this s
  have hP : ∀ s ∈ mCoordIdeal y, φ s = 0 := fun s hs => Subtype.ext <| by
    rw [hφ]
    exact aeval_eq_zero_of_mem (mCoordIdeal_ratioPt y c hc0 ▸ hs)
  obtain ⟨u, v, hu, hv, huv⟩ := hU ((IsLocalRing.maximalIdeal O).comap φ) (Ideal.comap_isPrime _ _)
    (fun s hs => by rw [Ideal.mem_comap, hP s hs]; exact zero_mem _) fun k => ⟨c k, fun h => by
      have e : φ (X ⟨k, c k⟩) = 1 := Subtype.ext (by rw [hφ]; simp [ratioPt, hc0])
      rw [Ideal.mem_comap, e] at h
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h)⟩
  have h1 : ∀ s, s ∉ (IsLocalRing.maximalIdeal O).comap φ → O.valuation (φ s) = 1 := fun s hs =>
    (O.valuation_eq_one_iff _).1 (IsLocalRing.notMem_maximalIdeal.1 hs)
  have h2 : O.valuation (aeval (ratioPt y c) f) = O.valuation (aeval (ratioPt y c) g) := by
    have e := congrArg (fun t : O => (t : Ω)) (hP _ huv)
    simp only [map_sub, map_mul] at e
    push_cast at e
    have e' := congrArg O.valuation (sub_eq_zero.1 e)
    rwa [map_mul, map_mul, h1 u hu, h1 v hv, one_mul, one_mul, hφ, hφ] at e'
  have h3 : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d →
      aeval y s = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (ratioPt y c) s := fun hs => by
    rw [← HilbertSamuel.LiftBirationalNef.aeval_scale (fun k => y ⟨k, c k⟩) hs]
    congr 2
    funext p
    rw [ratioPt, mul_div_cancel₀ _ (hc0 _)]
  have h4 : O.valuation (aeval (ratioPt y c) g) ≠ 0 := by
    rw [map_ne_zero]
    exact right_ne_zero_of_mul (h3 hg ▸ hne hg hgP)
  rw [UnitZ.vdeg_chart O y c hc0 hO, UnitZ.vdeg_chart O y c hc0 hO, h3 hf, h3 hg, map_div₀, map_mul, map_mul, h2,
    mul_div_mul_right _ _ h4, ← map_div₀, ← map_mul, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hc0 k), ← zpow_add₀ (hc0 k), hd, sub_add_cancel]

variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]

theorem exists_ratio (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (φ : L →+* Ω) (z : (Σ k, ι k) → L), (∀ p, φ (z p) = y p / y ⟨p.1, c p.1⟩) ∧
      (∀ t, t ∈ blockFnField y ↔ ∃ x, φ x = t) ∧ Birational z ∧ mCoordIdeal z = mCoordIdeal y := by
  refine ⟨ratioField y c, inferInstance, inferInstance, algebraMap (ratioField y c) Ω, ratioPtL y c, fun _ => rfl, fun t => ?_,
    birational y c hc, mCoordIdeal_ratioPtL y c hc⟩
  rw [← ratioField_eq_blockFnField y c hc]
  exact ⟨fun h => ⟨⟨t, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩

variable {L : Type} [Field L] [CharZero L]

theorem finrank_ratio {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {φ : L →+* Ω} {z : (Σ k, ι k) → L}
    (hφ : ∀ p, φ (z p) = y p / y ⟨p.1, c p.1⟩) (hr : ∀ t, t ∈ blockFnField y ↔ ∃ x, φ x = t) {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → Σ k, ι k} (hv : IsBlockMap κ v) :
    Module.finrank (fnField ℚ (z ∘ v)) L = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) := by
  have h1 : (fnField ℚ (z ∘ v)).map φ.toRatAlgHom = blockFnField (y ∘ v) := by
    rw [fnField, IntermediateField.adjoin_map, blockFnField]
    congr 1
    have e : ∀ p q : Σ k, ι₁ k, p.1 = q.1 → φ.toRatAlgHom ((z ∘ v) p / (z ∘ v) q) = (y ∘ v) p / (y ∘ v) q := fun p q h => by
      have h' : (⟨(v p).1, c (v p).1⟩ : Σ k, ι k) = ⟨(v q).1, c (v q).1⟩ :=
        congrArg (fun k => (⟨k, c k⟩ : Σ k, ι k)) ((hv.2.2.1 p).trans ((congrArg κ h).trans (hv.2.2.1 q).symm))
      show φ (z (v p) / z (v q)) = y (v p) / y (v q)
      rw [map_div₀, hφ, hφ, h', div_div_div_cancel_right₀ (hc _)]
    ext t
    constructor
    · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
      exact ⟨p, q, h, e p q h⟩
    · rintro ⟨p, q, h, rfl⟩
      exact ⟨_, ⟨p, q, h, rfl⟩, e p q h⟩
  have h2 : (⊤ : IntermediateField ℚ L).map φ.toRatAlgHom = blockFnField y := by
    ext t
    rw [hr, IntermediateField.mem_map]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩
  rw [← h1, ← h2, IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right]

open Classical in
theorem num_pull (hP : NumPull) {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hI : mCoordIdeal z = mCoordIdeal y) {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → Σ k, ι k} (hv : IsBlockMap κ v) {d : ℕ} (hz : IsPt ℚ z d) {e : ℕ}
    (hf : Module.finrank (fnField ℚ (z ∘ v)) L = e) (he : e ≠ 0) (a : Fin d → K₁ → ℤ) :
    num ℚ z (fun j => pullDeg κ (a j)) =
      (e : ℤ) * NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v)).map (MvPolynomial.map (Int.castRingHom ℚ))) a := by
  have hzv : IsPt ℚ (z ∘ v) d := by
    refine ⟨fun b => ?_, Module.finite_of_finrank_pos (by rw [hf]; exact Nat.pos_of_ne_zero he), hz.2.2⟩
    obtain ⟨i, hi⟩ := hz.1 (κ b)
    obtain ⟨⟨b', j⟩, hp⟩ := hv.2.2.2 ⟨κ b, i⟩ ⟨b, rfl⟩
    obtain rfl : b' = b := hv.1 ((hv.2.2.1 ⟨b', j⟩).symm.trans (congrArg Sigma.fst hp))
    exact ⟨j, by rwa [Function.comp_apply, hp]⟩
  have hI' : mCoordIdeal (z ∘ v) = mCoordIdeal (y ∘ v) := by
    rw [← JoinBlock.imageZ_coord κ v _ hv.1 hv.2.2.1, ← JoinBlock.imageZ_coord κ v _ hv.1 hv.2.2.1, hI]
  rw [hP ℚ _ _ _ _ _ κ v _ d a hv hz hzv, num, hf, inum, pointIdeal_rat, hI']

theorem isPt_of_birational {z : (Σ k, ι k) → L} (hb : Birational z) {d : ℕ} (hz : IsArithVar (mCoordIdeal z) (d + 1)) :
    IsPt ℚ z d := by
  have h0 : 0 < Module.finrank (RingHom.id L).fieldRange L := by
    rw [show (RingHom.id L).fieldRange = ⊤ from RingHom.fieldRange_eq_top_iff.2 Function.surjective_id]
    have : Module.Finite (⊤ : Subfield L) L :=
      Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield L) L) fun x => ⟨⟨x, trivial⟩, rfl⟩
    exact Module.finrank_pos
  exact (numMap L L (RingHom.id L) K ι z d hb hz h0).1

open Classical in

theorem intNum_cmp (hP : NumPull) {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] (y : (Σ k, ι k) → Ω)
    {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K} {v₂ : (Σ k, ι₂ k) → Σ k, ι k} (h₁ : IsBlockMap κ₁ v₁)
    (h₂ : IsBlockMap κ₂ v₂) {d : ℕ} (hy : IsArithVar (mCoordIdeal y) (d + 1))
    (e₁ : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0)
    (e₂ : IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) ≠ 0) (a₁ : Fin d → K₁ → ℤ) (a₂ : Fin d → K₂ → ℤ)
    (h : ∀ j, ∃ f g, IsLineIso (mCoordIdeal y) (pullDeg κ₁ (a₁ j)) (pullDeg κ₂ (a₂ j)) f g) :
    (IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) : ℤ) *
        NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v₁)).map (MvPolynomial.map (Int.castRingHom ℚ))) a₁ =
      (IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) : ℤ) *
        NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v₂)).map (MvPolynomial.map (Int.castRingHom ℚ))) a₂ := by
  choose c hc using ne_of_arith hy
  obtain ⟨L, _, _, φ, z, hφ, hr, hb, hI⟩ := exists_ratio y c hc
  rw [← hI] at hy h
  have hz : IsPt ℚ z d := isPt_of_birational hb hy
  refine (num_pull hP hI h₁ hz (finrank_ratio hc hφ hr h₁) e₁ a₁).symm.trans
    (Eq.trans ?_ (num_pull hP hI h₂ hz (finrank_ratio hc hφ hr h₂) e₂ a₂))
  refine numEq ptDim hP (unitZero ptDim) ℚ L K ι K ι z z d _ _ hz hz fun j => ?_
  obtain ⟨f, g, hfg⟩ := h j
  exact valEq_of_lineIso hz.1 hfg

open Classical in

theorem degNum_eq (hI : PB.Inputs) {d : ℕ} {σ : Type} {S : PB.AnSys d σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P)
    (w : Fin d → σ) :
    (Re.deg : ℝ) * S.degNum w =
      (NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => (Re.ref (w j)).a : ℤ) := by
  rw [← mInt_ref_eq Re w, ← ptsIntegral_one_eq_mInt hI.resExists resBridge Re.R Re.arith fun j => Re.ref_smooth _]
  exact Giv.degreeGeneric_of_degree hI.degree K ι P d _ Re.arith fun j => Re.ref_smooth _

end RootFieldNumerics.Sq
