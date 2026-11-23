import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecondUnitaryBlockOfPair
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RepKerP

noncomputable section

open MeasureTheory Matrix Set Topology

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem cpt_unitary (n : ℕ) : IsCompact (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hsub : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
      Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : ℂ) 1)) := by
    intro U hU i _ j _
    simpa using entry_norm_bound_of_unitary hU i j
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ hsub
  have hset : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
      {A | star A * A = 1 ∧ A * star A = 1} := by
    ext A
    exact Iff.rfl
  rw [hset]
  have h1 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => star A * A := by fun_prop
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * star A := by fun_prop
  exact (isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const)

instance cptU (n : ℕ) : CompactSpace (unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (cpt_unitary n)

variable {n : ℕ}

def kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : GR n := Classical.choose ((hK n).1 a.1 b.1 a.2 b.2)

theorem kE_mem (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : kE hK a b ∈ KR n :=
  (Classical.choose_spec ((hK n).1 a.1 b.1 a.2 b.2)).1

theorem mR_kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : mR (kE hK a b) = kM a.1 b.1 :=
  (Classical.choose_spec ((hK n).1 a.1 b.1 a.2 b.2)).2

theorem mR_inj {g h : GR n} (e : mR g = mR h) : g = h := Subtype.ext (Units.ext e)

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem kE_mul (hK : KIso) (a b a' b' : unitaryGroup (Fin n) ℂ) :
    kE hK a b * kE hK a' b' = kE hK (a * a') (b * b') := by
  apply mR_inj
  rw [mR_mul, mR_kE, mR_kE, mR_kE, (hK n).2.1]
  rfl

theorem mR_inv_kE (hK : KIso) (a b : unitaryGroup (Fin n) ℂ) : mR (kE hK a b)⁻¹ = kM (a⁻¹ : unitaryGroup (Fin n) ℂ).1 (b⁻¹ : unitaryGroup (Fin n) ℂ).1 := by
  have h1 : kE hK a b * kE hK a⁻¹ b⁻¹ = 1 := by
    rw [kE_mul, mul_inv_cancel, mul_inv_cancel]
    apply mR_inj
    rw [mR_kE]
    exact (hK n).2.2.1
  have h2 : (kE hK a b)⁻¹ = kE hK a⁻¹ b⁻¹ := (eq_inv_of_mul_eq_one_right h1).symm
  rw [h2, mR_kE]

theorem continuous_mR : Continuous (fun g : GR n => mR g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_kM : Continuous (fun ab : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => kM ab.1 ab.2) := by
  unfold kM
  refine Continuous.matrix_fromBlocks ?_ ?_ ?_ ?_ <;> fun_prop

theorem continuous_kE (hK : KIso) (a : unitaryGroup (Fin n) ℂ) : Continuous (fun b : unitaryGroup (Fin n) ℂ => kE hK a b) := by
  refine continuous_induced_rng.2 ((Units.continuous_iff).2 ⟨?_, ?_⟩)
  · exact (continuous_kM.comp (continuous_const.prodMk continuous_subtype_val)).congr
      fun b => (mR_kE hK a b).symm
  · exact (continuous_kM.comp (continuous_const.prodMk
      (continuous_subtype_val.comp continuous_inv))).congr fun b => (mR_inv_kE hK a b).symm

theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  have h21 : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))
  have h22 : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))
  unfold u2
  exact ((h21.const_smul Complex.I).neg).add h22

theorem lower_left_block_mul {X Y : M2 n} (hX : X.toBlocks₂₁ = 0) (hY : Y.toBlocks₂₁ = 0) : (X * Y).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks X, ← fromBlocks_toBlocks Y, fromBlocks_multiply, toBlocks_fromBlocks₂₁, hX, hY]
  simp

theorem projOp_of (hK : KIso) (hR : RepKer) (hI : Iwa) (hM : Mult) : ProjOp := by
  intro m n ε c t p q e sL ρ hL _ _ W hW hWinv
  letI : MeasurableSpace (unitaryGroup (Fin n) ℂ) := borel _
  haveI : BorelSpace (unitaryGroup (Fin n) ℂ) := ⟨rfl⟩
  let μ : Measure (unitaryGroup (Fin n) ℂ) := Measure.haar
  let L : PX m n →ₗ[ℂ] (unitaryGroup (Fin n) ℂ → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun c : unitaryGroup (Fin n) ℂ => kE hK 1 c) ∘ₗ sL
  have hLapp : ∀ (P : PX m n) (c : unitaryGroup (Fin n) ℂ), L P c = sL P (kE hK 1 c) :=
    fun _ _ => rfl
  have hVfin : FiniteDimensional ℂ (W.map L) := inferInstance
  have hupK : ∀ a : unitaryGroup (Fin n) ℂ, toBlocks₂₁ (mR (kE hK a a)) = 0 := by
    intro a
    rw [mR_kE]
    exact (hK n).2.2.2.2.1 a.1
  have hVcont : ∀ φ ∈ W.map L, Continuous φ := by
    rintro φ ⟨P, -, rfl⟩
    show Continuous fun c => sL P (kE hK 1 c)
    exact (hL.cont P).comp (continuous_kE hK 1)
  have hVinv : ∀ φ ∈ W.map L, ∀ a : unitaryGroup (Fin n) ℂ,
      (fun x : unitaryGroup (Fin n) ℂ => φ (a * x)) ∈ W.map L := by
    rintro φ ⟨P, hP, rfl⟩ a
    refine ⟨F0 p q e (kE hK a a) • ρ (kE hK a⁻¹ 1) P,
      W.smul_mem _ (hWinv _ (kE_mem hK a⁻¹ 1) P hP), ?_⟩
    funext x
    have hx : kE hK 1 (a * x) = kE hK a a * (kE hK 1 x * kE hK a⁻¹ 1) := by
      rw [kE_mul, kE_mul]
      simp
    show sL (F0 p q e (kE hK a a) • ρ (kE hK a⁻¹ 1) P) (kE hK 1 x) = sL P (kE hK 1 (a * x))
    rw [hx, hL.law _ _ _ (hupK a), hL.kact _ _ _ (kE_mem hK a⁻¹ 1), map_smul,
      Pi.smul_apply, smul_eq_mul]
  obtain ⟨κ0, hκ0c, hκ0img, hκ0fix⟩ := hR (unitaryGroup (Fin n) ℂ) μ (W.map L) hVfin hVcont hVinv
  have hu2mem : ∀ k : KR n, u2 (mR (k : GR n)) ∈ unitaryGroup (Fin n) ℂ :=
    fun k => ((hK n).2.2.2.2.2 (k : GR n) k.2).2.1
  let κ : KR n → ℂ := fun k => κ0 ⟨u2 (mR (k : GR n)), hu2mem k⟩
  let eK : unitaryGroup (Fin n) ℂ → KR n := fun v => ⟨kE hK 1 v, kE_mem hK 1 v⟩
  have heK : Continuous eK := (continuous_kE hK 1).subtype_mk _
  have hκe : ∀ v, κ (eK v) = κ0 v := by
    intro v
    show κ0 _ = κ0 v
    congr 1
    apply Subtype.ext
    show u2 (mR (kE hK 1 v)) = v.1
    rw [mR_kE]
    exact ((hK n).2.2.2.1 1 v.1).2
  have hκc : Continuous κ :=
    hκ0c.comp ((continuous_second_cayley_block_map.comp (continuous_mR.comp continuous_subtype_val)).subtype_mk _)
  have hint : ∀ g : KR n → ℂ, Continuous g →
      ∫ k, κ k * g k ∂(μ.map eK) = ∫ v, κ0 v * g (eK v) ∂μ := by
    intro g hg
    have hm : Continuous fun k => κ k * g k := hκc.mul hg
    rw [integral_map (f := fun k => κ k * g k) heK.measurable.aemeasurable hm.aestronglyMeasurable]
    simp only [hκe]
  have hdec : ∀ y : GR n, ∃ (p' : GR n) (c : unitaryGroup (Fin n) ℂ),
      toBlocks₂₁ (mR p') = 0 ∧ y = p' * kE hK 1 c := by
    intro y
    obtain ⟨p0, k0, hp0, hk0, rfl⟩ := hI n y
    obtain ⟨ha, hb, hk⟩ := (hK n).2.2.2.2.2 k0 hk0
    have hk0e : k0 = kE hK ⟨_, ha⟩ ⟨_, hb⟩ := mR_inj (by rw [mR_kE]; exact hk)
    refine ⟨p0 * kE hK ⟨_, ha⟩ ⟨_, ha⟩, (⟨_, ha⟩ : unitaryGroup (Fin n) ℂ)⁻¹ * ⟨_, hb⟩, ?_, ?_⟩
    · rw [mR_mul]
      exact lower_left_block_mul hp0 (hupK _)
    · rw [mul_assoc, kE_mul]
      simp only [mul_one, mul_inv_cancel_left]
      exact congrArg (p0 * ·) hk0e
  refine ⟨μ.map eK, κ, inferInstance, hκc, ?_, ?_⟩
  · intro Q hQ y
    obtain ⟨p', c, hp', rfl⟩ := hdec y
    rw [hint (fun k : KR n => sL Q (p' * kE hK 1 c * (k : GR n)))
      ((hL.cont Q).comp (continuous_const.mul continuous_subtype_val))]
    have h1 : ∀ v, κ0 v * sL Q (p' * kE hK 1 c * ((eK v : KR n) : GR n)) =
        F0 p q e p' * (κ0 v * L Q (c * v)) := by
      intro v
      show κ0 v * sL Q (p' * kE hK 1 c * kE hK 1 v) = F0 p q e p' * (κ0 v * sL Q (kE hK 1 (c * v)))
      rw [mul_assoc, kE_mul, one_mul, hL.law _ _ _ hp']
      ring
    simp only [h1]
    rw [integral_const_mul, hκ0fix (L Q) ⟨Q, hQ, rfl⟩ c, hL.law _ _ _ hp', hLapp]
  · intro w f hf hfeq
    obtain ⟨Q, hQ, hQeq⟩ := hκ0img (fun c => f (kE hK 1 c)) (hf.comp (continuous_kE hK 1))
    refine ⟨Q, hQ, fun y => ?_⟩
    obtain ⟨p', c, hp', rfl⟩ := hdec y
    rw [hint (fun k : KR n => f (p' * kE hK 1 c * (k : GR n)))
      (hf.comp (continuous_const.mul continuous_subtype_val))]
    have h2 : ∀ v, κ0 v * f (p' * kE hK 1 c * ((eK v : KR n) : GR n)) =
        ((hLoc p' : ℂ) ^ w * F0 p q e p') * (κ0 v * f (kE hK 1 (c * v))) := by
      intro v
      show κ0 v * f (p' * kE hK 1 c * kE hK 1 v) = _
      rw [mul_assoc, kE_mul, one_mul, hfeq _ _ hp']
      ring
    simp only [h2]
    have hc := congrFun hQeq c
    rw [integral_const_mul, ← hc, hLapp, hL.law _ _ _ hp',
      ((hM n p q e).1 p' (kE hK 1 c) (kE_mem hK 1 c)).2]
    ring

theorem projOp (hI : Iwa) (hM : Mult) : ProjOp := projOp_of kIso repKer hI hM

end PositivityTheory.Rg.Sw.AbsSt.Proj
