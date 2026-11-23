import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl
open scoped Topology

namespace GlobalTheory.CompanionTheory.ThetaInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ball (n : ℕ) (s : kˣ) :
    IsOpen {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} :=
  (isOpen_polyBall n s).preimage continuous_ofAdd

theorem isCompact_ball (n : ℕ) (s : kˣ) :
    IsCompact {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} := by
  have e : {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} =
      Multiplicative.toAdd '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))) := by
    ext a
    constructor
    · intro h
      exact ⟨Multiplicative.ofAdd a, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [e]
  exact (isCompact_polyBall n s).image continuous_toAdd

theorem isLocallyConstant_of_periodic {n : ℕ} {Y : Type} (g : (Fin n → k) → Y) (s : kˣ)
    (h : ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → g (v + a) = g v) :
    IsLocallyConstant g := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have h0 : (fun z : Fin n → k => -x + z) ⁻¹'
      {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} ∈ 𝓝 x :=
    ((isOpen_ball n s).preimage (by fun_prop)).mem_nhds (by
      show Multiplicative.ofAdd (-x + x) ∈ polyBall (k := k) n s
      rw [neg_add_cancel]
      exact one_mem _)
  filter_upwards [h0] with z hz
  have e : z = x + (-x + z) := by abel
  rw [e]
  exact h x _ hz

theorem hasCompactSupport_of_ball {n : ℕ} {E : Type} [AddCommGroup E] (g : (Fin n → k) → E) (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) : HasCompactSupport g := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine HasCompactSupport.intro (isCompact_ball n S) fun x hx => ?_
  by_contra h1
  exact hx (h x h1)

def tw (ψ : AddChar k Circle) {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]
    (g : (Fin (N + 1) → k) → E) : (Fin (N + 1) → k) → E :=
  fun v => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) • g v

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem isLocallyConstant_tw (ψ : AddChar k Circle) (hψ : Continuous ψ)
    {g : (Fin (N + 1) → k) → E} (hg : IsLocallyConstant g) : IsLocallyConstant (tw ψ g) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have h1 : IsLocallyConstant fun v : Fin (N + 1) → k => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) := by
    refine isLocallyConstant_of_periodic _ s fun v a ha => ?_
    have h2 : ψ (a (Fin.last N)) = 1 := hs _ (ha (Fin.last N))
    rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv (a := a (Fin.last N)), h2,
      inv_one, mul_one]
  exact h1.comp₂ hg fun c x => c • x

theorem hasCompactSupport_tw (ψ : AddChar k Circle) {g : (Fin (N + 1) → k) → E} (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) :
    HasCompactSupport (tw ψ g) := by
  refine hasCompactSupport_of_ball _ S fun v hv => h v fun h0 => hv ?_
  simp [tw, h0]

section Int

variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem smInt_comp_inv_mulVec (g : GL (Fin (N + 1)) k) {φ : (Fin (N + 1) → k) → E}
    (l : IsLocallyConstant φ) :
    smInt (Measure.pi fun _ : Fin (N + 1) => ν) (φ ∘ ((g⁻¹ : GL (Fin (N + 1)) k) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) •
        smInt (Measure.pi fun _ : Fin (N + 1) => ν) φ := by
  have hm : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) k, Measurable B.mulVec := fun B =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have key : ∀ B : Set (Fin (N + 1) → k), MeasurableSet B →
      (Measure.pi fun _ : Fin (N + 1) => ν)
          (((g⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec ⁻¹' B) =
        (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ENNReal) *
          (Measure.pi fun _ : Fin (N + 1) => ν) B := by
    intro B hB
    have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl
    conv_lhs => rw [← h1]
    rw [Measure.smul_apply, Measure.map_apply (hm _) ((hm _) hB), smul_eq_mul]
    congr 2
    ext x
    simp only [Set.mem_preimage, mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  rw [Set.preimage_comp, key (φ ⁻¹' {v}) (l.isOpen_fiber v).measurableSet, ENNReal.toReal_mul, smul_smul]
  congr 1
  simp [nabs]

end Int

theorem exists_twisted_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  intro k _ _ _ _ ψ hψ N X E _ _ _ _ r hper hsup tr htr lev A hlev
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ : ∃ ν : Measure k, ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let μ : Measure (Fin (N + 1) → k) := Measure.pi fun _ => ν
  haveI hμ : μ.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hl : ∀ f, IsLocallyConstant (tw ψ (r f)) := fun f => by
    obtain ⟨s, hs⟩ := hper f
    exact isLocallyConstant_tw ψ hψ (isLocallyConstant_of_periodic _ s fun v a ha => hs v a ha)
  have hc : ∀ f, HasCompactSupport (tw ψ (r f)) := fun f => by
    obtain ⟨S, hS⟩ := hsup f
    exact hasCompactSupport_tw ψ S hS
  let T : X →ₗ[ℂ] E :=
    { toFun := fun f => smInt μ (tw ψ (r f))
      map_add' := fun f g => by
        have e : tw ψ (r (f + g)) = tw ψ (r f) + tw ψ (r g) := by
          funext v
          simp [tw, map_add, smul_add]
        show smInt μ (tw ψ (r (f + g))) = smInt μ (tw ψ (r f)) + smInt μ (tw ψ (r g))
        rw [e, smInt_add μ (hl f) (hc f) (hl g) (hc g)]
      map_smul' := fun c f => by
        have e : tw ψ (r (c • f)) = (c • LinearMap.id : E →ₗ[ℂ] E) ∘ tw ψ (r f) := by
          funext v
          simp only [tw, Function.comp, map_smul, Pi.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
        show smInt μ (tw ψ (r (c • f))) = c • smInt μ (tw ψ (r f))
        rw [e, smInt_linear μ _ (hl f) (hc f)]
        rfl }
  have hT : ∀ f, T f = smInt μ (tw ψ (r f)) := fun _ => rfl
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a f
    let L : E →ₗ[ℂ] E := ((ψ (a (Fin.last N)) : Circle) : ℂ) • LinearMap.id
    have e : tw ψ (r (tr a f)) = (L ∘ tw ψ (r f)) ∘ fun v => v + a := by
      funext v
      simp only [tw, Function.comp, htr, L, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [Pi.add_apply]
      abel
    rw [hT, hT, e, smInt_comp_measurePreserving μ (measurePreserving_add_right μ a) ((hl f).comp _),
      smInt_linear μ L (hl f) (hc f)]
    rfl
  · intro m hm f
    have e : tw ψ (r (lev m f)) = (A m ∘ tw ψ (r f)) ∘
        ((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec := by
      funext v
      simp only [tw, Function.comp, hlev, map_smul]
      rw [mulVec_last_of_mem k _ (inv_mem hm) v]
    rw [hT, hT, e]
    refine (smInt_comp_inv_mulVec ν m ((hl f).comp _)).trans ?_
    congr 1
    exact smInt_linear μ (A m) (hl f) (hc f)
  · intro s hs
    have hLo := isOpen_ball (k := k) (N + 1) s
    have hLc := isCompact_ball (k := k) (N + 1) s
    refine ⟨(((μ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s}).toReal : ℝ) : ℂ), ?_, fun b e hb => ?_⟩
    · have h0 := (hLo.measure_pos μ ⟨0, one_mem (polyBall (k := k) (N + 1) s)⟩).ne'
      exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, hLc.measure_lt_top.ne⟩)
    · have e' : tw ψ (r b) = Set.indicator {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} fun _ => e := by
        funext v
        by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s
        · have h1 : ψ (v (Fin.last N)) = 1 := hs v hv
          simp only [tw]
          rw [hb v, if_pos hv, Set.indicator_of_mem (show v ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            AddChar.map_neg_eq_inv, h1]
          simp
        · simp only [tw]
          rw [hb v, if_neg hv, Set.indicator_of_notMem (show v ∉ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            smul_zero]
      rw [hT, e', smInt_indicator]

end GlobalTheory.CompanionTheory.ThetaInt
