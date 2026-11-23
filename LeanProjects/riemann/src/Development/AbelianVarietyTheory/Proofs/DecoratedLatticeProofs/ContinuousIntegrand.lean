import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.EvalCont

def Tame {B Z : Type} [TopologicalSpace B] [TopologicalSpace Z] (F : B → Z → ℂ) : Prop :=
  Continuous (fun p : B × Z => F p.1 p.2) ∧ ∀ b₀, ∃ C : ℝ, ∀ᶠ b in nhds b₀, ∀ z, ‖F b z‖ ≤ C

section General

variable {B Z Z' Y : Type} [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace Z'] [TopologicalSpace Y]

theorem Tame.comp {F : B → Z → ℂ} (h : Tame F) {u : Z' → Z} (hu : Continuous u) : Tame fun b z => F b (u z) :=
  ⟨h.1.comp (continuous_fst.prodMk (hu.comp continuous_snd)), fun b₀ =>
    (h.2 b₀).imp fun _ hC => hC.mono fun _ hb z => hb (u z)⟩

theorem Tame.mul {F G : B → Z → ℂ} (h : Tame F) (h' : Tame G) : Tame fun b z => F b z * G b z := by
  refine ⟨h.1.mul h'.1, fun b₀ => ?_⟩
  obtain ⟨C, hC⟩ := h.2 b₀
  obtain ⟨C', hC'⟩ := h'.2 b₀
  refine ⟨C * C', (hC.and hC').mono fun b hb z => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hb.1 z) (hb.2 z) (norm_nonneg _) ((norm_nonneg _).trans (hb.1 z))

theorem tame_of_bounded {F : B → Z → ℂ} (hc : Continuous fun p : B × Z => F p.1 p.2) {C : ℝ} (hb : ∀ b z, ‖F b z‖ ≤ C) :
    Tame F := ⟨hc, fun _ => ⟨C, .of_forall hb⟩⟩

theorem Tame.integral [FirstCountableTopology B] [FirstCountableTopology Z] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) (s : Set Y) (hs : μ s < ⊤) {F : B → Z → Y → ℂ} (h : Tame fun b (q : Z × Y) => F b q.1 q.2) :
    Tame fun b z => ∫ y in s, F b z y ∂μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  refine ⟨continuous_iff_continuousAt.2 fun p₀ => ?_, fun b₀ => ?_⟩
  · obtain ⟨C, hC⟩ := h.2 p₀.1
    refine continuousAt_of_dominated (bound := fun _ => C) (.of_forall fun p => ?_) ?_ (integrable_const C)
      (.of_forall fun y => ?_)
    · exact (h.1.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)) :
        Continuous fun y => F p.1 p.2 y).aestronglyMeasurable
    · exact (continuous_fst.continuousAt.eventually hC).mono fun p hp => .of_forall fun y => hp (p.2, y)
    · exact (h.1.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)) :
        Continuous fun p : B × Z => F p.1 p.2 y).continuousAt
  · obtain ⟨C, hC⟩ := h.2 b₀
    exact ⟨C * (μ.restrict s).real Set.univ, hC.mono fun b hb z =>
      norm_integral_le_of_norm_le_const (.of_forall fun y => hb (z, y))⟩

theorem Tame.continuous_integral [FirstCountableTopology B] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) (s : Set Y) (hs : μ s < ⊤) {F : B → Y → ℂ} (h : Tame F) : Continuous fun b => ∫ y in s, F b y ∂μ :=
  (Tame.integral μ s hs (F := fun b (_ : Unit) y => F b y) (h.comp continuous_snd)).1.comp
    (continuous_id.prodMk (continuous_const (y := ())))

end General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem vol_lt_top {V : HSp D} (hV : CoCpt V) (v : Vol V) : v.μ v.𝓕 < ⊤ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, hc⟩ := hV
  have := v.haar
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) v.μ
  refine lt_of_le_of_lt (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers v.fund (.of_forall fun g => ?_))
    hK.measure_lt_top
  obtain ⟨γ, hγ, h⟩ := hc g
  exact ⟨⟨γ, hγ⟩, h⟩

theorem bounded_of_contAut {V : HSp D} (hV : CoCpt V) {φ : GA D V → ℂ} (hφ : IsContAut V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨K, hK, hc⟩ := hV
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.2.continuousOn
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hc g
  rw [← hφ.1 γ hγ g]
  exact hC _ h

theorem heisO_apply_zero (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) : heisO ψ S T w f 0 = f w := by
  simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

theorem om_rat {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (w : WO S T) : om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w) := by
  have e : actO S T γ γ' (actO S T γ⁻¹ γ'⁻¹ w) = w := by
    rw [actO_eq, actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      mt_mul_inv, Matrix.mul_one]
  rw [← heisO_apply_zero (ψ := ψ) S T w (om (γ, γ') f), ← heisO_apply_zero (ψ := ψ) S T _ f,
    ← hom.om_aut γ hγ γ' hγ' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf _), hom.om_heis _ _ _ _ hf, e]

theorem tame_om {S T A T₀ : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hA : CoCpt A) (hT : CoCpt T₀) (a : GA D A →* GA D S)
    (b : GA D T₀ →* GA D T) (ha : Continuous a) (hb : Continuous b) (ha' : ∀ γ ∈ GQ A, a γ ∈ GQ S)
    (hb' : ∀ γ ∈ GQ T₀, b γ ∈ GQ T) :
    Tame fun (h : GA D T) (q : (GA D A × GA D T₀) × WO S T) => om (a q.1.1, b q.1.2 * h) f q.2 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have hc : Continuous fun p : GA D T × (GA D A × GA D T₀) × WO S T => om (a p.2.1.1, b p.2.1.2 * p.1) f p.2.2 :=
    (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hf).comp
      (((ha.comp continuous_snd.fst.fst).prodMk ((hb.comp continuous_snd.fst.snd).mul continuous_fst)).prodMk
        continuous_snd.snd)
  refine ⟨hc, fun h₀ => ?_⟩
  obtain ⟨U, hU, hU'⟩ := exists_compact_mem_nhds h₀
  obtain ⟨KA, hKA, cA⟩ := hA
  obtain ⟨KT, hKT, cT⟩ := hT
  obtain ⟨-, -, -, -, -, K, hK, cK⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨C, hC⟩ := (hU.prod ((hKA.prod hKT).prod hK)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, Filter.mem_of_superset hU' fun h hh => ?_⟩
  rintro ⟨⟨g, g'⟩, w⟩
  obtain ⟨γ, hγ, hg⟩ := cA g
  obtain ⟨γ', hγ', hg'⟩ := cT g'
  have e : ((a g, b g' * h) : GA D S × GA D T) = (a γ⁻¹, b γ'⁻¹) * (a (γ * g), b (γ' * g') * h) := by
    rw [Prod.mk_mul_mk, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_left, inv_mul_cancel_left]
  have ht := hom.om_pres (a (γ * g), b (γ' * g') * h) f hf
  change ‖om (a g, b g' * h) f w‖ ≤ C
  rw [e, map_mul, Module.End.mul_apply, om_rat hom ht (ha' _ (inv_mem hγ)) (hb' _ (inv_mem hγ'))]
  obtain ⟨_, ⟨δ, rfl⟩, hδ⟩ := cK (actO S T (a γ⁻¹)⁻¹ (b γ'⁻¹)⁻¹ w)
  have h1 := hC (h, (γ * g, γ' * g'), _) ⟨hh, ⟨hg, hg'⟩, hδ⟩
  have h2 := congrArg norm (ht.quasi δ (actO S T (a γ⁻¹)⁻¹ (b γ'⁻¹)⁻¹ w))
  rw [norm_mul, hom.std.1.2.1, one_mul] at h2
  rw [← h2]
  exact h1

section Mixed

variable {B Z : Type} [TopologicalSpace B] [TopologicalSpace Z] [FirstCountableTopology B] [FirstCountableTopology Z]

theorem tame_mixS (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)
    (x : Mx D T.rank ρ) {F : B → Z → WO S T → ℂ} (h : Tame fun b (q : Z × WO S T) => F b q.1 q.2) :
    Tame fun b (q : Z × WO S₀ T) => d.mixS T ψ v.μ v.𝓕 (F b q.1) x q.2 := by
  obtain ⟨i1, -, i3, -⟩ := lattice_Mx D T.rank S₀.rank
  have : FirstCountableTopology (WO S₀ T) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  obtain ⟨j1, -⟩ := lattice_Mx D T.rank S.rank
  have : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  refine Tame.integral v.μ v.𝓕 (by rw [v.covol.2.2]; exact ENNReal.one_lt_top) ?_
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have h0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
  refine Tame.mul (tame_of_bounded (C := 1) ?_ fun _ _ => (hψ.1.2.1 _).le) (h.comp
    (u := fun q : (Z × WO S₀ T) × Mx D T.rank ρ => (q.1.1, d.extY T q.2 + d.extX T x + d.ext0 T q.1.2)) ?_)
  · exact hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_snd.snd) continuous_const)
  · exact continuous_fst.fst.prodMk (((hY.comp continuous_snd).add continuous_const).add (h0.comp continuous_fst.snd))

theorem tame_mixT (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank)
    (y : Mx D S.rank ρ) {F : B → Z → WO S T → ℂ} (h : Tame fun b (q : Z × WO S T) => F b q.1 q.2) :
    Tame fun b (q : Z × WO S T₀) => d.mixT S ψ v.μ v.𝓕 (F b q.1) y q.2 := by
  obtain ⟨i1, -, i3, -⟩ := lattice_Mx D T₀.rank S.rank
  have : FirstCountableTopology (WO S T₀) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  obtain ⟨j1, -⟩ := lattice_Mx D T.rank S.rank
  have : BorelSpace (Mx D ρ S.rank) := ⟨rfl⟩
  simp only [HypDec.mixT, HypDec.integrandT_eq]
  refine Tame.integral v.μ v.𝓕 (by rw [v.covol.2.2]; exact ENNReal.one_lt_top) ?_
  have hY : Continuous (d.incX S) := continuous_const.matrix_mul continuous_id
  have h0 : Continuous (d.inc0 S) := continuous_const.matrix_mul continuous_id
  refine Tame.mul (tame_of_bounded (C := 1) ?_ fun _ _ => (hψ.1.2.1 _).le) (h.comp
    (u := fun q : (Z × WO S T₀) × Mx D ρ S.rank => (q.1.1, d.incX S q.2 + d.incAdj S y + d.inc0 S q.1.2)) ?_)
  · exact hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_snd.snd) continuous_const)
  · exact continuous_fst.fst.prodMk (((hY.comp continuous_snd).add continuous_const).add (h0.comp continuous_fst.snd))

end Mixed

section Step

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

theorem isTheta_evalBF (hv : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D) {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    IsThetaFunO ψ B.V₀ J.W₀ (evalBF s Ψ) :=
  (hv ψ s.weil.std).2 _ _ _ _ J.d _ _ s.vT.covol _ ((hv ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol _ hΨ _) _

theorem om_evalBF (hd : Descent D) (hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D) (hv : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D)
    {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (h₀ : GA D B.A) (h' : GA D J.W₀) :
    s.om₀ (B.o.emb (h₀, 1), h') (evalBF s Ψ) = evalBF s (s.om (embA B.d B.o h₀, J.d.emb0 h') Ψ) := by
  obtain ⟨om₁, h₁⟩ := (hd ψ _ _ _ _ _ s.weil).1 _ _ B.d
  have hS := hm.1 ψ _ _ _ _ B.d _ _ _ _ s.weil h₁ _ _ s.vS.covol
  have hT := hm.2 ψ _ _ _ _ J.d _ _ _ _ h₁ s.weil₀ _ _ s.vT.covol
  have hf := (hv ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol _ hΨ (xZero J.d)
  have ex : mt J.W (J.d.emb0 h')⁻¹ ⬝ xZero J.d = xZero J.d := by
    rw [← map_inv]; exact J.d.wittDecomp_anisotropicEmbedding_inclX _
  have ey : mt B.V₀ (B.o.emb (h₀, 1))⁻¹ ⬝ yZero B.V₀ ρ (vecB B.o B.ζ) = yZero B.V₀ ρ (vecB B.o B.ζ) := by
    rw [← map_inv, Prod.inv_mk, inv_one, yZero_vecB, ← Matrix.mul_assoc, B.o.emb_jB, mt_one, Matrix.mul_one]
  have e1 : ((embA B.d B.o h₀, J.d.emb0 h') : GA D B.V × GA D J.W) =
      (B.d.emb0 (B.o.emb (h₀, 1)), 1) * (1, J.d.emb0 h') := by
    rw [Prod.mk_mul_mk, mul_one, one_mul, embA_apply]
  have e2 : ((B.o.emb (h₀, 1), h') : GA D B.V₀ × GA D J.W₀) = (B.o.emb (h₀, 1), 1) * (1, h') := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  unfold evalBF evalZero evalAt
  rw [e1, e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    (hS _ (s.weil.om_pres _ _ hΨ)).core, (hS _ hΨ).target, ex, (hT _ (h₁.om_pres _ _ hf)).source, ey, (hT _ hf).core]

theorem fjKer_evalBF (hd : Descent D) (hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D) (hv : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D)
    {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) (h : GA D J.W) (h₀ : GA D B.A) (n : GA D J.W)
    (h' : GA D J.W₀) :
    fjKer ψ J.d B.o B.ζ s.om₀ (evalBF s (s.om (1, h) Φ)) h₀ n h' =
      ψ (cenT J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n) *
        evalBF s (s.om (embA B.d B.o h₀, J.d.emb0 h' * h) Φ)
          (actO B.V₀ J.W₀ (B.o.emb (h₀, 1)) 1 (ptT J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n)) := by
  have hΨ := s.weil.om_pres (1, h) Φ hΦ
  have hΞ := isTheta_evalBF s hv hΨ
  have e1 : ((embA B.d B.o h₀, J.d.emb0 h' * h) : GA D B.V × GA D J.W) =
      (embA B.d B.o h₀, J.d.emb0 h') * (1, h) := by
    rw [Prod.mk_mul_mk, mul_one]
  have e2 : ((B.o.emb (h₀, 1), h') : GA D B.V₀ × GA D J.W₀) = (B.o.emb (h₀, 1), 1) * (1, h') := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  rw [e1, map_mul, Module.End.mul_apply, ← om_evalBF s hd hm hv hΨ, e2, map_mul, Module.End.mul_apply, fjKer, opA, jacT,
    map_smul, s.weil₀.om_heis _ _ _ _ (s.weil₀.om_pres _ _ hΞ), Pi.smul_apply, smul_eq_mul, heisO_apply_zero]

theorem firstCountable_GA (V : HSp D) : FirstCountableTopology (GA D V) :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _

theorem continuous_embL (B : BesLev D ρ) : Continuous fun h₀ : GA D B.A => B.o.emb (h₀, 1) :=
  B.o.continuous_emb.comp (continuous_id.prodMk continuous_const)

theorem tame_evalBF {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    Tame fun (h : GA D J.W) (q : (GA D B.A × GA D J.W₀) × WO B.V₀ J.W₀) =>
      evalBF s (s.om (embA B.d B.o q.1.1, J.d.emb0 q.1.2 * h) Φ) q.2 := by
  have := firstCountable_GA B.A
  have := firstCountable_GA J.W
  have := firstCountable_GA J.W₀
  have t0 := tame_om s.weil hΦ B.cpt J.cpt (embA B.d B.o) J.d.emb0 (B.d.continuous_embed.comp (continuous_embL B))
    J.d.continuous_embed (fun γ hγ => B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))) (fun γ hγ => J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ)
  exact tame_mixT s.weil.std J.d s.vT _ (F := fun h (q : GA D B.A × GA D J.W₀) => B.d.mixS J.W ψ s.vS.μ s.vS.𝓕
      (s.om (embA B.d B.o q.1, J.d.emb0 q.2 * h) Φ) (xZero J.d))
      (tame_mixS s.weil.std B.d s.vS _ (F := fun h (q : GA D B.A × GA D J.W₀) =>
        s.om (embA B.d B.o q.1, J.d.emb0 q.2 * h) Φ) t0)

theorem continuous_mt_inv (V : HSp D) : Continuous fun g : GA D V => mt V g⁻¹ :=
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  (continuous_mt V).comp continuous_inv

theorem continuous_ptT {T T₀ : HSp D} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ) : Continuous (ptT d S y) :=
  continuous_const.matrix_mul ((continuous_mt_inv T).matrix_mul continuous_const)

theorem continuous_cenT {T T₀ : HSp D} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ) : Continuous (cenT d S y) :=
  GlobalTheory.OrientedHeis.continuous_symplOH continuous_const ((continuous_mt_inv T).matrix_mul continuous_const)

theorem continuous_psiFlag (hψ : Continuous ψ) {T T₀ : HSp D} (d : HypDec T T₀ ρ) : Continuous (psiFlag ψ d) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hb : Continuous (blockX d) := continuous_const.matrix_mul ((continuous_mt T).matrix_mul continuous_const)
  refine hψ.comp (ht.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_))
  split_ifs
  · exact hb.matrix_elem i j
  · exact continuous_const

theorem tame_fjKer (hd : Descent D) (hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D) (hv : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D)
    {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    Tame fun (h : GA D J.W) (q : GA D B.A × GA D J.W × GA D J.W₀) =>
      fjKer ψ J.d B.o B.ζ s.om₀ (evalBF s (s.om (1, h) Φ)) q.1 q.2.1 q.2.2 := by
  have hψ := s.weil.std
  simp only [fjKer_evalBF s hd hm hv hΦ]
  refine Tame.mul (tame_of_bounded (C := 1) ?_ fun _ _ => (hψ.1.2.1 _).le) ((tame_evalBF s hΦ).comp
    (u := fun q : GA D B.A × GA D J.W × GA D J.W₀ => ((q.1, q.2.2),
      actO B.V₀ J.W₀ (B.o.emb (q.1, 1)) 1 (ptT J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) q.2.1))) ?_)
  · exact hψ.1.1.comp ((continuous_cenT _ _ _).comp continuous_snd.snd.fst)
  · refine (continuous_fst.prodMk continuous_snd.snd).prodMk ?_
    exact (continuous_const.matrix_mul ((continuous_ptT _ _ _).comp continuous_snd.fst)).matrix_mul
      ((continuous_mt_inv B.V₀).comp ((continuous_embL B).comp continuous_fst))

theorem tame_inner (hd : Descent D) (hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D) (hv : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D)
    {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) :
    Tame fun (h : GA D J.W) (q : GA D J.W × GA D J.W₀) => ∫ h₀ in B.vA.𝓕,
      φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (evalBF s (s.om (1, h) Φ)) h₀ q.1 q.2 ∂B.vA.μ := by
  have := firstCountable_GA J.W
  have := firstCountable_GA J.W₀
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := bounded_of_contAut B.cpt hφ
  exact Tame.integral B.vA.μ B.vA.𝓕 (vol_lt_top B.cpt B.vA) (Tame.mul
    (tame_of_bounded (hφ.2.comp continuous_snd.snd) fun _ _ => hC _)
    ((tame_fjKer s hd hm hv hΦ).comp (u := fun q : (GA D J.W × GA D J.W₀) × GA D B.A => (q.2, q.1)) continuous_swap))

theorem tame_fjAllFun (hd : Descent D) (hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D) (hv : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D)
    {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ)
    {G : GA D J.W → ℂ} (hG : RapidDec J.W G) :
    Tame fun (h : GA D J.W) (q : GA D J.W₀ × flagN J.d) =>
      fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) q.1 q.2 := by
  have := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W).2.2.2.2.1
  have hψ := s.weil.std
  obtain ⟨C, hC⟩ := hG.bounded
  have hv' : Continuous fun q : GA D J.W₀ × flagN J.d => q.2.1 := continuous_subtype_val.comp continuous_snd
  refine Tame.mul (Tame.mul (tame_of_bounded ?_ fun _ _ => hC _) (tame_of_bounded (C := 1) ?_ fun _ _ => ?_))
    ((tame_inner s hd hm hv hΦ hφ).comp (u := fun q : GA D J.W₀ × flagN J.d => (q.2.1, q.1))
      (hv'.prodMk continuous_fst))
  · exact hG.continuous.comp (((hv'.comp continuous_snd).mul
      (J.d.continuous_embed.comp continuous_snd.fst)).mul continuous_fst)
  · exact ((continuous_psiFlag hψ.1.1 J.d).comp (hv'.comp continuous_snd)).star
  · rw [norm_star]; exact (hψ.1.2.1 _).le

end Step

theorem continuous_integrand : ∀ D : D7, Descent D → GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D →
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
      (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ →
      Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) := by
  intro D hd hm hv ψ ρ B J s φ G Φ hφ hG hΦ
  have := firstCountable_GA J.W
  have := firstCountable_GA J.W₀
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (GA D J.W₀) := ⟨rfl⟩
  have : OpensMeasurableSpace (flagN J.d) := Subtype.opensMeasurableSpace (flagN J.d : Set (GA D J.W))
  have t5 := Tame.integral J.vN.ν J.vN.𝓝 (by rw [J.vN.unit.2.2]; exact ENNReal.one_lt_top)
    (F := fun (h : GA D J.W) (q : GA D J.W₀) (n : flagN J.d) =>
      fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) q n)
    (tame_fjAllFun s hd hm hv hΦ hφ hG)
  simp only [JacLev.perAll, fjAll]
  exact t5.continuous_integral J.v0.μ J.v0.𝓕 (vol_lt_top J.cpt J.v0)

end GlobalTheory.Unf.EvalCont

end
