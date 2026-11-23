import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleInnerUnitaryCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleCharacterTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalNormIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizableApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupCompactInterFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryDenseClosureLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCompactOrbitFiniteDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementActsByScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimKStableContinuousInvariantStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
  GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV

noncomputable section

namespace GlobalTheory.ThetaCplV

open scoped ComplexConjugate
open GlobalTheory.ThetaFacCompl

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem om_mul (om : Rep σ Y W) (g h : UA σ W.J) (Φ : Fn F n d) : om (1, g * h) Φ = om (1, g) (om (1, h) Φ) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem om_one (om : Rep σ Y W) (Φ : Fn F n d) : om (1, 1) Φ = Φ := by
  rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]

def stabOf (om : Rep σ Y W) (N : Submodule ℂ (Fn F n d)) : Subgroup (UA σ W.J) where
  carrier := {g | ∀ Φ ∈ N, om (1, g) Φ ∈ N ∧ om (1, g⁻¹) Φ ∈ N}
  mul_mem' := fun {g h} hg hh Φ hΦ => ⟨by rw [om_mul]; exact (hg _ (hh Φ hΦ).1).1,
    by rw [mul_inv_rev, om_mul]; exact (hh _ (hg Φ hΦ).2).2⟩
  one_mem' := fun Φ hΦ => by simpa [om_one] using hΦ
  inv_mem' := fun {g} hg Φ hΦ => ⟨(hg Φ hΦ).2, by rw [inv_inv]; exact (hg Φ hΦ).1⟩

theorem exists_level (hK : KP) {B : Base F E} {M : Model σ Y W} {χX χW : Chr F E} {om : Rep σ Y W} {r s r' s' : ℕ}
    (hP : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) :
    ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧ ∀ k ∈ U, k ∈ finU σ W.J → om (1, k) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, -, φ, hSB, hev, rfl⟩ := hx
    obtain ⟨U, hU, h⟩ := GlobalTheory.T.exists_open_subgroup_fixing_pure_tensor F E σ B n d Y W M χX χW om _ _ _ _ hK hP f φ hSB hev
    exact ⟨U, hU, fun k hk hf => h k hk (mem_finU.1 hf)⟩
  | zero => exact ⟨⊤, isOpen_univ, fun k _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hf => by rw [map_add, h k hk.1 hf, h' k hk.2 hf]⟩
  | smul t x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hf => by rw [map_smul, h k hk hf]⟩

theorem closure_le_stabOf (hK : KP) {B : Base F E} {M : Model σ Y W} {χX χW : Chr F E} {om : Rep σ Y W}
    {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (N : Submodule ℂ (Fn F n d)) (hND : N ≤ PolData B M)
    (hfin : ∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N)
    (hcpt : ∀ k ∈ KInf σ W B.emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N) (Kf : Subgroup (UA σ W.J)) (hKf : Kf ≤ finU σ W.J) :
    Subgroup.closure (KInf σ W B.emb ∪ (Kf : Set (UA σ W.J))) ≤ stabOf om N := by
  have h1 : Subgroup.closure (⋃ v : Pl F, UAt σ W (evFin F v)) ≤ stabOf om N := by
    rw [Subgroup.closure_le]
    intro h hh
    obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hh
    exact fun Φ hΦ => ⟨hfin v h hv Φ hΦ, hfin v _ (inv_mem_UAt _ hv) Φ hΦ⟩
  have h2 : ∀ h ∈ finU σ W.J, ∀ Φ ∈ N, om (1, h) Φ ∈ N := by
    intro h hh Φ hΦ
    obtain ⟨U, hU, hfix⟩ := exists_level hK hP (hND hΦ)
    obtain ⟨h', hh', hU', hf'⟩ := GlobalTheory.T.finite_unitary_dense_closure_local F E σ d W hP.base.cm h hh U hU
    have e : h = h' * (h'⁻¹ * h) := by group
    rw [e, om_mul, hfix _ hU' hf']
    exact (h1 hh' Φ hΦ).1
  rw [Subgroup.closure_le]
  rintro k (hk | hk)
  · exact fun Φ hΦ => ⟨hcpt k hk Φ hΦ, hcpt _ (inv_mem_KInf _ hk) Φ hΦ⟩
  · exact fun Φ hΦ => ⟨h2 k (hKf hk) Φ hΦ, h2 _ (inv_mem (hKf hk)) Φ hΦ⟩

end Stab

theorem exists_stable_compl : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')), (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → N ≤ GlobalTheory.ThK.PolData B G.M → GlobalTheory.ThetaFac.WStable B om (GlobalTheory.ThK.PolData B G.M) N → ∃ N' : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')), (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N') ∧ N' ≤ GlobalTheory.ThK.PolData B G.M ∧ GlobalTheory.ThetaFac.WStable B om (GlobalTheory.ThK.PolData B G.M) N' ∧ (∀ Ψ ∈ N, Ψ ∈ N' → G.M.I om Ψ = 0) ∧ GlobalTheory.ThK.PolData B G.M ≤ N ⊔ N' := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hKN hND hN
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + a') G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : Countable (ratU σ G.W.J) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ G.W.J) (Measure.haar)
  set μ : Measure (UA σ G.W.J) := Measure.haar with hμdef
  have hμ : μ.IsHaarMeasure := inferInstance
  have hT := hM.triple
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_skew hT.base.cm B G.W hT.geo.hW μ
  set D := PolData B G.M with hD
  have lin0 := GlobalTheory.T.matched_triple_inner_unitary_compatible hKP F E σ B a a' G X om om' R Rf hM
  have lin : ∀ Φ ∈ D, ∀ Ψ ∈ D, ∀ c : ℂ, G.M.I om (Φ + c • Ψ) = G.M.I om Φ + c • G.M.I om Ψ := by
    intro Φ hΦ Ψ hΨ c
    rw [(lin0 Φ hΦ _ (D.smul_mem c hΨ) 1).1, (lin0 Ψ hΨ Ψ hΨ c).2]
  have sq := (GlobalTheory.T.square_integrability hKP F E σ B a a' G X om om' hT μ 𝓕 hμ h𝓕).1
  have cont := GlobalTheory.T.continuous_left_invariant_theta hKP F E σ B a a' G X om om' hT
  have stab := GlobalTheory.T.matched_triple_character_twist hKP F E σ B a a' G X om om' R Rf hM
  have I0 : G.M.I om 0 = 0 := by simpa using lin 0 D.zero_mem 0 D.zero_mem 1
  let q : (UA σ G.W.J → ℂ) → (UA σ G.W.J → ℂ) → ℂ := fun f g => ∫ x in 𝓕, f x * conj (g x) ∂μ
  let Z : Submodule ℂ (UA σ G.W.J → ℂ) := Submodule.span ℂ (G.M.I om '' (D : Set (Fn F a (a + a'))))
  have hZ : ∀ f ∈ Z, ∃ Φ ∈ D, G.M.I om Φ = f := fun f hf => exists_of_mem_span_image D D _ lin le_rfl hf
  have hIZ : ∀ Φ ∈ D, G.M.I om Φ ∈ Z := fun Φ hΦ => Submodule.subset_span ⟨Φ, hΦ, rfl⟩
  have hint : ∀ Φ ∈ D, ∀ Ψ ∈ D,
      Integrable (fun x => G.M.I om Φ x * conj (G.M.I om Ψ x)) (μ.restrict 𝓕) := by
    intro Φ hΦ Ψ hΨ
    have e : (fun x => G.M.I om Φ x * conj (G.M.I om Ψ x)) = fun x =>
        (((‖G.M.I om (Φ + (1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ) - ((‖G.M.I om (Φ + (-1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          + Complex.I * ((‖G.M.I om (Φ + Complex.I • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          - Complex.I * ((‖G.M.I om (Φ + (-Complex.I) • Ψ) x‖ ^ 2 : ℝ) : ℂ)) / 4 := by
      funext x
      rw [lin Φ hΦ Ψ hΨ 1, lin Φ hΦ Ψ hΨ (-1), lin Φ hΦ Ψ hΨ Complex.I, lin Φ hΦ Ψ hΨ (-Complex.I)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact mul_conj_polar _ _
    rw [e]
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖G.M.I om (Φ + c • Ψ) x‖ ^ 2 : ℝ) : ℂ)) (μ.restrict 𝓕) :=
      fun c => Integrable.ofReal (sq _ (D.add_mem hΦ (D.smul_mem c hΨ)))
    exact ((((hi 1).sub (hi (-1))).add ((hi Complex.I).const_mul Complex.I)).sub
      ((hi (-Complex.I)).const_mul Complex.I)).div_const 4
  have hadd : ∀ f ∈ Z, ∀ g ∈ Z, ∀ k ∈ Z, q (f + g) k = q f k + q g k := by
    intro f hf g hg k hk
    obtain ⟨Φ, hΦ, rfl⟩ := hZ f hf
    obtain ⟨Ψ, hΨ, rfl⟩ := hZ g hg
    obtain ⟨Θ, hΘ, rfl⟩ := hZ k hk
    simp only [q, Pi.add_apply, add_mul]
    exact integral_add (hint Φ hΦ Θ hΘ) (hint Ψ hΨ Θ hΘ)
  have hsmul : ∀ f ∈ Z, ∀ k ∈ Z, ∀ t : ℂ, q (t • f) k = t * q f k := by
    intro f _ k _ t
    simp only [q, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul t _
  have hherm : ∀ f ∈ Z, ∀ g ∈ Z, q g f = conj (q f g) := by
    intro f _ g _
    simp only [q]
    rw [← integral_conj]
    congr 1
    funext x
    simp [map_mul, mul_comm]
  have hpos : ∀ f ∈ Z, q f f = 0 → f = 0 := by
    intro f hf h0
    obtain ⟨Φ, hΦ, rfl⟩ := hZ f hf
    apply eq_zero_of_ae_restrict_fd σ G.W.J μ 𝓕 hμ h𝓕 _ (cont Φ hΦ).1 (cont Φ hΦ).2
    have e : q (G.M.I om Φ) (G.M.I om Φ) = ((∫ x in 𝓕, ‖G.M.I om Φ x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      simp only [q]
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e] at h0
    have h0' : ∫ x in 𝓕, ‖G.M.I om Φ x‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (sq Φ hΦ)).1 h0'
    filter_upwards [hae] with x hx
    simpa using hx
  have hleft : ∀ Φ ∈ D, ∀ Ψ ∈ D, ∀ γ ∈ ratU σ G.W.J, ∀ x,
      G.M.I om Φ (γ * x) * conj (G.M.I om Ψ (γ * x)) = G.M.I om Φ x * conj (G.M.I om Ψ x) := by
    intro Φ hΦ Ψ hΨ γ hγ x
    rw [(cont Φ hΦ).2 γ hγ, (cont Ψ hΨ).2 γ hγ]
  have Itr : ∀ (h : UA σ G.W.J) (Φ : Fn F a (a + a')), G.M.I om (om (1, h) Φ) = fun x => G.M.I om Φ (x * h) :=
    fun h Φ => funext fun x => I_transl _ _ _ _ _
  have transl : ∀ (h : UA σ G.W.J) (Φ Ψ : Fn F a (a + a')), Φ ∈ D → Ψ ∈ D →
      q (G.M.I om (om (1, h) Φ)) (G.M.I om (om (1, h) Ψ)) = q (G.M.I om Φ) (G.M.I om Ψ) := by
    intro h Φ Ψ hΦ hΨ
    simp only [q]
    rw [Itr, Itr]
    exact setIntegral_mul_right h𝓕 (fun x => G.M.I om Φ x * conj (G.M.I om Ψ x)) (hleft Φ hΦ Ψ hΨ) h
  have back : ∀ (h : UA σ G.W.J) (Φ : Fn F a (a + a')), om (1, h) (om (1, h⁻¹) Φ) = Φ := by
    intro h Φ
    rw [← om_mul, mul_inv_cancel, om_one]
  let C : Submodule ℂ (Fn F a (a + a')) :=
    { carrier := {Ψ | Ψ ∈ D ∧ ∀ Φ ∈ N, q (G.M.I om Φ) (G.M.I om Ψ) = 0}
      add_mem' := by
        rintro Ψ Ψ' ⟨h1, h2⟩ ⟨h1', h2'⟩
        refine ⟨D.add_mem h1 h1', fun Φ hΦ => ?_⟩
        have e := lin Ψ h1 Ψ' h1' 1
        rw [one_smul, one_smul] at e
        rw [e, q_add_right Z q hadd hherm (hIZ Ψ h1) (hIZ Ψ' h1') (hIZ Φ (hND hΦ)), h2 Φ hΦ, h2' Φ hΦ, add_zero]
      zero_mem' := ⟨D.zero_mem, fun Φ _ => by simp [q, I0]⟩
      smul_mem' := by
        rintro c Ψ ⟨h1, h2⟩
        refine ⟨D.smul_mem c h1, fun Φ hΦ => ?_⟩
        have e := lin 0 D.zero_mem Ψ h1 c
        rw [zero_add, I0, zero_add] at e
        rw [e, q_smul_right Z q hsmul hherm (hIZ Ψ h1) (hIZ Φ (hND hΦ)), h2 Φ hΦ, mul_zero] }
  have hCD : C ≤ D := fun Ψ h => h.1
  have hCW : GlobalTheory.ThetaFac.WStable B om D C := by
    constructor
    · intro v h hh Ψ hΨ
      obtain ⟨hΨD, hΨ⟩ := hΨ
      refine ⟨(stab Ψ hΨD).2.2.1 v h hh, fun Φ hΦ => ?_⟩
      have hΦ' : om (1, h⁻¹) Φ ∈ N := hN.fin v h⁻¹ (inv_mem_UAt _ hh) Φ hΦ
      have := transl h _ Ψ (hND hΦ') hΨD
      rw [back] at this
      rw [this]
      exact hΨ _ hΦ'
    · intro γ hγ Ψ hΨ Ψ₁ hΨ₁D hder
      obtain ⟨hΨD, hΨ⟩ := hΨ
      refine ⟨hΨ₁D, fun Φ hΦ => ?_⟩
      have hΦD := hND hΦ
      obtain ⟨Φ₁, hΦ₁D, hdΦ⟩ := GlobalTheory.T.matched_triple_local_norm_identity hKP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦD
      have dW := GlobalTheory.T.matched_triple_global_lift_identity hKP F E σ B a a' G X om om' R Rf hM γ hγ
      have h0 := hΨ Φ₁ (hN.lie γ hγ Φ hΦ Φ₁ hΦ₁D hdΦ)
      have hsum := setIntegral_deriv_eq_zero μ (ratU σ G.W.J) 𝓕 h𝓕
        (fun x => G.M.I om Φ x * conj (G.M.I om Ψ x))
        (fun x => G.M.I om Φ₁ x * conj (G.M.I om Ψ x) + G.M.I om Φ x * conj (G.M.I om Ψ₁ x))
        (hleft Φ hΦD Ψ hΨD) (fun c hc x => by rw [hleft Φ₁ hΦ₁D Ψ hΨD c hc, hleft Φ hΦD Ψ₁ hΨ₁D c hc])
        (((cont Φ₁ hΦ₁D).1.mul (Complex.continuous_conj.comp (cont Ψ hΨD).1)).add
          ((cont Φ hΦD).1.mul (Complex.continuous_conj.comp (cont Ψ₁ hΨ₁D).1)))
        (hint Φ hΦD Ψ hΨD) ((hint Φ₁ hΦ₁D Ψ hΨD).add (hint Φ hΦD Ψ₁ hΨ₁D)) γ hγ.1 (fun x => by
          have h := (dW Φ hΦD Φ₁ hΦ₁D hdΦ x).mul (dW Ψ hΨD Ψ₁ hΨ₁D hder x).star
          refine h.congr_deriv ?_
          simp)
      rw [integral_add (hint Φ₁ hΦ₁D Ψ hΨD) (hint Φ hΦD Ψ₁ hΨ₁D)] at hsum
      simp only [q] at h0 ⊢
      rw [h0, zero_add] at hsum
      exact hsum
    · intro k hk Ψ hΨ
      obtain ⟨hΨD, hΨ⟩ := hΨ
      refine ⟨(stab Ψ hΨD).2.2.2 k hk, fun Φ hΦ => ?_⟩
      have hΦ' : om (1, k⁻¹) Φ ∈ N := hN.cpt k⁻¹ (inv_mem_KInf _ hk) Φ hΦ
      have := transl k _ Ψ (hND hΦ') hΨD
      rw [back] at this
      rw [this]
      exact hΨ _ hΦ'
  refine ⟨C, fun Ψ hΨ h0 => ⟨hΨ, fun Φ _ => by simp [q, h0]⟩, hCD, hCW,
    fun Ψ hΨN hΨC => hpos _ (hIZ Ψ hΨC.1) (hΨC.2 Ψ hΨN), fun Ψ hΨ => ?_⟩

  obtain ⟨U₀, hU₀, hKfc⟩ := GlobalTheory.T.exists_open_subgroup_compact_inter_finite F E σ (a + a') G.W.J hT.base.cm
  set Kf : Subgroup (UA σ G.W.J) := U₀ ⊓ finU σ G.W.J with hKf
  set 𝒦 : Subgroup (UA σ G.W.J) := Subgroup.closure (KInf σ G.W B.emb ∪ (Kf : Set (UA σ G.W.J))) with h𝒦
  have stD : 𝒦 ≤ stabOf om D := closure_le_stabOf hKP hP D le_rfl (fun v h hh Φ hΦ => (stab Φ hΦ).2.2.1 v h hh)
    (fun k hk Φ hΦ => (stab Φ hΦ).2.2.2 k hk) Kf inf_le_right
  have stN : 𝒦 ≤ stabOf om N := closure_le_stabOf hKP hP N hND hN.fin hN.cpt Kf inf_le_right
  have rtI : ∀ (k : 𝒦) (Φ : Fn F a (a + a')), rt 𝒦 k (G.M.I om Φ) = G.M.I om (om (1, (k : UA σ G.W.J)) Φ) :=
    fun k Φ => by rw [Itr]; rfl
  let NI : Submodule ℂ (UA σ G.W.J → ℂ) := Submodule.span ℂ (G.M.I om '' (N : Set (Fn F a (a + a'))))
  have hNI : ∀ f ∈ NI, ∃ Φ ∈ N, G.M.I om Φ = f := fun f hf => exists_of_mem_span_image D N _ lin hND hf
  have hZst : ∀ k, ∀ f ∈ Z, rt 𝒦 k f ∈ Z := by
    intro k f hf
    obtain ⟨Φ, hΦ, rfl⟩ := hZ f hf
    rw [rtI]
    exact hIZ _ (stD k.2 Φ hΦ).1
  let Lin : D →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun Φ => G.M.I om Φ
      map_add' := fun Φ Φ' => (lin0 Φ Φ.2 Φ' Φ'.2 1).1
      map_smul' := fun c Φ => (lin0 Φ Φ.2 Φ Φ.2 c).2 }
  have hfinZ : ∀ f ∈ Z, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => rt 𝒦 k f)) := by
    intro f hf
    obtain ⟨Φ, hΦ, rfl⟩ := hZ f hf
    have hS := GlobalTheory.T.polynomial_data_compact_orbit_finite_dim hKP F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hP Kf hKfc inf_le_right Φ hΦ
    set S := Submodule.span ℂ (Set.range fun k : 𝒦 => om (1, (k : UA σ G.W.J)) Φ)
    let S' : Submodule ℂ D := S.comap D.subtype
    haveI : FiniteDimensional ℂ S' :=
      FiniteDimensional.of_injective (K := ℂ) (V₂ := S) ((D.subtype.domRestrict S').codRestrict S fun x => x.2)
        fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : Fn F a (a + a'))) e))
    refine Submodule.finiteDimensional_of_le (S₂ := S'.map Lin) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨om (1, (k : UA σ G.W.J)) Φ, (stD k.2 Φ hΦ).1⟩, Submodule.subset_span ⟨k, rfl⟩, (rtI k Φ).symm⟩
  have hlev : ∀ T : Submodule ℂ (UA σ G.W.J → ℂ), T.FG → T ≤ Z → ∃ U : Subgroup (UA σ G.W.J),
      IsOpen (U : Set (UA σ G.W.J)) ∧ ∀ t ∈ T, ∀ k ∈ U, k ∈ finU σ G.W.J → ∀ x, t (x * k) = t x := by
    intro T hTfg
    refine Submodule.fg_induction (R := ℂ) (M := UA σ G.W.J → ℂ) (motive := fun T _ => T ≤ Z → ∃ U : Subgroup (UA σ G.W.J),
      IsOpen (U : Set (UA σ G.W.J)) ∧ ∀ t ∈ T, ∀ k ∈ U, k ∈ finU σ G.W.J → ∀ x, t (x * k) = t x) ?_ ?_ T hTfg
    · intro f hf
      obtain ⟨Φ, hΦ, rfl⟩ := hZ f (hf (Submodule.mem_span_singleton_self f))
      obtain ⟨U, hU, hfix⟩ := exists_level hKP hP hΦ
      refine ⟨U, hU, fun t ht k hk hkf x => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
      simp only [Pi.smul_apply]
      rw [← I_transl, hfix k hk hkf]
    · intro T₁ T₂ _ _ h₁ h₂ hle
      obtain ⟨U₁, hU₁, e₁⟩ := h₁ (le_sup_left.trans hle)
      obtain ⟨U₂, hU₂, e₂⟩ := h₂ (le_sup_right.trans hle)
      refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun t ht k hk hkf x => ?_⟩
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.1 ht
      simp only [Pi.add_apply]
      rw [e₁ t₁ ht₁ k hk.1 hkf, e₂ t₂ ht₂ k hk.2 hkf]
  have hadm : FiniteDimensional ℂ (Submodule.span ℂ
      (typeSet (rt 𝒦) Z (Submodule.span ℂ (Set.range fun k => rt 𝒦 k (G.M.I om Ψ))))) := by
    set T := Submodule.span ℂ (Set.range fun k => rt 𝒦 k (G.M.I om Ψ)) with hTdef
    have hTf : FiniteDimensional ℂ T := hfinZ _ (hIZ Ψ hΨ)
    have hTZ : T ≤ Z := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hZst k _ (hIZ Ψ hΨ))
    have hTst : ∀ k, ∀ t ∈ T, rt 𝒦 k t ∈ T := by
      intro k u hu
      have : T.map (rt 𝒦 k) ≤ T := by
        rw [hTdef, Submodule.map_span_le]
        rintro _ ⟨k', rfl⟩
        exact Submodule.subset_span ⟨k * k', by simp⟩
      exact this ⟨u, hu, rfl⟩
    obtain ⟨U, hU, hUT⟩ := hlev T ((Submodule.fg_iff_finiteDimensional T).2 hTf) hTZ
    have hσ := GlobalTheory.SkewToHerm.sigma_invol σ hT.base.cm
    obtain ⟨y, hy⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hT.base.cm
    have hc : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    have hcc : σ (y - σ y) = -(y - σ y) := by rw [map_sub, hσ]; ring
    have hK𝒦 : Subgroup.closure (KInf σ G.W B.emb) ≤ 𝒦 := Subgroup.closure_mono Set.subset_union_left
    have hAZ : ∀ φ ∈ typeSet (rt 𝒦) Z T, ∃ Φ ∈ D, G.M.I om Φ = φ := by
      rintro _ ⟨L, hL, -, t, rfl⟩
      exact hZ _ (hL t)
    refine GlobalTheory.T.finite_dim_K_stable_continuous_invariant hKP F E σ hσ B _ _ _ G.W hT.base hT.geo.hW hT.geo.even _ hc hcc T hTf (fun t ht => ?_)
      (fun k t ht => hTst ⟨k, hK𝒦 k.2⟩ t ht) (U ⊓ U₀) (hU.inter hU₀) _ ?_ (fun φ hφ => ?_) ?_ (fun z hz => ?_)
    · obtain ⟨Φ, hΦ, rfl⟩ := hZ t (hTZ ht)
      exact (cont Φ hΦ).1
    · rintro _ ⟨L, -, hLe, t, rfl⟩
      exact ⟨L, fun _ => trivial, fun k s s' h => hLe ⟨k, hK𝒦 k.2⟩ s s' h, t, rfl⟩
    · obtain ⟨Φ, hΦ, rfl⟩ := hAZ φ hφ
      obtain ⟨K, -, hK⟩ := GlobalTheory.T.exists_maximal_compact_invariant F E σ hσ B a a' G X om om' hKP hT _ hc hcc Φ hΦ
      exact hK.mod
    · rintro _ ⟨L, -, hLe, t, rfl⟩ k hk hkf x
      have hk𝒦 : k ∈ 𝒦 := Subgroup.subset_closure (Or.inr ⟨hk.2, hkf⟩)
      have := hLe ⟨k, hk𝒦⟩ t t (funext fun x => (hUT t t.2 k hk.1 hkf x).symm)
      exact (congrFun this x).symm
    · obtain ⟨m, b, hb⟩ := GlobalTheory.T.central_element_acts_by_scalar hKP F E σ hσ B a a' G X om om' hT _ hc hcc z hz
      refine ⟨m, b, fun φ hφ => ?_⟩
      obtain ⟨Φ, hΦ, rfl⟩ := hAZ φ hφ
      exact hb Φ hΦ
  have hNIZ : NI ≤ Z := Submodule.span_mono (Set.image_mono hND)
  obtain ⟨n, hn, horth⟩ := exists_orth_of_types Z q hadd hsmul hherm hpos (rt 𝒦) hZst
    (fun k f hf g hg => by
      obtain ⟨Φ, hΦ, rfl⟩ := hZ f hf
      obtain ⟨Φ', hΦ', rfl⟩ := hZ g hg
      rw [rtI, rtI]
      exact transl _ _ _ hΦ hΦ')
    NI hNIZ
    (fun k f hf => by
      obtain ⟨Φ, hΦ, rfl⟩ := hNI f hf
      rw [rtI]
      exact Submodule.subset_span ⟨_, (stN k.2 Φ hΦ).1, rfl⟩)
    (fun f hf => hfinZ f (hNIZ hf)) _ (hIZ Ψ hΨ) hadm
  obtain ⟨w, hw, rfl⟩ := hNI n hn
  have hIsub : G.M.I om (Ψ - w) = G.M.I om Ψ - G.M.I om w := by
    have := lin Ψ hΨ _ (hND hw) (-1)
    rwa [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at this
  have hχC : Ψ - w ∈ C := ⟨D.sub_mem hΨ (hND hw), fun Φ hΦ => by
    rw [hIsub]
    exact horth _ (Submodule.subset_span ⟨Φ, hΦ, rfl⟩)⟩
  have e : Ψ = w + (Ψ - w) := by abel
  rw [e]
  exact Submodule.add_mem_sup hw hχC

end GlobalTheory.ThetaCplV

end
