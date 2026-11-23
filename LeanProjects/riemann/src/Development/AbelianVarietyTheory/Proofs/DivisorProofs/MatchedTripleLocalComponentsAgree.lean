import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaInvarianceStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaFacCompl

open scoped ComplexConjugate
open MeasureTheory GlobalTheory.ThetaFacCompl

theorem stableComplement_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F a' (a + a')), GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}) ≤ N → N ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) → ∃ C : Submodule ℂ (GlobalTheory.ThK.Fn F a' (a + a')), GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) C ∧ C ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ N ⊔ C = (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ N ⊓ C = (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN hKN hND
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.unitary_adelic_group_topology F E σ (a + a') G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  haveI := GlobalTheory.T.discreteTopology_rational_unitary F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ G.W.J) (Measure.haar)
  set μ : Measure (UA σ G.W.J) := Measure.haar with hμdef
  have hμ : μ.IsHaarMeasure := inferInstance
  set D := PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hD
  have lin := GlobalTheory.T.matched_pair_theta_local_global hKP F E σ B a a' G X om om' R Rf hM
  have sq := (GlobalTheory.T.square_integrability hKP F E σ B a a' G X om om' hM.triple μ 𝓕 hμ h𝓕).2
  have I0 : G.M'.I om' 0 = 0 := by simpa using lin 0 D.zero_mem 0 D.zero_mem 1
  let q : (UA σ G.W.J → ℂ) → (UA σ G.W.J → ℂ) → ℂ := fun f g => ∫ x in 𝓕, f x * conj (g x) ∂μ
  let Z : Submodule ℂ (UA σ G.W.J → ℂ) := Submodule.span ℂ (G.M'.I om' '' (D : Set (Fn F a' (a + a'))))
  have hZ : ∀ f ∈ Z, ∃ Φ ∈ D, G.M'.I om' Φ = f := fun f hf => exists_of_mem_span_image D D _ lin le_rfl hf
  have hIZ : ∀ Φ ∈ D, G.M'.I om' Φ ∈ Z := fun Φ hΦ => Submodule.subset_span ⟨Φ, hΦ, rfl⟩
  have hint : ∀ Φ ∈ D, ∀ Ψ ∈ D,
      Integrable (fun x => G.M'.I om' Φ x * conj (G.M'.I om' Ψ x)) (μ.restrict 𝓕) := by
    intro Φ hΦ Ψ hΨ
    have e : (fun x => G.M'.I om' Φ x * conj (G.M'.I om' Ψ x)) = fun x =>
        (((‖G.M'.I om' (Φ + (1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ) - ((‖G.M'.I om' (Φ + (-1 : ℂ) • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          + Complex.I * ((‖G.M'.I om' (Φ + Complex.I • Ψ) x‖ ^ 2 : ℝ) : ℂ)
          - Complex.I * ((‖G.M'.I om' (Φ + (-Complex.I) • Ψ) x‖ ^ 2 : ℝ) : ℂ)) / 4 := by
      funext x
      rw [lin Φ hΦ Ψ hΨ 1, lin Φ hΦ Ψ hΨ (-1), lin Φ hΦ Ψ hΨ Complex.I, lin Φ hΦ Ψ hΨ (-Complex.I)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact mul_conj_polar _ _
    rw [e]
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖G.M'.I om' (Φ + c • Ψ) x‖ ^ 2 : ℝ) : ℂ)) (μ.restrict 𝓕) :=
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
    apply GlobalTheory.T.matched_pair_theta_archimedean hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ hΦ
    have e : q (G.M'.I om' Φ) (G.M'.I om' Φ) = ((∫ x in 𝓕, ‖G.M'.I om' Φ x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      simp only [q]
      rw [← integral_complex_ofReal]
      congr 1
      funext x
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e] at h0
    have h0' : ∫ x in 𝓕, ‖G.M'.I om' Φ x‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (sq Φ hΦ)).1 h0'
    filter_upwards [hae] with x hx
    simpa using hx
  have hK : ∀ Ψ ∈ Submodule.span ℂ {Ψ | Ψ ∈ D ∧ G.M'.I om' Ψ = 0}, Ψ ∈ D ∧ G.M'.I om' Ψ = 0 := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨D.zero_mem, I0⟩
    | add x y _ _ hx hy =>
      refine ⟨D.add_mem hx.1 hy.1, ?_⟩
      have := lin x hx.1 y hy.1 1
      rw [one_smul, one_smul] at this
      rw [this, hx.2, hy.2, add_zero]
    | smul c x _ hx =>
      refine ⟨D.smul_mem c hx.1, ?_⟩
      have := lin 0 D.zero_mem x hx.1 c
      rw [zero_add, I0, zero_add] at this
      rw [this, hx.2, smul_zero]
  let C : Submodule ℂ (Fn F a' (a + a')) :=
    { carrier := {Ψ | Ψ ∈ D ∧ ∀ Φ ∈ N, q (G.M'.I om' Φ) (G.M'.I om' Ψ) = 0}
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
  have stab := GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM
  have rinv := GlobalTheory.T.matched_pair_theta_finite_places hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕
  have skew := GlobalTheory.T.matched_pair_theta_unramified hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕
  have transl : ∀ (h : UA σ G.W.J) (Φ Ψ : Fn F a' (a + a')), Φ ∈ D → Ψ ∈ D →
      q (G.M'.I om' (om' (1, h) Φ)) (G.M'.I om' (om' (1, h) Ψ)) = q (G.M'.I om' Φ) (G.M'.I om' Ψ) := by
    intro h Φ Ψ hΦ hΨ
    have e1 : G.M'.I om' (om' (1, h) Φ) = fun x => G.M'.I om' Φ (x * h) := funext fun x => I_transl _ _ _ _ _
    have e2 : G.M'.I om' (om' (1, h) Ψ) = fun x => G.M'.I om' Ψ (x * h) := funext fun x => I_transl _ _ _ _ _
    simp only [q]
    rw [e1, e2]
    exact rinv Φ hΦ Ψ hΨ h
  have back : ∀ (h : UA σ G.W.J) (Φ : Fn F a' (a + a')), om' (1, h) (om' (1, h⁻¹) Φ) = Φ := by
    intro h Φ
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, ← Prod.one_eq_mk, map_one,
      Module.End.one_apply]
  have hCW : GlobalTheory.ThetaFac.WStable B om' D C := by
    constructor
    · intro v h hh Ψ hΨ
      obtain ⟨hΨD, hΨ⟩ := hΨ
      refine ⟨stab.1 v h hh Ψ hΨD, fun Φ hΦ => ?_⟩
      have hΦ' : om' (1, h⁻¹) Φ ∈ N := hN.fin v h⁻¹ (inv_mem_UAt _ hh) Φ hΦ
      have := transl h _ Ψ (hND hΦ') hΨD
      rw [back] at this
      rw [this]
      exact hΨ _ hΦ'
    · intro γ hγ Ψ hΨ Ψ₁ hΨ₁D hder
      obtain ⟨hΨD, hΨ⟩ := hΨ
      refine ⟨hΨ₁D, fun Φ hΦ => ?_⟩
      obtain ⟨Φ₁, hΦ₁D, hdΦ, hsum⟩ := skew γ hγ Φ (hND hΦ) Ψ hΨD Ψ₁ hΨ₁D hder
      have h0 := hΨ Φ₁ (hN.lie γ hγ Φ hΦ Φ₁ hΦ₁D hdΦ)
      simp only [q] at h0 ⊢
      rw [h0, zero_add] at hsum
      exact hsum
    · intro k hk Ψ hΨ
      obtain ⟨hΨD, hΨ⟩ := hΨ
      refine ⟨stab.2 k hk Ψ hΨD, fun Φ hΦ => ?_⟩
      have hΦ' : om' (1, k⁻¹) Φ ∈ N := hN.cpt k⁻¹ (inv_mem_KInf _ hk) Φ hΦ
      have := transl k _ Ψ (hND hΦ') hΨD
      rw [back] at this
      rw [this]
      exact hΨ _ hΦ'
  have hinf : N ⊓ C = Submodule.span ℂ {Ψ | Ψ ∈ D ∧ G.M'.I om' Ψ = 0} := by
    apply le_antisymm
    · intro Φ hΦ
      obtain ⟨hΦN, hΦD, hΦ⟩ := Submodule.mem_inf.1 hΦ
      exact Submodule.subset_span ⟨hΦD, hpos _ (hIZ Φ hΦD) (hΦ Φ hΦN)⟩
    · refine le_inf hKN fun Ψ hΨ => ?_
      obtain ⟨hD', h0⟩ := hK Ψ hΨ
      exact ⟨hD', fun Φ _ => by simp [q, h0]⟩
  have hsup : N ⊔ C = D := by
    refine le_antisymm (sup_le hND hCD) fun Φ hΦD => ?_
    obtain ⟨P, hPΦ, hPP, hPsa, hPN, hfin⟩ := GlobalTheory.T.matched_pair_theta_invariance hKP F E σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 ⟨Φ, hΦD⟩
    let PN : Submodule ℂ (Fn F a' (a + a')) := ((N.comap D.subtype).map P).map D.subtype
    have hPN_N : PN ≤ N := by
      rintro _ ⟨_, ⟨Ψ, hΨ, rfl⟩, rfl⟩
      exact hPN N hN hND Ψ hΨ
    have hPN_D : PN ≤ D := hPN_N.trans hND
    let Y := Submodule.span ℂ (G.M'.I om' '' (PN : Set (Fn F a' (a + a'))))
    have hY : Y ≤ Submodule.span ℂ (Set.range fun Ψ : ↥D => G.M'.I om' (P Ψ : Fn F a' (a + a'))) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨_, ⟨Ψ, _, rfl⟩, rfl⟩, rfl⟩
      exact ⟨Ψ, rfl⟩
    haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hY
    obtain ⟨S, hS⟩ : Y.FG := Submodule.fg_iff_finiteDimensional Y |>.2 inferInstance
    have hSZ : (↑S : Set (UA σ G.W.J → ℂ)) ⊆ Z := by
      intro f hf
      have hfY : f ∈ Y := hS ▸ Submodule.subset_span hf
      obtain ⟨w, hw, rfl⟩ := exists_of_mem_span_image D PN _ lin hPN_D hfY
      exact hIZ w (hPN_D hw)
    obtain ⟨n, hn, horth⟩ := exists_orth Z q hadd hsmul hherm hpos S hSZ _ (hIZ Φ hΦD)
    rw [hS] at hn
    obtain ⟨w, hw, rfl⟩ := exists_of_mem_span_image D PN _ lin hPN_D hn
    obtain ⟨_, ⟨Ψw, hΨwN, rfl⟩, rfl⟩ := hw
    have hwD : ((P Ψw : ↥D) : Fn F a' (a + a')) ∈ D := (P Ψw).2
    have hIsub : G.M'.I om' (Φ - (P Ψw : Fn F a' (a + a'))) = G.M'.I om' Φ - G.M'.I om' (P Ψw : Fn F a' (a + a')) := by
      have := lin Φ hΦD _ hwD (-1)
      rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at this
      exact this
    have hχC : Φ - (P Ψw : Fn F a' (a + a')) ∈ C := by
      refine ⟨D.sub_mem hΦD hwD, fun Ψ hΨ => ?_⟩
      have hPχ : P (⟨Φ, hΦD⟩ - P Ψw) = ⟨Φ, hΦD⟩ - P Ψw := by rw [map_sub, hPΦ, hPP]
      have key := hPsa ⟨Ψ, hND hΨ⟩ (⟨Φ, hΦD⟩ - P Ψw)
      rw [hPχ] at key
      have hval : ((⟨Φ, hΦD⟩ - P Ψw : ↥D) : Fn F a' (a + a')) = Φ - (P Ψw : Fn F a' (a + a')) := rfl
      rw [hval] at key
      show q _ _ = 0
      simp only [q]
      rw [← key, hIsub]
      have hmem : G.M'.I om' (P ⟨Ψ, hND hΨ⟩ : Fn F a' (a + a')) ∈ Submodule.span ℂ (↑S : Set (UA σ G.W.J → ℂ)) := by
        rw [hS]
        exact Submodule.subset_span ⟨_, ⟨_, ⟨⟨Ψ, hND hΨ⟩, hΨ, rfl⟩, rfl⟩, rfl⟩
      exact q_span_left Z q hadd hsmul hSZ (Z.sub_mem (hIZ Φ hΦD) (hIZ _ hwD)) horth _ hmem
    have e : Φ = (P Ψw : Fn F a' (a + a')) + (Φ - (P Ψw : Fn F a' (a + a'))) := by abel
    rw [e]
    exact Submodule.add_mem_sup (hPN N hN hND Ψw hΨwN) hχC
  exact ⟨C, hCW, hCD, hsup, hinf⟩

end GlobalTheory.ThetaFacCompl

end
