import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSchwartzIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairLocalEvaluationPlanes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseAThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairPeriodIdentityCaseAFourStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactStabilizerLineNormOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermAdaptedCompactOpenVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompactIdeleVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAbsPowerLocallyConstantStatement

noncomputable section

namespace GlobalTheory.ConeBump

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped GlobalTheory.VacAny

theorem nonzero_coneFin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (v : Pl F) (μKv : Measure (KAt K (evFin F v)))
      (μv : Measure (idelesAt E (evFin F v))), IsNormK K (evFin F v) μKv → IsNormE E v μv →
    ∀ l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) → ℂ,
      (∀ p ∈ SB (Fin b × Fin (b + a') → Fv F v), ∀ q ∈ SB (Fin b × Fin (b + a') → Fv F v), l (p + q) = l p + l q) →
      (∀ c : ℂ, ∀ p ∈ SB (Fin b × Fin (b + a') → Fv F v), l (c • p) = c * l p) →
      (∃ p ∈ SB (Fin b × Fin (b + a') → Fv F v), l p ≠ 0) →
      (∀ g ∈ UAt σ G₁.V (evFin F v), ∀ p ∈ SB (Fin b × Fin (b + a') → Fv F v), ∀ p₁ ∈ SB (Fin b × Fin (b + a') → Fv F v),
        Acts (evFin F v) (om₁ (g, 1)) p p₁ → l p₁ = l p) →
      ∃ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μKv μv (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∈ SB (Fin b × Fin (b + a') → Fv F v) ∧
        l (coneFin B G.M om v (ev v) K μKv μv (shiftA H H') X.ν ((b + 2 - a') / 2) φ) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hfac K hK v μKv μv hμK hμ
    l hadd hsmul hne hinv
  classical
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hKP.base
  have hP₁ := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).1
  have hψ : Continuous B.ψ := hT.base.std.1
  have hKc : IsCompact (K : Set (UA σ G.V.J)) :=
    GlobalTheory.T.stabilizer_compact hKP F E σ B (b + 2) G.V _ _ K hT.base hT.geo.hV hK
  haveI : CompactSpace (KAt K (evFin F v)) := isCompact_iff_compactSpace.1 (isCompact_KAt hKc _)
  haveI : IsProbabilityMeasure μKv := ⟨hμK.2⟩
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  have hx0 : H.x ≠ 0 := by
    intro h0
    have h1 := hC.hH.xy
    rw [h0] at h1
    simp [form] at h1
  have hνc : Continuous X.ν := (GlobalTheory.ThK.Check.isHecke_div hT.chars.heckeα hT.chars.heckeβ).1
  have hg := GlobalTheory.T.character_abs_power_locally_constant F E X.ν hνc ((b + 2 - a') / 2) v
  have hevSB : ∀ p ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ev v p ∈ SB (Fin b × Fin (b + a') → Fv F v) := by
    intro p hp
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hp
  have hintSB : ∀ φ (k : UA σ G.V.J) (l' : (AE F E)ˣ),
      GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ k l' ∈ SB (Fin b × Fin (b + a') → Fv F v) :=
    fun φ k l' => hevSB _ (locOp_mem _ _ _)
  obtain ⟨p, hp, hlp⟩ := hne
  obtain ⟨ψ, hψSB, hψp⟩ : ∃ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ev v ψ = p := by
    have : p ∈ (SB _).map (ev v) := by rw [(hev v).2]; exact hp
    obtain ⟨ψ, h1, h2⟩ := this
    exact ⟨ψ, h1, h2⟩
  obtain ⟨φ₀, hφ₀, hi11⟩ : ∃ φ₀ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ₀ 1 1 = ev v ψ := by
    let w := GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' 1)
    have hφ₀ : schr (GlobalTheory.LatVac.psiAt B.ψ v) (-w) ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) :=
      GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v (-w) ψ hψSB
    refine ⟨_, hφ₀, ?_⟩
    have hone : locOp v (om ((1 : UA σ G.V.J), (1 : UA σ G.W.J))) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (-w) ψ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (-w) ψ :=
      locOp_of_fix (fun Φ _ => by
        show (om 1) Φ = Φ
        rw [map_one]
        rfl) hφ₀
    simp only [GlobalTheory.ConeBump.integ]
    rw [hone, (locOp_rho G.M.co hψ v (shiftA H H' 1) hφ₀).2]
    congr 1
    funext x
    simp only [schr, Prod.fst_neg, Prod.snd_neg]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right]
    have h2 : x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) + ((x + w.1) ⬝ᵥ -w.2 + ⅟(2 : Fv F v) * (-w.1 ⬝ᵥ -w.2)) = 0 := by
      simp only [add_dotProduct, dotProduct_neg, neg_dotProduct, neg_neg]
      linear_combination (w.1 ⬝ᵥ w.2) * (invOf_two_add_invOf_two (R := Fv F v))
    rw [h2, AddChar.map_zero_eq_one, one_mul]

  have hI₀ := GlobalTheory.T.pair_local_evaluation_planes hKP F E σ B _ _ _ _ G.V G.W G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 _ _ H H' v
    (ev v) K φ₀ hφ₀
  have hG0 : IsLocallyConstant fun q : KAt K (evFin F v) × idelesAt E (evFin F v) =>
      l (GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ₀ q.1.1 q.2.1) *
        ((X.ν q.2.1 : ℂ) * ((absE F E q.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) :=
    IsLocallyConstant.comp₂ (hI₀.comp l) (hg.comp_continuous continuous_snd) (· * ·)
  have hSig : ∀ q : KAt K (evFin F v) × idelesAt E (evFin F v), mat q.1.1 *ᵥ incV F H.x = (q.2.1 : AE F E) • incV F H.x →
      q ∈ {q : KAt K (evFin F v) × idelesAt E (evFin F v) |
        l (GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ₀ q.1.1 q.2.1) *
          ((X.ν q.2.1 : ℂ) * ((absE F E q.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) = l p} := by
    intro q hq
    obtain ⟨g₁, hg₁, hlaw⟩ := GlobalTheory.T.triple_pair_period_identity_case_a_four hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hfac v
      q.1.1 q.1.2.2 q.2.1 q.2.2 hq
    have habs : absE F E q.2.1 = 1 := GlobalTheory.T.compact_stabilizer_line_norm_one F E σ (b + 2) G.V H.x K hKc hx0 v q.1.1 q.1.2 q.2.1 hq
    have hP0 := hintSB φ₀ 1 1
    have hinv' := hinv g₁ hg₁ _ hP0 _ (locOp_mem _ _ _) (acts_locOp_om hA hP₁ hg₁ (mem_UAtSub.1 (one_mem _)) hP0)
    show _ = _
    rw [hlaw φ₀ hφ₀, hsmul _ _ (locOp_mem _ _ _), hinv', hi11, hψp, habs]
    simp only [NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_pow, mul_one, Chars.ν, MonoidHom.div_apply,
      Circle.coe_div]
    have h1 : ((X.β q.2.1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h2 : ((X.α q.2.1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    field_simp
  obtain ⟨U, hU, C, hCc, hUC⟩ := GlobalTheory.T.herm_adapted_compact_open_volume F E σ B (b + 2) b G.V G₁.V _ _ H 0 (b + 1) K hT.base hT.geo.hV hC.hH hKc v _
    (hG0.isOpen_fiber (l p)) hSig
  obtain ⟨V, hVU, hVo, hVc, h0V, hloc⟩ := GlobalTheory.T.triple_pair_period_identity_case_a_three hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev
    hei hev hfac v U hU
  obtain ⟨φ, hφ, hφeq⟩ := hloc φ₀ hφ₀
  refine ⟨φ, hφ, ?_⟩
  have hf0 : ∀ (k : KAt K (evFin F v)) (l' : idelesAt E (evFin F v)), l' ∉ C →
      GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ k.1 l'.1 = 0 := by
    intro k l' hl'
    rw [hφeq k.1 k.2.2 l'.1 l'.2, Set.indicator_of_notMem, zero_smul]
    intro hV
    exact hl' (hUC (k, l') (hVU hV)).2
  have hfl := GlobalTheory.T.pair_local_evaluation_planes hKP F E σ B _ _ _ _ G.V G.W G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 _ _ H H' v
    (ev v) K φ hφ
  obtain ⟨hSB, hL⟩ := GlobalTheory.T.locally_constant_schwartz_integral μKv μv (fun (k : KAt K (evFin F v)) (l' : idelesAt E (evFin F v)) =>
      GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ k.1 l'.1)
    (fun l' : idelesAt E (evFin F v) => (X.ν l'.1 : ℂ) * ((absE F E l'.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) C hCc hfl
    (fun k l' => hintSB φ _ _) hf0 hg.continuous l hadd hsmul
  have hcone : coneFin B G.M om v (ev v) K μKv μv (shiftA H H') X.ν ((b + 2 - a') / 2) φ = fun y =>
      ∫ k : KAt K (evFin F v), ∫ l' : idelesAt E (evFin F v),
        GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ k.1 l'.1 y *
          ((X.ν l'.1 : ℂ) * ((absE F E l'.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) ∂μv ∂μKv := by
    funext y
    simp only [coneFin, GlobalTheory.ConeBump.coneFinInt_eq]
  rw [hcone]
  refine ⟨hSB, ?_⟩
  rw [hL]
  have hpt : ∀ (k : KAt K (evFin F v)) (l' : idelesAt E (evFin F v)),
      l (GlobalTheory.ConeBump.integ B G.M om v (ev v) (shiftA H H') φ k.1 l'.1) *
          ((X.ν l'.1 : ℂ) * ((absE F E l'.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) =
        V.indicator (fun _ => (1 : ℂ)) (GlobalTheory.ConeBump.disp v H.x k.1 l'.1) * l p := by
    intro k l'
    rw [hφeq k.1 k.2.2 l'.1 l'.2, hsmul _ _ (hintSB φ₀ _ _)]
    by_cases hV : GlobalTheory.ConeBump.disp v H.x k.1 l'.1 ∈ V
    · rw [Set.indicator_of_mem hV, one_mul, one_mul]
      exact (hUC (k, l') (hVU hV)).1
    · rw [Set.indicator_of_notMem hV]
      simp
  simp_rw [hpt, integral_mul_const]
  exact mul_ne_zero (GlobalTheory.T.local_compact_idele_volume F E σ (b + 2) G.V H.x K v μKv μv hμK hμ V hVo hVc h0V C hCc
    (fun q hq => (hUC q (hVU hq)).2)) hlp

end GlobalTheory.ConeBump
