import Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.SmallCones.ThetaKernelGeneralIdentity
import Development.WeilBound.ThetaLifts.LocalTheory.SplitInv2
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le {n d : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  have h3 : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (h2.and hM.std).mono fun _ hv => hv.1.trans hv.2
  exact Submodule.subset_span ⟨f, _, ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem I_rat (hT : ThetaBasic) {n d : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s') {Φ} (hΦ : Φ ∈ PolData B M) :
    ∀ γ ∈ ratU σ W.J, ∀ h, M.I om Φ (γ * h) = M.I om Φ h := fun γ hγ h => by
  have hi := ((hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ (polData_le hp.good hΦ)).2.1
  simp only [Model.I]
  congr 1
  funext g
  simpa using hi 1 (one_mem _) γ hγ g h

theorem law_ne (α β : Chr F E) {t : (AE F E)ˣ} (ht : 1 < (absE F E t : ℝ)) {x y : ℝ} (h : x < y) :
    (α t : ℂ) * (((absE F E t : ℝ) ^ x : ℝ) : ℂ) ≠ (β t : ℂ) * (((absE F E t : ℝ) ^ y : ℝ) : ℂ) := fun e => by
  have := congrArg norm e
  simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg (absE F E t)) _)] at this
  exact (Real.rpow_lt_rpow_of_exponent_lt ht h).ne this

theorem splitInv2_of (hU : UnipEx) (hS : StabDec) (hT : ThetaBasic) (hP : TriplePair) (hG : GrpTop) (hE : EpsOf) :
    PositivityTheory.ThKG.Loc.SplitInv2 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h3 d₁ W₁ H' i₀ i₁ hH f hf fa fb hs
  obtain ⟨p1, p2, -⟩ := hP F E σ B a a' G X om om' h3
  have hinv : ∀ γ ∈ ratU σ G.W.J, ∀ h, f (γ * h) = f h := by
    rcases hf with ⟨Φ, hΦ, rfl⟩ | ⟨Φ, hΦ, -, rfl⟩
    exacts [I_rat hT p1 hΦ, I_rat hT p2 hΦ]
  refine ⟨?_, fun h0 => split_uniq hU h3 hH hs ⟨fun μ 𝓕 _ _ _ h => by simp [h0], fun t m _ h => by simp, fun t m _ h => by simp⟩⟩
  obtain ⟨⟨ν, 𝓕, a1, a2, a3⟩, -, -, a4, ⟨lev, -, hl, -⟩, -, t, ht⟩ :=
    hU F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ h3.base (Or.inr h3.geo.hW) hH
  obtain ⟨-, -, hn⟩ := hS F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ h3.base (Or.inr h3.geo.hW) hH
  obtain ⟨-, -, -, b4, -⟩ := hG F E σ h3.base.cm _ G.W.J (hE F E σ B h3.base _ G.W _ _ (Or.inr h3.geo.hW)).1
  have : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ G.W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : IsTopologicalGroup (unip σ G.W H') := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : BorelSpace (unip σ G.W H') := Subtype.borelSpace _
  have := a4 ν a1
  have : Countable ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) :=
    Function.Injective.countable (f := fun x => (⟨x.1.1, x.2⟩ : ratU σ G.W.J)) fun x y e =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ratU σ G.W.J => z.1) e))
  have hc : ∀ u ∈ unip σ G.W H', ∀ h, fa (u * h) + fb (u * h) = fa h + fb h := fun u hu h => by
    have e1 := hs.1 ν 𝓕 a1 a2 a3 (u * h)
    have e2 := hs.1 ν 𝓕 a1 a2 a3 h
    rw [Pi.add_apply] at e1 e2
    rw [e1, e2, ← PositivityTheory.ThKF.L2.integral_right a2 (fun v => f (v.1 * h))
      (fun γ hγ x => by rw [Subgroup.coe_mul, mul_assoc]; exact hinv γ.1 hγ _) ⟨u, hu⟩]
    simp only [Subgroup.coe_mul, mul_assoc]
  intro u hu h
  have hu' := hn _ _ _ (hl t⁻¹ 1) u hu
  have e : lev (t⁻¹, 1) = (lev (t, 1))⁻¹ := by rw [← map_inv, Prod.inv_mk, inv_one]
  have s1 := hc _ hu' (lev (t, 1) * h)
  rw [e, inv_inv, mul_assoc, inv_mul_cancel_left, mul_assoc, hs.2.1 t _ (hl t 1), hs.2.1 t _ (hl t 1), hs.2.2 t _ (hl t 1),
    hs.2.2 t _ (hl t 1)] at s1
  have s0 := hc u hu h
  have hne := law_ne X.α X.β ht (show (a' : ℝ) / 2 < (a : ℝ) / 2 by
    have : (a' : ℝ) < a := by exact_mod_cast h3.geo.lt
    linarith)
  have k : fa (u * h) = fa h := by
    refine sub_eq_zero.1 (mul_left_cancel₀ (sub_ne_zero.2 hne) ?_)
    linear_combination s1 - (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * s0
  exact ⟨k, by linear_combination s0 - k⟩

end PositivityTheory.ThKCT
