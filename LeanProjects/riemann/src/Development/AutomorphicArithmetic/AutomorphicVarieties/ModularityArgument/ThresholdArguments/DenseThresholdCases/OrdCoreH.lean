import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.UseAtL
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharOfScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSubquotientOfHasSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocOrdFlag

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    H.Out θ a K P (maximalIdeal _) D ψ := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP _ _ _ a K _ _ D ψ hU
  refine ⟨hU, _root_.UpperTheory.V.Hi.eq_zero_of_vanish_at_good_points_dense_weight hL L Ω l n c H hA A θ hθ ι P hP a K, fun lam hlam y hy => ?_⟩
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy ⊢
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨-, -, -, -, -, hpt, -⟩ :=
    _root_.UpperTheory.V.Hi.partAct0_alt hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
  obtain ⟨Y, F, e, hY, he, hF0, hF, hop⟩ := hpt y hx
  obtain ⟨hD, hch⟩ := _root_.UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨Y.r, Y.cont, Y.ss, hY, hD, fun hg v => ?_⟩
  obtain ⟨ω, hsm, hPS, hinv, hU'⟩ := _root_.UpperTheory.V.Hi.goodScalB_alt hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp hg Y K e he
    fun h0 => hF0 ((Submodule.mem_bot ℂ).1 (h0 ▸ hF))
  have hO := hch v (ω v) (hsm v) (hinv v) fun j =>
    smul_left_injective ℂ hF0 ((hop (.inr (v, j))).symm.trans ((hU' v j).2 F hF))
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt hL (H.ovr v)
  obtain ⟨φ⟩ := hPS v
  have hpol := (_root_.UpperTheory.V.Z.Win.T2.psRec_alt hL L Ω n (H.Sl v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v) rc hrc (Y.σl v) (ω v)
    (hsm v)).1 (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hdist : ∀ i j, i ≠ j → ∃ u : Uo ((H.Sl v).adicCompletion L), ω v i u ≠ ω v j u := fun i j hij => by
    obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
  have hdr := _root_.UpperTheory.V.Z.Ord.useAtL' (Y.atL v) (ω v) (hsm v) hdist ⟨φ⟩ rc hrc ((UpperTheory.V.Lev.ssCalc L Ω _ _ (H.ovr v)).1 n _ (fun j => (ω v j).comp (H.art v)) hpol)
  rw [funext hpol] at hdr
  refine _root_.UpperTheory.V.Loc.ordFlag_alt hL L Ω l hA.odd ι n (H.Sl v) (hA.Sl_over v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v)
    _ (Y.cont.comp (hA.prj_cont.comp continuous_subtype_val)) (htW lam) (fun τ i j hij => ?_) (ω v) _ hO
    (fun i j hij => ?_) hdr
  · have h1 := (lam τ).anti (Fin.rev_le_rev.2 hij.le)
    have h2 : (i : ℕ) < j := hij
    simp only [htW, lowW]
    omega
  · obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
end
