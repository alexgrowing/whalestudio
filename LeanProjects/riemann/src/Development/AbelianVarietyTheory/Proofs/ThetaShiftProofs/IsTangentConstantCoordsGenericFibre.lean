import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSectionValuesFormalThetaSumStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantTorusExtensionTangentRelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentEqFormalPointTransportedStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTangentReductionEqOriginStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantSectionMulCoordDualNumberPointStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FirstOrderJetConstSectionMulCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentValueEqJetConstantExpansionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentGenericFibreOfThetaSectionsStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTan

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}

theorem exists_isUnit_tau (Ξ : ConstPts W Λ) (u : Λ.A.V) :
    ∃ k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k ∧ IsUnit (Ξ.τ u k) := by
  obtain ⟨k, hk⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x u).left) (cpt ℂ⟦X⟧))
  have hk' : ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k := (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 hk
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex u.2).left
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex u.2).left :=
    ((Ξ.g_rel u 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b u))
  have hj : ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U
      (fun _ => FrameValue.chartAt a.D₀.P.isLB (Λ.u.ex u.2).left, jM) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ((congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr
      (FormalValue.top_le_comp h₀ _ trivial)), hM⟩
  refine ⟨k, hk', isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq u k jM _ hk' hj)).mpr ?_)⟩
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne _ u.2 h₀)).map _)

end

theorem isTan_of_diffHyp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback W.t.G.hom gen), Ξ.IsGen Φ → DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v.left → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → Φ.IsTan (h.symm z₀) νK := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ g h z₀ ν v ρ νK hΦ hd hρ hε hν₁ hν₂
  haveI := isLocalRing_dual ℂ⟦X⟧
  haveI := isLocalRing_dual ℂ
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.exists_constantTorusExtension_tangentRel h₁ E H D l Xo c O β Y b a χ W ν
  have hf := GlobalTheory.T.constantTangent_eq_formalPoint_transported E H D l Xo c O β Y b a χ W g _ z₀ ν v g₁ hd hg₁
  have hr := GlobalTheory.T.constantTangent_reduction_eq_origin E H D l Xo c O β Y b a χ W Λ g h z₀ ν Ξ v g₁ hd hg₁ hf
  obtain ⟨jL, hL⟩ := exists_chart W.P.U.LG.isLB
    ((show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from v.left) (cpt (DualNumber ℂ⟦X⟧)))
  replace hL : ⊤ ≤ v.left ⁻¹ᵁ W.P.U.LG.L.U jL := (top_le_iff_cpt (A := DualNumber ℂ⟦X⟧) _ _).2 hL
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB
    ((show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) (cpt (DualNumber ℂ⟦X⟧)))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB ((show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) (cpt (DualNumber ℂ)))
  have h₀' : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ a.D₀.P.L.U j₀ := (top_le_iff_cpt _ _).2 h₀
  have hb : (show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) ≫ W.φ = spMap constEps ≫ ν.b.left := (hg₁ 0).1 2
  have hj : ⊤ ≤ (show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) ⁻¹ᵁ
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ((congrArg (fun q => q (cpt (DualNumber ℂ⟦X⟧)) ∈ a.D₀.P.L.U _) hb).mpr
      (FormalValue.top_le_comp h₀' _ trivial)), hM⟩
  obtain ⟨ω, hω⟩ := FormalValue.isUnit_valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hz : ⊤ ≤ (Λ.u.ex 0).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
    have e := hd.1.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at e
    exact (congrArg (fun q : Sp ℂ ⟶ _ => ⊤ ≤ q ⁻¹ᵁ a.D₀.P.L.U j₀) e).mp (FormalValue.top_le_comp h₀' _)
  let φ₁ := constEps (jet (fun u : Λ.A.V => Λ.u.fr j₀ u.2) (h.symm z₀))
  have hφ : IsUnit φ₁ := IsUnit.map _ (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    rw [fst_jet]; exact Ne.isUnit (Λ.u.fr_ne j₀ 0 hz)))
  let τ₁ : DualNumber ℂ⟦X⟧ := ω⁻¹.val * ((FormalValue.tau W.P.U.toUnifPre idealEps v.left jL jM).val * φ₁)
  have hτ : IsUnit τ₁ := (Units.isUnit _).mul ((Units.isUnit _).mul hφ)
  refine GlobalTheory.T.isTangent_genericFibre_of_thetaSections E H Λ.A W.t Φ W.P.U.LG (fun u => (Ξ.x u).left) Ξ.τ (h.symm z₀) v.left jL τ₁ ρ νK W.P.bundle hΦ hr hL
    hτ hρ hε hν₁ hν₂ fun j _ α th hth F hF => ?_
  obtain ⟨m, σ, hσ⟩ := GlobalTheory.T.exists_section_values_formalThetaSum h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α th hth
  refine ⟨m, σ, fun u k hk => hσ u k hk, ?_⟩
  obtain ⟨N, n, r, s, hs, hsum⟩ := GlobalTheory.T.exists_pow_mul_eq_sum_constantExpansion h₁ E H D l Xo c O β Y b a χ W j σ NeZero.one_le
  choose x y hx hxv hy using fun i => GlobalTheory.T.tangentValue_eq_jet_constantExpansion h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ g₁ v.left (h.symm z₀) jL jM ω φ₁ τ₁
    j (s i) hf hL (fun z hz => (hj hz).2) ω.isUnit hτ (Units.mul_inv_cancel_left _ _)
    (fun α s₀ f r jf jt hc hcoh => by
      choose k hk using fun i => exists_chart a.D₀.P.isLB
        ((show Sp (DualNumber ℂ) ⟶ _ from Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α) i) (cpt (DualNumber ℂ)))
      have ht : ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) ![k 0, k 1, j₀, k 3] :=
        (top_le_iff_cpt (𝟙 (Sp (DualNumber ℂ)))
          (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) ![k 0, k 1, j₀, k 3])).2
          (Set.mem_iInter.2 fun i => by
            fin_cases i
            exacts [hk 0, hk 1, h₀, hk 3])
      have e₁ := GlobalTheory.T.constantSection_mul_coord_dualNumberPoint E H D l Xo c O β Y b a χ W ν g₁ j _ s₀ f r jM jf jt _ hg₁ hc hcoh ht
      have e₂ := GlobalTheory.T.firstOrderJet_constSection_mul_coordinate E H D l c O β b a Λ g h z₀ ν j α s₀ _ hd.1 hd.2.1 ht
      rw [e₂, map_mul, map_pow] at e₁
      rw [hω]
      exact e₁.trans (_root_.mul_assoc _ _ _).symm) (hs i)
  have hJ := IsJet.sum Finset.univ fun i _ => (hx i).const_mul (r i)
  have hX : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ^ N = HahnSeries.single (N : ℤ) (1 : ℂ) := by
    rw [LaurentSeries.coe_algebraMap, PowerSeries.coe_X, HahnSeries.single_pow]; simp
  have e₀ : HahnSeries.single ((N : ℤ) + m) (1 : ℂ) =
      (HahnSeries.single (N : ℤ) (1 : ℂ) * HahnSeries.single (m : ℤ) (1 : ℂ) : ℂ⸨X⸩) := by
    rw [HahnSeries.single_mul_single, _root_.one_mul]
  have key := hJ.dualMapR_eq (N + m) (fun u => Λ.A.FSum j α th u) (fun u => by
    obtain ⟨k, hk, hu⟩ := exists_isUnit_tau Ξ u
    have e := congrArg (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)
      (hsum ℂ⟦X⟧ (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (Ξ.x u).left k (Over.w (Ξ.x u)) hk)
    simp only [hxv _ u k hk, Algebra.algebraMap_self, RingHom.id_apply, ← _root_.mul_assoc, ← Finset.sum_mul] at e
    rw [map_mul, map_mul, map_pow, map_pow, hσ u k hk, hX] at e
    refine ((hu.map (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)).pow j).mul_right_cancel (e.symm.trans ?_)
    rw [e₀]; ring) F hF
  have e := congrArg ρ (hsum _ (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) v.left jL (Over.w v) hL)
  simp only [hy, TrivSqZeroExt.algebraMap_eq_inl, ← _root_.mul_assoc, ← Finset.sum_mul] at e
  rw [← eq_dualMapR _ ρ hρ hε] at key
  rw [map_mul, map_mul, map_pow, map_pow, key, hρ, TrivSqZeroExt.inl_pow, hX, e₀, TrivSqZeroExt.inl_mul] at e
  have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (N : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
  refine hu.mul_left_cancel (e.trans ?_)
  ring

end GlobalTheory.ConstTan
