import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairCentral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SdYFramesStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
set_option maxHeartbeats 1600000
namespace GlobalTheory.LevelLine
section Gen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat ValuativeRel
open GlobalTheory.LocMod (ofSplit MovedTo)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y : Type} [Fintype Y] [DecidableEq Y]
end Gen
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix
open GlobalTheory.LocMod (ofSplit)
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem single_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : _root_.GlobalTheory.MiTop.PlacedAlt f B) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg) :
    ∃ e, Formalism.L2.NTheta.IsIdemAt e PP ∧ ∀ c ∈ idAt D (· = PP.under (𝓞 D.host.F)),
      (mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ *ᵥ
        (fun i => c * incA D (W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) ∈
          latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = PP.under (𝓞 D.host.F)) ↔
        Cond e (2 * D.R.rS + 1) (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹)) := by
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, hv, ht, -, -, hR, hb⟩ := hP
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  obtain ⟨hq, hqv⟩ := hR.idem i
  rw [hi] at hq hqv
  change (G i).q.v = PP.under _ at hqv
  change Formalism.L2.NTheta.IsIdemAt _ PP at hq
  refine ⟨_, hq, fun c hcv => ?_⟩
  rw [← hqv] at hcv ⊢
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  have hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)
  obtain ⟨s, hs, he⟩ := GlobalTheory.LineIdeal.first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hsc := sc_mul (G i) n1 n3 (hb.last i) h₀
  have hT : ((D.mem u).A.T : 𝓞 D.host.E) ∉ PP.asIdeal := fun hT => by
    refine Finset.disjoint_left.1 hv.disj ((ht.gP _).2 ⟨PP, hPP, rfl⟩) ((ht.tP _).2 ?_)
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    rwa [map_natCast]
  have hTv := val_nat (G i).q hq _ hT
  have hz : star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = star μ * (μ * -((D.mem u).A.T : D.host.E)) := by
    have e : B.d.i₀ *ᵥ vecB B.o B.ζ = μ • GlobalTheory.Core.SBesEx.cY W.S.X W.Q.instEq (W.S.X.zu u) := funext n2
    refine (norm_vec B.lev).trans ?_
    change star (B.d.i₀ *ᵥ vecB B.o B.ζ) ⬝ᵥ (D.sp.Y 0).gram *ᵥ (B.d.i₀ *ᵥ vecB B.o B.ζ) = _
    rw [e, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, GlobalTheory.Core.SBesEx.cY_isom D _ _ hW.bot.idE, W.S.X.zu_norm]
    rfl
  have hzu := (G i).hz_unit 0 _ h₀
  have hzu' := hzu
  rw [← hb.lev h₀] at hzu'
  change valuation _ ((G i).q.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = 1 at hzu'
  have hμ1 : valuation _ ((G i).q.pr (incA D μ)) = 1 := by
    have := congrArg (valuation _) hsc
    rwa [map_mul, (G i).sc_unit, one_mul, map_one] at this
  have hμ2 : valuation _ ((G i).q.pr (incA D (star μ))) = 1 := by
    simp only [hz, RingHom.map_mul, RingHom.map_neg, map_natCast, Valuation.map_mul, Valuation.map_neg, hμ1, hTv, mul_one] at hzu'
    exact hzu'
  have hxi : valuation _ (ofSplit (G i).q).xi = 1 := by
    have := congrArg (valuation _) ((G i).sc_step 0)
    rw [map_mul, (G i).sc_unit, (G i).sc_unit, one_mul] at this
    exact this.symm
  obtain ⟨σ, -, hM⟩ := hR.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  obtain ⟨hsd, hfr⟩ := _root_.GlobalTheory.T.selfDual_and_frame_of_pkHyp W hW 0 (by omega)
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> simp
  have H := line_bes (G i).q hq (f.c.B 0 _ h₀) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) ((_root_.GlobalTheory.Fam.pk_z W).βY 0) hfr hsd (f.g.b 0) _ _ _
    (fun h0 => by simpa [h0] using (G i).sc_unit 0) ((G i).bes 0 _ h₀ _ (Nat.zero_add _)) _ (G i).S.ϖ
    (Matrix.fromBlocks_diagonal _ _) (σ.symm.trans (GlobalTheory.StepData.stdOrd _ _ 0 _ (Nat.zero_add _))) hM r hr
    (incA D (s * μ)⁻¹ * (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹))
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hcv))
  have e : (fun i => c * incA D (W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) i)))) =
      fun l => incA D (s * μ)⁻¹ * (c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹) * incA D (B.d.e l r) := by
    funext l
    rw [he, mul_comm (incA D _), mul_assoc, mul_assoc, ← RingHom.map_mul, ← RingHom.map_mul]
    congr 2
    field_simp
  rw [e, hd]
  refine H.trans ?_
  rw [cond_iff (G i).q (G i).S.unif]
  generalize c * incA D ((W.S.X.B.g : D.host.E) ^ D.R.rS)⁻¹ = a
  have hs1 : valuation _ ((G i).q.pr (incA D (s * μ)⁻¹)) = 1 := by
    rw [← RingHom.comp_apply, map_inv₀, map_inv₀, RingHom.comp_apply]
    rcases hs with rfl | rfl <;> simp [hμ1]
  have hs2 : valuation _ ((G i).q.pr (incA D (star (s * μ)⁻¹))) = 1 := by
    rw [star_inv₀, ← RingHom.comp_apply, map_inv₀, map_inv₀, RingHom.comp_apply]
    rcases hs with rfl | rfl <;> simp [hμ2]
  have hϖ : 0 < valuation _ ((G i).S.ϖ : (G i).k) := by simp [zero_lt_iff]
  simp only [Valuation.mem_integer_iff, RingHom.map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, Valuation.map_mul, map_div₀, Valuation.map_neg,
    Valuation.map_pow, Valuation.map_one, hs1, hs2, hxi, hzu, (G i).sc_unit, one_mul, one_pow, div_one, div_le_one₀ hϖ]
theorem line_indep_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → _root_.GlobalTheory.MiTop.PlacedAlt f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) = v) → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f'.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v ⟨PP, hPP, hv⟩ c hc
  subst hv
  obtain ⟨e, he, h⟩ := _root_.GlobalTheory.LevelLine.single_alt W hW ⟨0, hr⟩ rfl f B hP PP hPP
  obtain ⟨e', he', h'⟩ := _root_.GlobalTheory.LevelLine.single_alt W hW ⟨0, hr⟩ rfl f' B' hP' PP hPP
  obtain rfl := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D e e' PP PP he he').1 rfl
  exact (h c hc).trans (h' c hc).symm
end GlobalTheory.LevelLine
end
end
