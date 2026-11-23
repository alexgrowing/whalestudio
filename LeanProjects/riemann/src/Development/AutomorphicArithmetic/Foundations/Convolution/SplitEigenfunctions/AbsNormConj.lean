import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitOfNormalised
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemma

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem absQ_unrAt {F : Type} [Field F] [NumberField F] (s : ℂ) (w : HeightOneSpectrum (𝓞 F)) :
    (GlobalTheory.CuspRep.Model.absC F s).UnrAt w := by
  intro x hx
  apply Units.ext
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm F (GlobalTheory.Mem.Chr.localIdele F w x)) = 1
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x 0 (by simpa [IsUnitAt] using hx)]
  simp

open ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.UnitaryBC GlobalTheory.DiscSpec in
private theorem absQ_val {F : Type} [Field F] [NumberField F] (s : ℂ) (w : HeightOneSpectrum (𝓞 F)) :
    (((GlobalTheory.CuspRep.Model.absC F s).val w : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) := by
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm F (GlobalTheory.Mem.Chr.localIdele F w (atFin w (unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w _ 1 (unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring

open scoped Pointwise in
private theorem absNorm_conj {M : Type} [Field M] [NumberField M] (h2 : Module.finrank ℚ M = 2)
    {w w' : HeightOneSpectrum (𝓞 M)} (h : w'.under (𝓞 ℚ) = w.under (𝓞 ℚ)) :
    Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal := by
  haveI : Algebra.IsQuadraticExtension ℚ M := { finrank_eq_two' := h2 }
  haveI : IsGalois ℚ M := inferInstance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 ℚ) (𝓞 M) (M ≃ₐ[ℚ] M) w.asIdeal w'.asIdeal
    (congrArg HeightOneSpectrum.asIdeal h.symm)
  rw [hg, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv w.asIdeal (g • w.asIdeal) (MulSemiringAction.toRingEquiv _ _ g) rfl).toEquiv.symm

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.descS :
    UpperTheory.V.Z.Bc.DescS := by
  intro M _ _ h2 hM sat' inf' hc _ _ hi
  haveI := hM
  rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
  swap
  · exfalso
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v) (IsTotallyReal.isReal v)
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised M 2 (by norm_num) P
    fun τ => ⟨_, ParLaws.hasInfChar_infChar (CG.mk P) τ⟩
  have hval : ∀ w w' : HeightOneSpectrum (𝓞 M), Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal →
      (GlobalTheory.CuspRep.Model.absC M s).val w' = (GlobalTheory.CuspRep.Model.absC M s).val w := fun w w' e =>
    Units.ext (by rw [PositivityTheory.Rg.Rs.StrStepB.absC_val, PositivityTheory.Rg.Rs.StrStepB.absC_val, e])
  have hcon : ConjInv (P.twist (GlobalTheory.CuspRep.Model.absC M s)) := hi.mono fun w h w' e => by
    obtain ⟨B, h1, h3⟩ := h w' e
    refine ⟨B.map (· * (GlobalTheory.CuspRep.Model.absC M s).val w), PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC P h1 s, ?_⟩
    have := PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC P h3 s
    rwa [hval w w' (absNorm_conj h2 e)] at this
  obtain ⟨π', h3, h4⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.downN M h2 _ hs hcon
  refine ⟨(π'.twist (GlobalTheory.CuspRep.Model.absC ℚ (-s))).HasSat,
    fun τ => (π'.twist (GlobalTheory.CuspRep.Model.absC ℚ (-s))).HasInfChar (InfinitePlace.mk τ),
    Or.inr ⟨inferInstance, _, rfl, rfl⟩, ?_, ?_⟩
  · filter_upwards [hi, h3] with w a b e
    obtain ⟨B', c, d⟩ := b e
    obtain ⟨B, h1, -⟩ := a w rfl
    have h5 := PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC P h1 s
    have hB : B' = B.map (· * (GlobalTheory.CuspRep.Model.absC M s).val w) := GlobalTheory.LFun.HasSatGL.unique d h5
    subst hB
    refine ⟨B, ?_, h1⟩
    have h6 := c.twist (absQ_unrAt (-s) (w.under (𝓞 ℚ)))
    have h7 : (GlobalTheory.CuspRep.Model.absC M s).val w * (GlobalTheory.CuspRep.Model.absC ℚ (-s)).val (w.under (𝓞 ℚ)) = 1 := by
      apply Units.ext
      have hn : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 ℚ)).asIdeal := e
      have h0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      rw [Units.val_mul, PositivityTheory.Rg.Rs.StrStepB.absC_val, absQ_val, ← hn, neg_neg, Units.val_one,
        ← Complex.cpow_add _ _ h0]
      simp
    convert h6 using 1
    rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id B]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [mul_assoc, h7]
  · intro τ m hm
    have h5 := hm.twist (GlobalTheory.CuspRep.Model.absC M s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at h5
    have h6 := (h4 τ _ h5).twist (GlobalTheory.CuspRep.Model.absC ℚ (-s))
    rw [UpperTheory.V.TR.SS.expo_absC, Multiset.map_map] at h6
    convert h6 using 1
    conv_lhs => rw [← Multiset.map_id m]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
