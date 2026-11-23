import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SeparableConjugates.SepConjG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Imports
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
theorem sep_conj_g_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7}
    {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) {a : ℕ} (π : D.naut.CG a) (hc : D.naut.csd π) {w w' : PlE D.host}
    (hw : IsConjPl D.host w w') (k : Sep D.nd D.naut (D.naut.locG π w)) : Sep D.nd D.naut (D.naut.locG π w') := by
  have := host_isCMField D.host
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (C.e _ π).1
  have hmk : CG.mk π₀ = (C.e _ π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (C.csd _ π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hpar : ∀ v, T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 v) := fun v => by
    rw [C.loc, hmk]
    rfl
  rw [sep_iff T, hpar] at k ⊢
  obtain ⟨γ, hγ⟩ := GlobalTheory.exists_tameGenAt_of_isPlaceOver _ _ _ _ (D.nd.plOm.2 w')
  obtain ⟨γ', ⟨c, hcE, hcA, -⟩, -⟩ := GlobalTheory.conjGen_transport_exists D w' w γ (GlobalTheory.TwistDet.isConjPl_symm hw) hγ
  have hcp : ConjPl (IsCMField.complexConj D.host.E).toRingEquiv w w' :=
    (conjPl_iff_mem _ _ _).2 fun x y e => hw x y (e.trans (host_complexConj D.host _))
  obtain rfl : w' = conjSrc (IsCMField.complexConj D.host.E).toRingEquiv w := eq_conjSrc fun x => by
    simpa using (hcp (IsCMField.complexConj D.host.E x)).symm
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
  have good : ∀ (v : PlE D.host) (τ : SmIrr (GL (Fin a) (v.adicCompletion D.host.E))), π₀.IsLocComp v τ →
      UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep τ)) := fun v τ hτ => by
    have g := _root_.UpperTheory.One.M.New.cgGood sw C _ π v
    have h1 : (CG.mk π₀).IsLoc v (Quotient.mk _ τ) := hτ
    rw [← hmk, CG.IsLoc.unique _ a _ v _ _ h1.loc h1] at g
    exact g
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ] at k
  rw [_root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL (ParLaws.isLocComp_flip hc₀ hσ)]
  let π₁ : IrrRep (GL (Fin a) (w.adicCompletion D.host.E)) :=
    ⟨σ.V, σ.ρ.comp (GlobalTheory.TypeTame.invTranspose a), fun v => (σ.smooth v).preimage (GlobalTheory.TypeTame.continuous_invTranspose a),
      GlobalTheory.GelfandKazhdan.isIrreducible_comp _ (fun g => ⟨_, GlobalTheory.TypeTame.invTranspose_invTranspose a g⟩) σ.irred⟩
  have hE := GlobalTheory.GelfandKazhdan.equiv_contra _ a σ.V σ.ρ
    (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top _ a σ.V σ.ρ σ.smooth σ.irred) σ.irred
  have hr := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  let cc := (IsCMField.complexConj D.host.E).toRingEquiv
  let i := RingEquiv.ofBijective (conjLoc cc w) ⟨(conjLoc cc w).injective, ParLaws.conjLoc_surjective cc w⟩
  let L := longElt a (w.adicCompletion D.host.E)
  obtain ⟨b', b, h1, h2, -, h4⟩ := _root_.UpperTheory.One.M.New.field hL (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (conjSrc cc w))) hr c
    (D.host.conj : D.host.E →+* D.host.E) i (fun z => (hcA z).symm) hcE (conjLoc_spec cc w).1
    (fun x => ((conjLoc_spec cc w).2.1 x).trans (congrArg _ (host_complexConj D.host x))) a
    (ParLaws.toRep ⟨σ.V, σ.ρ.comp (ParLaws.flip (conjLoc cc w) a),
        isSmooth_comp σ.smooth _ (ParLaws.continuous_flip (conjLoc_spec _ w).1),
        ParLaws.isIrreducible_comp σ.irred _ (ParLaws.flip_surjective (ParLaws.conjLoc_surjective _ w))⟩) π₁
    (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.ρ.asGroupHom L)) (fun g v => by
      change σ.ρ L (σ.ρ (invRevT (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) v) =
        σ.ρ (invT a _ (Matrix.GeneralLinearGroup.map (conjLoc cc w) g)) (σ.ρ L v)
      have e : ∀ (x y : GL (Fin a) (w.adicCompletion D.host.E)) (u : σ.V), σ.ρ x (σ.ρ y u) = σ.ρ (x * y) u :=
        fun x y u => by rw [map_mul]; rfl
      refine (e _ _ v).trans (Eq.trans ?_ (e _ _ v).symm)
      rw [ParLaws.invRevT_eq, inv_mul_cancel_right]) (good _ _ (ParLaws.isLocComp_flip hc₀ hσ))
  first | (have hOpn := UpperTheory.One.M.opn _ (hr); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hr
  have kd := k.dual
  rw [← _root_.UpperTheory.One.M.LawsM.dual H a (ParLaws.toRep σ) π₁ (good _ _ hσ) hE, ← h2] at kd
  exact h1 ▸ kd.transport c (D.host.conj : D.host.E ≃+* D.host.E) hcE hcA h4
end UpperTheory.GalS
end
end
