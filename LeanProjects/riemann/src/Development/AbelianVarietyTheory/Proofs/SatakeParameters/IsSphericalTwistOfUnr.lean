import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CrysTwistBack

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {a : ℕ}

theorem isCrysAt_of_tw {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
    [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ)
    (r : ↥Gw →* GL (Fin a) (Om l)) (h : IsCrysAt P Bw (UpperTheory.V.Af.tw r c))
    (hc : IsCrysAt P Bw (GlobalTheory.TripleGal.rk1 c)) : IsCrysAt P Bw r := by
  obtain ⟨L₁, r₁, m₁, hr₁⟩ := h
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  have hp := (local_ext P Bw l₁ r₁).1.2 hr₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    simp [GlobalTheory.TripleGal.rk1]
  have hM : IsModel Bw r L (UpperTheory.V.Af.tw r₁' d⁻¹) := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        ((UpperTheory.V.Af.tw r c g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((UpperTheory.V.Af.tw r₁' d⁻¹ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul, map_mul, e, UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀,
      show algebraMap ↥L.1 (Om l) (d g : ↥L.1) = (c g : Om l) from hcd g, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  refine ⟨L, _, hM, ?_⟩
  let θ : ↥(GK Bw.Kw) →* (↥L.1)ˣ := d.comp Bw.e.symm.toMonoidHom
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T Bw.Kw L (Bw.repE L (UpperTheory.V.Af.tw r₁' d⁻¹)) (Bw.repE L r₁') θ
    (fun g x => ?_) ?_).2 hp
  · rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul]
    change _ = ((d (Bw.e.symm g) : ↥L.1) * ((d⁻¹ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)) • _
    rw [MonoidHom.inv_apply, Units.mul_inv, one_smul]
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) hq
    change (Bw.repE L c₂' g x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm g))

end GlobalTheory.CrysTwistBack

namespace GlobalTheory.CrysTwistBack

theorem isSpherical_twist_of_unr {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (κ : HChar E) (hκ : κ.UnrAt w)
    (h : GlobalTheory.SmGL.IsSpherical σ.ρ) :
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a κ w) (CuspSub.isOpen_ker_locDet κ w)).ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w a :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have hg : g.1 ∈ GlobalTheory.LFun.KGL w a := hK ▸ g.2
  have h1 : CuspSub.locDet a κ w g.1 = 1 := hκ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)
  have h3 := hv g
  show ((CuspSub.locDet a κ w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

theorem holds_good_crys : AutomorphicFormsFiniteGL → HeckeLAdicCharacterAbove → Holds .csd .crys → Holds .good .crys := by
  intro hF hA hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw
  intro P AI hT A hAw O _ _ _ Bw hj σ hσ hsph
  obtain ⟨κ, m, hκ, hκu, hcs⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hch⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hch l ι κ m (fun k _ => hκ k)
  have hw' : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ hr.1 hμc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have h1 := hC E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hcs (UpperTheory.V.Af.tw r μ) hw' w hw P AI hT A hAw O Bw hj _
    (hσ.twist κ) (isSpherical_twist_of_unr a w σ κ hκu hsph)
  have h2 := (hA E Ω l P AI hT ι art hart κ m μ (fun k _ => hκ k) hμc hμ w A hAw O Bw hj).2.2.1 hκu
  obtain ⟨T⟩ := hT
  exact isCrysAt_of_tw T Bw (μ.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype) h1 h2

end GlobalTheory.CrysTwistBack

end
