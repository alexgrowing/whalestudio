import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterOnStabilizerEqProdResidueCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred
  classical
  obtain ⟨ψ, hψ, hdec⟩ := GlobalTheory.T.levelCharacter_on_stabilizer_eq_prod_residue_characters_alt R F X h hIs hGrp
  have hc : ∀ PP ∈ R.Pg, ∃ c : (kP PP)ˣ, ∀ t, ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.conjRes PP t) = ψ PP ((c : kP PP) * t) := by
    intro PP hP
    refine GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal) (ψ PP)
      ((ψ (GlobalTheory.IdemSupport.cP PP)).compAddMonoidHom (GlobalTheory.SeeConjChar.conjRes PP).toAddMonoidHom) (hψ PP hP).1 ?_
    intro h1
    apply (hψ PP hP).2
    ext t
    obtain ⟨s, rfl⟩ := (GlobalTheory.SeeConjChar.conjRes PP).surjective t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ s) h1
    simpa using this
  choose! c hc using hc
  refine ⟨fun PP => (ψ PP).mulShift (-1), fun PP i j =>
    if (i.1 < D.R.rS ∨ (i.1 + 1 < D.R.rS + D.R.k ∧ GlobalTheory.SeeConjChar.sideAt X h PP = true)) then 1
    else if i.1 = D.R.rS + D.R.k then c PP else -c PP, ?_, ?_⟩
  · intro PP hP h1
    apply (hψ PP hP).1
    ext t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ (-t)) h1
    simpa [AddChar.mulShift_apply] using this
  · intro κ hS hK2
    have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
    rw [hdec κ hK, ← starRingEnd_apply, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [GlobalTheory.T.residue_levelCharacterArgument_at_typePlace R F X h hIs hGrp β hβ hred PP hP κ hS, GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum R F X h hIs hGrp β hβ hred PP hP κ hS hK2, hc PP hP,
      map_mul, ← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, AddChar.mulShift_apply]
    congr 1
    rw [Finset.mul_sum, ← neg_add, ← Finset.sum_add_distrib, neg_one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hE
    · unfold GlobalTheory.SeeConjChar.wA GlobalTheory.SeeConjChar.wB
      simp only [apply_ite (fun u : (kP PP)ˣ => (u : kP PP)), Units.val_one, Units.val_neg]
      split_ifs <;> first | (exfalso; tauto) | (push_cast; ring1) | omega | (simp_all <;> omega)
    · simp
