import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiSRfl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralAdeleCongrZeroOfResiduesSquarefreeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConjStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairSlotStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterResidueFieldsEqProdGenericShiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjProd
open Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis Formalism.L2.SG.HidaSetting
open scoped TensorProduct
variable {D : D7}

theorem sigInt_oToS (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem conjRes_mk (PP : Pl D.host.E) (x : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (Ideal.Quotient.mk PP.asIdeal x) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cO D x) := rfl

theorem conj_res_oToS (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) (oToS D.host.F D.host.E a))) =
      Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a := by
  rw [sigInt_oToS, resS_oToS, conjRes_mk, GlobalTheory.IdemSupport.cO_cO]

theorem resS_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F (GlobalTheory.IdemSupport.cP PP) s =
      GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) s)) := by
  set f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
    (GlobalTheory.SeeConjChar.conjRes PP).toRingHom.comp ((resS D.host.F PP).comp (sigInt (instOf D))) with hf
  have hf0 : ∀ x, f1 x = GlobalTheory.SeeConjChar.conjRes PP (resS D.host.F PP (sigInt (instOf D) x)) := fun x => rfl
  have hf1 : ∀ a, f1 (oToS D.host.F D.host.E a) = Ideal.Quotient.mk (GlobalTheory.IdemSupport.cP PP).asIdeal a :=
    fun a => (hf0 _).trans (conj_res_oToS PP a)
  have hker : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker f1 := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hf1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  obtain ⟨a, ha⟩ := (cmpS_bij (F := D.host.F) (GlobalTheory.IdemSupport.cP PP).asIdeal (GlobalTheory.IdemSupport.cP PP).ne_bot).2
    (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have e : Ideal.Quotient.mk (idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal) s =
      Ideal.Quotient.mk _ (oToS D.host.F D.host.E a) := ha.symm
  have hd : s - oToS D.host.F D.host.E a ∈ idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal := Ideal.Quotient.eq.1 e
  have hker2 : idS D.host.F (GlobalTheory.IdemSupport.cP PP).asIdeal ≤ RingHom.ker (resS D.host.F (GlobalTheory.IdemSupport.cP PP)) := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, resS_oToS]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hc
  have h2 : resS D.host.F (GlobalTheory.IdemSupport.cP PP) s = resS D.host.F (GlobalTheory.IdemSupport.cP PP) (oToS D.host.F D.host.E a) := by
    have := hker2 hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  have h1 : f1 s = f1 (oToS D.host.F D.host.E a) := by
    have := hker hd
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact h2.trans ((resS_oToS _ a).trans ((hf1 a).symm.trans (h1.symm.trans (hf0 s))))

theorem exists_addChar_ne_one (k : Type) [Field k] [Finite k] : ∃ ψ : AddChar k ℂ, ψ ≠ 1 := by
  have h1 : Multiplicative.ofAdd (1 : k) ≠ 1 := by
    intro h
    exact one_ne_zero (congrArg Multiplicative.toAdd h)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative k) ℂ h1
  let ψ : AddChar k ℂ :=
    { toFun := fun x => ((φ (Multiplicative.ofAdd x) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by simp [ofAdd_add] }
  refine ⟨ψ, fun h => hφ (Units.ext ?_)⟩
  have := congrArg (fun χ : AddChar k ℂ => χ 1) h
  simpa [ψ] using this

theorem addChar_comp_ne_one {k k' : Type} [Field k] [Field k'] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) (ha : a ≠ 0)
    (e : k' ≃+* k) : ψ.compAddMonoidHom ((AddMonoidHom.mulLeft a).comp e.toAddMonoidHom) ≠ 1 := by
  intro h
  apply hψ
  ext t
  have := congrArg (fun χ : AddChar k' ℂ => χ (e.symm (a⁻¹ * t))) h
  change ψ (a * e (e.symm (a⁻¹ * t))) = (1 : AddChar k' ℂ) (e.symm (a⁻¹ * t)) at this
  rw [RingEquiv.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, AddChar.one_apply] at this
  rw [this, AddChar.one_apply]

theorem cP_cP (P : Pl D.host.E) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem sigInt_sigInt (s : Formalism.L2.Herm.intAf D.host.F D.host.E) : sigInt (instOf D) (sigInt (instOf D) s) = s :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA (instOf D) s.1)

theorem conjRes_cP (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) =
      resS D.host.F (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (sigInt (instOf D) s) := by
  rw [resS_cP (GlobalTheory.IdemSupport.cP PP) (sigInt (instOf D) s), sigInt_sigInt]

open Classical in

theorem core (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E,
      psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (Pg : Finset (Pl D.host.E)) (hdiv : ∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hcov : ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') :
    ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
      ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
        psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) =
          ∏ PP ∈ Pg, ψ PP (resS D.host.F PP s) *
            ψ (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s) := by
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | rfl⟩ := hcov Q hQ
    · exact (hs _ hPP).1
    · exact (resS_cP PP s).trans (by rw [(hs _ hPP).2]; exact map_zero _)
  choose ψ0 hψ0 using fun P : Pl D.host.E => exists_addChar_ne_one (kP P)
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ψ0 (fun PP _ => hψ0 PP)
    (fun s t => (congrArg psiEf (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans
      (hadd _ _))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) = 1
      rw [this, hint t ht])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hdiv hnc (fun s => psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1)
      fun Q hQ => GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ)
  have hout : ∀ PP ∈ Pg, GlobalTheory.IdemSupport.cP PP ∉ Pg := fun PP hPP h =>
    hnc PP hPP _ h ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
  let ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ := fun P =>
    if P ∈ Pg then (ψ0 P).compAddMonoidHom ((AddMonoidHom.mulLeft (a₁ P)).comp (RingEquiv.refl (kP P)).toAddMonoidHom)
    else if GlobalTheory.IdemSupport.cP P ∈ Pg then (ψ0 (GlobalTheory.IdemSupport.cP P)).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP P))).comp (GlobalTheory.SeeConjChar.conjRes P).toAddMonoidHom)
    else 1
  have hψ1 : ∀ PP ∈ Pg, ψ PP = (ψ0 PP).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₁ PP)).comp (RingEquiv.refl (kP PP)).toAddMonoidHom) := fun PP hPP => if_pos hPP
  have hψ2 : ∀ PP ∈ Pg, ψ (GlobalTheory.IdemSupport.cP PP) = (ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP))).compAddMonoidHom
      ((AddMonoidHom.mulLeft (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)))).comp
        (GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP)).toAddMonoidHom) := fun PP hPP => by
    have h2 : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP) ∈ Pg := by rw [cP_cP]; exact hPP
    exact (if_neg (hout PP hPP)).trans (if_pos h2)
  refine ⟨ψ, fun PP hPP => ⟨?_, ?_⟩, fun s => ?_⟩
  · rw [hψ1 PP hPP]
    exact addChar_comp_ne_one _ (hψ0 PP) _ (ha PP hPP).1 _
  · rw [hψ2 PP hPP]
    refine addChar_comp_ne_one _ (hψ0 _) _ ?_ _
    rw [cP_cP]
    exact (ha PP hPP).2
  · refine (hχ s).trans (Finset.prod_congr rfl fun PP hPP => ?_)
    refine (AddChar.map_add_eq_mul (ψ0 PP) _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · rw [hψ1 PP hPP]
      rfl
    rw [hψ2 PP hPP]
    show _ = ψ0 (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) (a₂ (GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP PP)) *
      GlobalTheory.SeeConjChar.conjRes (GlobalTheory.IdemSupport.cP PP) (resS D.host.F (GlobalTheory.IdemSupport.cP PP) s))
    rw [conjRes_cP]
    have key : ∀ Q : Pl D.host.E, Q = PP → ψ0 Q (a₂ Q * resS D.host.F Q (sigInt (instOf D) s)) =
        ψ0 PP (a₂ PP * resS D.host.F PP (sigInt (instOf D) s)) := by
      rintro Q rfl
      rfl
    exact (key _ (cP_cP PP)).symm

theorem chiS_eq_prod : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, GlobalTheory.SeeConjChar.chiS X h c = ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
  intro D X h Pg hdiv hcov hnc
  have key : ∀ (I : AutInst) (hI : I = instOf D) (g : ℕ) (_ : g = D.host.g 0 * D.host.g 1)
      (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ) (_ : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
      (_ : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
      (_ : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1),
      ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧
        ∀ c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
          psiEf (divN I g (cast (congrArg (fun I : AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) hI).symm c)) =
            ∏ PP ∈ Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP c) *
              ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) c) := by
    intro I hI g hg psiEf hadd hint hrat
    subst hI hg
    obtain ⟨ψ, hψ, hprod⟩ := core psiEf hadd hint hrat Pg hdiv hcov hnc
    refine ⟨ψ, hψ, fun c hc => ?_⟩
    have e1 : ∀ P : Pl D.host.E, GlobalTheory.SeeConjChar.resT P c = resS D.host.F P ⟨c, hc⟩ := fun P => dif_pos hc
    simp only [e1, cast_eq]
    exact hprod ⟨c, hc⟩
  exact key X.B.I h X.B.g X.g_eq X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat

end GlobalTheory.SeeConjProd
