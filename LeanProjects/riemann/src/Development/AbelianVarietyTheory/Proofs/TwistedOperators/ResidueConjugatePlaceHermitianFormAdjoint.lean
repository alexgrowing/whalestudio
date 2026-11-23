import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjAdj
open GlobalTheory.SeeConjChar Matrix
variable {D : D7}

theorem hform_unitary {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) {M : GL n A} (hM : M ∈ Formalism.UG.UJ σ J) (u v : n → A) :
    Formalism.UG.hform σ J (M.val *ᵥ u) (M.val *ᵥ v) = Formalism.UG.hform σ J u v := by
  have e2 : ∀ a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (M.val *ᵥ u) = (σ ∘ u) ᵥ* Formalism.UG.cT σ M.val := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  have hM' : Formalism.UG.cT σ M.val * J * M.val = J := hM
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM']

theorem eq_of_kill {R : Type} [CommRing R] (PP : Pl D.host.E) (f : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hf : ∀ p ∈ PP.asIdeal, f (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (b : 𝓞 D.host.E) (hb : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal) :
    f s = f (oToS D.host.F D.host.E b) := by
  have hle : idS D.host.F PP.asIdeal ≤ RingHom.ker f := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    exact hf p hp
  have := hle hb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact this

theorem ext_oToS {R : Type} [CommRing R] (PP : Pl D.host.E) (f g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hfg : ∀ a, f (oToS D.host.F D.host.E a) = g (oToS D.host.F D.host.E a))
    (hg : ∀ p ∈ PP.asIdeal, g (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    f s = g s := by
  obtain ⟨bq, hb⟩ := cmpS_surj (F := D.host.F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
  change Ideal.Quotient.mk _ (oToS D.host.F D.host.E b) = _ at hb
  have hb' : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal := by
    rw [← Ideal.Quotient.eq]
    exact hb.symm
  have h1 := eq_of_kill PP f (fun p hp => (hfg p).trans (hg p hp)) s b hb'
  have h2 := eq_of_kill PP g hg s b hb'
  rw [h1, h2, hfg]

noncomputable def cjS (D : D7) : Formalism.L2.Herm.intAf D.host.F D.host.E →+* Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D).restrict (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun _ h => GlobalTheory.AdIsom.cjA_mem h)

theorem cjS_oToS (a : 𝓞 D.host.E) :
    cjS D (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) := Subtype.ext rfl

theorem resT_cjA (PP : Pl D.host.E) (z : EAf D) :
    resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z) = conjRes PP (resT PP z) := by
  by_cases hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.AdIsom.cjA_mem hz
    rw [resT, dif_pos hz', resT, dif_pos hz]
    let f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (resS D.host.F (GlobalTheory.IdemSupport.cP PP)).comp (cjS D)
    let f2 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (conjRes PP).toRingHom.comp (resS D.host.F PP)
    have hO : ∀ a : 𝓞 D.host.E, f1 (oToS D.host.F D.host.E a) = f2 (oToS D.host.F D.host.E a) := by
      intro a
      show resS D.host.F (GlobalTheory.IdemSupport.cP PP) (cjS D (oToS D.host.F D.host.E a)) =
        conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E a))
      rw [cjS_oToS, resS_oToS, resS_oToS]
      exact (Ideal.quotientEquiv_mk _ _ _ _ _).symm
    have hg : ∀ p ∈ PP.asIdeal, f2 (oToS D.host.F D.host.E p) = 0 := by
      intro p hp
      show conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E p)) = 0
      rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    have hfin := ext_oToS PP f1 f2 hO hg ⟨z, hz⟩
    have e : (⟨GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = cjS D ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact hfin
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∉ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun h => hz (GlobalTheory.AdIsom.cjA_mem_iff.1 h)
    rw [resT, dif_neg hz', resT, dif_neg hz, map_zero]

theorem resCP_adjoint : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) (κ : GA D (Yc D 0)) (x y : Fin (Yc D 0).rank → EAf D), (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y)) = GlobalTheory.SeeConjChar.conjRes PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x))) := by
  intro D X h PP κ x y
  have hH : ∀ u v, GlobalTheory.SeeConjChar.hT X h u v =
      Formalism.UG.hform (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) u v := by
    intro u v
    obtain ⟨⟨I⟩⟩ := X
    dsimp only at h
    subst h
    rfl
  have hU : finE (Yc D 0) κ ∈
      Formalism.UG.UJ (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) := by
    have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    rw [(Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ] at hf
    have := ((Formalism.IndefR.RationalEmbedding.iota D κ).2).2
    exact hf ▸ this
  have key : GlobalTheory.SeeConjChar.hT X h x ((finE (Yc D 0) κ).val *ᵥ y) =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D (GlobalTheory.SeeConjChar.hT X h y (((finE (Yc D 0) κ)⁻¹).val *ᵥ x)) := by
    rw [hH, hH]
    have e1 : x = (finE (Yc D 0) κ).val *ᵥ (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have e2 := GlobalTheory.AdIsom.cjA_hA (Yc D 0) (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hA] at e2
    rw [e2]
    conv_lhs => rw [e1]
    exact hform_unitary _ _ hU _ _
  rw [key]
  exact ⟨GlobalTheory.AdIsom.cjA_mem_iff, resT_cjA PP _⟩

end GlobalTheory.SeeConjAdj
