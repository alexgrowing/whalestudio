import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceStabilizerPartialProductsFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinsetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology

namespace GlobalTheory.StabSetFix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stab_fix_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop), (∀ v, P v → Tame D v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT hS hT P hP f hf κ κ' hκ hκ'
  have hloc := ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ S T χS χT om hW LS LT hS hT P (fun v hv => (hP v hv).1) f).1.1 hf)
  have one_inK : ∀ (V : HSp D) (L : Lat V) (v : Pl D), InK V L (· = v) 1 := by
    intro V L v
    refine ⟨one_mem _, fun y _ => ?_⟩
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.one_mulVec]
  have single : ∀ v, P v → ∀ y y', InK S LS (· = v) y → InK T LT (· = v) y' → om (y, y') f = f :=
    fun v hv y y' hy hy' => GlobalTheory.VacStabFixed.vacFixedAt D v ψ S T χS χT om hW (hP v hv).2.1 (hP v hv).2.2 LS LT hS hT f
      hloc.1 (hloc.2 v hv).2 y y' (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D S LS v y hS hy) (GlobalTheory.T.inLatticeStabilizerAtPlace_of_supportedStabilizer D T LT v y' hT hy')
  have listS : ∀ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S LS (· = v) y) → om (l.prod, 1) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : ((y * l.prod, (1 : GA D T)) : GA D S × GA D T) = (y, 1) * (l.prod, 1) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv y 1 hy (one_inK T LT v)]
  have listT : ∀ l : List (GA D T), (∀ y ∈ l, ∃ v, P v ∧ InK T LT (· = v) y) → om (1, l.prod) f = f := by
    intro l
    induction l with
    | nil => intro _; rw [List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
    | cons y l ih =>
      intro h
      obtain ⟨v, hv, hy⟩ := h y (List.mem_cons_self ..)
      have e : (((1 : GA D S), y * l.prod) : GA D S × GA D T) = (1, y) * (1, l.prod) := by simp
      rw [List.prod_cons, e, map_mul, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        single v hv 1 y (one_inK S LS v) hy]
  choose lS hlS hiS hinS houtS using GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet D S LS P κ hS hκ
  choose lT hlT hiT hinT houtT using GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet D T LT P κ' hT hκ'
  have tS := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D S κ (fun Fs => (lS Fs).prod) hiS hinS houtS
  have tT := GlobalTheory.T.tendsto_unitaryAdelicPoints_agree_on_growing_finset D T κ' (fun Fs => (lT Fs).prod) hiT hinT houtT
  funext w
  have hc := ((hW.om_cont f hloc.1 w).tendsto (κ, κ')).comp (tS.prodMk_nhds tT)
  have heq : ∀ Fs, f w = ((fun p : GA D S × GA D T => om p f w) ∘ fun Fs => ((lS Fs).prod, (lT Fs).prod)) Fs := by
    intro Fs
    have e : (((lS Fs).prod, (lT Fs).prod) : GA D S × GA D T) = ((lS Fs).prod, 1) * (1, (lT Fs).prod) := by simp
    simp only [Function.comp_apply]
    rw [e, map_mul, Module.End.mul_apply, listT _ (hlT Fs), listS _ (hlS Fs)]
  exact tendsto_nhds_unique hc (tendsto_const_nhds.congr heq)

end GlobalTheory.StabSetFix
