import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqThF

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

section Gen

open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)

theorem liftForm_lvlAct (hok : A3.fam3.Ok3 1) (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x) : A3.A.fam.amb.FL k s) =
      ∑ g : G, a.coeff g • A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.ok2.conj _ ((hok.ok2.lifts k s).hpos _) _ (hok.ok2.lifts k s).act _ _ a ha x

variable (R) in

theorem jV_sum (k : Fin D.R.m) (s : T) (c : G → D.what₂.LL) (v : G → A3.A.fam.amb.FL k s) :
    R.jV k s (∑ g, c g • v g) = ∑ g, D.what₂.embLL (c g) • R.jV k s (v g) :=
  (map_sum (R.jV k s) (fun g => c g • v g) Finset.univ).trans
    (Finset.sum_congr rfl fun g _ => (R.jV k s).map_smulₛₗ (c g) (v g))

variable (R) in

theorem extV_sum (k : Fin D.R.m) (s : T) (c : G → ℂ) (w : G → (R.HV k s).H) (y : GA D (Vc D k)) :
    R.extV k s (∑ g, c g • w g) y = ∑ g, c g • R.extV k s (w g) y := by
  have e := map_sum (R.extV k s) (fun g => c g • w g) Finset.univ
  refine (congrFun e y).trans ((Finset.sum_apply y Finset.univ _).trans (Finset.sum_congr rfl fun g _ => ?_))
  exact congrFun ((R.extV k s).map_smul (c g) (w g)) y

theorem extV_act {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks) (hM : R.IsModels) (hred : R.grp_red_L)
    (k : Fin D.R.m) (s : T) (g : G) {κ : GA D (Vc D k)} (hκ : IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) κ)
    (v : A.fam.amb.FL k s) (y : GA D (Vc D k)) :
    R.extV k s (R.jV k s (A.fam.amb.opL k s (Sum.inr g) v)) y =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ • R.extV k s (R.jV k s v) (y * κ) := by
  have e1 := Formalism.IndefR.Eqv.Act.jV_act R hM k s g v _ (Formalism.IndefR.Eqv.Act.red_of_liftV R hred k s g hκ)
  have e2 := Formalism.IndefR.Eqv.Act.ext_g0Act (R.cV k) (hM.cV k) (levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch
    ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩ κ hκ.1 rfl ((R.HV k s).e (R.jV k s v)) y
  have e3 := congrArg (fun f => (R.cV k).ext f y) e1
  have hch : ((((levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩)⁻¹ : ℂˣ) : ℂ) =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ := Units.val_inv_eq_inv_val _
  refine (Formalism.IndefR.Eqv.Act.extV_apply R k s _ y).trans (e3.trans (e2.trans ?_))
  exact congrArg₂ (fun (c : ℂ) (w : (R.cV k).W) => c • w) hch (Formalism.IndefR.Eqv.Act.extV_apply R k s _ (y * κ)).symm

theorem actRead_of (hM : R.toRealDat.IsModels) (hred : R.toRealDat.grp_red_L) (hok : A3.fam3.Ok3 1) : ActRead Y := by
  intro s h k a ha κ hκ x y
  have hr : ∀ x', adForm Y (Y.tup s) h k (ratForm Y k s x') =
      R.extV k s (R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x')) := fun x' => Y.mtRead k s h x'
  have e1 : R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x)) =
      ∑ g : G, D.what₂.embLL (a.coeff g) •
        R.jV k s (A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x)) :=
    (congrArg (R.jV k s) (liftForm_lvlAct hok k s a ha x)).trans (jV_sum R k s _ _)
  refine (congrFun (hr _) y).trans ((congrFun (congrArg (R.extV k s) e1) y).trans
    ((extV_sum R k s _ _ y).trans (Finset.sum_congr rfl fun g _ => ?_)))
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) (extV_act R.toRealDat hM hred k s g (hκ g) _ y)).trans ?_
  exact (smul_smul _ _ _).trans (congrArg _ (congrFun (hr x) (y * κ g)).symm)

end Gen

theorem actRead_at : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ =>
    actRead_of t.r.Y t.r.z.pins.char.base.models t.r.z.pins.char.base.grp.red_L t.r.intersectionNumber_baseChange.ok

end GlobalTheory.CenLocAt

end
