import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces

noncomputable section

namespace GlobalTheory.SeeSaw.LevMem

section Columns

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.LevRead GlobalTheory.Mem.Col2.TC.GLev0 Matrix
open scoped TensorProduct

section Pts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsInt (m : GL (Fin n) (AfE F E)) : Prop := (∀ i j, m.1 i j ∈ RInt F E) ∧ ∀ i j, (m⁻¹).1 i j ∈ RInt F E

theorem isInt_of {m : GL (Fin n) (AfE F E)} (h : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (m.1 *ᵥ z) i ∈ RInt F E) :
    IsInt m := by
  have h1 : ∀ j i, (Pi.single j 1 : Fin n → AfE F E) i ∈ RInt F E := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => by simpa using (h _).1 (h1 j) i, fun i j => ?_⟩
  have := (h ((m⁻¹).1 *ᵥ Pi.single j 1)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact h1 j) i
  simpa using this

def LastOne (P : HeightOneSpectrum (𝓞 E)) (m : GL (Fin n) (AfE F E)) : Prop :=
  ∀ r : Fin n, r.1 + 1 = n → ∀ j, HasRes P (adAt F P (m.1 r j)) (if j = r then 1 else 0)

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

end Pts

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end Columns

section LocalField

open ValuativeRel IsLocalRing Matrix GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos Reduces)

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

end LocalField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge

section Adelic

variable {D : D7}

theorem mem_latHat_iff {n : ℕ} {L : Set (Fin n → D.host.E)} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D n)
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) : z ∈ latHat D.host.F D.host.E L ↔ ∀ i, z i ∈ intAE D := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (hL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (hL _).2 fun j => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [x.isIntegral_coe, isIntegral_zero]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

set_option maxHeartbeats 1000000 in

theorem moves_iff {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D V.rank) {κ : GA D V} {n : ℕ} (hn : V.rank = n)
    {y : GL (Fin n) (EF D)} (hy : finM V hn κ = y.1) :
    GlobalTheory.FinPl.Moves V κ L L (fun _ => True) ↔ IsInt (F := D.host.F) (E := D.host.E) y := by
  subst hn
  have h1 : ∀ a : Fin V.rank → AE D, (∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True) →
      (a ∈ GlobalTheory.FinPl.latV V L (fun _ => True) ↔ ∀ i, toEAf D (a i) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E) := fun a ha =>
    (GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ a ha).trans ((mem_latHat_iff hL _).trans
      (forall_congr' fun i => GlobalTheory.IdemSupport.mem_intAE_iff _))
  have h2 : ∀ (a : Fin V.rank → AE D) i, toEAf D ((mt V κ *ᵥ a) i) = (y.1 *ᵥ fun j => toEAf D (a j)) i := fun a i => by
    rw [← hy]
    exact RingHom.map_mulVec (toEAf D) _ a i
  constructor
  · intro h
    refine isInt_of fun z => ?_
    let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
    choose a ha ha' using fun i => GlobalTheory.KStabBridge.exists_fin_lift (D := D) (sw.symm (z i))
    have hz : ∀ i, toEAf D (a i) = z i := fun i => (congrArg sw (ha' i)).trans (sw.apply_symm_apply _)
    have hi : ∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True := fun i =>
      Submodule.mem_inf.2 ⟨ha i, (Submodule.mem_iInf _).2 fun u => absurd trivial u.2⟩
    have := h a hi
    rw [h1 a hi, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ hi)] at this
    simp only [h2, hz] at this
    exact this
  · intro h a ha
    rw [h1 a ha, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ ha)]
    simp only [h2]
    refine ⟨PtExist.mulVec_int h.1, fun h' i => ?_⟩
    have := PtExist.mulVec_int h.2 h' i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

section Split

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

end Split

variable {u : D.what₂.Word} {a : XPart D u}

def ColAt {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) (κ : GA D (D.sp.X 0)) : Prop :=
  H.mat0 κ ∈ colGroup H.k D.R.k (Fin D.R.t)

end Adelic

end GlobalTheory.SeeSaw.LevMem

end
