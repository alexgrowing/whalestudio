import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd

theorem isIntegral_mulVec {E : Type} [Field E] {m n : ℕ} (M : Matrix (Fin m) (Fin n) E)
    (hM : ∀ i j, IsIntegral ℤ (M i j)) (x : Fin n → E) (hx : ∀ k, IsIntegral ℤ (x k)) (k : Fin m) :
    IsIntegral ℤ ((M *ᵥ x) k) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem (integralClosure ℤ E) fun l _ => (hM k l).mul (hx l)

theorem isIntegral_ite {E : Type} [Field E] (p : Prop) [Decidable p] :
    IsIntegral ℤ (if p then (1 : E) else 0) := by
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

theorem orthAt_oTop : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) (n : ℕ) (h : n = (I.rec7 l Z).R.m) (x : GlobalTheory.FinPl.Pl (I.rec7 l Z)), GlobalTheory.FinPl.OrthAt (GlobalTheory.XGeoStd.oTop l Z hI n h) (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X n)) (GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X') (GlobalTheory.PlaceModel.latFrame (GlobalTheory.XGeoStd.lineZ (I.rec7 l Z))) x := by
  intro B X I l Z hI n h x
  subst h
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have hS : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.PinInhab.lat_X hI]; rfl
  have hA : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X' ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hs _ h2]; rfl
  have hB : ∀ y, y ∈ GlobalTheory.PlaceModel.latFrame (lineZ (I.rec7 l Z)) ↔ ∀ k, IsIntegral ℤ (y k) := fun y => by
    rw [← SetLike.mem_coe, GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ Examples₂.star_isIntegral 1 rfl]; rfl
  have ho : oTop l Z hI _ rfl = GlobalTheory.AdForm.LiveModel.topDec (GlobalTheory.AdForm.PinInhab.gram_X hI _) (gram_X' hI) := rfl
  rw [ho]
  set o := GlobalTheory.AdForm.LiveModel.topDec (GlobalTheory.AdForm.PinInhab.gram_X (l := l) (Z := Z) hI (I.rec7 l Z).R.m) (gram_X' hI)
  have iA_int : ∀ i j, IsIntegral ℤ (o.iA i j) := fun i j => by
    simp only [o, GlobalTheory.AdForm.LiveModel.topDec, Matrix.of_apply]; exact isIntegral_ite _
  have iB_int : ∀ i j, IsIntegral ℤ (o.iB i j) := fun i j => by
    simp only [o, GlobalTheory.AdForm.LiveModel.topDec, Matrix.of_apply]; exact isIntegral_ite _
  have qA_eq : o.qA = o.iAᴴ := by
    rw [OrthDec.qA, gram_X' hI, GlobalTheory.AdForm.PinInhab.gram_X hI, inv_one, Matrix.one_mul, Matrix.mul_one]
  have qB_eq : o.qB = o.iBᴴ := by
    rw [OrthDec.qB, GlobalTheory.AdForm.PinInhab.gram_X hI, GlobalTheory.AdForm.LiveModel.gram_pos, inv_one, Matrix.one_mul, Matrix.mul_one]
  have qA_int : ∀ i j, IsIntegral ℤ (o.qA i j) := fun i j => by
    rw [qA_eq, Matrix.conjTranspose_apply]; exact hs _ (iA_int j i)
  have qB_int : ∀ i j, IsIntegral ℤ (o.qB i j) := fun i j => by
    rw [qB_eq, Matrix.conjTranspose_apply]; exact hs _ (iB_int j i)
  intro y
  constructor
  · intro hy
    refine ⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun z hz => ?_) _ hy,
      GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun z hz => ?_) _ hy⟩
    · exact (hA _).2 (isIntegral_mulVec _ qA_int z ((hS z).1 hz))
    · exact (hB _).2 (isIntegral_mulVec _ qB_int z ((hS z).1 hz))
  · rintro ⟨hyA, hyB⟩
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
      have := o.sum_eq_one
      rw [show o.jA * o.pA + o.jB * o.pB = 1 from this, Matrix.one_mulVec]
    rw [e]
    refine add_mem (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA (fun z hz => ?_) _ hyA)
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB (fun z hz => ?_) _ hyB)
    · exact (hS _).2 (isIntegral_mulVec _ iA_int z ((hA z).1 hz))
    · exact (hS _).2 (isIntegral_mulVec _ iB_int z ((hB z).1 hz))

end GlobalTheory.XGeoStd

end
