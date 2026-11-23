import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.LatStd

open NumberField IsDedekindDomain Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem map_comp_apply_evalV (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
        (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp; rfl
  | add y z hy hz => simp only [map_add, hy, hz]

theorem eventually_matV_mem_intLoc {n : ℕ} (h : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ a c, PositivityTheory.SiegelWeilFormula.Gen.matV v h a c ∈ intLoc F E v :=
  eventually_all.2 fun a => eventually_all.2 fun c => by
    filter_upwards [eventually_map_evalV_mem_intLoc
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) (h a c))] with v hv
    change Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E) (h a c) ∈ _
    rw [map_comp_apply_evalV]
    exact hv

omit [NumberField E] in

theorem matV_mul_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {h h' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    (hh : h * h' = 1) : PositivityTheory.SiegelWeilFormula.Gen.matV v h * PositivityTheory.SiegelWeilFormula.Gen.matV v h' = 1 := by
  have e := map_mul (AlgHom.mapMatrix (m := Fin n) (Algebra.TensorProduct.map
    ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E))) h h'
  rw [hh, map_one] at e
  exact e.symm

omit [NumberField E] in

theorem mulVec_mem_intLoc {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {M : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)}
    (hM : ∀ a c, M a c ∈ intLoc F E v) {x : Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E} (hx : ∀ c, x c ∈ intLoc F E v)
    (a : Fin n) : M.mulVec x a ∈ intLoc F E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun c _ => mul_mem (hM a c) (hx c)

theorem eventually_map_latLoc_eq_latO {n d : ℕ} {h h' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} (hh : h * h' = 1)
    (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      (((latLoc F (stdLattice E n) v).toAddSubgroup.map
        (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v h)).toAddMonoidHom : AddSubgroup _) :
          Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v := by
  filter_upwards [GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr bs, eventually_matV_mem_intLoc h,
    eventually_matV_mem_intLoc h'] with v hb h1 h2
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := mem_latLoc_stdLattice.1 hx
    intro a k
    refine (hb _).1 ?_ k
    exact mulVec_mem_intLoc h1 hx' a
  · intro hy
    have hy' : ∀ a, y a ∈ intLoc F E v := fun a => (hb _).2 (hy a)
    refine ⟨(PositivityTheory.SiegelWeilFormula.Gen.matV v h').mulVec y,
      mem_latLoc_stdLattice.2 (mulVec_mem_intLoc h2 hy'), ?_⟩
    change (PositivityTheory.SiegelWeilFormula.Gen.matV v h).mulVec ((PositivityTheory.SiegelWeilFormula.Gen.matV v h').mulVec y) = y
    rw [Matrix.mulVec_mulVec, matV_mul_eq_one v hh, Matrix.one_mulVec]

theorem latAt_eq_latO : ∀ (D : D7) (n : ℕ) (h : GL (Fin n) (AE D)) (d : ℕ) (bs : Module.Basis (Fin d) D.host.F D.host.E), ∀ᶠ v in Filter.cofinite, ((latAt h.1 v : AddSubgroup _) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) = PositivityTheory.PfSWUS.Loc.latO bs v := by
  intro D n h d bs
  have hh : h.1 * (h⁻¹).1 = 1 := by simp
  exact eventually_map_latLoc_eq_latO hh bs

end GlobalTheory.CompanionTheory.MM.LatStd
