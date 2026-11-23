import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegralStatement

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory NumberField IsDedekindDomain
open scoped Matrix TensorProduct

namespace GlobalTheory.CompanionTheory.SwFinM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def compV (v : HeightOneSpectrum (𝓞 F)) :
    (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) →ₐ[F] (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E)

theorem matV_eq (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (h : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v h = (compV v).mapMatrix h := rfl

theorem repr_map {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (f : A →ₐ[F] B) {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (x : A ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis B bs).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) k =
      f ((Algebra.TensorProduct.basis A bs).repr x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem ev_int (y : HeckeCharacterZeroLocus.SiegelWeilU.AF F) :
    ∀ᶠ v in Filter.cofinite, HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (HeckeCharacterZeroLocus.SiegelWeilU.sndA F y) ∈ v.adicCompletionIntegers F :=
  (HeckeCharacterZeroLocus.SiegelWeilU.sndA F y).2

theorem comp_mem_Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, compV v x ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := by
  have h := Filter.eventually_all.2 fun k => ev_int (F := F) ((Algebra.TensorProduct.basis _ bs).repr x k)
  filter_upwards [h] with v hv k
  rw [compV, repr_map]
  exact hv k

theorem matV_mem_Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, ∀ i j, PositivityTheory.SiegelWeilFormula.Gen.matV v X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => comp_mem_Rv bs (X i j)

theorem intAt_eventually {d : ℕ} (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet (AlgHom.id F E) bs) :=
  GlobalTheory.T.unramified_finite_integral F _

section Lat

variable {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_ringOf {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs))
    (x : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) : x ∈ GlobalTheory.CompanionTheory.RvRingPf.ringOf h ↔ x ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := Iff.rfl

theorem mulVec_mem_latO {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs)) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hX : ∀ i j, X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v)
    (y : Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (hy : y ∈ PositivityTheory.PfSWUS.Loc.latO bs v) :
    X *ᵥ y ∈ PositivityTheory.PfSWUS.Loc.latO bs v := by
  have hy' : ∀ j, y j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := (GlobalTheory.CompanionTheory.SiegLoc.NuIndex.mem_latO_iff bs v y).1 hy
  refine (GlobalTheory.CompanionTheory.SiegLoc.NuIndex.mem_latO_iff bs v _).2 fun i => ?_
  have e : (X *ᵥ y) i = ∑ j, X i j * y j := rfl
  rw [e]
  have hs : (∑ j, X i j * y j) ∈ GlobalTheory.CompanionTheory.RvRingPf.ringOf h :=
    Subring.sum_mem _ fun j _ => Subring.mul_mem _ ((mem_ringOf h _).2 (hX i j)) ((mem_ringOf h _).2 (hy' j))
  exact (mem_ringOf h _).1 hs

theorem image_latO {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs)) {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hX : ∀ i j, X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v)
    (hY : ∀ i j, Y i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v) (hXY : X * Y = 1) :
    (fun y => X *ᵥ y) '' PositivityTheory.PfSWUS.Loc.latO bs v = PositivityTheory.PfSWUS.Loc.latO bs v := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mulVec_mem_latO h X hX y hy
  · intro hz
    refine ⟨Y *ᵥ z, mulVec_mem_latO h Y hY z hz, ?_⟩
    show X *ᵥ (Y *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec]

end Lat

end GlobalTheory.CompanionTheory.SwFinM

end
