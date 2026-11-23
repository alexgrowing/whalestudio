import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ptEx' (d : SD σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  have hone : incM F (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hPQ : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.mul_inv, hone]
  have hQP : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.inv_mul, hone]
  have hM'M : ∀ c, M' c * M c = 1 := fun c => by
    first
    | exact mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_symm (h c)
  let N : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M c * incM F (d.b⁻¹).1
  let N' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M' c * incM F (d.b⁻¹).1
  have hNN' : ∀ c, N c * N' c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M c) (M' c), h c, Matrix.one_mul, hPQ]
  have hN'N : ∀ c, N' c * N c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M' c) (M c), hM'M c, Matrix.one_mul, hPQ]
  let u : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨N c, N' c, hNN' c, hN'N c⟩
  have mem : ∀ c, u c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε (M c) (M' c) (h c) (hu c)
    have hx' : x.1.1 = N c := by
      show x.1.1 = incM F d.b.1 * M c * incM F (d.b⁻¹).1
      rw [← hx]
      show x.1.1 = incM F d.b.1 * (incM F (d.b⁻¹).1 * x.1.1 * incM F d.b.1) * incM F (d.b⁻¹).1
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    have e : u c = x.1 := Units.ext hx'.symm
    rw [e]
    exact x.2
  refine ⟨fun c => ⟨u c, mem c⟩, ?_, ?_⟩
  · apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · intro c
    show incM F (d.b⁻¹).1 * N c * incM F d.b.1 = M c
    simp only [N, Matrix.mul_assoc]
    rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

end PositivityTheory.SiegelWeilFormula.Act.CL

end
