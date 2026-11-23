import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

private theorem det_aE {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) :
    Matrix.GeneralLinearGroup.det (aE (E := F) a) = a := by
  ext
  simp [aE, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]

theorem UpperTheory.ConvolutionTheory.R2.D.genE :
    ∀ (F : Type) [Field F] [NumberField F], Subgroup.closure (Set.range (fun b => gl (nU (F := F) b)) ∪ {gl (wW F)} ∪ Set.range (aE (E := F))) = ⊤ := by
  intro F _ _
  rw [eq_top_iff]
  intro h _
  set C := Subgroup.closure (Set.range (fun b => gl (nU (F := F) b)) ∪ {gl (wW F)} ∪ Set.range (aE (E := F))) with hC
  have hSL : ∀ s : G1 F, gl s ∈ C := by
    intro s
    have hs : s ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
      rw [(UpperTheory.ConvolutionTheory.R2.gen F).1]
      trivial
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
      apply Subgroup.subset_closure
      rcases hx with ⟨b, rfl⟩ | hx
      · exact Or.inl (Or.inl ⟨b, rfl⟩)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Or.inl (Or.inr rfl)
    | one => simpa using C.one_mem
    | mul x y _ _ hx hy => simpa using C.mul_mem hx hy
    | inv x _ hx => simpa using C.inv_mem hx
  have hA : ∀ a, aE (E := F) a ∈ C := fun a => Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  set d := Matrix.GeneralLinearGroup.det h with hd
  have hdet : Matrix.det (h * (aE (E := F) d)⁻¹).val = 1 := by
    have : Matrix.GeneralLinearGroup.det (h * (aE (E := F) d)⁻¹) = 1 := by
      rw [map_mul, map_inv, det_aE, ← hd, mul_inv_cancel]
    exact congrArg Units.val this
  have hs : gl (⟨(h * (aE (E := F) d)⁻¹).val, hdet⟩ : G1 F) = h * (aE (E := F) d)⁻¹ := by
    ext i j
    rfl
  have h1 : h * (aE (E := F) d)⁻¹ ∈ C := hs ▸ hSL _
  have := C.mul_mem h1 (hA d)
  simpa using this
