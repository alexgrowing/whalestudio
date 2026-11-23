import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctSat :
    UpperTheory.V.Cj.S.CtSat := by
  intro E _ _ _ n r φ ψ hφ hψ h0 w B hB
  let C : Submodule ℂ (Sm E n) :=
    { carrier := {f | Continuous f.1}
      add_mem' := fun h h' => Continuous.add h h'
      zero_mem' := continuous_const
      smul_mem' := fun c _ h => Continuous.const_smul h c }
  have hC : ∀ g, ∀ f ∈ C, fL n w g f ∈ C := fun g f hf =>
    show Continuous fun x => f.1 (x * finGL E n (locGL E n w g)) from
      Continuous.comp (show Continuous f.1 from hf) (continuous_id.mul continuous_const)
  have hc : φ ∈ C := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  let F : C →ₗ[ℂ] (GA E n → ℂ) :=
    { toFun := fun f => constantTerm r f.1.1
      map_add' := fun f f' => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_add f.2 f'.2 g
      map_smul' := fun c f => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_smul c f.1.1 g }
  have h1 : IsSatVecGL w (GlobalTheory.PRep.sub (fL n w) C hC) ⟨φ, hc⟩ B :=
    IsSatVecGL.of_map C.subtype (fun _ _ => rfl) Subtype.val_injective hB
  have hF : F ⟨φ, hc⟩ = ψ.1 := hψ.symm
  have h2 := h1.map (ρ' := (GlobalTheory.PRep.rightReg ℂ (GA E n) ℂ).comp ((finGL E n).comp (locGL E n w))) F
    (fun g f => funext fun x =>
      GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate f.1.1 (finGL E n (locGL E n w g)) x)
    (by rw [hF]; exact fun h => h0 (Subtype.ext h))
  rw [hF] at h2
  exact IsSatVecGL.of_map (Sm E n).subtype (fun _ _ => rfl) Subtype.val_injective h2
