import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.IrrAbs
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.irrCo :
    UpperTheory.V.Cj.IrrCo := by
  intro E _ _ _ a π τ hτ Ξ q P hP hst hV
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.2 hP
  haveI : Module.Finite ℝ (Herm E a) := inferInstance
  let b := Module.finBasis ℝ (Herm E a)
  let ρW : Representation ℂ (GL (Fin a) (Af E)) P :=
    { toFun := fun x => (transRep Ξ q x).restrict (fun ω hω => hst x ω hω)
      map_one' := LinearMap.ext fun w => Subtype.ext (by simp)
      map_mul' := fun x y => LinearMap.ext fun w =>
        Subtype.ext (LinearMap.congr_fun (map_mul (transRep Ξ q) x y) w.1) }
  let p : (Fin q → Fin (Module.finrank ℝ (Herm E a))) × Fin Ξ.d → P →ₗ[ℂ] π.V := fun j =>
    { toFun := fun w => ⟨Bor.cmp j.2 (w.1 fun k => b (j.1 k)), mem_tens.1 (hV w.1 w.2 _) j.2⟩
      map_add' := fun x y => Subtype.ext (by
        change Bor.cmp j.2 ((x.1 + y.1) _) = Bor.cmp j.2 _ + Bor.cmp j.2 _
        rw [AlternatingMap.add_apply, map_add])
      map_smul' := fun c x => Subtype.ext (by
        change Bor.cmp j.2 ((c • x.1) _) = c • Bor.cmp j.2 _
        rw [AlternatingMap.smul_apply, map_smul]) }
  obtain ⟨Φ, h1, h2⟩ := irrAbs _ τ.V π.V P _ τ.ρ π.finPart ρW τ.irred hτ.iSup_range p
    (fun j g w => Subtype.ext (cmp_trans g w.1 _ j.2))
    (fun w hw => Subtype.ext (by
      refine Module.Basis.ext_alternating b fun v _ => ?_
      rw [← sum_cmp (w.1 _)]
      have : ∀ i, Bor.cmp i (w.1 fun k => b (v k)) = 0 := fun i => congrArg Subtype.val (hw (v, i))
      simp [this]))
  exact ⟨P.subtype ∘ₗ Φ, P.subtype_injective.comp h1, fun v => (Φ v).2, fun g v => congrArg Subtype.val (h2 g v)⟩
