import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem fin_mem {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (m : (E →+* ℂ) → Multiset ℂ) (g : GL (Fin a) (Af E)) {φ : Sm E a} (hφ : φ ∈ CI a m) : finRep E a g φ ∈ CI a m := by
  refine mem_CI.2 ⟨UpperTheory.V.Cm.isCuspForm_act (.fin g) (mem_CI.1 hφ).1, fun t u => ?_⟩
  have h := LinearMap.congr_fun ((capAct E a t u).2.1 (.fin g)).eq φ
  rw [Module.End.mul_apply, Module.End.mul_apply, (mem_CI.1 hφ).2 t u, map_smul] at h
  exact h

private noncomputable def ciRep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (m : (E →+* ℂ) → Multiset ℂ) : Representation ℂ (GL (Fin a) (Af E)) (CI a m) where
  toFun g := (finRep E a g).restrict fun _ h => fin_mem m g h
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp [LinearMap.restrict_apply])
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by simp [LinearMap.restrict_apply])

theorem UpperTheory.V.Cj.S.suppCusp :
    UpperTheory.V.Cj.S.CuspProj → UpperTheory.V.Cj.S.SuppCusp := by
  intro hP E _ _ _ a ha φ m B h hc
  let x : CI a m := ⟨φ, mem_CI.2 ⟨hc, fun t => (h.cap t).2⟩⟩
  obtain ⟨π, h1, p, h2, h3⟩ := hP E a ha m (fun t => (h.cap t).1) x fun e => h.ne (congrArg Subtype.val e)
  refine ⟨Unit, inferInstance, fun _ => a, fun _ => CG.mk π, fun _ => m, by simp, fun _ => ha, by simp,
    fun _ t => h1 t, fun t => by simp, ?_⟩
  filter_upwards [h.sat, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat π] with w hw ⟨C, hC⟩
  have h4 : IsSatVecGL w (locOf (ciRep a m) w) x (B w) :=
    IsSatVecGL.of_map (CI a m).subtype (fun _ _ => rfl) Subtype.val_injective hw
  have h5 : IsSatVecGL w (π.locRep w) (p x) (B w) := h4.map p (fun g y => h3 _ y _ rfl) h2
  have h6 : C = B w := (((CG.hasSat_mk π w C).1 hC).2 _ h5.2.1 h2).unique h5
  exact ⟨fun _ => C, fun _ => hC, by simpa using h6⟩
