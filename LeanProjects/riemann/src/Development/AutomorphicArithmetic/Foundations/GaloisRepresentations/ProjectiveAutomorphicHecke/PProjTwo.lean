import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
open Module
universe u v

theorem UpperTheory.Gal.CertificateRingHomMap.pProjTwo_holds :
    UpperTheory.Gal.CertificateRingHomMap.ProjTwo.{u,v} := by
  intro F K _ _ e A _ _ _ I _ B _ _ _ J T S hT hS θ
  letI : Algebra F K := e.toRingHom.toAlgebra
  letI : ∀ i, Algebra F (B i) := fun i =>
    ((algebraMap K (B i)).comp e.toRingHom).toAlgebra' (fun c x => Algebra.commutes _ _)
  haveI : Module.Finite F K :=
    Module.Finite.of_surjective (Algebra.linearMap F K) e.surjective
  haveI : ∀ i, IsScalarTower F K (B i) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ i, Module.Finite F (B i) := fun i => Module.Finite.trans K (B i)
  have hcomm : ∀ j j', Commute ((T j, fun i => S i j) : A × ∀ i, B i) (T j', fun i => S i j') := by
    intro j j'
    exact Prod.ext (hT j j') (funext fun i => hS i j j')
  obtain ⟨t, ht⟩ := UpperTheory.Gal.CertificateRingHomMap.pProjOne_holds.{max u v} F (A × ∀ i, B i) J
    (fun j => (T j, fun i => S i j)) hcomm θ
  have hid : UpperTheory.Gal.CertificateRingHomMap.wmap (RingHom.id F) t = t := by
    ext w
    simp [UpperTheory.Gal.CertificateRingHomMap.wmap]
  refine ⟨t, ?_, fun i => ?_⟩
  · have h := UpperTheory.Gal.CertificateRingHomMap.Cert.map (RingHom.id F) (RingHom.fst A (∀ i, B i)) (fun _ => rfl) ht
    rw [hid] at h
    exact h
  · exact UpperTheory.Gal.CertificateRingHomMap.Cert.map e.toRingHom
      ((Pi.evalRingHom B i).comp (RingHom.snd A (∀ i, B i))) (fun c => rfl) ht
