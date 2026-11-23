import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ThetaKernelFiring
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaPrimeMultiplicity

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Sinf] [Module ℂ Sinf]
  [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]

theorem exists_isThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by
  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν) ?_ ?_ ?_ ?_, hint,
    fun f e g => rfl⟩
  · intro f f' e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    exact integral_add (hint f e g) (hint f' e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]
    exact integral_smul c _
  · intro f e e'
    funext g
    simp only [Pi.add_apply, map_add, LinearMap.add_apply]
    exact integral_add (hint f e g) (hint f e' g)
  · intro c f e
    funext g
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply]
    exact integral_smul c _

theorem exists_isThetaP' (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 th pt io A thP := by
  obtain rfl : th = fun g h s => thL g h s := funext fun g => funext fun h => funext fun s => h1 g h s
  obtain rfl : pt = fun s => ptL s := funext h2
  exact exists_isThetaP ν 𝓕 thL ptL io A hint

theorem exists_linear_choice {X M N : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (W : Submodule ℂ M) (r : M →ₗ[ℂ] N) (u : X →ₗ[ℂ] N)
    (h : ∀ x, ∃ m ∈ W, r m = u x) : ∃ y : X →ₗ[ℂ] M, (∀ x, y x ∈ W) ∧ ∀ x, r (y x) = u x := by
  choose m hm hr using h
  let b := Module.Basis.ofVectorSpace ℂ X
  let y' : X →ₗ[ℂ] W := b.constr ℂ fun k => ⟨m (b k), hm _⟩
  refine ⟨W.subtype ∘ₗ y', fun x => (y' x).2, fun x => ?_⟩
  have : r ∘ₗ W.subtype ∘ₗ y' = u := b.ext fun k => by
    simp only [LinearMap.comp_apply, y', Module.Basis.constr_basis, Submodule.subtype_apply, hr]
  exact LinearMap.congr_fun this x

theorem exists_linear_lift {ι X : Type} [AddCommGroup X] [Module ℂ X] {M : ι → Type} [∀ a, AddCommGroup (M a)]
    [∀ a, Module ℂ (M a)] (low : ∀ a, Submodule ℂ (M a)) (W : Submodule ℂ (MultilinearMap ℂ M (G' → ℂ)))
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : (⨂[ℂ] a, low a) →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (ext : X →ₗ[ℂ] (H' → Tau))
    (h : ∀ x, (∀ e g, IntegrableOn (fun h => th g h (pt (io e (ext x h)))) 𝓕 ν) ∧
      ∃ U ∈ W, ∀ v : ∀ a, low a, U (fun a => (v a : M a)) = Lift.thetaPInt ν 𝓕 th pt io (ext x) (PiTensorProduct.tprod ℂ v)) :
    ∃ y : X →ₗ[ℂ] MultilinearMap ℂ M (G' → ℂ), (∀ x, y x ∈ W) ∧
      ∃ thP : LinearMap.range ext →ₗ[ℂ] ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)),
        Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range ext) thP ∧
          ∀ (x : X) (v : ∀ a, low a), y x (fun a => (v a : M a)) = thP (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) := by
  obtain ⟨thP, hP⟩ := exists_isThetaP' ν 𝓕 th pt thL ptL h1 h2 io (LinearMap.range ext) (by
    rintro ⟨_, x, rfl⟩ e g
    exact (h x).1 e g)
  let r : MultilinearMap ℂ M (G' → ℂ) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U fun a => (v a : M a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U (PiTensorProduct.tprod ℂ v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨y, hy, hr⟩ := exists_linear_choice W r (p ∘ₗ thP ∘ₗ ext.rangeRestrict) fun x => by
    obtain ⟨U, hU, hv⟩ := (h x).2
    exact ⟨U, hU, funext fun v => funext fun g =>
      (congrFun (hv v) g).trans (hP.eq (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) g).symm⟩
  exact ⟨y, hy, thP, hP, fun x v => congrFun (hr x) v⟩

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring GlobalTheory.IndefiniteRowSideFullHecke.ThetaPrimeMultiplicity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernelL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : WO (Vc D i) (Wc D i) => ℂ) 0 ∘ₗ R.ωP i t (h, g)

end GlobalTheory.ThetaFiresLinear

end
