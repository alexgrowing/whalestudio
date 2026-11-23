import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section
namespace GlobalTheory.CompanionTheory.FormOpen

variable {K : Type} [CommRing K]

theorem mOm_bijective {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {φ : A →+* B} (hφ : SemiHom (RingHom.id K) φ) (hb : Function.Bijective φ) (j : ℕ) :
    Function.Bijective (hφ.mOm j) := by
  let e : A ≃+* B := RingEquiv.ofBijective φ hb
  have he : ∀ a, e a = φ a := fun _ ↦ rfl
  have hψ : SemiHom (RingHom.id K) (e.symm : B →+* A) := fun r b ↦ by
    apply e.injective
    change e (e.symm (r • b)) = e (RingHom.id K r • e.symm b)
    rw [RingEquiv.apply_symm_apply, he, RingHom.id_apply, show φ (r • e.symm b) = _ from hφ r _,
      ← he, RingEquiv.apply_symm_apply, RingHom.id_apply]
  have hA : SemiHom (RingHom.id K) (RingHom.id A) := fun _ _ ↦ rfl
  have hB : SemiHom (RingHom.id K) (RingHom.id B) := fun _ _ ↦ rfl
  have l : Function.LeftInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hφ hψ hA (fun a ↦ e.symm_apply_apply a) x).trans
      (hA.mOm_id (fun _ ↦ rfl) x)
  have r : Function.RightInverse (hψ.mOm j) (hφ.mOm j) := fun x ↦
    (SemiHom.mOm_mOm (ρ := RingHom.id K) hψ hφ hB (fun a ↦ e.apply_symm_apply a) x).trans
      (hB.mOm_id (fun _ ↦ rfl) x)
  exact ⟨l.injective, r.surjective⟩

variable {X : Scheme.{0}}

theorem app_map_eq (V : X.Opens) (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.app V ≫ V.toScheme.presheaf.map (homOfLE h).op = V.topIso.inv := by
  simp only [Scheme.Opens.topIso, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map,
    Iso.op_inv, Functor.mapIso_inv, eqToIso.inv, ← Functor.map_comp, ← op_comp]
  rfl

theorem res_appSec_bijective (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens)
    (h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V) :
    Function.Bijective ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) := by
  have e : ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp (appSec q (V.ι ≫ q) V.ι V) :
      Sec q V → Sec (V.ι ≫ q) ⊤) = V.topIso.inv.hom := by
    rw [← app_map_eq V h]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso V.topIso.inv

theorem formRes_formPull_open_bijective {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) :
    Function.Bijective fun x : OmU q V a => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a
      (formPull (f := V.ι) rfl V a x) := by
  have h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have hγ : SemiHom (RingHom.id K) ((Sec.res (V.ι ≫ q) h : Sec (V.ι ≫ q) (V.ι ⁻¹ᵁ V) →+* Sec (V.ι ≫ q) ⊤).comp
      (appSec q (V.ι ≫ q) V.ι V)) :=
    (semiHom_appSec rfl V).comp (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h))
  have e : (fun x : OmU q V a => formRes (V.ι ≫ q) h a (formPull (f := V.ι) rfl V a x)) =
      hγ.mOm a := funext fun x ↦
    SemiHom.mOm_mOm (semiHom_appSec rfl V) (SemiHom.of_algHom (Sec.res (V.ι ≫ q) h)) hγ
      (fun _ ↦ rfl) x
  rw [e]
  exact mOm_bijective hγ (res_appSec_bijective q V h) a

end GlobalTheory.CompanionTheory.FormOpen
