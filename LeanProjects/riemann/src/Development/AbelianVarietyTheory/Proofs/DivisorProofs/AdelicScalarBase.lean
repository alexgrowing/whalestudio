import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem typePart_base (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart R i (sg0 D A) A.μ0 R.triv c =
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.cuspPart R i c).comap (R.HW i (sg0 D A)).e := by
  classical
  have e : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS R A.μ0 = GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.finS R := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.finS
    rw [Q_base R h]
    congr 1
    ext; simp
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift.cuspPart
  rw [e]

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (e : Y →ₗ[ℂ] Z) (f : X →ₗ[ℂ] Z) (V : Submodule ℂ Z) (hinj : Function.Injective e) (hr : LinearMap.range e = V)
    (hm : ∀ x, f x ∈ V) : ∃ th : X →ₗ[ℂ] Y, ∀ x, e (th x) = f x := by
  subst hr
  refine ⟨(LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ f.codRestrict _ hm, fun x => ?_⟩
  have := congrArg Subtype.val ((LinearEquiv.ofInjective _ hinj).apply_symm_apply ⟨f x, hm x⟩)
  rwa [LinearEquiv.ofInjective_apply] at this

theorem exists_lift {F : Face D A} (h : R.Char F) (i : Fin D.R.m) (t : T0) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem integrableOn_of_isThetaLift {G' H' S' Sinf TK Tau X : Type} [MeasurableSpace H'] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK]
    [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup X] [Module ℂ X] {ν : Measure H'} {𝓕 : Set H'}
    {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf} {φ : X →ₗ[ℂ] (H' → Tau)}
    {thP : LinearMap.range φ →ₗ[ℂ] TK →ₗ[ℂ] G' → ℂ} (h : Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range φ) thP)
    (x : X) (e : TK) (g : G') :
    IntegrableOn (fun a => th g a (pt (io e (φ x a)))) 𝓕 ν ∧
      thP (φ.rangeRestrict x) e g = Lift.thetaPInt ν 𝓕 th pt io (φ x) e g :=
  ⟨h.integ (φ.rangeRestrict x) e g, h.eq (φ.rangeRestrict x) e g⟩

theorem adjLev_triv {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev (D := D) R.triv th = LinearMap.adjoint th := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev
  have : Nat.card (R.triv).H = 1 := Subgroup.card_bot
  rw [this]; simp

end GlobalTheory.BaseScalar

end
