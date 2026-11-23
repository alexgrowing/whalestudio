import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2BaseAct :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R) (J : Ideal R), H.IsJ θ a K D₀ ψ₀ lam J → ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ RingHom.ker μ = J ∧ (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K), H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) := by
  intro L Ω _ _ _ _ _ l _ n c H _ A _ _ _ θ _ a K R _ _ D₀ ψ₀ lam J hJ
  rcases hJ with ⟨h0, hJ⟩ | ⟨x, x1, f, hne, hmap, hsurj, hlam, hker⟩
  · haveI : Subsingleton (H.MK θ a K) := by
      rw [h0]
      infer_instance
    haveI : Subsingleton (Module.End A (H.MK θ a K)) := inferInstance
    let μ : R →+* Module.End A (H.MK θ a K) :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    refine ⟨μ, ?_, ?_, Or.inl h0⟩
    · intro b y
      exact Subsingleton.elim _ _
    · rw [hJ]
      ext t
      simp only [RingHom.mem_ker, Submodule.mem_top, iff_true]
      exact Subsingleton.elim _ _
  · refine ⟨(UpperTheory.V.Hi.heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom.comp f.toRingHom, ?_, ?_, Or.inr ⟨x, x1, f, hmap, fun t => rfl⟩⟩
    · intro b y
      have h := hlam b
      show ((f (lam b) : Module.End A (H.MK θ a K))) y = b • y
      rw [h]
      rfl
    · rw [hker]
      ext t
      simp only [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      constructor
      · intro ht
        exact Subtype.ext ht
      · intro ht
        rw [ht]
        rfl
