import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eval_comm {A E σ : Type} [CommRing A] [Ring E] [Algebra A E] (f : σ → E)
    (h : ∀ i j, Commute (f i) (f j)) :
    ∃ φ : MvPolynomial σ A →ₐ[A] E, ∀ i, φ (MvPolynomial.X i) = f i := by
  classical
  let S := Algebra.adjoin A (Set.range f)
  letI : CommRing S := Algebra.adjoinCommRingOfComm A (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact h i j)
  refine ⟨S.val.comp (MvPolynomial.aeval fun i => (⟨f i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : S)), fun i => ?_⟩
  simp

theorem UpperTheory.V.Pa.Lev.thEx :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, IsUnit (qj w j : A)) → Nonempty (ThData l ρ x δ) := by
  intro L _ _ n q w l A M _ _ _ ρ x δ hq
  obtain ⟨Θ1, h1⟩ := thetaQ L n q w A M ρ (fun _ => ellC l _) hq
  obtain ⟨Θw, hw⟩ := thetaQ L n q w A M ρ (fun _ => ⊤) hq
  have c1 : ∀ j j' t t', Commute (Θ1 j t : Module.End A (fixd ρ (UC n w fun _ => ellC l _))) (Θ1 j' t') :=
    fun j j' t t' => (h1.2 j j' t t').units_val
  have cw : ∀ j j' t t', Commute (Θw j t : Module.End A (fixd ρ (UC n w fun _ => ⊤))) (Θw j' t') :=
    fun j j' t t' => (hw.2 j j' t t').units_val
  obtain ⟨a1, ha1⟩ := eval_comm (A := A) (E := Module.End A (fixd ρ (UC n w fun _ => ellC l _)))
    (Sum.elim (fun p : Fin q × Fin n => ((qj w p.1 : A) ^ (p.2 : ℕ)) • (Θ1 p.1 (Pi.mulSingle p.2 (x p.1)) : Module.End A _))
      (fun p : Fin q × Fin n => (Θ1 p.1 (Pi.mulSingle p.2 (δ p.1)) : Module.End A _) - 1)) (by
      rintro (p | p) (p' | p')
      · exact ((c1 _ _ _ _).smul_left _).smul_right _
      · exact ((c1 _ _ _ _).sub_right (Commute.one_right _)).smul_left _
      · exact ((c1 _ _ _ _).sub_left (Commute.one_left _)).smul_right _
      · exact ((c1 _ _ _ _).sub_left (Commute.one_left _)).sub_right (Commute.one_right _))
  obtain ⟨aw, haw⟩ := eval_comm (A := A) (E := Module.End A (fixd ρ (UC n w fun _ => ⊤)))
    (fun p : Fin q × Fin n => ((qj w p.1 : A) ^ (p.2 : ℕ)) • (Θw p.1 (Pi.mulSingle p.2 (x p.1)) : Module.End A _))
    (fun p p' => ((cw _ _ _ _).smul_left _).smul_right _)
  exact ⟨{ Θ1 := Θ1, h1 := h1, Θw := Θw, hw := hw, act1 := a1
           act_uVariable_eq_pow := fun j i => ha1 (.inl (j, i))
           act_yVariable := fun j i => by
             rw [map_add, map_one, ha1]
             exact add_sub_cancel _ _
           actw := aw
           actw_u := fun j i => haw (j, i) }⟩
