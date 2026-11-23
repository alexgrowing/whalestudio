import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexSemilinearMapCompBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private noncomputable def UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx {R : Type} [CommRing R] {L B : Cx R} (ρ : SemiMap L B) :
    SemiMap L ((rcx (Int.castRingHom R)).obj B) where
  app U s := ((idSemi (Int.castRingHom R) B).app U s).comp (ρ.app U s)
  nat g s a := ((idSemi (Int.castRingHom R) B).nat g s _).trans
    (congrArg ((idSemi (Int.castRingHom R) B).app _ s) (ρ.nat g s a))
  comm U s t a := ((idSemi (Int.castRingHom R) B).comm U s t _).trans
    (congrArg ((idSemi (Int.castRingHom R) B).app U t) (ρ.comm U s t a))

theorem UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward :
    ∀ (R : Type) [CommRing R] (L B : Cx R) (ρ : SemiMap L B) (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains ℤ).obj E) ρ.toZ n) → Function.Bijective (ρ.op.app E n) := by
  intro R _ L B ρ E n hb
  have idBij : ∀ (K : Cx R) (U : Scheme.{0}) (s : ℤ),
      Function.Bijective ((idSemi (Int.castRingHom R) K).app U s) :=
    fun _ _ _ => ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
  have bL := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) L) (idSemi (Int.castRingHom R) L) (𝟙 _)
    (fun _ _ _ => rfl)).2 (idBij L) E n
  have bB := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) B) (idSemi (Int.castRingHom R) B) (𝟙 _)
    (fun _ _ _ => rfl)).2 (idBij B) E n
  have key : ∀ x, (idSemi (Int.castRingHom R) B).op.app E n (ρ.op.app E n x) =
      cpush ((chains ℤ).obj E) ρ.toZ n ((idSemi (Int.castRingHom R) L).op.app E n x) := by
    intro x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).1 E n α
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (idSemi (Int.castRingHom R) B)).1 E n β
    have h1 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).2 E n α β hβ
    have h2 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (idSemi (Int.castRingHom R) B)).2 E n β γ hγ
    have h3 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx ρ)).2 E n α γ
      (fun p s h U y => (hγ p s h U y).trans (congrArg _ (hβ p s h U y)))
    rw [h1, h2, ← h3]
    exact (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) L) (UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx ρ) ρ.toZ
      (fun _ _ _ => rfl)).1 E n _
  have comp : Function.Bijective
      ((idSemi (Int.castRingHom R) B).op.app E n ∘ ρ.op.app E n) := by
    have : ((idSemi (Int.castRingHom R) B).op.app E n ∘ ρ.op.app E n) =
        (cpush ((chains ℤ).obj E) ρ.toZ n ∘ (idSemi (Int.castRingHom R) L).op.app E n) := funext key
    rw [this]
    exact hb.comp bL
  exact (Function.Bijective.of_comp_iff' bB _).1 comp
