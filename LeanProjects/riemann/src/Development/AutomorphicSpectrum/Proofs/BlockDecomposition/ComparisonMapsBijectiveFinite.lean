import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

section Pi

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

def piS {I : Type} {M N : I → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) :
    (∀ i, M i) →ₛₗ[algebraMap R S] (∀ i, N i) where
  toFun x i := u i (x i)
  map_add' x y := funext fun i ↦ map_add (u i) _ _
  map_smul' r x := funext fun i ↦ (u i).map_smulₛₗ r (x i)

theorem liftSemi_piS_bijective {I : Type} [Finite I] {M N : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]
    (u : ∀ i, M i →ₛₗ[algebraMap R S] N i) (hu : ∀ i, Function.Bijective (liftSemi (u i))) :
    Function.Bijective (liftSemi (piS u)) := by
  classical
  haveI := Fintype.ofFinite I
  let e := TensorProduct.piRight R S S M
  have key : (liftSemi (piS u) : S ⊗[R] (∀ i, M i) → ∀ i, N i) =
      (Pi.map fun i ↦ liftSemi (u i)) ∘ e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero =>
      funext i
      simp
    | add a b ha hb =>
      simp only [map_add, Function.comp_apply] at ha hb ⊢
      rw [ha, hb]
      funext i
      simp
    | tmul s x =>
      funext i
      simp [e, liftSemi_tmul, piS]
  rw [key]
  exact (Function.Bijective.piMap hu).comp e.bijective

end Pi

section Cochains

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

def cT (m : BC F F') (T : C) : F.obj T →ₛₗ[algebraMap R S] F'.obj T where
  toFun := m.α T
  map_add' := map_add (m.α T)
  map_smul' := m.smul T

theorem liftSemi_cT_bijective (m : BC F F') (T : C) : Function.Bijective (liftSemi (cT m T)) := by
  obtain ⟨e, he⟩ := m.bij T
  have key : (liftSemi (cT m T) : S ⊗[R] F.obj T → F'.obj T) = e := by
    funext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s b =>
      have h1 : s ⊗ₜ[R] b = s • ((1 : S) ⊗ₜ[R] b) := by simp [TensorProduct.smul_tmul']
      rw [liftSemi_tmul, h1, map_smul, he]
      rfl
  rw [key]
  exact e.bijective

theorem comparison_degree_zero_bijective [Finite C] (m : BC F F') : Function.Bijective (th0 m) :=
  liftSemi_piS_bijective (fun T ↦ cT m T) fun T ↦ liftSemi_cT_bijective m T

theorem comparison_degree_one_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th1 m) :=
  liftSemi_piS_bijective (fun T ↦ piS fun T' ↦ piS fun _ : T ⟶ T' ↦ cT m T') fun _ ↦
    liftSemi_piS_bijective _ fun T' ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T'

theorem comparison_degree_two_bijective [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    Function.Bijective (th2 m) :=
  liftSemi_piS_bijective
    (fun T ↦ piS fun T' ↦ piS fun T'' ↦ piS fun _ : T ⟶ T' ↦ piS fun _ : T' ⟶ T'' ↦ cT m T'')
    fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun T'' ↦
      liftSemi_piS_bijective _ fun _ ↦ liftSemi_piS_bijective _ fun _ ↦ liftSemi_cT_bijective m T''

end Cochains

theorem th_bijective (R S P : Type) [CommRing R] [CommRing S] [Algebra R S] [SemilatticeInf P]
    [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (F' : Pᵒᵖ ⥤ CommAlgCat.{0} S) (m : BC F F') :
    Function.Bijective (th0 m) ∧ Function.Bijective (th1 m) ∧ Function.Bijective (th2 m) := by
  haveI : Finite Pᵒᵖ := Finite.of_injective (Opposite.unop : Pᵒᵖ → P) Opposite.unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun T T' ↦ inferInstance
  exact ⟨comparison_degree_zero_bijective m, comparison_degree_one_bijective m, comparison_degree_two_bijective m⟩

end GlobalTheory.CompanionTheory.PerfVB
