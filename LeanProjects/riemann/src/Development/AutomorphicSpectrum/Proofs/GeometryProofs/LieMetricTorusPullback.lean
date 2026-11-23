import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos

theorem core_gram_posDef {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).PosDef := by
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp

theorem cochar_indep {Xc : Type} [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] {r : ℕ}
    (β : Fin r → (Xc →+ ℤ)) (hβ : LinearIndependent ℤ β) :
    LinearIndependent ℂ (fun a => (Int.castAddHom ℂ).comp (β a)) := by
  let b := Module.Free.chooseBasis ℤ Xc
  let ev : (Xc →+ ℤ) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ Xc → ℤ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have : f.toIntLinearMap = 0 := b.ext fun i => congrFun hf i
    ext x
    exact LinearMap.congr_fun this x
  have h1 : LinearIndependent ℤ (ev ∘ β) := hβ.map' ev hev
  have h2 : LinearIndependent ℂ (fun a => algebraMap ℤ ℂ ∘ (ev ∘ β) a) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  let evC : (Xc →+ ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ Xc → ℂ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp evC h2

theorem exists_diff {S : Scheme.{0}} {T G : Over S} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    {R : Type} [CommRing R] {x : Sp R ⟶ S} {E F : Type} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (M : LieModel T x E) (N : LieModel G x F) : ∃ A : E →ₗ[R] F, ∀ e, N.pt (A e) = M.pt e ≫ u := by
  have ht : ∀ e, IsTanAt G x (M.pt e ≫ u) := by
    intro e
    have h1 := (LieEx.isTanAt_iff x T _).1 (M.tan e)
    refine (LieEx.isTanAt_iff x G _).2 ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (h1 =≫ u).trans ?_
    exact MonObj.one_comp u
  choose A hA using fun e => N.onto _ (ht e)
  refine ⟨{ toFun := A, map_add' := fun e e' => N.inj ?_, map_smul' := fun c e => N.inj ?_ }, hA⟩
  · rw [N.add, hA, hA, hA, M.add, MonObj.mul_comp]
  · apply Over.OverMorphism.ext
    rw [N.smul, hA, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc]

theorem gramAt_posDef_of_diff_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  intro X Ω _ K J y ξ G _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β zc Mz _ hker v hv
  obtain ⟨V, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ (zc ≫ ρ)
  obtain ⟨A, hA⟩ := exists_diff u Mz (LiePull.modelPull hΦ zc MR)
  have hA' : ∀ δ, (MR.pt (A δ)).left = (Mz.pt δ ≫ u).left ≫ Φ := by
    intro δ
    rw [← hA, ← LiePull.pts_left hΦ (LiePull.eps_assoc zc)]
    exact congrArg (fun k => k.left) ((LiePull.tanPts hΦ zc).apply_symm_apply (MR.pt (A δ))).symm
  have hk : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro δ hδ
    apply hker
    rw [← hA, hδ]
    have := (LiePull.modelPull hΦ zc MR).add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hli := (cochar_indep β β.linearIndependent).map' A hk
  obtain ⟨core, hcore⟩ := h.herm (zc ≫ ρ) V MR
  have key := core_gram_posDef core _ hli
  have hv' : ∀ a, v a = MR.pt (A ((Int.castAddHom ℂ).comp (β a))) := fun a =>
    Over.OverMorphism.ext ((hv a).trans (hA' _).symm)
  have hm : RootHt.gramAt h (zc ≫ ρ) v = Matrix.of fun a b =>
      core.inner ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) a) ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) b) := by
    ext a c
    simp only [RootHt.gramAt, Matrix.of_apply, hcore, hv', Function.comp_apply]
  rw [hm]
  exact key

end GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos
