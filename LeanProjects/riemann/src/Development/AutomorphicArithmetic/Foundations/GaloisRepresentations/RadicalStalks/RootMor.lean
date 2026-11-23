import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobEpi

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.rootMor :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ σ' : k →+* k) (ψ ψ' : A.left ⟶ A.left), SMor A σ ψ → (∀ x, σ' x ^ p = σ x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ → SMor A σ' ψ' := by
  intro p _ k _ _ hk A _ _ hAb σ σ' ψ ψ' hS hpow hfr
  haveI := hAb
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  haveI hP : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hAb hAb
  haveI : Smooth (A ⊗ A).hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced (A ⊗ A).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (A ⊗ A).hom
  haveI : Epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A)) := (epi p A.left (cast_left p k hk A)).1
  haveI : Epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) :=
    (epi p (A ⊗ A).left (cast_left p k hk (A ⊗ A))).1
  have hσ : spMap (frobR p k hk) ≫ spMap σ' = spMap σ := by
    rw [← Geo.Tor.spMap_comp]
    congr 1
    ext x
    rw [RingHom.comp_apply, GlobalTheory.ConjSeq.frobR_apply, hpow]
  have hw' : ψ' ≫ A.hom = A.hom ≫ spMap σ' := by
    apply (cancel_epi (GlobalTheory.VB.frob A.left p (cast_left p k hk A))).mp
    rw [← Category.assoc, hfr, hS.w, ← Category.assoc,
      GlobalTheory.ConjSeq.frob_comp_hom p k hk A.hom (cast_left p k hk A), Category.assoc, hσ]
  have hnat : ∀ f : (A ⊗ A).left ⟶ A.left,
      GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)) ≫ f ≫ ψ' = f ≫ ψ := by
    intro f
    rw [← Category.assoc, GlobalTheory.VB.frob_naturality p (cast_left p k hk A) f (cast_left p k hk (A ⊗ A)),
      Category.assoc, hfr]
  let F : Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A))) (by
      simp only [Over.mk_hom]
      rw [← Category.assoc,
        GlobalTheory.ConjSeq.frob_comp_hom p k hk (A ⊗ A).hom (cast_left p k hk (A ⊗ A)), Category.assoc, hσ])
  let u : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ') ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ') (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hw', ← Category.assoc, Over.w g])
  let v : ∀ g : A ⊗ A ⟶ A, Over.mk ((A ⊗ A).hom ≫ spMap σ) ⟶ A := fun g =>
    Over.homMk (g.left ≫ ψ) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, hS.w, ← Category.assoc, Over.w g])
  have hFu : ∀ g : A ⊗ A ⟶ A, F ≫ u g = v g := by
    intro g
    apply Over.OverMorphism.ext
    simp only [F, u, v, Over.comp_left, Over.homMk_left]
    exact hnat g.left
  have huniv : (u (fst A A) * u (snd A A)).left = (fst A A * snd A A).left ≫ ψ' := by
    apply (cancel_epi (GlobalTheory.VB.frob (A ⊗ A).left p (cast_left p k hk (A ⊗ A)))).mp
    rw [hnat]
    have e1 : (F ≫ (u (fst A A) * u (snd A A))).left = (v (fst A A) * v (snd A A)).left := by
      rw [MonObj.comp_mul, hFu, hFu]
    rw [Over.comp_left] at e1
    exact e1.trans (hS.mul (A ⊗ A) (fst A A) (snd A A) (v (fst A A)) (v (snd A A)) rfl rfl)
  refine GlobalTheory.DeRham.GrpMor.mk (isDPMorphism_of_eq_bot (dp0 k) rfl (dp0 k) σ') (by simp) hw' ?_
  intro T x y x₀ y₀ hx0 hy0
  let h : T ⟶ A ⊗ A := lift x y
  let hh : Over.mk (T.hom ≫ spMap σ') ⟶ Over.mk ((A ⊗ A).hom ≫ spMap σ') :=
    Over.homMk h.left (by
      simp only [Over.mk_hom]
      rw [← Category.assoc, Over.w h])
  have ex : x₀ = hh ≫ u (fst A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hx0, ← Category.assoc, ← Over.comp_left, lift_fst]
  have ey : y₀ = hh ≫ u (snd A A) := by
    apply Over.OverMorphism.ext
    simp only [hh, u, Over.comp_left, Over.homMk_left]
    rw [hy0, ← Category.assoc, ← Over.comp_left, lift_snd]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left, huniv]
  simp only [hh, Over.homMk_left]
  rw [← Category.assoc, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
