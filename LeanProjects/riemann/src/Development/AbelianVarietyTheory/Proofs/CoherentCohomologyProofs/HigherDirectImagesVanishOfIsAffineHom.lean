import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfSheafPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe w t v u

noncomputable section

namespace GlobalTheory

section Space

open SheafPull SheafLES

attribute [-instance] hasSheafify_topCat hasExt_sheaf_topCat

variable {X Y : TopCat.{u}} [HasExt.{u} (AbSheaf X)] [HasExt.{u} (AbSheaf Y)] (f : Y ⟶ X)
  {F F' : AbSheaf X} {G G' : AbSheaf Y} (φ : F ⟶ (push f).obj G) (n : ℕ)
  {V V' : Opens X} {W W' : Opens Y}

theorem SheafPull.pull_map (s : F' ⟶ F) (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F' n V) :
    pull.{u, u} f φ n i (map s n V x) = pull.{u, u} f (s ≫ φ) n i x :=
  sitePull_map _ _ _ n _ x

theorem SheafPull.map_pull (s : G ⟶ G') (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F n V) :
    map s n W (pull.{u, u} f φ n i x) = pull.{u, u} f (φ ≫ (push f).map s) n i x :=
  map_sitePull _ _ _ n _ x

theorem SheafPull.pull_res (k : V' ⟶ V) (i : W ⟶ (Opens.map f).obj V') (x : Sheaf.H'.{u} F n V) :
    pull.{u, u} f φ n i (res F n k x) = pull.{u, u} f φ n (i ≫ (Opens.map f).map k) x :=
  sitePull_res _ _ n _ _ x

theorem SheafPull.res_pull (k : W' ⟶ W) (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F n V) :
    res G n k (pull.{u, u} f φ n i x) = pull.{u, u} f φ n (k ≫ i) x :=
  res_sitePull _ _ n _ _ x

theorem SheafPull.equivZero_pull (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F 0 V) :
    equivZero G W (pull.{u, u} f φ 0 i x) = G.obj.map i.op (φ.hom.app (op V) (equivZero F V x)) :=
  equivZero_sitePull _ _ _ x

theorem SheafPull.pull_δ {A : ShortComplex (AbSheaf X)} {B : ShortComplex (AbSheaf Y)}
    (hA : A.ShortExact) (hB : B.ShortExact) (ψ : A ⟶ B.map (push f))
    (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} A.X₃ n V) :
    pull.{u, u} f (G := B.X₁) ψ.τ₁ (n + 1) i (δ hA n V x) =
      δ hB n W (pull.{u, u} f (G := B.X₃) ψ.τ₃ n i x) :=
  sitePull_δ _ hA hB ψ n i x

end Space

section Morphism

variable {X Y : Scheme.{u}} {g : Y ⟶ X}

theorem smulHom_pushforward (g : Y ⟶ X) (G : Y.Modules) (r : Γ(X, ⊤)) :
    smulHom ((Scheme.Modules.pushforward g).obj G) r =
      (Scheme.Modules.pushforward g).map (smulHom G (g.appTop r)) := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  have h : g.app W (restrictGlobal X W r) = restrictGlobal Y (g ⁻¹ᵁ W) (g.appTop r) :=
    ConcreteCategory.congr_hom (g.naturality (homOfLE le_top : W ⟶ ⊤).op) _
  exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ W) => (a • (show Γ(G, g ⁻¹ᵁ W) from x) : Γ(G, g ⁻¹ᵁ W))) h

section Pull

variable {F F' : X.Modules} {G G' : Y.Modules}

def toAbSheafPush (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) :
    (toAbSheaf X).obj F ⟶ (SheafPull.push g.base).obj ((toAbSheaf Y).obj G) :=
  (toAbSheaf X).map φ

theorem toAbSheafPush_comp (s : F' ⟶ F) (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) :
    toAbSheafPush (s ≫ φ) = (toAbSheaf X).map s ≫ toAbSheafPush φ := rfl

theorem toAbSheafPush_comp_map (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (s : G ⟶ G') :
    toAbSheafPush (φ ≫ (Scheme.Modules.pushforward g).map s) =
      toAbSheafPush φ ≫ (SheafPull.push g.base).map ((toAbSheaf Y).map s) := rfl

variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))

def cohOn.pull (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) {V : X.Opens} {W : Y.Opens}
    (h : W ≤ g ⁻¹ᵁ V) (n : ℕ) : cohOn F V n →ₛₗ[σ] cohOn G W n where
  toFun x := (cohOn.toH' G W n).symm (SheafPull.pull.{u, u} g.base
    (toAbSheafPush φ) n (homOfLE h) (cohOn.toH' F V n x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' r x := by
    have e : smulHom F (algebraMap R Γ(X, ⊤) r) ≫ φ = φ ≫ (Scheme.Modules.pushforward g).map
        (smulHom G (algebraMap S Γ(Y, ⊤) (σ r))) := by
      rw [smulHom_comp, smulHom_pushforward, hσ]
    have h₁ := SheafPull.pull_map g.base (toAbSheafPush φ) n
      ((toAbSheaf X).map (smulHom F (algebraMap R Γ(X, ⊤) r))) (homOfLE h) (cohOn.toH' F V n x)
    have h₂ := SheafPull.map_pull g.base (toAbSheafPush φ) n
      ((toAbSheaf Y).map (smulHom G (algebraMap S Γ(Y, ⊤) (σ r)))) (homOfLE h) (cohOn.toH' F V n x)
    rw [← toAbSheafPush_comp, e] at h₁
    rw [← toAbSheafPush_comp_map] at h₂
    apply (cohOn.toH' G W n).injective
    rw [AddEquiv.apply_symm_apply, cohOn.toH'_smul, cohOn.toH'_smul, AddEquiv.apply_symm_apply]
    exact h₁.trans h₂.symm

variable (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) {V V' : X.Opens} {W W' : Y.Opens} {n : ℕ}

theorem cohOn.toH'_pull (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    cohOn.toH' G W n (cohOn.pull hσ φ h n x) =
      SheafPull.pull.{u, u} g.base (toAbSheafPush φ) n (homOfLE h) (cohOn.toH' F V n x) :=
  (cohOn.toH' G W n).apply_symm_apply _

theorem cohOn.pull_map (s : F' ⟶ F) (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F' V n) :
    cohOn.pull hσ φ h n (cohOn.map R s V n x) = cohOn.pull hσ (s ≫ φ) h n x := by
  apply (cohOn.toH' G W n).injective
  rw [cohOn.toH'_pull, cohOn.toH'_pull, cohOn.toH'_map, toAbSheafPush_comp]
  exact SheafPull.pull_map g.base (toAbSheafPush φ) n ((toAbSheaf X).map s) (homOfLE h) _

theorem cohOn.map_pull (s : G ⟶ G') (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    cohOn.map S s W n (cohOn.pull hσ φ h n x) =
      cohOn.pull hσ (φ ≫ (Scheme.Modules.pushforward g).map s) h n x := by
  apply (cohOn.toH' G' W n).injective
  rw [cohOn.toH'_map, cohOn.toH'_pull, cohOn.toH'_pull, toAbSheafPush_comp_map]
  exact SheafPull.map_pull g.base (toAbSheafPush φ) n ((toAbSheaf Y).map s) (homOfLE h) _

theorem cohOn.pull_res (k : V' ≤ V) (h : W ≤ g ⁻¹ᵁ V') (x : cohOn F V n) :
    cohOn.pull hσ φ h n (cohOn.res R F k n x) =
      cohOn.pull hσ φ (h.trans (g.preimage_mono k)) n x := by
  apply (cohOn.toH' G W n).injective
  rw [cohOn.toH'_pull, cohOn.toH'_pull, cohOn.toH'_res]
  exact SheafPull.pull_res g.base (toAbSheafPush φ) n (homOfLE k) (homOfLE h) _

theorem cohOn.res_pull (k : W' ≤ W) (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    cohOn.res S G k n (cohOn.pull hσ φ h n x) = cohOn.pull hσ φ (k.trans h) n x := by
  apply (cohOn.toH' G W' n).injective
  rw [cohOn.toH'_res, cohOn.toH'_pull, cohOn.toH'_pull]
  exact SheafPull.res_pull g.base (toAbSheafPush φ) n (homOfLE k) (homOfLE h) _

theorem cohOn.zeroEquiv_pull (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V 0) :
    cohOn.zeroEquiv S G W (cohOn.pull hσ φ h 0 x) =
      sectionsOn.res S G h (sectionsOn.mapOver hσ φ V (cohOn.zeroEquiv R F V x)) := by
  apply (sectionsOn.toΓ G W).injective
  rw [cohOn.toΓ_zeroEquiv, cohOn.toH'_pull, sectionsOn.toΓ_res, sectionsOn.toΓ_mapOver,
    cohOn.toΓ_zeroEquiv]
  exact SheafPull.equivZero_pull g.base (toAbSheafPush φ) (homOfLE h) _

theorem cohOn.pull_δ {A : ShortComplex X.Modules} {B : ShortComplex Y.Modules}
    (hA : A.ShortExact) (hB : B.ShortExact) (ψ : A ⟶ B.map (Scheme.Modules.pushforward g))
    (h : W ≤ g ⁻¹ᵁ V) (x : cohOn A.X₃ V n) :
    cohOn.pull hσ (G := B.X₁) ψ.τ₁ h (n + 1) (cohOn.δ R hA V n x) =
      cohOn.δ S hB W n (cohOn.pull hσ (G := B.X₃) ψ.τ₃ h n x) := by
  apply (cohOn.toH' B.X₁ W (n + 1)).injective
  refine (cohOn.toH'_pull hσ (G := B.X₁) ψ.τ₁ h _).trans (Eq.trans ?_ (cohOn.toH'_δ S hB W n _).symm)
  exact SheafPull.pull_δ g.base n (shortExact_toAbSheaf hA) (shortExact_toAbSheaf hB)
    ((toAbSheaf X).mapShortComplex.map ψ) (homOfLE h) (cohOn.toH' A.X₃ V n x)

theorem cohOn.pull_bijective_of_toAbSheaf (h : W ≤ g ⁻¹ᵁ V)
    (H : Function.Bijective (SheafPull.pull.{u, u} g.base (toAbSheafPush φ) n (homOfLE h))) :
    Function.Bijective (cohOn.pull hσ φ h n) :=
  (cohOn.toH' G W n).symm.bijective.comp (H.comp (cohOn.toH' F V n).bijective)

theorem higherDirectImagesVanish_of_isAffineHom (g : Y ⟶ X) [IsAffineHom g] (G : Y.Modules)
    [G.IsQuasicoherent] :
    SheafPull.HigherDirectImagesVanish.{u} g.base ((toAbSheaf Y).obj G) :=
  SheafPull.higherDirectImagesVanish_of_basis _ _ fun V x hx => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact ⟨W, hWV, hxW, fun n hn =>
      cohOn.subsingleton_of_isAffineOpen G (IsAffineOpen.preimage hW g) hn⟩

variable (G V n) in

theorem cohOn.pull_id_bijective [IsAffineHom g] [G.IsQuasicoherent] :
    Function.Bijective (cohOn.pull hσ (𝟙 ((Scheme.Modules.pushforward g).obj G))
      (le_refl (g ⁻¹ᵁ V)) n) :=
  cohOn.pull_bijective_of_toAbSheaf hσ _ _
    (SheafPull.pushComparison_bijective.{u, u} (higherDirectImagesVanish_of_isAffineHom g G) n V)

variable (F n) in

theorem cohOn.pull_restrict_bijective [IsOpenImmersion g] (h : W ≤ g ⁻¹ᵁ V) (h' : V ≤ g ''ᵁ W) :
    Function.Bijective
      (cohOn.pull hσ (G := F.restrict g) ((Scheme.Modules.restrictAdjunction g).unit.app F) h n) :=
  cohOn.pull_bijective_of_toAbSheaf hσ _ _
    (SheafPull.pull_restrUnit_bijective.{u, u} g.isOpenEmbedding ((toAbSheaf X).obj F) n
      (homOfLE h) h')

end Pull

section Linear

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

section Push

variable [IsAffineHom g] (G : Y.Modules) [G.IsQuasicoherent]

def cohOn.pushforwardEquiv (V : X.Opens) (n : ℕ) :
    cohOn ((Scheme.Modules.pushforward g).obj G) V n ≃ₗ[R] cohOn G (g ⁻¹ᵁ V) n :=
  LinearEquiv.ofBijective _ (cohOn.pull_id_bijective G (σ := RingHom.id R) hg V n)

theorem cohOn.pushforwardEquiv_apply (V : X.Opens) (n : ℕ)
    (x : cohOn ((Scheme.Modules.pushforward g).obj G) V n) :
    cohOn.pushforwardEquiv R hg G V n x =
      cohOn.pull (σ := RingHom.id R) hg (𝟙 _) (le_refl (g ⁻¹ᵁ V)) n x := rfl

variable {G} in

theorem cohOn.pushforwardEquiv_map {G' : Y.Modules} [G'.IsQuasicoherent] (s : G ⟶ G')
    (V : X.Opens) (n : ℕ) (x : cohOn ((Scheme.Modules.pushforward g).obj G) V n) :
    cohOn.pushforwardEquiv R hg G' V n
        (cohOn.map R ((Scheme.Modules.pushforward g).map s) V n x) =
      cohOn.map R s (g ⁻¹ᵁ V) n (cohOn.pushforwardEquiv R hg G V n x) := by
  rw [cohOn.pushforwardEquiv_apply, cohOn.pushforwardEquiv_apply, cohOn.pull_map, cohOn.map_pull,
    Category.comp_id, Category.id_comp]

theorem cohOn.zeroEquiv_pushforwardEquiv (V : X.Opens)
    (x : cohOn ((Scheme.Modules.pushforward g).obj G) V 0) :
    sectionsOn.toΓ G (g ⁻¹ᵁ V) (cohOn.zeroEquiv R G _ (cohOn.pushforwardEquiv R hg G V 0 x)) =
      sectionsOn.toΓ _ V (cohOn.zeroEquiv R _ V x) := by
  rw [cohOn.pushforwardEquiv_apply, cohOn.zeroEquiv_pull, sectionsOn.res_refl]
  rfl

def coh.pushforwardEquiv (n : ℕ) :
    coh ((Scheme.Modules.pushforward g).obj G) n ≃ₗ[R] coh G n :=
  cohOn.pushforwardEquiv R hg G ⊤ n

theorem coh.pushforwardEquiv_def (n : ℕ) :
    coh.pushforwardEquiv R hg G n = cohOn.pushforwardEquiv R hg G ⊤ n := rfl

variable {G} in

theorem coh.pushforwardEquiv_map {G' : Y.Modules} [G'.IsQuasicoherent] (s : G ⟶ G')
    (n : ℕ) (x : coh ((Scheme.Modules.pushforward g).obj G) n) :
    coh.pushforwardEquiv R hg G' n (cohOn.map R ((Scheme.Modules.pushforward g).map s) ⊤ n x) =
      cohOn.map R s ⊤ n (coh.pushforwardEquiv R hg G n x) :=
  cohOn.pushforwardEquiv_map R hg s ⊤ n x

end Push

section Restrict

variable [IsOpenImmersion g] (F : X.Modules)

def cohOn.restrictEquiv {V : X.Opens} {W : Y.Opens} (h : g ''ᵁ W = V) (n : ℕ) :
    cohOn F V n ≃ₗ[R] cohOn (F.restrict g) W n :=
  LinearEquiv.ofBijective _ (cohOn.pull_restrict_bijective F (σ := RingHom.id R) hg n
    ((g.preimage_image_eq W).ge.trans (g.preimage_mono h.le)) h.ge)

end Restrict

end Linear

theorem hdim_pushforward (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
    (hg : ∀ r, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r) [IsAffineHom g]
    (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ) :
    hdim k ((Scheme.Modules.pushforward g).obj G) n = hdim k G n :=
  (coh.pushforwardEquiv k hg G n).finrank_eq

theorem appTop_algebraΓOfHom {R : Type u} [CommRing R] (g : Y ⟶ X) (p : X ⟶ Spec (.of R))
    {q : Y ⟶ Spec (.of R)} (w : g ≫ p = q) (r : R) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom q
    g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r := by
  subst w
  rfl

end Morphism

end GlobalTheory
