import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAbPullApp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModuleCubePullHomTermCommCechDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullbackStatement

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
open GlobalTheory.PD

noncomputable section

namespace GlobalTheory

open SheafPull

namespace Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R S : Type} [Ring R] [Ring S]
  {σ : R →+* S} {τ : κ → ι}

theorem termMap_term {A A' : Cube.{0} ι R} {B B' : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B)
    (ψ' : Cube.PullHom σ τ A' B') (α : A ⟶ A') (β : B ⟶ B')
    (h : ∀ s x, ψ'.app s ((α.app (s.image τ)).hom x) = (β.app s).hom (ψ.app s x)) (q : ℕ)
    (z : Cube.Term A q) :
    Cube.termMap β q (ψ.term q z) = ψ'.term q (Cube.termMap α q z) := by
  funext t
  by_cases hi : Set.InjOn τ (t.1 : Set κ)
  · rw [Cube.termMap_apply, ψ.term_apply_of_injOn _ _ hi, ψ'.term_apply_of_injOn _ _ hi,
      Cube.termMap_apply, map_zsmul, h]
  · rw [Cube.termMap_apply, ψ.term_apply_of_not_injOn _ _ hi, ψ'.term_apply_of_not_injOn _ _ hi,
      map_zero]

theorem term_mem_ker {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B) (p : ℕ)
    (x : LinearMap.ker (Cube.d A p)) : ψ.term p x.1 ∈ LinearMap.ker (Cube.d B p) := by
  rw [LinearMap.mem_ker, ← GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential ψ p x.1, x.2, map_zero]

theorem cechClass_eq {A : Cube.{0} ι R} {B : Cube.{0} κ S} (ψ : Cube.PullHom σ τ A B) (p : ℕ)
    (x x₂ : LinearMap.ker (Cube.d A (p + 1))) (y y₂ : LinearMap.ker (Cube.d B (p + 1)))
    (hy : y.1 = ψ.term (p + 1) x.1) (hy₂ : y₂.1 = ψ.term (p + 1) x₂.1)
    (h : cechClass A p x = cechClass A p x₂) : cechClass B p y = cechClass B p y₂ := by
  rw [← sub_eq_zero, ← map_sub] at h ⊢
  cases p with
  | zero =>
    rw [cechClass_zero_eq_zero_iff] at h ⊢
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, hy, hy₂, ← map_sub, ← Submodule.coe_sub, h, Submodule.coe_zero, map_zero,
      Submodule.coe_zero]
  | succ p =>
    obtain ⟨z, hz⟩ := (cechClass_succ_eq_zero_iff A p _).1 h
    refine (cechClass_succ_eq_zero_iff B p _).2 ⟨ψ.term (p + 1) z, ?_⟩
    rw [← GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential ψ (p + 1) z, hz, Submodule.coe_sub, Submodule.coe_sub, hy, hy₂, map_sub]

theorem cechClass_δ {S₀ : ShortComplex (Cube.{0} ι R)} {S₁ : ShortComplex (Cube.{0} κ S)}
    (hS₀ : (S₀.map (cechFunctor ι R)).ShortExact) (hS₁ : (S₁.map (cechFunctor κ S)).ShortExact)
    (ψ₁ : Cube.PullHom σ τ S₀.X₁ S₁.X₁) (ψ₂ : Cube.PullHom σ τ S₀.X₂ S₁.X₂)
    (ψ₃ : Cube.PullHom σ τ S₀.X₃ S₁.X₃)
    (hf : ∀ s x, ψ₂.app s ((S₀.f.app (s.image τ)).hom x) = (S₁.f.app s).hom (ψ₁.app s x))
    (hg : ∀ s x, ψ₃.app s ((S₀.g.app (s.image τ)).hom x) = (S₁.g.app s).hom (ψ₂.app s x))
    (p : ℕ) (x₃ : LinearMap.ker (Cube.d S₀.X₃ (p + 1)))
    (y₃ : LinearMap.ker (Cube.d S₁.X₃ (p + 1))) (hy : y₃.1 = ψ₃.term (p + 1) x₃.1) :
    ∃ (x₁ : LinearMap.ker (Cube.d S₀.X₁ (p + 1 + 1)))
      (y₁ : LinearMap.ker (Cube.d S₁.X₁ (p + 1 + 1))),
      y₁.1 = ψ₁.term (p + 1 + 1) x₁.1 ∧
      (hS₀.δ p (p + 1) rfl).hom (cechClass S₀.X₃ p x₃) = cechClass S₀.X₁ (p + 1) x₁ ∧
      (hS₁.δ p (p + 1) rfl).hom (cechClass S₁.X₃ p y₃) = cechClass S₁.X₁ (p + 1) y₁ := by
  obtain ⟨x₂, x₁, h₂, h₁⟩ := exists_lift_cechCocycle hS₀ p x₃
  refine ⟨x₁, ⟨_, ψ₁.term_mem_ker _ x₁⟩, rfl, δ_cechClass hS₀ p x₃ x₂ x₁ h₂ h₁,
    δ_cechClass hS₁ p y₃ (ψ₂.term _ x₂) _ ?_ ?_⟩
  · rw [termMap_term ψ₂ ψ₃ S₀.g S₁.g hg, h₂, hy]
  · show Cube.termMap S₁.f _ (ψ₁.term _ x₁.1) = Cube.d S₁.X₂ (p + 1) (ψ₂.term (p + 1) x₂)
    rw [termMap_term ψ₁ ψ₂ S₀.f S₁.f hf, h₁, GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential]

end Cube.PullHom

theorem cechAbPull_δ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    {S₀ : ShortComplex (AbSheaf T)} {S₁ : ShortComplex (AbSheaf T')} (hS₀ : S₀.ShortExact)
    (hS₁ : S₁.ShortExact) (h₀ : CechAcyclic V U S₀.X₁) (h₁ : CechAcyclic V' U' S₁.X₁)
    (ψ : S₀ ⟶ S₁.map (push f)) (n : ℕ)
    (x₃ : LinearMap.ker (Cube.d (cechAbCube S₀.X₃.obj V U) (n + 1)))
    (y₃ : LinearMap.ker (Cube.d (cechAbCube S₁.X₃.obj V' U') (n + 1)))
    (hy : y₃.1 = (cechAbPull f τ hτ (G := S₁.X₃) ψ.τ₃).term (n + 1) x₃.1) :
    ∃ (x₁ : LinearMap.ker (Cube.d (cechAbCube S₀.X₁.obj V U) (n + 1 + 1)))
      (y₁ : LinearMap.ker (Cube.d (cechAbCube S₁.X₁.obj V' U') (n + 1 + 1))),
      y₁.1 = (cechAbPull f τ hτ (G := S₁.X₁) ψ.τ₁).term (n + 1 + 1) x₁.1 ∧
      cechAbδ hS₀ h₀ n (cechClass _ n x₃) = cechClass _ (n + 1) x₁ ∧
      cechAbδ hS₁ h₁ n (cechClass _ n y₃) = cechClass _ (n + 1) y₁ := by
  refine Cube.PullHom.cechClass_δ (S₀ := S₀.map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor V U))
    (S₁ := S₁.map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor V' U'))
    (cechAbSheafFunctor_shortExact hS₀ h₀) (cechAbSheafFunctor_shortExact hS₁ h₁)
    (cechAbPull f τ hτ ψ.τ₁) (cechAbPull f τ hτ ψ.τ₂) (cechAbPull f τ hτ ψ.τ₃)
    (fun s x => ?_) (fun s x => ?_) n x₃ y₃ hy
  · let x' : S₀.X₁.obj.obj (op (cechOpen V U (s.image τ))) := x
    have e₁ : ψ.τ₂.hom.app (op (cechOpen V U (s.image τ)))
        (S₀.f.hom.app (op (cechOpen V U (s.image τ))) x') =
        S₁.f.hom.app (op ((Opens.map f).obj (cechOpen V U (s.image τ))))
          (ψ.τ₁.hom.app (op (cechOpen V U (s.image τ))) x') :=
      ConcreteCategory.congr_hom
        (congrArg (fun g => g.hom.app (op (cechOpen V U (s.image τ)))) ψ.comm₁₂) x' |>.symm
    have e₂ := ConcreteCategory.congr_hom (S₁.f.hom.naturality (homOfLE (hτ s)).op)
      (ψ.τ₁.hom.app (op (cechOpen V U (s.image τ))) x')
    exact (congrArg (fun z => S₁.X₂.obj.map (homOfLE (hτ s)).op z) e₁).trans e₂.symm
  · let x' : S₀.X₂.obj.obj (op (cechOpen V U (s.image τ))) := x
    have e₁ : ψ.τ₃.hom.app (op (cechOpen V U (s.image τ)))
        (S₀.g.hom.app (op (cechOpen V U (s.image τ))) x') =
        S₁.g.hom.app (op ((Opens.map f).obj (cechOpen V U (s.image τ))))
          (ψ.τ₂.hom.app (op (cechOpen V U (s.image τ))) x') :=
      ConcreteCategory.congr_hom
        (congrArg (fun g => g.hom.app (op (cechOpen V U (s.image τ)))) ψ.comm₂₃) x' |>.symm
    have e₂ := ConcreteCategory.congr_hom (S₁.g.hom.naturality (homOfLE (hτ s)).op)
      (ψ.τ₂.hom.app (op (cechOpen V U (s.image τ))) x')
    exact (congrArg (fun z => S₁.X₃.obj.map (homOfLE (hτ s)).op z) e₁).trans e₂.symm

end GlobalTheory

namespace GlobalTheory

open SheafPull

theorem cechAbHEquivH'_pull {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι]
    [LinearOrder κ] [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'}
    {U' : κ → Opens T'} (τ : κ → ι)
    (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V) (n : ℕ) :
    ∀ {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
      (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (n + 1)))
      (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (n + 1))),
      y.1 = (cechAbPull f τ hτ φ).term (n + 1) x.1 →
      cechAbHEquivH' hc' hG n (cechClass _ n y) =
        SheafPull.pull f φ n (homOfLE hV) (cechAbHEquivH' hc hF n (cechClass _ n x)) := by
  induction n with
  | zero => exact fun φ hF hG x y h => GlobalTheory.T.cechComparison_degreeZero_alternatingPullback f τ hτ hc hc' hV φ hF hG x y h
  | succ n ih =>
    intro F G φ hF hG x y hy
    have hSF := Flasque.injectiveShortComplex_shortExact F
    have hSG := Flasque.injectiveShortComplex_shortExact G
    obtain ⟨ψ, rfl⟩ := exists_hom_injectiveShortComplex f φ
    have injF : Injective (Flasque.injectiveShortComplex F).X₂ :=
      inferInstanceAs (Injective (Injective.under F))
    have injG : Injective (Flasque.injectiveShortComplex G).X₂ :=
      inferInstanceAs (Injective (Injective.under G))
    have a₃F := CechAcyclic.of_shortExact₃ hSF hF (cechAcyclic_of_injective _)
    have a₃G := CechAcyclic.of_shortExact₃ hSG hG (cechAcyclic_of_injective _)
    obtain ⟨c, hc₃⟩ := cechAbδ_surjective hSF hF n (cechClass _ (n + 1) x)
    obtain ⟨x₃, rfl⟩ := cechClass_surjective _ n c
    let y₃ : LinearMap.ker (Cube.d (cechAbCube (Flasque.injectiveShortComplex G).X₃.obj V' U')
        (n + 1)) :=
      ⟨(cechAbPull f τ hτ (G := (Flasque.injectiveShortComplex G).X₃) ψ.τ₃).term (n + 1) x₃.1, by
        rw [LinearMap.mem_ker, ← GlobalTheory.T.moduleCubePullHom_term_comm_cechDifferential, x₃.2, map_zero]⟩
    obtain ⟨x₁, y₁, hy₁, hx₁, hy₁'⟩ := cechAbPull_δ f τ hτ hSF hSG hF hG ψ n x₃ y₃ rfl
    have hxy : cechClass _ (n + 1) y = cechClass _ (n + 1) y₁ :=
      Cube.PullHom.cechClass_eq _ (n + 1) x x₁ y y₁ hy hy₁ (hc₃.symm.trans hx₁)
    rw [hxy, ← hy₁']
    refine (cechAbHEquivH'_δ hc' hSG hG a₃G n _).trans ?_
    rw [ih ψ.τ₃ a₃F a₃G x₃ y₃ rfl, ← hc₃]
    refine Eq.trans ?_ (congrArg _ (cechAbHEquivH'_δ hc hSF hF a₃F n _).symm)
    exact (SheafPull.pull_δ f n hSF hSG ψ (homOfLE hV) _).symm

end GlobalTheory

namespace GlobalTheory

open SheafPull

theorem cechOpen_le_preimage_image {X X' : Scheme.{0}} (f : X' ⟶ X) {ι κ : Type} [LinearOrder ι] (U : ι → X.Opens)
    (U' : κ → X'.Opens) (τ : κ → ι) (hτ : ∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) (s : Finset κ) :
    cechOpen ⊤ U' s ≤ f ⁻¹ᵁ cechOpen ⊤ U (s.image τ) := by
  intro x hx
  rw [mem_cechOpen] at hx
  show f.base x ∈ cechOpen ⊤ U (s.image τ)
  rw [mem_cechOpen]
  refine ⟨by simp, fun i hi => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
  exact hτ k (hx.2 k hk)

theorem exists_cechAbCocycle {X : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]
    {ι : Type} [LinearOrder ι] (F : X.Modules) (V : X.Opens) (U : ι → X.Opens) (n : ℕ)
    (x : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1))) :
    ∃ xa : LinearMap.ker (Cube.d (cechAbCube F.presheaf V U) (n + 1)),
      (∀ s, xa.1 s = sectionsOn.toΓ F _ (x.1 s)) ∧
      cechAbHEquiv R F V U n (cechClass _ n xa) = cechClass _ n x := by
  have hb : ∀ s : Finset ι, s.Nonempty → Function.Bijective ((cechAbCubeToCube R F V U).app s) :=
    fun _ _ => Function.bijective_id
  obtain ⟨y, hy⟩ := ((cechAbCubeToCube R F V U).term_bijective hb n).2 x.1
  have hk : Cube.d _ (n + 1) y = 0 :=
    ((cechAbCubeToCube R F V U).term_bijective hb (n + 1)).1
      (((cechAbCubeToCube R F V U).term_d _ y).trans ((congrArg _ hy).trans
        (x.2.trans (map_zero _).symm)))
  refine ⟨⟨y, LinearMap.mem_ker.2 hk⟩, fun s => ?_, ?_⟩
  · have := congrFun hy s
    rw [Cube.SemiHom.term_apply] at this
    rw [← this]
    rfl
  · exact ((cechAbCubeToCube R F V U).homology_cechClass n _).trans (congrArg _ (Subtype.ext hy))

theorem cechHEquivCoh_pull : ∀ (X X' : Scheme.{0}) (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)] (f : X' ⟶ X) (hσ : ∀ r, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) ((RingHom.id R) r)) (F : X.Modules) (G : X'.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ (Scheme.Modules.pushforward f).obj G) (ι κ : Type) [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ] (U : ι → X.Opens) (U' : κ → X'.Opens) (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hc' : ⨆ i, U' i = ⊤) (hU' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i)) (τ : κ → ι), (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) → ∀ (n : ℕ) (x : LinearMap.ker (Cube.d (cechCube R F ⊤ U) (n + 1))) (x' : LinearMap.ker (Cube.d (cechCube R G ⊤ U') (n + 1))), (∀ (t : {t : Finset κ // t.card = n + 1}) (s : {s : Finset ι // s.card = n + 1}) (h : cechOpen ⊤ U' t.1 ≤ f ⁻¹ᵁ cechOpen ⊤ U s.1), Set.InjOn τ (t.1 : Set κ) → s.1 = t.1.image τ → x'.1 t = sortSign τ t.1 • sectionsOn.res R G h (sectionsOn.map R φ (cechOpen ⊤ U s.1) (x.1 s))) → (∀ t : {t : Finset κ // t.card = n + 1}, ¬ Set.InjOn τ (t.1 : Set κ) → x'.1 t = 0) → cechHEquivCoh R hc' hU' G n (cechClass (cechCube R G ⊤ U') n x') = cohOn.pull hσ φ (le_top : (⊤ : X'.Opens) ≤ f ⁻¹ᵁ ⊤) n (cechHEquivCoh R hc hU F n (cechClass (cechCube R F ⊤ U) n x)) := by
  intro X X' R _ _ _ f hσ F G _ _ φ ι κ _ _ _ _ U U' hc hU hc' hU' τ hτ n x x' hx' h0
  have hτ' := cechOpen_le_preimage_image f U U' τ hτ
  obtain ⟨xa, hxa, hcx⟩ := exists_cechAbCocycle R F ⊤ U n x
  obtain ⟨ya, hya, hcy⟩ := exists_cechAbCocycle R G ⊤ U' n x'
  have hF := cechAcyclicMod_top_of_isAffineOpen hU F
  have hG := cechAcyclicMod_top_of_isAffineOpen hU' G
  have key : ya.1 = (cechAbPull f.base τ hτ' (toAbSheafPush φ)).term (n + 1) xa.1 := by
    funext t
    rw [hya]
    by_cases hi : Set.InjOn τ (t.1 : Set κ)
    · refine Eq.trans ?_ (Cube.PullHom.term_apply_of_injOn _ xa.1 t hi).symm
      rw [hx' t ⟨t.1.image τ, Cube.PullHom.card_image t hi⟩ (hτ' t.1) hi rfl, hxa]
      exact map_zsmul (sectionsOn.toΓ G _) (sortSign τ t.1) _
    · refine Eq.trans ?_ (Cube.PullHom.term_apply_of_not_injOn _ xa.1 t hi).symm
      rw [h0 t hi]
      exact map_zero (sectionsOn.toΓ G _)
  apply (cohOn.toH' G ⊤ n).injective
  rw [← hcx, ← hcy]
  refine (toH'_cechHEquivCohOn R hc'.ge hG n _).trans ?_
  refine Eq.trans ?_ (cohOn.toH'_pull hσ φ _ _).symm
  refine Eq.trans ?_ (congrArg _ (toH'_cechHEquivCohOn R hc.ge hF n _).symm)
  exact cechAbHEquivH'_pull (T := X.toPresheafedSpace.carrier) f.base τ hτ' hc.ge hc'.ge le_top n
    (toAbSheafPush φ) (cechAcyclicMod_iff.1 hF) (cechAcyclicMod_iff.1 hG) xa ya key

end GlobalTheory
