import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.hasPres_of_injective_equivariant :
    ∀ {G O LL : Type} [Group G] [CommRing O] [IsNoetherianRing O] [Field LL] [Algebra O LL] {Xs : Type} {n : ℕ}
      (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      (actP : G → P → P) (actQ : G → Q → Q) (ι : P →ₗ[O] Q) (f' : G → P) (f : G → Q),
      Function.Injective ι → (∀ g u, ι (actP g u) = actQ g (ι u)) → (∀ g, ι (f' g) = f g) →
      HasPres LL N actQ f → HasPres LL N actP f' := by
  intro G O LL _ _ _ _ _ Xs n N P Q _ _ _ _ actP actQ ι f' f hinj heq hf h
  obtain ⟨a, x, E, Y, hfg, hst, hE, φ, hφ, hfφ⟩ := h
  let Y' : Submodule O (Fin a → Fin n → LL) := ((LinearMap.range ι).comap φ).map Y.subtype
  have hle : Y' ≤ Y := Submodule.map_subtype_le _ _
  have hmem : ∀ y : Y, (y : Fin a → Fin n → LL) ∈ Y' ↔ φ y ∈ LinearMap.range ι := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := Subtype.ext hzy
      subst this
      exact hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hfg' : Y'.FG := by
    haveI : IsNoetherian O Y := isNoetherian_of_fg_of_noetherian Y hfg
    exact Submodule.FG.map _ (IsNoetherian.noetherian _)
  have hst' : ∀ g, ∀ y ∈ Y', actN LL (fun j => N (x j)) g y ∈ Y' := by
    intro g y hy
    have h1 := (hmem ⟨y, hle hy⟩).1 hy
    obtain ⟨u, hu⟩ := h1
    refine (hmem ⟨_, hst g y (hle hy)⟩).2 ⟨actP g u, ?_⟩
    rw [heq, hu]
    exact (hφ g ⟨y, hle hy⟩).symm
  have hE' : ∀ g, actN LL (fun j => N (x j)) g E - E ∈ Y' := by
    intro g
    exact (hmem ⟨_, hE g⟩).2 ⟨f' g, by rw [hf, hfφ]⟩
  let ψ : Y' →ₗ[O] LinearMap.range ι :=
    LinearMap.codRestrict _ (φ ∘ₗ Submodule.inclusion hle)
      (fun y => (hmem ⟨y.1, hle y.2⟩).1 y.2)
  let φ' : Y' →ₗ[O] P := (LinearEquiv.ofInjective ι hinj).symm.toLinearMap ∘ₗ ψ
  have key : ∀ y : Y', ι (φ' y) = φ ⟨y.1, hle y.2⟩ := by
    intro y
    have h2 : ((LinearEquiv.ofInjective ι hinj) (φ' y)) = ψ y :=
      (LinearEquiv.ofInjective ι hinj).apply_symm_apply (ψ y)
    exact congrArg Subtype.val h2
  refine ⟨a, x, E, Y', hfg', hst', hE', φ', ?_, ?_⟩
  · intro g y
    apply hinj
    rw [heq, key, key]
    exact hφ g ⟨y.1, hle y.2⟩
  · intro g
    apply hinj
    rw [key, hf]
    exact hfφ g
