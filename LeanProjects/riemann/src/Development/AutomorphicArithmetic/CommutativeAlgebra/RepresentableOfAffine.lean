import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.EquivOfAffineBijective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

theorem UpperTheory.representable_of_affine :
    LeafHI → B3 → C4 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {P P' : PSh} (r : P' ⟶ P) (c : ∀ T : Scheme.{0}, P'.obj (op T) → Γ(T, ⊤)), (∀ {T T' : Scheme.{0}} (f : T' ⟶ T) (x : P'.obj (op T)), c T' (P'.map f.op x) = f.appTop.hom (c T x)) → (∀ T : Scheme.{0}, Function.Bijective fun x : P'.obj (op T) => (r.app (op T) x, c T x)) → ∀ Y : Scheme.{0}, IsUnit (q : Γ(Y, ⊤)) → ∀ φ : P ⟶ yoneda.obj Y, (∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T))) → Eqv _ (disc.map r) (tw q i) := by
  intro hHI hB hC q _ i P P' r c hc hb Y hq φ hφ
  have hnat : ∀ {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V) (x : P'.obj U),
      φ.app V (r.app V (P'.map f x)) = f.unop ≫ φ.app U (r.app U x) := by
    intro U V f x
    have h1 : r.app V (P'.map f x) = P.map f (r.app U x) :=
      ConcreteCategory.congr_hom (r.naturality f) x
    have h2 : φ.app V (P.map f (r.app U x)) = f.unop ≫ φ.app U (r.app U x) :=
      ConcreteCategory.congr_hom (φ.naturality f) (r.app U x)
    rw [h1, h2]
  let φ' : P' ⟶ yoneda.obj 𝔸(Fin 1; Y) :=
    { app := fun U => TypeCat.ofHom fun x =>
        AffineSpace.homOfVector (φ.app U (r.app U x)) (fun _ => c U.unop x)
      naturality := fun U V f => by
        ext x
        change AffineSpace.homOfVector (φ.app V (r.app V (P'.map f x))) (fun _ => c V.unop (P'.map f x)) =
          f.unop ≫ AffineSpace.homOfVector (φ.app U (r.app U x)) (fun _ => c U.unop x)
        rw [AffineSpace.comp_homOfVector, hnat f x]
        congr 1
        funext _
        exact hc f.unop x }
  have hφ'v : ∀ (T : Scheme.{0}) (x : P'.obj (op T)), φ'.app (op T) x =
      AffineSpace.homOfVector (φ.app (op T) (r.app (op T) x)) (fun _ => c T x) := fun _ _ => rfl
  have hφ' : ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ'.app (op T)) := by
    intro T hT
    constructor
    · intro x y hxy
      rw [hφ'v, hφ'v] at hxy
      have h1 := congrArg (· ≫ 𝔸(Fin 1; Y) ↘ Y) hxy
      simp only [AffineSpace.homOfVector_over] at h1
      have h2 := congrArg (fun g => g.appTop (AffineSpace.coord Y (0 : Fin 1))) hxy
      simp only [AffineSpace.homOfVector_appTop_coord] at h2
      exact (hb T).1 (Prod.ext ((hφ T hT).1 h1) h2)
    · intro g
      obtain ⟨p, hp⟩ := (hφ T hT).2 (g ≫ 𝔸(Fin 1; Y) ↘ Y)
      obtain ⟨x, hx⟩ := (hb T).2 (p, g.appTop (AffineSpace.coord Y (0 : Fin 1)))
      have hx1 : r.app (op T) x = p := congrArg Prod.fst hx
      have hx2 : c T x = g.appTop (AffineSpace.coord Y (0 : Fin 1)) := congrArg Prod.snd hx
      refine ⟨x, ?_⟩
      rw [hφ'v]
      refine AffineSpace.hom_ext ?_ ?_
      · rw [AffineSpace.homOfVector_over, hx1]
        exact hp
      · intro j
        rw [AffineSpace.homOfVector_appTop_coord, hx2, Subsingleton.elim j 0]
  have comm : φ' ≫ yoneda.map (𝔸(Fin 1; Y) ↘ Y) = r ≫ φ := by
    ext U x
    exact AffineSpace.homOfVector_over _ _
  have comm2 : disc.map φ' ≫ sch.map (𝔸(Fin 1; Y) ↘ Y) = disc.map r ≫ disc.map φ := by
    change disc.map φ' ≫ disc.map (yoneda.map (𝔸(Fin 1; Y) ↘ Y)) = _
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  have e1 := UpperTheory.equiv_of_affine_bijective _ (tw q i) φ hφ
  have e2 := UpperTheory.equiv_of_affine_bijective _ (tw q i) φ' hφ'
  have e3 := hHI hB hC q i Y hq
  intro n
  have key : pull _ (disc.map r) (tw q i) n ∘ pull _ (disc.map φ) (tw q i) n =
      pull _ (disc.map φ') (tw q i) n ∘ pull _ (sch.map (𝔸(Fin 1; Y) ↘ Y)) (tw q i) n := by
    funext x
    have a1 := pull_comp (ZMod q) (disc.map r) (disc.map φ) (tw q i) n x
    have a2 := pull_comp (ZMod q) (disc.map φ') (sch.map (𝔸(Fin 1; Y) ↘ Y)) (tw q i) n x
    exact a1.symm.trans ((congrArg (fun g => pull (ZMod q) g (tw q i) n x) comm2.symm).trans a2)
  refine (Function.Bijective.of_comp_iff (pull _ (disc.map r) (tw q i) n) (e1 n)).1 ?_
  rw [key]
  exact (e2 n).comp (e3 n)
