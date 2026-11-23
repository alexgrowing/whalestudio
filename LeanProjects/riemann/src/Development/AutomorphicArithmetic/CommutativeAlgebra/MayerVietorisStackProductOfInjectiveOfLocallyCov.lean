import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.FullyFaithfulLift

private theorem cancel_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) [F.Faithful] (c c' : J ⥤ C) (h : c ⋙ F = c' ⋙ F) : c = c' := by
  have hob : ∀ j, c.obj j = c'.obj j := fun j => hobj (congrArg (fun G => G.obj j) h)
  refine CategoryTheory.Functor.ext hob ?_
  intro X Y f
  apply F.map_injective
  have e := CategoryTheory.Functor.congr_hom h f
  simp only [CategoryTheory.Functor.comp_map] at e
  rw [e]
  simp [eqToHom_map]

private theorem lift_comp {J C D : Type} [Category J] [Category C] [Category D] (F : C ⥤ D)
    [F.Full] [F.Faithful] (c : J ⥤ D) (l : J → C) (hl : ∀ j, F.obj (l j) = c.obj j) :
    ∃ c' : J ⥤ C, c' ⋙ F = c := by
  refine ⟨{ obj := l
            map := fun {i j} f => F.preimage (eqToHom (hl i) ≫ c.map f ≫ eqToHom (hl j).symm)
            map_id := fun i => F.map_injective (by simp)
            map_comp := fun f g => F.map_injective (by simp) }, ?_⟩
  refine CategoryTheory.Functor.ext hl (fun i j f => ?_)
  simp

private theorem sp_map_eq {E : Spc} {a b : Act} (φ : Act.Hom a b) {k : ℕ} {T : Scheme.{0}} (x : Sx (Sp E a) k T) :
    Sx.map (Sp.map E φ) x = ((x.1, Sx.map (spcMap φ) x.2) : Sx (Sp E b) k T) := rfl

private theorem fn_obj_inj {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (A : CommRingCat.{0}) : Function.Injective (φ.fn A).obj := by
  intro x y h
  have e : φ.d.app A x.pt = φ.d.app A y.pt := congrArg Ob.pt h
  cases x
  cases y
  congr
  exact hi A e

private theorem fn_faithful {a b : Act} (φ : Act.Hom a b) (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g))
    (A : CommRingCat.{0}) : (φ.fn A).Faithful :=
  ⟨fun {_ _} _ _ h => Subtype.ext ((hb A).1 (congrArg Subtype.val h))⟩

private theorem fn_full {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) (A : CommRingCat.{0}) : (φ.fn A).Full := by
  constructor
  intro x y u
  obtain ⟨g, hg⟩ := (hb A).2 u.1
  refine ⟨⟨g, ?_⟩, ?_⟩
  · apply hi A
    have e := φ.eq A g y.pt
    have hg' : φ.g.app A g = u.1 := hg
    rw [hg'] at e
    exact u.2.trans e.symm
  · apply Subtype.ext
    exact hg

private theorem mono_sp (E : Spc) {a b : Act} (φ : Act.Hom a b) (hi : ∀ A, Function.Injective (fun x : a.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Mono (Sp.map E φ) := by
  apply UpperTheory.mono_of_injective_on_simplices
  intro k T x y h
  simp only [sp_map_eq] at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  haveI := fn_faithful φ hb Γ(T, ⊤)
  have h2' : (show ComposableArrows (Ob a Γ(T, ⊤)) k from x.2) ⋙ φ.fn Γ(T, ⊤) =
      (show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2) ⋙ φ.fn Γ(T, ⊤) := h2
  exact Prod.ext h1 (cancel_comp (φ.fn Γ(T, ⊤)) (fn_obj_inj φ hi _) _ _ h2')

private theorem lift_sp (E : Spc) {a₁ a : Act} (φ : Act.Hom a₁ a) (hi : ∀ A, Function.Injective (fun x : a₁.D.obj A => φ.d.app A x))
    (hb : ∀ A, Function.Bijective (fun g : a₁.G.obj A => φ.g.app A g)) {k : ℕ} {W : Scheme.{0}} (y : Sx (Sp E a) k W)
    (y₀ : a₁.D.obj Γ(W, ⊤))
    (h0 : φ.d.app _ y₀ = ((show ComposableArrows (Ob a Γ(W, ⊤)) k from y.2).obj 0).pt) :
    ∃ x : Sx (Sp E a₁) k W, Sx.map (Sp.map E φ) x = y := by
  classical
  set c : ComposableArrows (Ob a Γ(W, ⊤)) k := y.2 with hc
  have hl : ∀ j : Fin (k + 1), ∃ o : Ob a₁ Γ(W, ⊤), (φ.fn Γ(W, ⊤)).obj o = c.obj j := by
    intro j
    have hle : (0 : Fin (k + 1)) ≤ j := Fin.zero_le _
    obtain ⟨u, hu⟩ := c.map (homOfLE hle)
    obtain ⟨g, hg⟩ := (hb Γ(W, ⊤)).2 u⁻¹
    refine ⟨⟨a₁.smul _ g y₀⟩, ?_⟩
    have e := φ.eq Γ(W, ⊤) g y₀
    have hg' : φ.g.app Γ(W, ⊤) g = u⁻¹ := hg
    have h0' : φ.d.app Γ(W, ⊤) y₀ = (c.obj 0).pt := h0
    have key : (c.obj j).pt = φ.d.app Γ(W, ⊤) (a₁.smul _ g y₀) := by
      erw [e, hg', h0', hu, ← a.mul_smul, inv_mul_cancel, a.one_smul]
    exact congrArg Ob.mk key.symm
  choose l hl' using hl
  haveI := fn_full φ hi hb Γ(W, ⊤)
  haveI := fn_faithful φ hb Γ(W, ⊤)
  obtain ⟨c', hc'⟩ := lift_comp (φ.fn Γ(W, ⊤)) c l hl'
  refine ⟨((y.1, show Sx (spc a₁) k W from c') : Sx (Sp E a₁) k W), ?_⟩
  refine (sp_map_eq φ _).trans ?_
  exact Prod.ext rfl hc'

end UpperTheory.FullyFaithfulLift

theorem UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered :
    ∀ (R : Type) [CommRing R] (E : Spc) {a₁ a₂ a : Act} (φ₁ : Act.Hom a₁ a) (φ₂ : Act.Hom a₂ a),
        (∀ A, Function.Injective (fun x : a₁.D.obj A => φ₁.d.app A x)) → (∀ A, Function.Injective (fun x : a₂.D.obj A => φ₂.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a₁.G.obj A => φ₁.g.app A g)) → (∀ A, Function.Bijective (fun g : a₂.G.obj A => φ₂.g.app A g)) →
        (∀ (T : Scheme.{0}) (x : a.D.obj Γ(T, ⊤)), Loc T fun V g =>
          (∃ y, φ₁.d.app _ y = a.D.map g.appTop x) ∨ (∃ y, φ₂.d.app _ y = a.D.map g.appTop x)) →
        Cover2 R (Sp.map E φ₁) (Sp.map E φ₂) := by
  intro R _ E a₁ a₂ a φ₁ φ₂ i₁ i₂ b₁ b₂ hl
  refine UpperTheory.mayerVietorisCover_of_mono_of_zariskiLocal R _ _ (UpperTheory.FullyFaithfulLift.mono_sp E φ₁ i₁ b₁) (UpperTheory.FullyFaithfulLift.mono_sp E φ₂ i₂ b₂) (fun k T y => ?_)
  obtain ⟨S, hS, hP⟩ := hl T ((show ComposableArrows (Ob a Γ(T, ⊤)) k from y.2).obj 0).pt
  refine ⟨S, hS, fun W h hh => ?_⟩
  rcases hP W h hh with ⟨y₀, e⟩ | ⟨y₀, e⟩
  · exact Or.inl (UpperTheory.FullyFaithfulLift.lift_sp E φ₁ i₁ b₁ (y.res h) y₀ e)
  · exact Or.inr (UpperTheory.FullyFaithfulLift.lift_sp E φ₂ i₂ b₂ (y.res h) y₀ e)
