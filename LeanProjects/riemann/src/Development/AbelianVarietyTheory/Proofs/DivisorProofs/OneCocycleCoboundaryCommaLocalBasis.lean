import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.Basis

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']

theorem span_map_eq_top (F : C ⥤ CommAlgCat.{0} R) {S S' : C} (u : S ⟶ S') {n : ℕ}
    {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
  have := congrArg (Ideal.map (mp F u)) hb
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

theorem eq_zero_of_local (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  obtain ⟨w₁⟩ := h₁
  obtain ⟨w₂⟩ := h₂
  obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S w₁ w₂
  exact sep_std H hb z fun S' ψ ⟨i, hi⟩ ↦ by
    obtain ⟨t₃, h1, h2, h3⟩ := h i S' ψ hi
    exact hz t₃ S' ψ h1 h2 h3

theorem eq_zero_of_local₃ (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ t₃ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S))
    (h₃ : Nonempty (G.obj t₃ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → Nonempty (t₃ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  refine eq_zero_of_local F G H hdir h₁ h₂ z fun t S' ψ h1 h2 ⟨w⟩ ↦ ?_
  obtain ⟨w₃⟩ := h₃
  obtain ⟨a1⟩ := h1
  obtain ⟨a2⟩ := h2
  refine eq_zero_of_local F G H hdir ⟨w⟩ ⟨w₃ ≫ ψ⟩ _ fun t' S'' χ ⟨a⟩ h3 h4 ↦ ?_
  rw [← mp_comp]
  exact hz t' S'' (ψ ≫ χ) ⟨a1 ≫ a⟩ ⟨a2 ≫ a⟩ h3 h4

theorem exists_glue_points (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (t₁ t₂ : C') (s : ∀ t, F.obj (G.obj t))
    (hs : ∀ t t' (a : t ⟶ t'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → s t' = mp F (G.map a) (s t)) :
    ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ (x S) = mp F w (s t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
        x S' = mp F ψ (x S)) := by
  have key : ∀ t t' (S : C) (w : G.obj t ⟶ S) (w' : G.obj t' ⟶ S), Nonempty (t₁ ⟶ t) →
      Nonempty (t₂ ⟶ t) → Nonempty (t₁ ⟶ t') → Nonempty (t₂ ⟶ t') →
      mp F w (s t) = mp F w' (s t') := by
    intro t t' S w w' h1 h2 h1' h2'
    refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w⟩ ⟨w'⟩ _ fun t'' S' ψ ⟨a⟩ ⟨a'⟩ ⟨w''⟩ ↦ ?_)
    have e1 : w ≫ ψ = G.map a ≫ w'' := Subsingleton.elim _ _
    have e2 : w' ≫ ψ = G.map a' ≫ w'' := Subsingleton.elim _ _
    rw [map_sub, ← mp_comp, ← mp_comp, e1, e2, mp_comp, mp_comp, ← hs t t'' a h1 h2,
      ← hs t' t'' a' h1' h2', sub_self]
  classical
  let σ : ∀ S, F.obj S := fun S ↦
    if h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) then
      mp F h.choose_spec.2.2.some (s h.choose) else 0
  have hσ : ∀ t S (w : G.obj t ⟶ S), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      σ S = mp F w (s t) := by
    intro t S w h1 h2
    have h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) :=
      ⟨t, h1, h2, ⟨w⟩⟩
    simp only [σ, dif_pos h]
    exact key _ _ _ _ _ h.choose_spec.1 h.choose_spec.2.1 h1 h2
  have h1 : ∀ S, ∃ x : F.obj S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ x = mp F w (s t) := by
    intro S
    by_cases hS : Nonempty (G.obj t₁ ⟶ S) ∧ Nonempty (G.obj t₂ ⟶ S)
    · obtain ⟨⟨w₁⟩, ⟨w₂⟩⟩ := hS
      obtain ⟨n, b, hb, hcov⟩ := hdir t₁ t₂ S w₁ w₂
      obtain ⟨x, hx⟩ := glue_std H hb (fun S' _ ↦ σ S') fun S' S'' ψ χ ⟨i, hi⟩ ↦ by
        obtain ⟨t, h1, h2, ⟨w⟩⟩ := hcov i S' ψ hi
        show σ S'' = mp F χ (σ S')
        rw [hσ t S'' (w ≫ χ) h1 h2, hσ t S' w h1 h2, mp_comp]
      refine ⟨x, fun _ _ t S' ψ w h1 h2 ↦
        sub_eq_zero.1 <| sep_std H (span_map_eq_top F ψ hb) _ fun S'' χ ⟨i, hi⟩ ↦ ?_⟩
      have hi' : IsUnit (mp F (ψ ≫ χ) (b i)) := by rw [mp_comp]; exact hi
      rw [map_sub, ← mp_comp, hx S'' (ψ ≫ χ) ⟨i, hi'⟩, ← mp_comp, hσ t S'' (w ≫ χ) h1 h2,
        sub_self]
    · exact ⟨0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hS⟩
  choose x hx using h1
  refine ⟨x, hx, fun S S' ψ h1 h2 ↦ ?_⟩
  obtain ⟨w₁⟩ := h1
  obtain ⟨w₂⟩ := h2
  refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ _ fun t S'' χ h1' h2' ⟨w⟩ ↦ ?_)
  rw [map_sub, hx S' ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ t S'' χ w h1' h2', ← mp_comp,
    hx S ⟨w₁⟩ ⟨w₂⟩ t S'' (ψ ≫ χ) w h1' h2', sub_self]

theorem oneCocycle_coboundary_comma_localBasis (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] [Quiver.IsThin C']
    (H : HasLoc F) (hcov : (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) →
        ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u))
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'))
    (hy : ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
      y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) :
    ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'),
      g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  classical

  let yb : ∀ t t' : C', F.obj (G.obj t') := fun t t' ↦
    if h : Nonempty (T ⟶ G.obj t) ∧ Nonempty (t ⟶ t') then y t t' h.1.some h.2.some else 0
  have hyb : ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), y t t' u a = yb t t' := by
    intro t t' u a
    have h : Nonempty (T ⟶ G.obj t) ∧ Nonempty (t ⟶ t') := ⟨⟨u⟩, ⟨a⟩⟩
    simp only [yb, dif_pos h]
    exact congrArg₂ (y t t') (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hyc : ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
      yb t t'' = mp F (G.map b) (yb t t') + yb t' t'' := by
    intro t t' t'' u a b
    rw [← hyb t t'' u (a ≫ b), ← hyb t t' u a, ← hyb t' t'' (u ≫ G.map a) b]
    exact hy t t' t'' u a b

  obtain ⟨n, b, hb, hcT⟩ := hcov T
  have hpt : ∀ i : Fin n, ∃ (p : C') (_ : T ⟶ G.obj p), ∀ S (u : T ⟶ S),
      IsUnit (mp F u (b i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H T (b i)
    obtain ⟨p, v, w, -⟩ := hcT i T' l hl
    exact ⟨p, v, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p v hp using hpt

  have hc0 : ∀ i j : Fin n, ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj (p i) ⟶ S) →
      Nonempty (G.obj (p j) ⟶ S) → ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (p i ⟶ t) →
        Nonempty (p j ⟶ t) → mp F ψ (x S) = mp F w (yb (p j) t - yb (p i) t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj (p i) ⟶ S) → Nonempty (G.obj (p j) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i j
    refine exists_glue_points F G H hdir (p i) (p j) _ fun t t' a ⟨ai⟩ ⟨aj⟩ ↦ ?_
    rw [map_sub, hyc (p j) t t' (v j) aj a, hyc (p i) t t' (v i) ai a]
    ring
  choose c hc hc' using hc0
  have hs : ∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j)))
      (fun S (_ : T ⟶ S) ↦ c i j S) := fun i j S S' u ψ h ↦
    hc' i j S S' ψ (hp i S u h.1) (hp j S u h.2)
  have hcc : ∀ i j k S (u : T ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      IsUnit (mp F u (b k)) → c j k S - c i k S + c i j S = 0 := by
    intro i j k S u hi hj hk
    refine eq_zero_of_local₃ F G H hdir (hp i S u hi) (hp j S u hj) (hp k S u hk) _
      fun t S' ψ ai aj ak ⟨w⟩ ↦ ?_
    rw [map_add, map_sub, hc j k S (hp j S u hj) (hp k S u hk) t S' ψ w aj ak,
      hc i k S (hp i S u hi) (hp k S u hk) t S' ψ w ai ak,
      hc i j S (hp i S u hi) (hp j S u hj) t S' ψ w ai aj]
    simp only [map_sub]
    ring
  obtain ⟨e, he, he'⟩ := cech1 H hb (fun i j S (_ : T ⟶ S) ↦ c i j S) hs hcc
  have he'' : ∀ i j S (u : T ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      c i j S = e j S u - e i S u := he'

  have hX0 : ∀ i (t : C') (_ : T ⟶ G.obj t), ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t ⟶ S) →
      Nonempty (G.obj (p i) ⟶ S) → ∀ t' S' (ψ : S ⟶ S') (w : G.obj t' ⟶ S'), Nonempty (t ⟶ t') →
        Nonempty (p i ⟶ t') → mp F ψ (x S) = mp F w (yb (p i) t' - yb t t')) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t ⟶ S) → Nonempty (G.obj (p i) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i t u
    refine exists_glue_points F G H hdir t (p i) _ fun t' t'' a ⟨a0⟩ ⟨ai⟩ ↦ ?_
    rw [map_sub, hyc (p i) t' t'' (v i) ai a, hyc t t' t'' u a0 a]
    ring
  choose X hX hX' using hX0

  have indep : ∀ t (u : T ⟶ G.obj t) S (ψ : G.obj t ⟶ S) i j, IsUnit (mp F (u ≫ ψ) (b i)) →
      IsUnit (mp F (u ≫ ψ) (b j)) → X i t u S - e i S (u ≫ ψ) = X j t u S - e j S (u ≫ ψ) := by
    intro t u S ψ i j hi hj
    have key : X i t u S - X j t u S + c i j S = 0 :=
      eq_zero_of_local₃ F G H hdir ⟨ψ⟩ (hp i S _ hi) (hp j S _ hj) _ fun t' S' χ a0 ai aj ⟨w⟩ ↦ by
        rw [map_add, map_sub, hX i t u S ⟨ψ⟩ (hp i S _ hi) t' S' χ w a0 ai,
          hX j t u S ⟨ψ⟩ (hp j S _ hj) t' S' χ w a0 aj,
          hc i j S (hp i S _ hi) (hp j S _ hj) t' S' χ w ai aj]
        simp only [map_sub]
        ring
    linear_combination key - he'' i j S (u ≫ ψ) hi hj

  have hg0 : ∀ t (u : T ⟶ G.obj t), ∃ x : F.obj (G.obj t), ∀ S (ψ : G.obj t ⟶ S) i,
      IsUnit (mp F (u ≫ ψ) (b i)) → mp F ψ x = X i t u S - e i S (u ≫ ψ) := by
    intro t u
    let σ : ∀ S, (G.obj t ⟶ S) → F.obj S := fun S ψ ↦
      if h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) then X h.choose t u S - e h.choose S (u ≫ ψ) else 0
    have hσ : ∀ S ψ i, IsUnit (mp F (u ≫ ψ) (b i)) → σ S ψ = X i t u S - e i S (u ≫ ψ) := by
      intro S ψ i hi
      have h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := ⟨i, hi⟩
      simp only [σ, dif_pos h]
      exact indep t u S ψ _ i h.choose_spec hi
    obtain ⟨x, hx⟩ := glue_std H (span_map_eq_top F u hb) σ fun S S' ψ χ ⟨i, hi⟩ ↦ by
      have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
      have hi'' : IsUnit (mp F (u ≫ ψ ≫ χ) (b i)) := by
        rw [← Category.assoc, mp_comp]; exact hi'.map _
      rw [hσ S' (ψ ≫ χ) i hi'', hσ S ψ i hi', map_sub, ← hX' i t u S S' χ ⟨ψ⟩ (hp i S _ hi'),
        ← he i S S' (u ≫ ψ) χ hi', Category.assoc]
    exact ⟨x, fun S ψ i hi ↦ by
      rw [hx S ψ ⟨i, by rw [mp_comp] at hi; exact hi⟩, hσ S ψ i hi]⟩
  choose g hg using hg0
  refine ⟨g, fun t t' u a ↦ ?_⟩
  rw [hyb]
  refine sub_eq_zero.1 (sep_std H (span_map_eq_top F (u ≫ G.map a) hb) _ fun S χ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F ((u ≫ G.map a) ≫ χ) (b i)) := by rw [mp_comp]; exact hi
  have hi'' : IsUnit (mp F (u ≫ G.map a ≫ χ) (b i)) := by rw [← Category.assoc]; exact hi'
  rw [map_sub, map_sub, hg t' (u ≫ G.map a) S χ i hi', ← mp_comp, hg t u S (G.map a ≫ χ) i hi'',
    Category.assoc]
  have key : X i t' (u ≫ G.map a) S - X i t u S - mp F χ (yb t t') = 0 :=
    eq_zero_of_local F G H hdir ⟨χ⟩ (hp i S _ hi') _ fun t'' S' ψ ⟨a'⟩ ai ⟨w⟩ ↦ by
      rw [map_sub, map_sub, hX i t' (u ≫ G.map a) S ⟨χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a'⟩ ai,
        hX i t u S ⟨G.map a ≫ χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a ≫ a'⟩ ai, ← mp_comp,
        (Subsingleton.elim _ _ : χ ≫ ψ = G.map a' ≫ w), mp_comp, hyc t t' t'' u a a']
      simp only [map_sub, map_add]
      ring
  linear_combination key

theorem oneCocycle_vanishing_comma_of_basis : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T y hy
  exact oneCocycle_coboundary_comma_localBasis F G H hcov hdir T y hy

end GlobalTheory.CatCoh.Desc.Basis
