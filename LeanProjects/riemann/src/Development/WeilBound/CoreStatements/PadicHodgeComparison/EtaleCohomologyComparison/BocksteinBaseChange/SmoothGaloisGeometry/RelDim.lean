import Mathlib

open AlgebraicGeometry CategoryTheory

namespace CrystallineSemistableComparison

namespace RelDim

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

def Chart (n : ℕ) (x : X) : Prop :=
  ∃ (U : (Spec (CommRingCat.of K)).Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
    (e : V ≤ f ⁻¹ᵁ U), RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

theorem eq_top {U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) {x : X} (hx : x ∈ V) :
    U = ⊤ := by
  have : Subsingleton (Spec (CommRingCat.of K)) := by
    refine ⟨fun a b => PrimeSpectrum.ext ?_⟩
    have := a.isPrime
    have := b.isPrime
    rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal]
  have hy : f x ∈ U := e hx
  refine eq_top_iff.mpr fun z _ => ?_
  rwa [Subsingleton.elim z (f x)]

theorem basicOpen {n : ℕ} {U : (Spec (CommRingCat.of K)).Opens} {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) (a : Γ(X, V))
    (W : X.Opens) (hW : X.basicOpen a = W) (e' : W ≤ f ⁻¹ᵁ U) :
    RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U W e').hom := by
  subst hW
  have := hV.isLocalization_basicOpen a
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    Γ(X, X.basicOpen a) a (f.appLE U V e).hom h
  convert h2 using 1
  rw [← Scheme.Hom.appLE_map f e (homOfLE (X.basicOpen_le a)).op]
  rfl

theorem uniq {n m : ℕ} {U : (Spec (CommRingCat.of K)).Opens} (W : X.Opens) [Nonempty W] (e : W ≤ f ⁻¹ᵁ U)
    (hn : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U W e).hom)
    (hm : RingHom.IsStandardSmoothOfRelativeDimension m (f.appLE U W e).hom) : n = m := by
  let := (f.appLE U W e).hom.toAlgebra
  have h1 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ n hn
  have h2 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _ _ _ _ _ _ m hm
  exact_mod_cast h1.symm.trans h2

theorem chart_uniq {n m : ℕ} {x : X} (hn : Chart f n x) (hm : Chart f m x) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn
  obtain ⟨U', hU', V', hV', hx', e', h'⟩ := hm
  have h1 := eq_top f e hx
  have h2 := eq_top f e' hx'
  subst h1 h2
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter hV hV' x ⟨hx, hx'⟩
  have ea : X.basicOpen a ≤ f ⁻¹ᵁ ⊤ := (X.basicOpen_le a).trans e
  have ha := basicOpen f hV e h a _ rfl ea
  have hb := basicOpen f hV' e' h' b _ hab.symm ea
  have : Nonempty (X.basicOpen a) := ⟨⟨x, hxa⟩⟩
  exact uniq f _ ea ha hb

theorem exists_chart [Smooth f] (x : X) : ∃ n, Chart f n x := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, U, hU, V, hV, hx, e, P.isStandardSmoothOfRelativeDimension rfl⟩

theorem isOpen_chart (n : ℕ) : IsOpen {x | Chart f n x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hU, V, hV, hx, e, h⟩
  exact ⟨V, fun y hy => ⟨U, hU, V, hV, hy, e, h⟩, V.isOpen, hx⟩

end RelDim

open RelDim in

theorem exists_smoothOfRelativeDimension {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] [ConnectedSpace X] : ∃ d, SmoothOfRelativeDimension d f := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨n, hn⟩ := exists_chart f x0
  have hclopen : IsClopen {x | Chart f n x} := by
    refine ⟨?_, isOpen_chart f n⟩
    rw [← isOpen_compl_iff]
    have : {x | Chart f n x}ᶜ = ⋃ m ∈ {m | m ≠ n}, {x | Chart f m x} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_chart f x
        exact ⟨m, fun h => hx (h ▸ hm), hm⟩
      · rintro ⟨m, hmn, hm⟩ hx
        exact hmn (chart_uniq f hm hx)
    rw [this]
    exact isOpen_biUnion fun m _ => isOpen_chart f m
  have huniv := (isClopen_iff.mp hclopen).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨x0, hn⟩)
  refine ⟨n, ⟨fun x => ?_⟩⟩
  have hx : x ∈ {x | Chart f n x} := huniv ▸ Set.mem_univ x
  exact hx

end CrystallineSemistableComparison
