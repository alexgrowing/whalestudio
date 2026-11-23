import Development.EtaleCohomology.EtaleSheaves.LeafTwPairUniquePf
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairHtpyPf

def LeafTwTensExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTensFactor : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
  ∀ ν : Pair I J K, ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T),
  τ.IsTensor → IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResHtpy : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∀ u u' : T ⟶ res _ (tw q k), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem secMap_id_f {R : Type} [CommRing R] (I : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (I.X s) U) :
    Sec.map ((𝟙 I : I ⟶ I).f s) x = x := by
  rw [HomologicalComplex.id_f]; rfl

theorem secMap_addx {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem secMap_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem hom_reindex {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (Hh : ∀ i j, T.X i ⟶ K.X j)
    (U : Scheme.{0}) (s t v n : ℤ) (hv : v + 1 = n) (hs : s + t = n) (hs' : s + t = v + 1)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (Hh (v + 1) v) (τ.mul U s t (v + 1) hs' a b) = Sec.map (Hh n v) (τ.mul U s t n hs a b) := by
  subst hv; rfl

theorem pairHtpy_of_homotopy {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (μ μ' : Pair I J K) (u u' : T ⟶ K)
    (hu : τ.Compat μ (𝟙 I) (𝟙 J) u) (hu' : τ.Compat μ' (𝟙 I) (𝟙 J) u') (H : Homotopy u u') :
    LateralTheory.E.LeafTwPairUniquePf.PairHtpy μ μ' := by
  refine ⟨fun U s t w hw => (τ.mul U s t (w + 1) hw).compr₂ (((H.hom (w + 1) w).hom.app (op U)).hom), ?_, ?_⟩
  · intro V U g s t w hw a b
    simp only [LinearMap.compr₂_apply]
    rw [← τ.nat g s t (w + 1) hw a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (τ.mul _ s t (w + 1) hw a b)) ((H.hom (w + 1) w).hom.naturality g.op)).symm
  · intro U s t w hw a b
    simp only [LinearMap.compr₂_apply]
    have e1 := hu U s t w hw a b
    have e2 := hu' U s t w hw a b
    rw [secMap_id_f, secMap_id_f] at e1 e2
    rw [← e1, ← e2]
    have hc := H.comm w
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel w (w + 1) by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (w - 1) w by simp)] at hc
    rw [hc, secMap_add, secMap_add, secMap_comp, secMap_comp]
    have e3 := hom_reindex τ H.hom U s t (w - 1) w (by omega) hw (by omega) a b
    have e3' : (ModuleCat.Hom.hom ((H.hom (w - 1 + 1) (w - 1)).hom.app (op U))) (τ.mul U s t (w - 1 + 1) (by omega) a b) =
        Sec.map (H.hom w (w - 1)) (τ.mul U s t w hw a b) := e3
    rw [e3']
    rw [τ.leibniz, secMap_addx, secMap_usmul]
    dsimp only [Sec.map]
    abel

end LateralTheory.E.LeafTwPairHtpyPf

open LateralTheory.E.LeafTwPairHtpyPf in
theorem LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of (hE : LeafTwTensExists) (hF : LeafTensFactor) (hR : LeafTwTensRes)
    (hH : LeafTwResHtpy) : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := by
  intro q _ i j μ μ' hμ hμ'
  obtain ⟨T, τ, hτ⟩ := hE q i j
  obtain ⟨u, hu⟩ := hF (ZMod q) τ hτ μ
  obtain ⟨u', hu'⟩ := hF (ZMod q) τ hτ μ'
  obtain ⟨H⟩ := hH q (i + j) _ (hR q i j τ hτ) u u' (fun U ζ => by
    have a1 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    have a2 := hu' U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [secMap_id_f, secMap_id_f] at a1 a2
    rw [a1, a2, hμ U ζ, hμ' U ζ])
  exact pairHtpy_of_homotopy τ μ μ' u u' hu hu' H
