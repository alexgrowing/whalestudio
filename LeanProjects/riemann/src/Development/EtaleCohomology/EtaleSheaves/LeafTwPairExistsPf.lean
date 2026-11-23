import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable {R : Type} [CommRing R]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using h.symm

theorem map_map {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

def post {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (Sec.map (u.f w) _) = Sec.map (u.f w) _
    rw [res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) _) =
      Sec.map (u.f (w + 1)) _ + s.negOnePow • Sec.map (u.f (w + 1)) _
    rw [map_map, u.comm w (w + 1), ← map_map, μ.leibniz]
    simp only [Sec.map, map_add, map_zsmul_unit]

theorem post_mul {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : (post μ u).mul U s t w h a b = Sec.map (u.f w) (μ.mul U s t w h a b) := rfl

def LeafTwTensEx : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (T : Cx (ZMod q))
  (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor →
    IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResExt : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) (T : Cx (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∃ u : T ⟶ res _ (tw q k), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen k ζ

theorem LeafTwPairExists_of (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) (h3 : LeafTwResExt) :
    LateralTheory.E.CupProductRingLaws.LeafTwPairExists := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 q i j
  obtain ⟨u, hu⟩ := h3 q (i + j) T _ (h2 q i j T τ hτ)
  exact ⟨post τ u, fun U ζ => by rw [post_mul]; exact hu U ζ⟩

end LateralTheory.E.LeafTwPairExistsPf
