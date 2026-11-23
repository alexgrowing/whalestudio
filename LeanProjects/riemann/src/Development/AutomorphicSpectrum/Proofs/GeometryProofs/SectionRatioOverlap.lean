import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp

theorem iter_sum {B J : Type} [AddCommMonoid B] (D : B →+ B) (s : Finset J) (k : ℕ) (g : J → B) :
    D^[k] (∑ j ∈ s, g j) = ∑ j ∈ s, D^[k] (g j) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [map_sum, ih]

theorem iter_const_mul {B : Type} [CommRing B] (D : B →+ B) (c : B) (hc : ∀ g, D (c * g) = c * D g) (k : ℕ) (g : B) :
    D^[k] (c * g) = c * D^[k] g := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [hc, ih]

theorem jet_cmp_ring {B K : Type} [CommRing B] [Field K] (D : B →+ B)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a) (e : B →+* K) (r : ℕ) (c a a' : Fin r → B) (u : B)
    (hc : ∀ j g, D (c j * g) = c j * D g) (hu : e u ≠ 0) (ha : ∀ j, a j = u * a' j) (i : ℕ)
    (h : ∀ k < i, ∑ j, e (c j) * e (D^[k] (a j)) = 0) :
    ∑ j, e (c j) * e (D^[i] (a j)) = e u * ∑ j, e (c j) * e (D^[i] (a' j)) := by
  have hval : ∀ (b : Fin r → B) (k : ℕ), e (D^[k] (∑ j, c j * b j)) = ∑ j, e (c j) * e (D^[k] (b j)) := by
    intro b k
    rw [iter_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iter_const_mul D (c j) (hc j), map_mul]
  have hΦ : ∑ j, c j * a j = u * ∑ j, c j * a' j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]; ring
  have h1 : ∀ k < i, e (D^[k] (u * ∑ j, c j * a' j)) = 0 := by
    intro k hk
    rw [← hΦ, hval]; exact h k hk
  have h2 := jet_vanish_of_mul D hD e u _ hu i h1
  have h3 := jet_mul_of_vanish D hD e i u _ h2
  rw [← hΦ, hval, hval] at h3
  exact h3

theorem iter_der_res {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (v : epsAt (𝟙 (Sp R)) ⟶ G)
    (hv : IsTanAt G (𝟙 (Sp R)) v) {V V' : G.left.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (le : V' ≤ V) (k : ℕ) (g : Γ(G.left, V)) :
    (der v hv hV')^[k] ((G.left.presheaf.map (homOfLE le).op).hom g) =
      (G.left.presheaf.map (homOfLE le).op).hom ((der v hv hV)^[k] g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [der_res v hv hV hV' le, ih]

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (l1 : V ≤ U) (l2 : W ≤ V) (l3 : W ≤ U) (g : Γ(X, U)) :
    (X.presheaf.map (homOfLE l2).op).hom ((X.presheaf.map (homOfLE l1).op).hom g) =
      (X.presheaf.map (homOfLE l3).op).hom g := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem jet_cmp : ∀ (R K : Type) [CommRing R] [Field K] (G : Over (Sp R)) [GrpObj G] (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (y : Sp K ⟶ G.left) (V₀ V₁ : G.left.Opens) (h₀ : IsAffineOpen V₀) (h₁ : IsAffineOpen V₁) (t₀ : ⊤ ≤ y ⁻¹ᵁ V₀) (t₁ : ⊤ ≤ y ⁻¹ᵁ V₁) (t : ⊤ ≤ y ⁻¹ᵁ (V₀ ⊓ V₁)) (r : ℕ) (f : Fin r → Γ(G.left, V₀)) (f' : Fin r → Γ(G.left, V₁)) (uu : Γ(G.left, V₀ ⊓ V₁)), ev y _ t uu ≠ 0 → (∀ j, (G.left.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op).hom (f j) = uu * (G.left.presheaf.map (homOfLE (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op).hom (f' j)) → ∀ (i : ℕ) (c : Fin r → R), (∀ k < i, ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[k] (f j)) = 0) → ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[i] (f j)) = ev y _ t uu * ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₁ t₁ ((der v₀ hv₀ h₁)^[i] (f' j)) := by
  intro R K _ _ G _ v₀ hv₀ y V₀ V₁ h₀ h₁ t₀ t₁ t r f f' uu hu hf i c hyp
  obtain ⟨W, hWa, hWy, hWle'⟩ := exists_isAffineOpen_mem_and_subset
    (X := G.left) (x := y (default : PrimeSpectrum K)) (U := V₀ ⊓ V₁) (t (show _ ∈ (⊤ : (Sp K).Opens) from trivial))
  have hWle : W ≤ V₀ ⊓ V₁ := hWle'
  have tW : ⊤ ≤ y ⁻¹ᵁ W := by
    intro p _
    rw [Subsingleton.elim p (default : PrimeSpectrum K)]
    exact hWy
  have l0 : W ≤ V₀ := hWle.trans inf_le_left
  have l1 : W ≤ V₁ := hWle.trans inf_le_right
  have key := jet_cmp_ring (der v₀ hv₀ hWa) (der_mul v₀ hv₀ hWa) (ev y W tW) r
    (fun j => constFn G.hom W (c j))
    (fun j => (G.left.presheaf.map (homOfLE l0).op).hom (f j))
    (fun j => (G.left.presheaf.map (homOfLE l1).op).hom (f' j))
    ((G.left.presheaf.map (homOfLE hWle).op).hom uu)
    (fun j g => der_const_mul v₀ hv₀ hWa (c j) g)
    (by rw [ev_res y hWle t tW]; exact hu)
    (fun j => by
      have := congrArg (G.left.presheaf.map (homOfLE hWle).op).hom (hf j)
      rw [map_mul, res_res _ _ l0, res_res _ _ l1] at this
      exact this)
    i
    (fun k hk => by
      have := hyp k hk
      simp only [iter_der_res v₀ hv₀ h₀ hWa l0, ev_res y l0 t₀ tW, ev_const]
      exact this)
  simp only [iter_der_res v₀ hv₀ h₀ hWa l0, iter_der_res v₀ hv₀ h₁ hWa l1, ev_res y l0 t₀ tW, ev_res y l1 t₁ tW,
    ev_res y hWle t tW, ev_const] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp
