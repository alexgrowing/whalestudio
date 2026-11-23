import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellSpanPreservedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellCoordinatesExistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependentStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl.CellGlue

theorem linearIndependent_of_leftInv {K : Type} [Field K] {m M : ℕ} {D c : Fin m → Fin M → K} (h : LeftInv D c) :
    LinearIndependent K c := by
  rw [Fintype.linearIndependent_iff]
  intro g hg z
  have e := congrArg (fun v : Fin M → K => ∑ r, D z r * v r) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    Finset.mul_sum] at e
  rw [Finset.sum_comm] at e
  have key : ∀ i, ∑ r, D z r * (g i * c i r) = if z = i then g i else 0 := fun i => by
    have e1 : ∑ r, D z r * (g i * c i r) = g i * ∑ r, D z r * c i r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [e1, h z i]
    split_ifs <;> simp
  simpa [key] using e

theorem span_comp_castLE {S : Type} [CommRing S] {Q : Type} [AddCommGroup Q] [Module S Q] {m k : ℕ} (hk : k ≤ m)
    (v : Fin m → Q) : Submodule.span S (Set.range (v ∘ Fin.castLE hk)) = initSpan S v k := by
  unfold initSpan
  congr 1
  ext y
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨Fin.castLE hk l, l.2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

theorem map_gell {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {m a k b N : ℕ} (hk : k ≤ m)
    (D : Fin m → Fin (N + 1) → S) (w : GPm m a b) (q : Fin (plN N k + 1)) :
    φ (gell a b hk D w q) = gell a b hk (fun l => φ ∘ D l) w q := by
  simp only [gell, lform, map_prod, Function.comp_apply]

theorem comp_gxi {R K : Type} [CommRing R] [CommRing K] {m a k b N : ℕ} (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R)
    (w : GPm m a b) (ψ : MvPolynomial (GVar m a k b) R →+* K) :
    ψ ∘ gxi a b hk c w =
      plk (gvec (fun l => (ψ.comp MvPolynomial.C) ∘ c l) w (ψ ∘ MvPolynomial.X) ∘ Fin.castLE hk) id := by
  unfold gxi
  rw [GlobalTheory.FlagEmb.map_plk]
  simp only [comp_gvec]
  rfl

theorem mem_cell_of_initSpan_eq : ∀ (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (m a k b N : ℕ) (hk : k ≤ m)
    (D c : Fin m → Fin (N + 1) → R) (D' c' : Fin m → Fin (N + 1) → R') (φ : R →+* K)
    (ψ' : MvPolynomial (GVar m a k b) R' →+* K) (w' : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → LeftInv D' c' →
    (∀ e : ℕ, e = a ∨ e = b →
      initSpan K (fun l => φ ∘ c l) e = initSpan K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) e) →
    (∃ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0) ∧
      ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0 →
        ∃ (ψ : MvPolynomial (GVar m a k b) R →+* K) (u : Kˣ),
          ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ gxi a b hk c' w' = (u : K) • (ψ ∘ gxi a b hk c w) := by
  intro K R R' _ _ _ m a k b N hk D c D' c' φ ψ' w' hak hkb hDc hDc' hab
  have hcK : LinearIndependent K (fun l => φ ∘ c l) := linearIndependent_of_leftInv (hDc.map φ)
  have hcK' : LinearIndependent K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) :=
    linearIndependent_of_leftInv (hDc'.map (ψ'.comp MvPolynomial.C))
  obtain ⟨hGi, -, hGe⟩ := GlobalTheory.T.grassmann_cell_span_preserved K m a k b (Fin (N + 1) → K) (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w'
    (ψ' ∘ MvPolynomial.X) hak hkb
  have hUi := (hGi hcK').comp _ (Fin.castLE_injective hk)
  have hlo : initSpan K (fun l => φ ∘ c l) a ≤ Submodule.span K (Set.range
      (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk)) := by
    rw [hab a (Or.inl rfl), ← hGe a (Or.inl le_rfl), span_comp_castLE]
    exact GlobalTheory.FlagMod.initSpan_mono _ hak
  have hhi : Submodule.span K (Set.range
      (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk)) ≤
        initSpan K (fun l => φ ∘ c l) b := by
    rw [hab b (Or.inr rfl), ← hGe b (Or.inr le_rfl), span_comp_castLE]
    exact GlobalTheory.FlagMod.initSpan_mono _ hkb
  obtain ⟨hex, hcell⟩ := GlobalTheory.T.grassmann_cell_coordinates_exist K m a k b N hk (fun l => φ ∘ D l) (fun l => φ ∘ c l) _ hak hkb (hDc.map φ) hUi
    hlo hhi
  have hsum : ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) =
      ∑ q, gell a b hk (fun l => φ ∘ D l) w q *
        plk (gvec (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) w' (ψ' ∘ MvPolynomial.X) ∘ Fin.castLE hk) id q :=
    fun w => Finset.sum_congr rfl fun q _ => by rw [map_gell, ← comp_gxi]; rfl
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨w, hw⟩ := hex
    exact ⟨w, by rwa [hsum]⟩
  · rw [hsum] at hw
    obtain ⟨x, hx⟩ := hcell w hw
    have hC : (MvPolynomial.eval₂Hom φ x).comp MvPolynomial.C = φ := by
      ext r; simp
    have hX : MvPolynomial.eval₂Hom φ x ∘ MvPolynomial.X = x := by
      funext v; simp
    obtain ⟨hVi, -, -⟩ := GlobalTheory.T.grassmann_cell_span_preserved K m a k b (Fin (N + 1) → K) (fun l => φ ∘ c l) w x hak hkb
    have hVi' := (hVi hcK).comp _ (Fin.castLE_injective hk)
    obtain ⟨r, hr⟩ := ((GlobalTheory.T.plucker_nonzero_iff_independent K N k _ _).2 hVi').1 ⟨hUi, by rw [hx, span_comp_castLE]⟩
    refine ⟨MvPolynomial.eval₂Hom φ x, r, hC, ?_⟩
    rw [comp_gxi, comp_gxi, hC, hX]
    exact hr

end GlobalTheory.GrCl.CellGlue
