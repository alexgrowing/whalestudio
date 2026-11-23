import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellGen

variable {S : Type} [CommRing S] {m a k b N : ℕ}

theorem pair_gvec (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (x : GVar m a k b → S)
    (j l : Fin m) : ∑ r, D (w.1 j) r * gvec c w x l r = gcell x j l := by
  simp only [gvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ i, ∑ r, D (w.1 j) r * (gcell x i l * c (w.1 i) r) = if j = i then gcell x i l else 0 := by
    intro i
    have h1 : ∑ r, D (w.1 j) r * (gcell x i l * c (w.1 i) r) = gcell x i l * ∑ r, D (w.1 j) r * c (w.1 i) r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [h1, h]
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem det_updateCol_one (j : Fin k) (v : Fin k → S) :
    (Matrix.updateCol (1 : Matrix (Fin k) (Fin k) S) j v).det = v j := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

theorem gcell_castLE (hk : k ≤ m) (x : GVar m a k b → S) (l l' : Fin k) :
    gcell x (Fin.castLE hk l') (Fin.castLE hk l) = (1 : Matrix (Fin k) (Fin k) S) l l' := by
  have h1 : ¬ k ≤ (l' : ℕ) := not_le.2 l'.2
  unfold gcell
  rw [dif_neg (fun h => h1 h.2.2.1), Matrix.one_apply]
  by_cases h : l = l'
  · simp [h]
  · rw [if_neg h, if_neg fun e => h (Fin.castLE_injective hk e).symm]

theorem lform_gxi (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (j : Fin k → Fin m) :
    ∑ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) (lform D (w.1 ∘ j) q) * gxi a b hk c w q =
      (Matrix.of fun l l' => gcell (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S) (j l')
        (Fin.castLE hk l)).det := by
  have h1 : ∀ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) (lform D (w.1 ∘ j) q) =
      lform (fun z => (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) ∘ D z) (w.1 ∘ j) q := fun q => by
    simp only [lform, map_prod, Function.comp_apply]
  simp only [h1, gxi]
  rw [GlobalTheory.FlagEmb.CauchyBinet.lform_plk]
  congr 1
  ext1 l l'
  exact pair_gvec _ _ (h.map (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S)) w _ (j l') _

theorem lform_gxi_var (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → S) (h : LeftInv D c) (w : GPm m a b) (v : GVar m a k b) :
    ∑ q, (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S)
      (lform D (w.1 ∘ Function.update (Fin.castLE hk) ⟨v.1.2, v.2.2.1⟩ v.1.1) q) * gxi a b hk c w q =
      MvPolynomial.X v := by
  rw [lform_gxi hk D c h w]
  have h1 : (Matrix.of fun l l' => gcell (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S)
      (Function.update (Fin.castLE hk) ⟨v.1.2, v.2.2.1⟩ v.1.1 l') (Fin.castLE hk l)) =
      Matrix.updateCol (1 : Matrix (Fin k) (Fin k) _) ⟨v.1.2, v.2.2.1⟩
        fun l => gcell MvPolynomial.X v.1.1 (Fin.castLE hk l) := by
    ext1 l l'
    rw [Matrix.of_apply, Matrix.updateCol_apply]
    by_cases hl : l' = ⟨v.1.2, v.2.2.1⟩
    · rw [if_pos hl, hl, Function.update_self]
    · rw [if_neg hl, Function.update_of_ne hl, gcell_castLE]
  rw [h1, det_updateCol_one]
  exact dif_pos v.2

theorem main : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (w : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → ∑ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D w q) * gxi a b hk c w q = 1 ∧ Function.Surjective (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)) := by
  intro R _ m a k b N hk D c w _ _ h
  refine ⟨?_, fun p => ?_⟩
  · unfold gell
    rw [lform_gxi hk D c h w, ← Matrix.det_one (n := Fin k)]
    congr 1
    ext1 l l'
    exact gcell_castLE hk _ l l'
  · change p ∈ (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)).range
    induction p using MvPolynomial.induction_on with
    | C r => exact ⟨MvPolynomial.C r, by simp⟩
    | add p q hp hq => exact add_mem hp hq
    | mul_X p v hp =>
      refine mul_mem hp ?_
      rw [← lform_gxi_var hk D c h w v]
      exact sum_mem fun q _ => mul_mem ⟨MvPolynomial.C _, MvPolynomial.eval₂Hom_C _ _ _⟩
        ⟨MvPolynomial.X q, MvPolynomial.eval₂Hom_X' _ _ _⟩

end GlobalTheory.GrCl.CellGen
