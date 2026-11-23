import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataBaseChangeSectionsMatricesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulSectionsExactAlgClosedPolarisedAVStatement
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KosResidueExact

theorem kosD_apply_map {k K : Type} [CommRing k] [CommRing K] (f : k →+* K) {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k) (p q : KIx g 0 N) :
    kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0) p q =
      f (kosD (d := 0) m (fun _ => 0) p q) := by
  rcases p with p | a
  · rcases q with q | a
    · simp only [kosD, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · exact a.elim0
  · exact a.elim0

theorem descend {k K : Type} [Field k] [Field K] [Algebra k K] {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k)
    (H : ∀ v : KIx g 0 N → K,
      (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec w (.inl p))
    (v : KIx g 0 N → k) (hv : (kosD (d := 0) m (fun _ => 0)).mulVec v = 0) :
    ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (LinearMap.ker_eq_bot.2 (algebraMap k K).injective)
  have hl : ∀ a, lam (algebraMap k K a) = a := fun a => LinearMap.congr_fun hlam a
  obtain ⟨w, hw⟩ := H (fun p => algebraMap k K (v p)) (by
    funext p
    have := congrArg (algebraMap k K) (congrFun hv p)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this ⊢
    simpa only [kosD_apply_map] using this)
  refine ⟨fun q => lam (w q), fun p hp => ?_⟩
  have := congrArg lam (hw p hp)
  rw [hl] at this
  rw [this]
  simp only [Matrix.mulVec, dotProduct, map_sum, kosD_apply_map]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem transport {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {g g' : ℕ} (hg : g' = g) (l n : ℕ)
    (m : Fin g → ∀ j j', Matrix (Fin ((l - j * n) ^ g)) (Fin ((l - j' * n) ^ g)) O)
    (m' : Fin g' → ∀ j j', Matrix (Fin ((l - j * n) ^ g')) (Fin ((l - j' * n) ^ g')) K)
    (hm : ∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j'
      (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg))))
    (H : ∀ v : KIx g' 0 (fun j => (l - j * n) ^ g') → K, (kosD m' (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m' (fun _ => 0)).mulVec w (.inl p)) :
    ∀ v : KIx g 0 (fun j => (l - j * n) ^ g) → K,
      (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p) := by
  subst hg
  have : m' = fun i j j' => (m i j j').map f := by
    funext i j j'
    ext k k'
    exact hm i j j' k k'
  subst this
  exact H

theorem main : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (k : Type) [Field k] (f : O →+* k) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → FinZ x s → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → k, (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p)) := by
  intro hL O _ _ _ k _ f x n l s b m hn hl hb hm hZ
  obtain ⟨x', φ, w, hg, s', b', m', -, -, -, hb', hm', hmm, hZ'⟩ :=
    GlobalTheory.T.exists_keyData_baseChange_sections_matrices hL O (AlgebraicClosure k) ((algebraMap k (AlgebraicClosure k)).comp f) x n l s b m hl hb hm
  have hfin : Finite (Sp (AlgebraicClosure k)) :=
    inferInstanceAs (Finite (PrimeSpectrum (AlgebraicClosure k)))
  have hc : ∀ y : x'.P.A.left, ∃ i, y ∈ x'.P.L.U i := fun y => exists_chart x'.P.isLB y
  choose c hc using hc
  have H := (GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV hL (AlgebraicClosure k) x' n l s' b' m' c hn (by rw [hg]; exact hl)
    (hZ' hfin hZ) hb' hm' hc).1
  have H' := transport ((algebraMap k (AlgebraicClosure k)).comp f) hg l n m m' hmm H
  exact descend (K := AlgebraicClosure k) (N := fun j => (l - j * n) ^ x.P.g)
    (fun i j j' => (m i j j').map f) H'

end GlobalTheory.KosResidueExact
