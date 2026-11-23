import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataBaseChangeSectionsMatricesStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TransversalZerosOfJacobianNeZeroDomainStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKoszulTorsionTransversalSplitZerosStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
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

noncomputable section
namespace GlobalTheory.KeyKa.KoszulGenExact

theorem exact_of_rescale {K Ix : Type} [CommRing K] [Fintype Ix] [DecidableEq Ix] (D D' h : Matrix Ix Ix K)
    (σ : Ix → Kˣ) (h1 : D' * h + h * D' = 1) (h2 : ∀ p q, D p q = σ p * D' p q)
    (h3 : ∀ p q, D' p q * ((σ q)⁻¹ : Kˣ) = D' p q) (v : Ix → K) (hv : D.mulVec v = 0) :
    ∃ w, D.mulVec w = v := by
  have key : ∀ (x : Ix → K) (p : Ix), D.mulVec x p = (σ p : K) * D'.mulVec x p := by
    intro x p
    simp only [Matrix.mulVec, dotProduct, h2, Finset.mul_sum, _root_.mul_assoc]
  have hD'v : D'.mulVec v = 0 := by
    funext p
    have hp := congrFun hv p
    rw [key] at hp
    exact (Units.mul_right_eq_zero (σ p)).mp hp
  have hcol : ∀ x : Ix → K, D'.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * x q) = D'.mulVec x := by
    intro x
    funext p
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← _root_.mul_assoc, h3]
  have hu : D'.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q) = 0 := by
    rw [hcol]
    exact hD'v
  have hback : D'.mulVec (h.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q)) = fun q => ((σ q)⁻¹ : Kˣ) * v q := by
    have e := congrArg (fun M => M.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q)) h1
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero, add_zero,
      Matrix.one_mulVec] at e
    exact e
  refine ⟨h.mulVec (fun q => ((σ q)⁻¹ : Kˣ) * v q), ?_⟩
  funext p
  rw [key, hback]
  exact Units.mul_inv_cancel_left (σ p) (v p)

theorem exact_kosD_map {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {g g' d : ℕ} (hg : g' = g) (c : ℕ → ℕ)
    (m : Fin g → ∀ j j', Matrix (Fin (c j ^ g)) (Fin (c j' ^ g)) O) (ev : ∀ j, Matrix (Fin d) (Fin (c j ^ g)) O)
    (m' : Fin g' → ∀ j j', Matrix (Fin (c j ^ g')) (Fin (c j' ^ g')) K)
    (ev' : ∀ j, Matrix (Fin d) (Fin (c j ^ g')) K) (u : Fin d → Kˣ)
    (hm : ∀ i j, j < g' → ∀ k k', m' i j (j + 1) k k' = f (m (i.cast hg) j (j + 1)
      (k.cast (congrArg (fun r => c j ^ r) hg)) (k'.cast (congrArg (fun r => c (j + 1) ^ r) hg))))
    (hev : ∀ a k, ev' 0 a k * u a = f (ev 0 a (k.cast (congrArg (fun r => c 0 ^ r) hg))))
    (t : K) (ht : TorsSq kdeg (kosD (N := fun j => c j ^ g') m' ev') t) (v)
    (hv : ((kosD (N := fun j => c j ^ g) m ev).map f).mulVec v = 0) :
    ∃ w, ((kosD (N := fun j => c j ^ g) m ev).map f).mulVec w = v := by
  subst hg
  obtain ⟨h, -, hh, -⟩ := ht
  have hm2 : ∀ (i : Fin g') (j j' : ℕ), j' = j + 1 → j < g' →
      ∀ k k', m' i j j' k k' = f (m i j j' k k') := by
    intro i j j' hj hlt k k'
    subst hj
    have e := hm i j hlt k k'
    simp only [Fin.cast_eq_self] at e
    exact e
  have hev2 : ∀ j : ℕ, j = 0 → ∀ a k, f (ev j a k) = (u a : K) * ev' j a k := by
    intro j hj a k
    subst hj
    have e := hev a k
    simp only [Fin.cast_eq_self] at e
    rw [← e, mul_comm]
  refine exact_of_rescale ((kosD m ev).map f) (kosD m' ev') h (Sum.elim (fun _ => 1) u) hh ?_ ?_ v hv
  · intro p q
    rcases p with ⟨P, kp⟩ | a <;> rcases q with ⟨Q, kq⟩ | b
    · simp only [Matrix.map_apply, kosD, Sum.elim_inl, Units.val_one, _root_.one_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hc
      · obtain ⟨hi, hQ⟩ := hc
        have hQc : Q.card = P.card + 1 := by rw [hQ, Finset.card_insert_of_notMem hi]
        have hlt : P.card < g' := by
          have hle := Finset.card_le_univ (insert i P)
          rw [Finset.card_insert_of_notMem hi, Fintype.card_fin] at hle
          omega
        rw [hm2 i P.card Q.card hQc hlt]
        simp
      · simp
    · simp [kosD]
    · simp only [Matrix.map_apply, kosD, Sum.elim_inr]
      split_ifs with hQ
      · exact hev2 _ (by simp [hQ]) a kq
      · simp
    · simp [kosD]
  · intro p q
    rcases q with _ | b
    · simp
    · rcases p with _ | a <;> simp [kosD]

theorem kosD_exact_generic : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] (K : Type) [Field K] (f : O →+* K) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (d : ℕ) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), Function.Injective f → 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, (∃ q : Sp K, spMap f q = x.P.A.hom y) → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∀ v, ((kosD (N := (fun j => (l - j * n) ^ x.P.g)) m (fun j => Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))).map f).mulVec v = 0 → ∃ w, ((kosD (N := (fun j => (l - j * n) ^ x.P.g)) m (fun j => Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))).map f).mulVec w = v := by
  intro hL O _ _ _ _ K _ f x n l s b m d z ch hf hn hl hb hmul hz0 hs0 hjac hzi hcov v hv
  obtain ⟨x', φ, w, hg, s', b', m', hkv, hsv, hbv, hb', hmul', hm', -⟩ :=
    GlobalTheory.T.exists_keyData_baseChange_sections_matrices hL O K f x n l s b m hl hb hmul
  obtain ⟨z', ch', u, het, hval⟩ :=
    GlobalTheory.T.transversal_zeros_of_jacobian_ne_zero_domain O K x x' f φ w n d hg s s' z ch hf hkv hsv hz0 hs0 hjac hzi hcov
  have hl' : x'.P.g * n < l := by rw [hg]; exact hl
  obtain ⟨-, t, m'', hmul'', ht⟩ := GlobalTheory.T.exists_koszulTorsion_transversal_split_zeros hL K x' n l d s' b' z' ch' hn hl' hb' het
  refine exact_kosD_map f hg (fun j => l - j * n) m
    (fun j => Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a))) m''
    (fun j => Matrix.of fun a k => valT (T := K) (z' a).left (x'.P.L.U (ch' a)) ((b' j k).f (ch' a)))
    (fun a => u a ^ (l - 0 * n)) ?_ ?_ (t : K) ht v hv
  · intro i j hj k k'
    have hS := hb' j hj.le
      (GlobalTheory.KeyKa.KoszulCx.mulSec x'.P.L (GlobalTheory.KeyKa.KoszulCx.cast_step hl' hj) (s' i) (b' (j + 1) k'))
    have e := hS.unique (hmul'' i j hj k') (hmul' i j hj k')
    exact (congrFun e k).trans (hm' i j (j + 1) k k')
  · intro a k
    have e := hval (l - 0 * n) (b 0 (k.cast (congrArg (fun r => (l - 0 * n) ^ r) hg))) (b' 0 k) a (hbv 0 k)
    rw [Units.val_pow_eq_pow_val]
    exact e

end GlobalTheory.KeyKa.KoszulGenExact
end
