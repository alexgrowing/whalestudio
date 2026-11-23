import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_succ_ne_of_parity (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hev : Even (nP D p))
    (hR : OrbitPlaces.IsReps D p R) {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) {s s' : ℕ}
    (hs : s < nP D p) (hs' : s' < nP D p) (hpar : s % 2 = s' % 2) :
    posPl D p (posPl D p r s) 1 ≠ posPl D p r' s' := by
  intro h
  rw [posPl_add] at h
  have hrr : r = r' :=
    (hR (posPl D p r' s')).unique ⟨hr, s + 1, h⟩ ⟨hr', s', rfl⟩
  subst hrr
  have hpos : 0 < nP D p := by omega
  have h2 : posPl D p r ((s + 1) % nP D p) = posPl D p r s' := by rw [posPl_mod, h]
  have h3 : (s + 1) % nP D p = s' := posPl_inj D p r _ _ (Nat.mod_lt _ hpos) hs' h2
  obtain ⟨m, hm⟩ := hev
  rcases Nat.lt_or_ge (s + 1) (nP D p) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h3
    omega
  · have hsn : s + 1 = nP D p := by omega
    rw [hsn, Nat.mod_self] at h3
    omega

theorem sum_sigma_comb_mul_comb (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' n : ℕ} (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin n → MaximalUnramifiedExtension p)
    (hev : Even (nP D p)) (hR : OrbitPlaces.IsReps D p R)
    (hg : ∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i)
    (hp : ∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0)
    {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) (a a' : Fin N) (b b' : Fin N')
    (c c' : ZMod (nP D p) → MaximalUnramifiedExtension p) (q : ℕ)
    (hc : ∀ t, t.val % 2 ≠ q → c t = 0) (hc' : ∀ t, t.val % 2 ≠ q → c' t = 0) :
    ∑ i, σ (∑ t, c t * g (OrbitPlaces.orbMap D p r t) a b i) * ∑ t, c' t * g (OrbitPlaces.orbMap D p r' t) a' b' i = 0 := by
  have hterm : ∀ t t' : ZMod (nP D p),
      ∑ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
        (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) = 0 := by
    intro t t'
    by_cases h1 : t.val % 2 = q
    · by_cases h2 : t'.val % 2 = q
      · have hne : posPl D p (OrbitPlaces.orbMap D p r t) 1 ≠ OrbitPlaces.orbMap D p r' t' :=
          posPl_succ_ne_of_parity D p R hev hR hr hr' (ZMod.val_lt t) (ZMod.val_lt t') (h1.trans h2.symm)
        have e : ∀ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
            (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) =
            (σ (c t) * c' t') * (h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i *
              g (OrbitPlaces.orbMap D p r' t') a' b' i) := fun i => by ring
        simp only [e]
        rw [← Finset.mul_sum, hp, if_neg (fun hh => hne hh.1), mul_zero]
      · simp [hc' t' h2]
    · simp [hc t h1]
  simp only [map_sum, map_mul, hg, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun t' _ => hterm t t'

theorem fOf_isotropic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → (∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf D p σ om R g e' i = 0) ∧ (∀ e e', ∑ i, σ (fOf' D p σ oms R g e i) * fOf' D p σ oms R g e' i = 0) := by
  intro D p _ σ om oms R N N' r g h hO hR hg hp
  constructor
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e.1.2) else 0)
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e'.1.2) else 0) 0
      (fun t ht => if_neg ht) (fun t ht => if_neg ht)
    simpa only [fOf, ite_mul, zero_mul] using key
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e.1.2))
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e'.1.2)) 1
      (fun t ht => if_pos (by omega)) (fun t ht => if_pos (by omega))
    simpa only [fOf', ite_mul, zero_mul] using key

end GlobalTheory.KerStd.HypCoord
