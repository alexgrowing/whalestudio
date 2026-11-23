import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScalGLCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasHodgeTateWeightFrameCharacterTwistStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

theorem fr_mul_of_fixed (r N : ℕ) (c : ↥(MaximalUnramifiedExtension l)) (h : fr l r c = c) : fr l (r * N) c = c := by
  induction N with
  | zero => simp [fr]
  | succ k ih =>
    change (frobUr l ^ (r * (k + 1))) c = c
    rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]
    change (frobUr l ^ (r * k)) (fr l r c) = c
    rw [h]
    exact ih

theorem isRat_twist {K K' : FinExt l} (hK : K.1 ≤ K'.1) (r N : ℕ) (hN : 0 < N) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (hρ : IsRat r ρ)
    (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l (r * N) c = c → (c : Om l) ∈ K'.1) (hfr : ∀ g, fr l (r * N) (χ g : ↥(MaximalUnramifiedExtension l)) = χ g)
    (hcont : Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) :
    IsRat (r * N) (twist hK ρ χ a) := ⟨Nat.mul_pos hρ.pos hN, hle, fun g i j => by
    rw [twist_val, Matrix.smul_apply, smul_eq_mul, map_mul, fr_mul_of_fixed r N _ (hρ.rat _ i j),
      Units.val_zpow_eq_zpow_val, map_zpow₀, hfr], fun i j => by
    have h1 : Continuous fun g : ↥(GK K') => (((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) :=
      (hρ.cont i j).comp (continuous_subtype_val.subtype_mk _)
    have h2 : Continuous fun g : ↥(GK K') => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l) ^ a :=
      hcont.zpow₀ _ fun g => Or.inl (by
        intro h0
        exact (χ g).ne_zero (Subtype.ext h0))
    refine (h2.mul h1).congr fun g => ?_
    simp only [twist_val, Matrix.smul_apply, smul_eq_mul, Units.val_zpow_eq_zpow_val]
    push_cast
    rfl⟩

theorem potentiallySemistable_of_lubinTateTwist (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ)
    (hact : ∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) :
    AdmSt P (twist hK ρ χ a) → AdmSt P ρ := by
  have msmul : ∀ {R S : Type} [CommRing R] [CommRing S] {F : Type} [FunLike F R S] [RingHomClass F R S] (f : F) (c : R)
      (M : Matrix n n R), (c • M).map f = f c • M.map f := fun f c M => by
    ext i j; simp
  rintro ⟨K'', hK'', Q', hQ'⟩
  refine ⟨K'', hK.trans hK'', scalGL n (Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (x ^ a)) * Q', fun g => ?_⟩
  have hg := hQ' g
  rw [twist_val, msmul, Matrix.smul_mul] at hg
  set g' : ↥(GK K') := ⟨(g : GQ l), GK_le hK'' g.2⟩
  have hx : Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x =
      Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') * x := by
    apply Units.ext
    simpa using hact g'
  have hxa : actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) =
      ks P ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) * Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) := by
    have h2 := congrArg (fun u : P.R.Bˣ => Polynomial.C ((u ^ a : P.R.Bˣ) : P.R.B)) hx
    have e1 : ((Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x ^ a : P.R.Bˣ) : P.R.B) =
        P.actQ (g : GQ l) ((x ^ a : P.R.Bˣ) : P.R.B) := by rw [← map_zpow]; rfl
    have e2 : ((Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') ^ a : P.R.Bˣ) : P.R.B) =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) := by rw [← map_zpow]; rfl
    simp only [mul_zpow] at h2
    rw [e1, Units.val_mul, e2, map_mul] at h2
    rw [actSt_C]
    exact h2
  rw [scalGL_mul_val, msmul, Matrix.mul_smul, Units.coe_map]
  change actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) • _ =
    Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) • _
  rw [hxa]
  conv_rhs => rw [← hg]
  rw [smul_smul, mul_comm (Polynomial.C _)]

omit [DecidableEq n] in
theorem sum_weights (r N : ℕ) (hr : 0 < r) (w : Fin r → n → ℤ) (hN : Fintype.card n = N) :
    ∑ m : Fin (r * N), ∑ j, (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then -∑ m, ∑ j, w m j else 0) = 0 := by
  subst hN
  simp only [Finset.sum_add_distrib]
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range (r * N), (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) i =
      N * ∑ m, ∑ j, w m j := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have : ∑ x ∈ Finset.range r, (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x) =
          ∑ m, ∑ j, w m j := by
        rw [← Fin.sum_univ_eq_sum_range (fun x => (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x))]
        refine Finset.sum_congr rfl fun m _ => ?_
        have e : (⟨(r * k + (m : ℕ)) % r, Nat.mod_lt _ hr⟩ : Fin r) = m := by
          apply Fin.ext
          simp only
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt m.2]
        simp only [e]
      rw [this]
      push_cast
      ring
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j), key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i = 0 then -∑ m, ∑ j, w m j else 0),
    Finset.sum_ite_eq' (Finset.range _) 0]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · simp [h0]
  · rw [if_pos (Finset.mem_range.mpr (Nat.mul_pos hr h0))]
    ring

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon

theorem twistStep : TwistStep := by
  intro l _ P AI T n _ _ K r ρ w hρ hw
  by_cases hn : Fintype.card n = 0
  · refine ⟨K, r, ρ, w, hρ, hw, ?_, id⟩
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    simp
  · have hN : 0 < Fintype.card n := Nat.pos_of_ne_zero hn
    have hs : 0 < r * Fintype.card n := Nat.mul_pos hρ.pos hN
    obtain ⟨K', hK, x, χ, hle, hfr, hcont, hact, h1, h2, hj⟩ := GlobalTheory.T.exists_lubinTate_character_unramified_period l P AI T K (r * Fintype.card n) hs
    exact ⟨K', r * Fintype.card n, Twist.twist hK ρ χ (-∑ m, ∑ j, w m j), _,
      Twist.isRat_twist hK r _ hN ρ χ _ hρ hle hfr hcont,
      GlobalTheory.T.hasHodgeTateWeightFrame_character_twist l P AI T n K K' hK r (Fintype.card n) hρ.pos ρ w χ x _ hρ hw hact h1 h2 hj,
      Twist.sum_weights r _ hρ.pos w rfl, Twist.potentiallySemistable_of_lubinTateTwist P hK ρ χ x _ hact⟩

end GlobalTheory.PMon

end
