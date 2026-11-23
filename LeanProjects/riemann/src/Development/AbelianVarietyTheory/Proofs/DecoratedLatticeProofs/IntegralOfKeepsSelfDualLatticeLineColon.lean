import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ColonInt

theorem mem_int_of_pow {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (c y : Q.adicCompletion E) (hc : c ≠ 0) (h : ∀ n : ℕ, c * y ^ n ∈ Q.adicCompletionIntegers E) :
    y ∈ Q.adicCompletionIntegers E := by
  have h' : ∀ n : ℕ, Valued.v (c * y ^ n) ≤ 1 := fun n =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).1 (h n)
  refine (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).2 ?_
  by_contra hy
  push_neg at hy
  have hc' : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 hc'
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.1 hy0
  have hb1 : (1 : Multiplicative ℤ) < b := by
    rw [← hb] at hy
    exact WithZero.coe_lt_coe.1 hy
  have h2 := h' (Int.natAbs (Multiplicative.toAdd a) + 1)
  rw [Valuation.map_mul, Valuation.map_pow, ← ha, ← hb, ← WithZero.coe_pow, ← WithZero.coe_mul] at h2
  have h3 : a * b ^ (Int.natAbs (Multiplicative.toAdd a) + 1) ≤ 1 := WithZero.coe_le_coe.1 h2
  have h4 : Multiplicative.toAdd a + (Int.natAbs (Multiplicative.toAdd a) + 1 : ℕ) * Multiplicative.toAdd b ≤ 0 := by
    have := Multiplicative.toAdd_le.2 h3
    simpa [toAdd_mul, toAdd_pow] using this
  have h5' : 0 < Multiplicative.toAdd b := by
    have := Multiplicative.toAdd_lt.2 hb1
    simpa using this
  have h5 : 1 ≤ Multiplicative.toAdd b := by omega
  push_cast at h4
  have h6 : (0:ℤ) ≤ |Multiplicative.toAdd a| := abs_nonneg _
  have h7 : -Multiplicative.toAdd a ≤ |Multiplicative.toAdd a| := neg_le_abs _
  nlinarith

variable {D : D7}

def evQ {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E where
  toFun x := x Q
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem herm_cols {S : HSp D} {ρ : ℕ} (A B : Mx D S.rank ρ) (κ a : AE D) (l l' : Fin ρ) :
    GlobalTheory.IwaPlace.hermAt S (fun j => a * A j l) (fun i => κ * B i l') = cA D κ * a * (adj B ⬝ (gA S ⬝ A)) l' l := by
  simp only [GlobalTheory.IwaPlace.hermAt, Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mul_incA_mem {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (o : 𝓞 D.host.E) :
    a * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
  rw [map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨1, fun w => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

theorem exists_den {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ D.host.E) :
    ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ ∀ k l, ∃ o : 𝓞 D.host.E, (t : D.host.E) * M k l = o := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E))
    (Finset.univ : Finset (ι × κ)) (fun p => M p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun k l => ?_⟩
  obtain ⟨o, ho⟩ := hb (k, l) (Finset.mem_univ _)
  refine ⟨o, ?_⟩
  rw [show ((o : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o from rfl, ho, Algebra.smul_def]

theorem colon_int : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (x : AE D), x - 1 ∈ idAt D (· = v) → (∀ r ∈ idAt D (· = v), (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → ∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * x * a) ∈ latV S L (· = v)) → x - 1 ∈ intAt D (· = v) := by
  intro D S S₀ ρ d L L₀ v _ hL _ i j x hx hK
  obtain ⟨hsupp, ⟨m, hm, hmul⟩, hchar⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL
  obtain ⟨ε, hcε, hε, hεa⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hεε : ε * ε = ε := hεa ε hε.1
  obtain ⟨t, ht0, ht⟩ := exists_den (Matrix.fromCols d.e d.e')
  set T : AE D := incA D (t : D.host.E) with hT
  have hX : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jX k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inl l)
    have e : T * d.jX k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inl, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hY : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jY k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inr l)
    have e : T * d.jY k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inr, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hU : ∀ l (a : AE D), colMul d.jX l a ∈ latV S L (· = v) →
      ((m : AE D) * ε * cA D T) * a ∈ intAt D (· = v) := by
    intro l a ha
    have hxΛ : (fun k => ((m : AE D) * (ε * T)) * d.jY k l) ∈ latV S L (· = v) := by
      have := hmul (fun k => ε * (T * d.jY k l)) (fun k => hY ε hε l k)
      convert this using 1
      funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have h1 := ((hchar _ (hsupp _ ha)).1 ha) _ hxΛ
    rw [show colMul d.jX l a = fun j => a * d.jX j l from rfl, herm_cols, d.gram_YX, Matrix.one_apply_eq,
      mul_one] at h1
    convert h1 using 1
    rw [map_mul, map_mul, map_natCast, hcε]; ring
  obtain ⟨β, hβ⟩ : ∃ β : AE D, β = (m : AE D) * ε * cA D T := ⟨_, rfl⟩
  rw [← hβ] at hU
  have hβI : β ∈ idAt D (· = v) := by
    rw [hβ]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hε.1)
  have hc0 : colMul d.jX j ((m : AE D) * (ε * T)) ∈ latV S L (· = v) := by
    have := hmul (fun k => ε * (T * d.jX k j)) (fun k => hX ε hε j k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = (m : AE D) * (T * β) := ⟨_, rfl⟩
  have hcK : ∀ a, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (c * a) ∈ latV S L (· = v) := by
    intro a ha
    have := hmul (fun k => (β * a) * (T * d.jX k i)) (fun k => hX _ (hU j a ha) i k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul, hc]; ring
  have hcI : c ∈ idAt D (· = v) := by
    rw [hc]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hβI)
  have hit : ∀ n : ℕ, c * x ^ n ∈ idAt D (· = v) ∧ ∀ a, colMul d.jX j a ∈ latV S L (· = v) →
      colMul d.jX i (c * x ^ n * a) ∈ latV S L (· = v) := by
    intro n
    refine ⟨Ideal.mul_mem_right _ _ hcI, ?_⟩
    induction n with
    | zero => rw [pow_zero, mul_one]; exact hcK
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact hK _ (Ideal.mul_mem_right _ _ hcI) ih
  have hbd : ∀ n : ℕ, β * (c * x ^ n * ((m : AE D) * (ε * T))) ∈ intAt D (· = v) := fun n =>
    hU i _ ((hit n).2 _ hc0)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine ⟨hx, (hΦ.int _).2 fun Q => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AE D →+* Q.adicCompletion D.host.E, ∀ z, ψ z = Φ z Q :=
    ⟨(evQ Q).comp Φ, fun _ => rfl⟩
  have hψinc : ∀ e : D.host.E, ψ (incA D e) = algebraMap D.host.E _ e := fun e => by
    rw [hψ, hΦ.inc]; rfl
  have hεQ : ψ ε = 0 ∨ ψ ε = 1 := by
    have h := congrArg ψ hεε
    rw [map_mul] at h
    rcases mul_eq_zero.1 (show ψ ε * (ψ ε - 1) = 0 by rw [mul_sub, h, mul_one, sub_self]) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  rw [← hψ]
  rcases hεQ with h0 | h1
  · rw [← hεa _ hx, map_mul, h0, zero_mul]; exact zero_mem _
  · rw [map_sub, map_one]
    refine sub_mem ?_ (one_mem _)
    have ht' : (t : D.host.E) ≠ 0 := by exact_mod_cast ht0
    have hκ : (m : D.host.E) ^ 4 * star (t : D.host.E) ^ 2 * (t : D.host.E) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hm.ne')) (pow_ne_zero _ (star_ne_zero.2 ht')))
        (pow_ne_zero _ ht')
    refine mem_int_of_pow Q _ (ψ x) ((map_ne_zero (algebraMap D.host.E _)).2 hκ) fun n => ?_
    have h := (hΦ.int _).1 (hbd n).2 Q
    rw [← hψ] at h
    have e1 : ψ T = algebraMap D.host.E _ (t : D.host.E) := hψinc _
    have e2 : ψ (cA D T) = algebraMap D.host.E _ (star (t : D.host.E)) := hψinc _
    rw [hc, hβ] at h
    simp only [RingHom.map_mul, RingHom.map_pow, map_natCast, h1] at h ⊢
    rw [← e1, ← e2]
    convert h using 1
    ring

end GlobalTheory.ColonInt
