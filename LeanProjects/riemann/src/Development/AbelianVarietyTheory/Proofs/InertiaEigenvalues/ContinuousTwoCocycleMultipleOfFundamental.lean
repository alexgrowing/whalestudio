import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntTwoCocycleEqPowSmulOfReductionCoboundary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.GenSpan

open GlobalTheory.TateTop ReciprocityTheory.Gal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem gen_zmod {χ : G →* ℤ_[l]ˣ} {r : ℕ} {c : G × G → ℤ_[l]} (h : Gen χ r c) :
    (IsLocallyConstant (fun p => PadicInt.toZModPow r (c p)) ∧
      ∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * PadicInt.toZModPow r (c (k, m))
        - PadicInt.toZModPow r (c (g * k, m)) + PadicInt.toZModPow r (c (g, k * m))
        - PadicInt.toZModPow r (c (g, k)) = 0) ∧
    (∀ z : G × G → ZMod (l ^ r), IsLocallyConstant z →
      (∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * z (k, m) - z (g * k, m) + z (g, k * m)
        - z (g, k) = 0) →
      ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
        z p = PadicInt.toZModPow r (c p) * x +
          (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1)) ∧
    (∀ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b →
      (∀ p, PadicInt.toZModPow r (c p) * x =
          PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) → x = 0) := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let : Module ℤ_[l] (ZMod (l ^ r)) := Module.compHom _ (PadicInt.toZModPow r)
  have hs : ∀ (a : ℤ_[l]) (m : ZMod (l ^ r)), a • m = PadicInt.toZModPow r a * m := fun _ _ => rfl
  have h0 : PadicInt.toZModPow r ((l : ℤ_[l]) ^ r) = 0 := (dvd_iff_toZModPow _).1 dvd_rfl
  have hM : ∀ m : ZMod (l ^ r), (l : ℤ_[l]) ^ r • m = 0 := fun m => by rw [hs, h0, zero_mul]
  obtain ⟨h1, h2, h3⟩ := h _ hM
  refine ⟨?_, fun z hz hz' => ?_, fun x b hb hx => h3 x b hb fun p => ?_⟩
  · obtain ⟨a1, a2⟩ := h1 1
    simp only [hs, mul_one] at a1 a2
    exact ⟨a1, a2⟩
  · obtain ⟨x, b, hb, e⟩ := h2 z ⟨hz, fun g k m => by simpa only [hs] using hz' g k m⟩
    exact ⟨x, b, hb, fun p => by simpa only [GlobalTheory.TateTop.cob, hs] using e p⟩
  · simpa only [GlobalTheory.TateTop.cob, hs] using hx p

open GlobalTheory.PadicH2Separated in

theorem span : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) → (∀ r, GlobalTheory.TateTop.Gen χ r c) → (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) → (Continuous (fun p => (c p : ℚ_[l])) ∧ ∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * (c (h, k) : ℚ_[l]) - (c (g * h, k) : ℚ_[l]) + (c (g, h * k) : ℚ_[l]) - (c (g, h) : ℚ_[l]) = 0) ∧ ∀ z : G × G → ℚ_[l], Continuous z → (∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ (x : ℚ_[l]) (f : G → ℚ_[l]), Continuous f ∧ ∀ g h, ((χ g : ℤ_[l]) : ℚ_[l]) * f h - f (g * h) + f g = z (g, h) - x * (c (g, h) : ℚ_[l]) := by
  intro l _ G _ _ _ _ χ c hχ hgen hfin
  have hl : l.Prime := Fact.out
  have hG := fun r => gen_zmod (hgen r)
  have hcc : Continuous c := continuous_of_reductions c fun s => (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add, map_mul, map_zero] using (hG n).1.2 g h k
  refine ⟨⟨continuous_subtype_val.comp hcc, fun g h k => ?_⟩, fun z hz hzc => ?_⟩
  · have e := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) (hcoc g h k)
    push_cast at e
    exact e
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hz.continuousOn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (by exact_mod_cast hl.one_lt : (1 : ℝ) < l)
  have hnorm : ∀ p, ‖(l : ℚ_[l]) ^ m * z p‖ ≤ 1 := fun p => by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hp : (0 : ℝ) < (l : ℝ) ^ m := by have := hl.pos; positivity
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact (hC p trivial).trans hm.le
  let w : G × G → ℤ_[l] := fun p => ⟨(l : ℚ_[l]) ^ m * z p, hnorm p⟩
  have hw : ∀ p, (w p : ℚ_[l]) = (l : ℚ_[l]) ^ m * z p := fun _ => rfl
  have hwc : Continuous w := (continuous_const.mul hz).subtype_mk _
  have hwcoc : ∀ g h k, (χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) = 0 := by
    intro g h k
    have e : (((χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) : ℤ_[l]) :
        ℚ_[l]) = 0 := by
      push_cast [hw]
      linear_combination (l : ℚ_[l]) ^ m * hzc g h k
    exact PadicInt.coe_eq_zero.1 e
  have hlev : ∀ r, ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
      PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * x +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) := fun r =>
    (hG r).2.1 _ ((IsLocallyConstant.iff_continuous _).2 ((continuous_reduction r).comp hwc))
      fun g k m => by
        simpa only [map_sub, map_add, map_mul, map_zero] using
          congrArg (PadicInt.toZModPow r) (hwcoc g k m)
  choose X B hB hXB using hlev
  have hred : ∀ r, PadicInt.toZModPow r (((X r).val : ℕ) : ℤ_[l]) = X r := fun r => by
    have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hcomp : ∀ r, ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) (X (r + 1)) = X r := by
    intro r
    set ψ := ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))
    have hψ : ∀ a : ℤ_[l], ψ (PadicInt.toZModPow (r + 1) a) = PadicInt.toZModPow r a := fun a => by
      rw [ZMod.castHom_apply]
      exact PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r) a
    rw [← sub_eq_zero]
    refine (hG r).2.2 _ (fun g => B r g - ψ (B (r + 1) g)) ((hB r).sub ((hB (r + 1)).comp ψ))
      fun p => ?_
    have e1 : PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * ψ (X (r + 1)) +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * ψ (B (r + 1) p.2) - ψ (B (r + 1) (p.1 * p.2)) +
          ψ (B (r + 1) p.1)) := by
      have := congrArg ψ (hXB (r + 1) p)
      simpa only [map_add, map_sub, map_mul, hψ] using this
    have e2 := hXB r p
    show PadicInt.toZModPow r (c p) * (ψ (X (r + 1)) - X r) =
      PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * (B r p.2 - ψ (B (r + 1) p.2)) -
        (B r (p.1 * p.2) - ψ (B (r + 1) (p.1 * p.2))) + (B r p.1 - ψ (B (r + 1) p.1))
    linear_combination e2 - e1
  obtain ⟨x, hx⟩ := exists_lim (fun r => (((X r).val : ℕ) : ℤ_[l])) fun r => by
    rw [dvd_iff_toZModPow, map_sub, hred, ← PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r),
      hred]
    exact sub_eq_zero.2 (hcomp r)
  have hxr : ∀ r, PadicInt.toZModPow r x = X r := fun r => by
    have := (dvd_iff_toZModPow _).1 (hx r)
    rwa [map_sub, hred, sub_eq_zero] at this
  have hcont : ContAction (charRep χ) := by
    show Continuous fun p : G × ℤ_[l] => charRep χ p.1 p.2
    simp only [charRep_apply]
    exact (hχ.comp continuous_fst).mul continuous_snd
  have hcompat : ∀ (r : ℕ) (g : G) (a : ℤ_[l]), PadicInt.toZModPow r (charRep χ g a) =
      charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) g
        (PadicInt.toZModPow r a) := fun r g a => by
    simp [charRep_apply]
  have hyZ : (fun p => w p - x * c p) ∈ Z2 (charRep χ) := by
    refine (mem_cocycles2 _ _).2 ⟨hwc.sub (continuous_const.mul hcc), fun g h k => ?_⟩
    simp only [charRep_apply]
    linear_combination hwcoc g h k - x * hcoc g h k
  have hyB : ∀ r, (fun p => PadicInt.toZModPow r (w p - x * c p)) ∈
      B2 (charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)) := by
    intro r
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨B r, (hB r).continuous, funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    simp only [d1_apply, charRep_apply, MonoidHom.comp_apply, Units.coe_map, map_sub, map_mul, hxr]
    have e := hXB r (g, h)
    simp only at e
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    linear_combination -e
  have hker : ∀ r : ℕ, ∃ w' ∈ Z2 (charRep χ), (fun p => w p - x * c p) - (l : ℤ_[l]) ^ r • w' ∈
      B2 (charRep χ) := fun r =>
    GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary l G (charRep χ) hcont r _
      (hcompat r) _ hyZ (hyB r)
  obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1 (mem_coboundaries_of_forall_pow l G (charRep χ) _ hcompat hfin _ hyZ hker)
  have hl0 : (l : ℚ_[l]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  refine ⟨(x : ℚ_[l]) / (l : ℚ_[l]) ^ m, fun g => (f g : ℚ_[l]) / (l : ℚ_[l]) ^ m,
    (continuous_subtype_val.comp hf).div_const _, fun g h => ?_⟩
  have e := congrFun hfd (g, h)
  simp only [d1_apply, charRep_apply] at e
  have e' := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) e
  push_cast [hw] at e'
  field_simp
  linear_combination e'

end GlobalTheory.GenSpan
