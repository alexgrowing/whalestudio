import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDiff
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.FrameReduction
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

def HypRep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ

def Unram : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E → ∀ v : HeightOneSpectrum (𝓞 E), v ∈ Formalism.BasicNotions.placesOver E p → ((p : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1

def SatBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V),
    Submodule.IsLattice E Λ → ∀ (n : ℕ) (w : Fin (n + 1) → S.V), LinearIndependent E w →
    ∀ a : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E, (∀ i, a i ≠ 0) →
    ∃ (e : Fin (n + 1) → S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      LinearIndependent E e ∧ Submodule.span E (Set.range e) = Submodule.span E (Set.range w) ∧ c ≠ 0 ∧
      Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) =
        Formalism.L2.SG.Saturated.latSpan (Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 E)) E) a c) e

def GenFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V),
    Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) →
    ∀ (n : ℕ) (e : Fin n → S.V) (c : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      LinearIndependent E e → (∀ a b, S.hT (e a) (e b) = 0) → (∀ a, c a ≠ 0) →
      Λ ⊓ (Submodule.span E (Set.range e)).restrictScalars (𝓞 E) = Formalism.L2.SG.Saturated.latSpan c e →
      ∃ f : Fin n → S.V, (∀ a b, S.hT (f a) (f b) = 0) ∧
        (∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) ∧ ∀ b, ∀ x ∈ Λ, S.hT (f b) x ∈ c b

end GlobalTheory.St.Lat

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsoW (D : D7) : Prop :=
  ∃ w : (VS D).V, w ≠ 0 ∧ (VS D).hT w w = 0 ∧ ∀ i, (VS D).hT (D.sp.hypE i) w = 0 ∧ (VS D).hT (D.sp.hypF i) w = 0

def DdG (D : D7) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
    ¬ (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≤ P.asIdeal)

end GlobalTheory.St.Lat

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

section Gen

open Formalism.L2.SG.Saturated

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h

theorem hsmulL (c : E) (x y : S.V) : S.hT (c • x) y = star c * S.hT x y := by
  simp [starRingEnd_apply]

theorem mem_latSpan {r : ℕ} (c : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V)
    (y : S.V) : y ∈ latSpan c v ↔ ∃ x : Fin r → E, (∀ i, x i ∈ c i) ∧ y = ∑ i, x i • v i := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      refine ⟨Pi.single a x, fun i => ?_, ?_⟩
      · by_cases h : i = a
        · subst h; simpa using hx
        · rw [Pi.single_eq_of_ne h]; exact PI.SRW.fi_zero _
      · simp [Pi.single_apply, ite_smul]
    | zero => exact ⟨0, fun i => PI.SRW.fi_zero _, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨x, hx, rfl⟩ := h1
      obtain ⟨x', hx', rfl⟩ := h2
      exact ⟨x + x', fun i => PI.SRW.fi_add (hx i) (hx' i), by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul o y _ h1 =>
      obtain ⟨x, hx, rfl⟩ := h1
      refine ⟨fun i => (o : E) * x i, fun i => ?_, ?_⟩
      · have := PI.SRW.fi_smul o (hx i)
        simpa [Algebra.smul_def] using this
      · rw [PI.SRW.osmul o, Finset.smul_sum]
        simp [smul_smul]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, x i, hx i, rfl⟩)

theorem latSpan_le {r : ℕ} (c : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V)
    (Λ : Submodule (𝓞 E) S.V) (h : ∀ a, ∀ x ∈ c a, x • v a ∈ Λ) : latSpan c v ≤ Λ :=
  Submodule.span_le.2 (by rintro _ ⟨a, x, hx, rfl⟩; exact h a x hx)

def perpL (Λ : Submodule (𝓞 E) S.V) {r : ℕ} (e f : Fin r → S.V) : Submodule (𝓞 E) S.V where
  carrier := {x | x ∈ Λ ∧ ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨Λ.add_mem hx hy, fun a => ⟨by simp [(hx' a).1, (hy' a).1], by simp [(hx' a).2, (hy' a).2]⟩⟩
  zero_mem' := ⟨Λ.zero_mem, fun a => by simp⟩
  smul_mem' := by
    rintro o x ⟨hx, hx'⟩
    refine ⟨Λ.smul_mem o hx, fun a => ?_⟩
    rw [PI.SRW.osmul]
    simp [(hx' a).1, (hx' a).2]

theorem hfe_of {r : ℕ} {e f : Fin r → S.V} (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) (a b : Fin r) :
    S.hT (f a) (e b) = if a = b then 1 else 0 := by
  rw [← hconj, hef b a]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem decomp {r : ℕ} (e f : Fin r → S.V) (hee : ∀ a b, S.hT (e a) (e b) = 0)
    (hff : ∀ a b, S.hT (f a) (f b) = 0) (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) (y : S.V)
    (b : Fin r) : S.hT (e b) (y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a) = 0 ∧
      S.hT (f b) (y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a) = 0 := by
  have hfe := hfe_of hef
  constructor
  · simp only [map_sub, map_sum, map_smul, hee, hef, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · simp only [map_sub, map_sum, map_smul, hff, hfe, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

theorem key_split (Λ : Submodule (𝓞 E) S.V) {r : ℕ} (e f : Fin r → S.V)
    (P Q : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hee : ∀ a b, S.hT (e a) (e b) = 0)
    (hff : ∀ a b, S.hT (f a) (f b) = 0) (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hPe : ∀ a, ∀ x ∈ P a, x • e a ∈ Λ) (hQf : ∀ a, ∀ x ∈ Q a, x • f a ∈ Λ)
    (hfΛ : ∀ a, ∀ y ∈ Λ, S.hT (f a) y ∈ P a) (heΛ : ∀ a, ∀ y ∈ Λ, S.hT (e a) y ∈ Q a) :
    Λ = latSpan P e ⊔ perpL Λ e f ⊔ latSpan Q f := by
  have hpΛ := latSpan_le P e Λ hPe
  have hqΛ := latSpan_le Q f Λ hQf
  apply le_antisymm
  · intro y hy
    have hp : ∑ a, S.hT (f a) y • e a ∈ latSpan P e := (mem_latSpan P e _).2 ⟨_, fun a => hfΛ a y hy, rfl⟩
    have hq : ∑ a, S.hT (e a) y • f a ∈ latSpan Q f := (mem_latSpan Q f _).2 ⟨_, fun a => heΛ a y hy, rfl⟩
    have hw : y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a ∈ perpL Λ e f :=
      ⟨Λ.sub_mem (Λ.sub_mem hy (hpΛ hp)) (hqΛ hq), decomp e f hee hff hef y⟩
    have he : y = (∑ a, S.hT (f a) y • e a + (y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a)) +
        ∑ a, S.hT (e a) y • f a := by abel
    rw [he]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hp hw) hq
  · exact sup_le (sup_le hpΛ (fun x hx => hx.1)) hqΛ

end Gen

end GlobalTheory.St.Lat

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

section Gen2

open Formalism.L2.SG.Saturated

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem orth_span_right {ι : Type} {v : ι → S.V} {u : S.V} (h : ∀ i, S.hT u (v i) = 0) {y : S.V}
    (hy : y ∈ Submodule.span E (Set.range v)) : S.hT u y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact h j
  | zero => simp
  | add y y' _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h1 => simp [h1]

theorem orth_span_left {ι : Type} {v : ι → S.V} {u : S.V} (h : ∀ i, S.hT (v i) u = 0) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range v)) : S.hT x u = 0 := by
  rw [← hconj]
  have : S.hT u x = 0 := orth_span_right (fun i => by rw [← hconj, h i, star_zero]) hx
  rw [this, star_zero]

theorem iso_span {ι : Type} {v : ι → S.V} (h : ∀ i j, S.hT (v i) (v j) = 0) {x y : S.V}
    (hx : x ∈ Submodule.span E (Set.range v)) (hy : y ∈ Submodule.span E (Set.range v)) : S.hT x y = 0 :=
  orth_span_right (fun j => orth_span_left (fun i => h i j) hx) hy

theorem orth_pair {u a b y : S.V} (ha : S.hT u a = 0) (hb : S.hT u b = 0)
    (hy : y ∈ Submodule.span E ({a, b} : Set S.V)) : S.hT u y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact hb
  | zero => simp
  | add y y' _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h1 => simp [h1]

theorem zero_of_dual {r : ℕ} {e f : Fin r → S.V} (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0)
    {v : S.V} (hv : v ∈ Submodule.span E (Set.range e)) (h0 : ∀ b, S.hT (f b) v = 0) : v = 0 := by
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  have ht : ∀ b, t b = 0 := by
    intro b
    have h := h0 b
    simp only [map_sum, map_smul, hfe, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h
    exact h
  simp [ht]

theorem mem_of_dual {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x : S.V}
    (h : ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x) : x ∈ Λ := by
  have hU' := hU
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU'
  rw [← hU', PI.SRW.mem_dual_iff']
  exact h

theorem dualE {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (hI : I ≠ 0) (hst : ∀ x ∈ I, star x ∈ I) {e : S.V} (hIe : ∀ x ∈ I, x • e ∈ Λ) {y : S.V} (hy : y ∈ Λ) :
    S.hT e y ∈ I⁻¹ := by
  rw [FractionalIdeal.mem_inv_iff hI]
  intro t ht
  obtain ⟨o, ho⟩ := PI.SRW.pair_int S hU hy (hIe _ (hst t ht))
  rw [FractionalIdeal.mem_one_iff]
  refine ⟨o, ?_⟩
  rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]

theorem dualF {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (hI : I ≠ 0) (hst : ∀ x ∈ I, star x ∈ I) {f : S.V} (hf : ∀ y ∈ Λ, S.hT f y ∈ I) {x : E} (hx : x ∈ I⁻¹) :
    x • f ∈ Λ := by
  refine mem_of_dual hU (fun l hl => ?_)
  have h2 := (FractionalIdeal.mem_inv_iff hI).1 hx _ (hst _ (hf l hl))
  rw [FractionalIdeal.mem_one_iff] at h2
  obtain ⟨o, ho⟩ := h2
  refine ⟨o, ?_⟩
  rw [ho, map_smul, smul_eq_mul, ← hconj f l]

end Gen2

end GlobalTheory.St.Lat

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

section GF

open Formalism.L2.SG.Saturated

theorem fi_neg {E : Type} [Field E] [NumberField E] {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} {u : E}
    (hu : u ∈ I) : -u ∈ I :=
  FractionalIdeal.mem_coe.1 (Submodule.neg_mem _ (FractionalIdeal.mem_coe.2 hu))

theorem fi_sum {E : Type} [Field E] [NumberField E] {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} {r : ℕ}
    (g : Fin r → E) (hg : ∀ k, g k ∈ I) : ∑ k, g k ∈ I :=
  FractionalIdeal.mem_coe.1 (Submodule.sum_mem _ (fun k _ => FractionalIdeal.mem_coe.2 (hg k)))

theorem fi_intm {E : Type} [Field E] [NumberField E] {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (o : 𝓞 E) {t : E} (ht : t ∈ I) : (o : E) * t ∈ I := by
  have h1 := Submodule.smul_mem (I : Submodule (𝓞 E) E) o (FractionalIdeal.mem_coe.2 ht)
  rw [Algebra.smul_def] at h1
  exact FractionalIdeal.mem_coe.1 h1

theorem genFrame_holds : GenFrame := by
  intro E _ _ _ S Λ hlat hU htr n e c hind hiso hc0 hX
  obtain ⟨s0, hs0⟩ := htr
  obtain ⟨s1, hs1⟩ := PI.SRW.star_int s0
  let N : Submodule (𝓞 E) S.V := Λ ⊓ (Submodule.span E (Set.range e)).restrictScalars (𝓞 E)
  have hNΛ : N ≤ Λ := inf_le_left
  have hsat : ∀ (o : 𝓞 E) (x : S.V), o ≠ 0 → x ∈ Λ → o • x ∈ N → x ∈ N := by
    intro o x ho hx hox
    have h1 := (Submodule.mem_inf.1 hox).2
    rw [Submodule.restrictScalars_mem] at h1
    have hoE : (o : E) ≠ 0 := (RingOfIntegers.coe_ne_zero_iff).2 ho
    rw [PI.SRW.osmul] at h1
    have h2 := (Submodule.span E (Set.range e)).smul_mem (o : E)⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ hoE, one_smul] at h2
    exact Submodule.mem_inf.2 ⟨hx, (Submodule.restrictScalars_mem _ _ _).2 h2⟩
  obtain ⟨ρ, hρN, hρid⟩ := PI.SRW.retraction_reduction E S.V Λ N hNΛ hlat.fg hsat
  obtain ⟨cf, hcf⟩ := PI.SRW.dualFamilyExists E S.V n e hind
  have hcfN : ∀ b, ∀ y ∈ N, cf b y ∈ c b := by
    intro b y hy
    have hy' : y ∈ latSpan c e := by rw [← hX]; exact hy
    obtain ⟨x, hx, rfl⟩ := (mem_latSpan c e y).1 hy'
    simp only [map_sum, map_smul, hcf, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact hx b
  have hw := fun b : Fin n =>
    PI.SRW.sesquilinearRepresentation E S.V S.hT S.nondeg Λ hlat (((cf b).restrictScalars (𝓞 E)).comp ρ)
  choose f0 hf0 using hw
  have hf0v : ∀ b, ∀ y (hy : y ∈ Λ), S.hT (f0 b) y = cf b (ρ ⟨y, hy⟩) := fun b y hy => hf0 b ⟨y, hy⟩
  have hf0Λ : ∀ b, ∀ y ∈ Λ, S.hT (f0 b) y ∈ c b := fun b y hy => by
    rw [hf0v b y hy]; exact hcfN b _ (hρN _)
  have hceN : ∀ a, ∀ x ∈ c a, x • e a ∈ N := fun a x hx => by
    have h1 : x • e a ∈ latSpan c e := Submodule.subset_span ⟨a, x, hx, rfl⟩
    rw [← hX] at h1; exact h1
  have hceΛ : ∀ a, ∀ x ∈ c a, x • e a ∈ Λ := fun a x hx => (hceN a x hx).1
  have hf0e : ∀ b a, S.hT (f0 b) (e a) = if b = a then 1 else 0 := by
    intro b a
    have hne : (c a : Submodule (𝓞 E) E) ≠ ⊥ := FractionalIdeal.coeToSubmodule_ne_bot.2 (hc0 a)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxN := hceN a x hx
    have h1 := hf0v b (x • e a) hxN.1
    rw [hρid ⟨_, hxN.1⟩ hxN] at h1
    simp only [map_smul, hcf, smul_eq_mul] at h1
    exact mul_left_cancel₀ hx0 h1
  have hef0 : ∀ a b, S.hT (e a) (f0 b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hconj, hf0e b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hstar : ∀ k, ∀ y ∈ Λ, S.hT (e k) y • f0 k ∈ Λ := by
    intro k y hy
    refine mem_of_dual hU (fun l hl => ?_)
    obtain ⟨o, ho⟩ := PI.SRW.pair_int S hU hy (hceΛ k _ (hf0Λ k l hl))
    refine ⟨o, ?_⟩
    rw [ho, hsmulL, map_smul, smul_eq_mul, ← hconj (f0 k) l]
    ring
  let cc : Fin n → Fin n → E := fun a b =>
    if a < b then -S.hT (f0 a) (f0 b) else if a = b then -(S.hT (f0 b) (f0 b) * (s0 : E)) else 0
  have hsum : ∀ a b, S.hT (f0 a) (f0 b) + cc a b + star (cc b a) = 0 := by
    intro a b
    rcases lt_trichotomy a b with hab | hab | hab
    · have h1 : ¬ b < a := not_lt.2 hab.le
      have h2 : b ≠ a := hab.ne'
      simp [cc, hab, h1, h2]
    · subst hab
      simp only [cc, lt_irrefl, ↓reduceIte]
      rw [star_neg, star_mul', hconj]
      have h3 : S.hT (f0 a) (f0 a) * (s0 : E) + S.hT (f0 a) (f0 a) * star (s0 : E) = S.hT (f0 a) (f0 a) := by
        rw [← mul_add, hs0, mul_one]
      linear_combination -h3
    · have h1 : ¬ a < b := not_lt.2 hab.le
      have h2 : a ≠ b := hab.ne'
      simp [cc, hab, h1, h2, hconj]
  have hterm : ∀ k b, ∀ y ∈ Λ, star (cc k b) * S.hT (e k) y ∈ c b := by
    intro k b y hy
    have hm := hf0Λ b _ (hstar k y hy)
    rw [map_smul, smul_eq_mul] at hm
    rcases lt_trichotomy k b with hkb | hkb | hkb
    · simp only [cc, hkb, ↓reduceIte, star_neg, hconj, neg_mul]
      exact fi_neg (by rw [mul_comm]; exact hm)
    · subst hkb
      have key : star (cc k k) * S.hT (e k) y = -((s1 : E) * (S.hT (e k) y * S.hT (f0 k) (f0 k))) := by
        simp only [cc, lt_irrefl, ↓reduceIte]
        rw [star_neg, star_mul', hconj, hs1]
        ring
      rw [key]
      exact fi_neg (fi_intm s1 hm)
    · have h1 : ¬ k < b := not_lt.2 hkb.le
      have h2 : k ≠ b := hkb.ne'
      simp only [cc, h1, h2, ↓reduceIte, star_zero, zero_mul]
      exact PI.SRW.fi_zero _
  refine ⟨fun b => f0 b + ∑ k, cc k b • e k, ?_, ?_, ?_⟩
  · intro a b
    have h := hsum a b
    simp [map_sum, hf0e, hef0, hiso, Finset.sum_ite_eq', starRingEnd_apply]
    linear_combination h
  · intro a b
    simp [map_sum, hiso, hef0]
  · intro b y hy
    have hexp : S.hT (f0 b + ∑ k, cc k b • e k) y = S.hT (f0 b) y + ∑ k, star (cc k b) * S.hT (e k) y := by
      simp [map_sum, starRingEnd_apply]
    rw [hexp]
    exact PI.SRW.fi_add (hf0Λ b y hy) (fi_sum _ (fun k => hterm k b y hy))

end GF

end GlobalTheory.St.Lat

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

end GlobalTheory.St.Lat

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem locgen {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) {P : Ideal (𝓞 E)}
    {c : E} (hcI : c ∈ I) (hcP : c ∉ I * (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) :
    ∀ x ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = (o : E) * c := by
  intro x hx
  set J := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c * I⁻¹ with hJ
  have hJ1 : J ≤ 1 := by
    have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c ≤ I :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hcI
    calc J ≤ I * I⁻¹ := by rw [hJ]; gcongr
      _ = 1 := mul_inv_cancel₀ hI
  have hJP : ¬ J ≤ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro h
    apply hcP
    have h2 : J * I ≤ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * I := by gcongr
    rw [hJ, mul_assoc, inv_mul_cancel₀ hI, mul_one, mul_comm] at h2
    exact h2 (FractionalIdeal.mem_spanSingleton_self _ _)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJP
  obtain ⟨s', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 (hJ1 hsJ)
  refine ⟨s', fun h => hsP (FractionalIdeal.mem_coeIdeal_of_mem _ h), ?_⟩
  have h3 : (algebraMap (𝓞 E) E s') * x ∈ J * I := FractionalIdeal.mul_mem_mul hsJ hx
  rw [hJ, mul_assoc, inv_mul_cancel₀ hI, mul_one, FractionalIdeal.mem_spanSingleton] at h3
  obtain ⟨o, ho⟩ := h3
  refine ⟨o, ?_⟩
  rw [← ho, Algebra.smul_def]

theorem exists_gen {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) :
    ∃ c ∈ I, c ∉ I * (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
  have hle : I * (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ I := by
    calc I * (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ I * 1 := by gcongr; exact FractionalIdeal.coeIdeal_le_one
      _ = I := mul_one I
  have hne : I * (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ I := by
    intro h
    have h2 : I * (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = I * 1 := by rw [h, mul_one]
    have h3 := mul_left_cancel₀ hI h2
    exact hP (by rw [FractionalIdeal.coeIdeal_eq_one.1 h3, Ideal.one_eq_top])
  obtain ⟨c, hc, hcn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  exact ⟨c, hc, hcn⟩

theorem mem_locP {V : Type} [AddCommGroup V] [Module (𝓞 E) V] (P : Ideal (𝓞 E)) [P.IsPrime]
    (L : Submodule (𝓞 E) V) (x : V) : x ∈ Formalism.HermitianLatticesTheory.localization₂ P L ↔ ∃ s : 𝓞 E, s ∉ P ∧ s • x ∈ L := by
  show (∃ s ∈ P.primeCompl, s • x ∈ L) ↔ _
  rfl

theorem localization_le_of_le_localization₂ {V : Type} [AddCommGroup V] [Module (𝓞 E) V] (P : Ideal (𝓞 E)) [P.IsPrime]
    {A B : Submodule (𝓞 E) V} (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ P B) : Formalism.HermitianLatticesTheory.localization₂ P A ≤ Formalism.HermitianLatticesTheory.localization₂ P B := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP P A x).1 hx
  obtain ⟨t, ht, htx⟩ := (mem_locP P B _).1 (h hsx)
  refine (mem_locP P B x).2 ⟨t * s, fun hm => ?_, by rw [mul_smul]; exact htx⟩
  rcases Ideal.IsPrime.mem_or_mem inferInstance hm with h1 | h1
  · exact ht h1
  · exact hs h1

theorem le_locP {V : Type} [AddCommGroup V] [Module (𝓞 E) V] (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    {A : Submodule (𝓞 E) V} : A ≤ Formalism.HermitianLatticesTheory.localization₂ P A := fun x hx =>
  (mem_locP P A x).2 ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h), by rw [one_smul]; exact hx⟩

theorem localization_latSpan {S : HSpace E} {r : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime]
    (I : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) (cl : Fin r → E)
    (hcl : ∀ a, cl a ∈ I a) (hgen : ∀ a, ∀ x ∈ I a, ∃ s : 𝓞 E, s ∉ P ∧ ∃ o : 𝓞 E, (s : E) * x = (o : E) * cl a) :
    Formalism.HermitianLatticesTheory.localization₂ P (latSpan I v) = Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 E) (Set.range fun a => cl a • v a)) := by
  apply le_antisymm
  · refine localization_le_of_le_localization₂ P (Submodule.span_le.2 ?_)
    rintro _ ⟨a, x, hx, rfl⟩
    obtain ⟨s, hs, o, ho⟩ := hgen a x hx
    refine (mem_locP P _ _).2 ⟨s, hs, ?_⟩
    have he : s • (x • v a) = o • (cl a • v a) := by
      rw [PI.SRW.osmul, PI.SRW.osmul, smul_smul, smul_smul, ho]
    rw [he]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨a, rfl⟩)
  · refine localization_le_of_le_localization₂ P (le_trans ?_ (le_locP P))
    exact Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact Submodule.subset_span ⟨a, cl a, hcl a, rfl⟩)

end Gen3

end GlobalTheory.St.Lat

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

theorem satBasis_of (h : LatEx.SatBasisV) : SatBasis := by
  intro E _ _ _ S Λ hΛ n w hw a ha
  obtain ⟨e, c, h1, h2, h3, h4⟩ := h E S.V Λ hΛ n w hw a ha
  exact ⟨e, c, h1, h2, h3, h4⟩

section D7sec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ddG_of (hU : Unram) (hSD : LatEx.SplitDiff) : DdG D := by
  intro P hP
  have hg : ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    simp [gS]
  rw [hg] at hP
  have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rcases P.isPrime.mem_or_mem hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hk⟩ := hk
  have hsq := (hU D.host.E _ (D.host.g_prime k) (D.nd.g_split k) P hk).1
  exact hSD D.host.F D.host.E (D.host.g k) P.asIdeal (D.host.g_prime k) P.isMaximal hk hsq

end D7sec

end GlobalTheory.St.Lat

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

section D7asm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem aa_gen_one (hDd : DdG D) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : Fin D.R.rS) :
    (1 : D.host.E) ∈ aaS D a ∧
      (1 : D.host.E) ∉ aaS D a * (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hd0 : ddS D ≠ 0 := PI.SRW.ddS_ne D
  have hd1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  set j : ℕ := D.R.rS - (a : ℕ) with hj
  have hex : -((D.R.rS : ℤ) - (a : ℕ)) = -(j : ℤ) := by
    have := a.isLt
    rw [hj]; push_cast [Nat.cast_sub this.le]; ring
  have haa : aaS D a = (ddS D ^ j)⁻¹ := by
    simp only [aaS]
    rw [hex, zpow_neg, zpow_natCast]
  have hpow0 : ddS D ^ j ≠ 0 := pow_ne_zero _ hd0
  have hpow1 : ddS D ^ j ≤ 1 := pow_le_one₀ zero_le hd1
  rw [haa]
  constructor
  · rw [FractionalIdeal.mem_inv_iff hpow0]
    intro y hy
    rw [one_mul]
    exact hpow1 hy
  · intro h1
    apply hDd P hP
    have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (1 : D.host.E) ≤
        (ddS D ^ j)⁻¹ * (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 h1
    rw [FractionalIdeal.spanSingleton_one] at h2
    have h3 : ddS D ^ j * 1 ≤ ddS D ^ j * ((ddS D ^ j)⁻¹ *
        (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) := by gcongr
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hpow0, one_mul] at h3
    have h4 : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ j ≤ P.asIdeal := by
      rw [← FractionalIdeal.coeIdeal_le_coeIdeal D.host.E, FractionalIdeal.coeIdeal_pow]
      exact h3
    exact P.isPrime.le_of_pow_le h4

end D7asm

end GlobalTheory.St.Lat

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

section D7main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem latExists_of_steps (hSB : SatBasis) (hH : HypRep) (hI : IsoW D) (hDd : DdG D) :
    Formalism.L2.SG.SplitPrimeNormLemmas.LatExists D := by
  classical
  obtain ⟨w, hw0, hww, hwo⟩ := hI
  let wf : Fin (D.R.rS + 1) → (VS D).V := Fin.snoc (α := fun _ => (VS D).V) D.sp.hypE w
  have hfe_hyp : ∀ j i, (VS D).hT (D.sp.hypF j) (D.sp.hypE i) = if j = i then 1 else 0 :=
    hfe_of D.sp.hyp_ef
  have hind : LinearIndependent D.host.E wf := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hc : ∀ j : Fin D.R.rS, g (Fin.castSucc j) = 0 := by
      intro j
      have h1 := congrArg ((VS D).hT (D.sp.hypF j)) hg
      rw [map_sum, map_zero, Fin.sum_univ_castSucc] at h1
      simp only [wf, map_smul, Fin.snoc_castSucc, Fin.snoc_last, (hwo j).2, hfe_hyp, smul_eq_mul, mul_zero,
        add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
      exact h1
    have hl : g (Fin.last _) = 0 := by
      rw [Fin.sum_univ_castSucc] at hg
      simp only [wf, hc, zero_smul, Finset.sum_const_zero, zero_add, Fin.snoc_last] at hg
      exact (smul_eq_zero.1 hg).resolve_right hw0
    intro i
    exact Fin.lastCases hl (fun j => hc j) i
  have hsnoc_iso : ∀ i j, (VS D).hT (wf i) (wf j) = 0 := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp only [wf, Fin.snoc_last, Fin.snoc_castSucc]
    · exact hww
    · rw [← hconj, (hwo j).1, star_zero]
    · exact (hwo i).1
    · exact D.sp.hyp_ee i j
  have haa := PI.SRW.adjoint_action_reduction D
  obtain ⟨e', c, hind', hspan, hc0, hX⟩ :=
    hSB D.host.E (VS D) (VS D).L0 (VS D).standardTuple_isLattice D.R.rS wf hind (aaS D) (fun a => (haa a).1)
  have hmem : ∀ a, e' a ∈ Submodule.span D.host.E (Set.range wf) := fun a =>
    hspan ▸ Submodule.subset_span ⟨a, rfl⟩
  have he'iso : ∀ a b, (VS D).hT (e' a) (e' b) = 0 := fun a b => iso_span hsnoc_iso (hmem a) (hmem b)
  let cc : Fin (D.R.rS + 1) → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
    Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (aaS D) c
  have hcc0 : ∀ a, cc a ≠ 0 := fun a =>
    Fin.lastCases (by simpa [cc] using hc0) (fun a => by simpa [cc] using (haa a).1) a
  have hX' : (VS D).L0 ⊓ (Submodule.span D.host.E (Set.range e')).restrictScalars (𝓞 D.host.E) =
      latSpan cc e' := by rw [hspan]; exact hX
  obtain ⟨f', hf'iso, he'f', hf'Λ⟩ := genFrame_holds D.host.E (VS D) (VS D).L0 (VS D).standardTuple_isLattice
    (VS D).baseLattice_isUnimodular (PI.SRW.trace_reduction D) _ e' cc hind' he'iso hcc0 hX'
  have hccΛ : ∀ a, ∀ x ∈ cc a, x • e' a ∈ (VS D).L0 := fun a x hx => by
    have h1 : x • e' a ∈ latSpan cc e' := Submodule.subset_span ⟨a, x, hx, rfl⟩
    rw [← hX'] at h1
    exact h1.1
  let eX : Fin D.R.rS → (VS D).V := fun a => e' (Fin.castSucc a)
  let fY : Fin D.R.rS → (VS D).V := fun a => f' (Fin.castSucc a)
  let el : (VS D).V := e' (Fin.last _)
  let fl : (VS D).V := f' (Fin.last _)
  have hee : ∀ a b, (VS D).hT (eX a) (eX b) = 0 := fun a b => he'iso _ _
  have hff : ∀ a b, (VS D).hT (fY a) (fY b) = 0 := fun a b => hf'iso _ _
  have hef : ∀ a b, (VS D).hT (eX a) (fY b) = if a = b then 1 else 0 := fun a b => by
    simp only [eX, fY, he'f', Fin.castSucc_inj]
  have hPe : ∀ a, ∀ x ∈ aaS D a, x • eX a ∈ (VS D).L0 := fun a x hx =>
    hccΛ (Fin.castSucc a) x (by simpa [cc] using hx)
  have hfΛ : ∀ a, ∀ y ∈ (VS D).L0, (VS D).hT (fY a) y ∈ aaS D a := fun a y hy => by
    simpa [cc] using hf'Λ (Fin.castSucc a) y hy
  have heΛ : ∀ a, ∀ y ∈ (VS D).L0, (VS D).hT (eX a) y ∈ (aaS D a)⁻¹ := fun a y hy =>
    dualE (VS D).baseLattice_isUnimodular (haa a).1 (haa a).2 (hPe a) hy
  have hQf : ∀ a, ∀ x ∈ (aaS D a)⁻¹, x • fY a ∈ (VS D).L0 := fun a x hx =>
    dualF (VS D).baseLattice_isUnimodular (haa a).1 (haa a).2 (hfΛ a) hx
  have hsplit := key_split (VS D).L0 eX fY (aaS D) (fun a => (aaS D a)⁻¹) hee hff hef hPe hQf hfΛ heΛ
  have hel_el : (VS D).hT el el = 0 := he'iso _ _
  have hfl_fl : (VS D).hT fl fl = 0 := hf'iso _ _
  have hel_fl : (VS D).hT el fl = 1 := by simp [el, fl, he'f']
  have hcel : ∀ x ∈ c, x • el ∈ (VS D).L0 := fun x hx => hccΛ (Fin.last _) x (by simpa [cc] using hx)
  have hflc : ∀ y ∈ (VS D).L0, (VS D).hT fl y ∈ c := fun y hy => by simpa [cc] using hf'Λ (Fin.last _) y hy
  have hl1 : ∀ a, (VS D).hT (eX a) el = 0 := fun a => he'iso _ _
  have hl2 : ∀ a, (VS D).hT (eX a) fl = 0 := fun a => by
    simp only [eX, fl, he'f']; rw [if_neg (Fin.castSucc_ne_last a)]
  have hl3 : ∀ a, (VS D).hT (fY a) el = 0 := fun a => by
    rw [← hconj]; simp only [fY, el, he'f']; rw [if_neg (Fin.castSucc_ne_last a).symm, star_zero]
  have hl4 : ∀ a, (VS D).hT (fY a) fl = 0 := fun a => hf'iso _ _
  have hz : ∀ u : D.what₂.Word, ∃ z : (VS D).V, z ∈ Submodule.span D.host.E {el, fl} ∧ z ∈ (VS D).L0 ∧
      (VS D).hT z z = -(((D.mem u).A.T : ℕ) : D.host.E) ∧
      ∀ γ : D.host.E, γ • z ∈ (VS D).L0 → ∃ o : 𝓞 D.host.E, (o : D.host.E) = γ := by
    intro u
    exact hH D.host.F D.host.E D.sp.cm (VS D) (VS D).L0 (VS D).baseLattice_isUnimodular (PI.SRW.trace_reduction D)
      el fl c hc0 hel_el hfl_fl hel_fl hcel hflc _ (D.mem u).A.T_prime.ne_zero
  choose zu hzspan hzL hznorm hzprim using hz
  have hzo : ∀ u a, (VS D).hT (eX a) (zu u) = 0 ∧ (VS D).hT (fY a) (zu u) = 0 := fun u a =>
    ⟨orth_pair (hl1 a) (hl2 a) (hzspan u), orth_pair (hl3 a) (hl4 a) (hzspan u)⟩
  have heX_ind : LinearIndependent D.host.E eX := hind'.comp _ (Fin.castSucc_injective _)
  let Fu : ∀ u, FlagS D u := fun u =>
    { e := eX, z := zu u, e_indep := heX_ind, e_iso := hee, z_orth := fun a => (hzo u a).1,
      z_norm := hznorm u }
  have hXL : (VS D).L0 ⊓ (Submodule.span D.host.E (Set.range eX)).restrictScalars (𝓞 D.host.E) =
      latSpan (aaS D) eX := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyΛ, hyX⟩ := Submodule.mem_inf.1 hy
      rw [Submodule.restrictScalars_mem] at hyX
      have hβ : ∀ a, (VS D).hT (eX a) y = 0 := fun a => orth_span_right (fun b => hee a b) hyX
      have hwperp := decomp eX fY hee hff hef y
      have hw0 : y - ∑ a, (VS D).hT (fY a) y • eX a = 0 := by
        refine zero_of_dual (hfe_of hef) (Submodule.sub_mem _ hyX (Submodule.sum_mem _
          (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)))) (fun b => ?_)
        have h1 := (hwperp b).2
        simpa [hβ] using h1
      rw [sub_eq_zero.1 hw0]
      exact (mem_latSpan (aaS D) eX _).2 ⟨_, fun a => hfΛ a y hyΛ, rfl⟩
    · refine le_inf (latSpan_le _ _ _ hPe) ?_
      exact Submodule.span_le.2 (by
        rintro _ ⟨a, x, hx, rfl⟩
        exact (Submodule.restrictScalars_mem _ _ _).2 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)))
  have hloc : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ cl : Fin D.R.rS → D.host.E, (∀ a, cl a ≠ 0) ∧
      (((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, cl a = 1) ∧
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latSpan (aaS D) eX) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => cl a • eX a)) := by
    intro P
    have hPt : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
    have hgen : ∀ a, ∃ c' ∈ aaS D a, c' ∉ aaS D a * (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧
        (((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → c' = 1) := by
      intro a
      by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
      · obtain ⟨h1, h2⟩ := aa_gen_one D hDd P hg a
        exact ⟨1, h1, h2, fun _ => rfl⟩
      · obtain ⟨c', hc', hc'n⟩ := exists_gen (haa a).1 hPt
        exact ⟨c', hc', hc'n, fun h => absurd h hg⟩
    choose cl hclI hclP hcl1 using hgen
    refine ⟨cl, fun a h0 => hclP a (by rw [h0]; exact FractionalIdeal.zero_mem _), fun hg a => hcl1 a hg, ?_⟩
    exact localization_latSpan P.asIdeal (aaS D) eX cl hclI (fun a => locgen (haa a).1 (hclI a) (hclP a))
  have hprim : ∀ u (γ : D.host.E), γ • zu u ∈ Lsub (VS D).L0 (⟨Fu u, zu u⟩ : LFlag (VS D) D.R.rS _) →
      ∃ o : 𝓞 D.host.E, (o : D.host.E) = γ := by
    intro u γ hγ
    obtain ⟨h1, -⟩ := Submodule.mem_inf.1 hγ
    obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 h1
    obtain ⟨hlΛ, hlo⟩ := Submodule.mem_inf.1 hl
    have hx' : x ∈ Submodule.span D.host.E (Set.range eX) := hx
    have hlo' : l ∈ orth (VS D) (Submodule.span D.host.E (Set.range eX)) := hlo
    have hβ : ∀ a, (VS D).hT (eX a) l = 0 := fun a =>
      (PI.SRW.mem_orth_iff.1 hlo') (eX a) (Submodule.subset_span ⟨a, rfl⟩)
    have hwperp := decomp eX fY hee hff hef l
    have hp : ∑ a, (VS D).hT (fY a) l • eX a ∈ (VS D).L0 :=
      latSpan_le _ _ _ hPe ((mem_latSpan _ _ _).2 ⟨_, fun a => hfΛ a l hlΛ, rfl⟩)
    have hw : l - ∑ a, (VS D).hT (fY a) l • eX a ∈ (VS D).L0 := (VS D).L0.sub_mem hlΛ hp
    have hwf : ∀ b, (VS D).hT (fY b) (l - ∑ a, (VS D).hT (fY a) l • eX a) = 0 := fun b => by
      have h2 := (hwperp b).2
      simpa [hβ] using h2
    have hxp : x + ∑ a, (VS D).hT (fY a) l • eX a = γ • zu u - (l - ∑ a, (VS D).hT (fY a) l • eX a) := by
      rw [← hlx]; abel
    have hxpX : x + ∑ a, (VS D).hT (fY a) l • eX a ∈ Submodule.span D.host.E (Set.range eX) :=
      Submodule.add_mem _ hx' (Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)))
    have hxp0 : x + ∑ a, (VS D).hT (fY a) l • eX a = 0 := by
      refine zero_of_dual (hfe_of hef) hxpX (fun b => ?_)
      rw [hxp, map_sub, map_smul, (hzo u b).2, hwf b, smul_zero, sub_zero]
    have hγz : γ • zu u = l - ∑ a, (VS D).hT (fY a) l • eX a := sub_eq_zero.1 (hxp.symm.trans hxp0)
    exact hzprim u γ (hγz ▸ hw)
  refine ⟨{
      eX := eX
      fY := fY
      ee := hee
      ff := hff
      ef := hef
      Lb := perpL (VS D).L0 eX fY
      Lb_perp := fun x hx a => hx.2 a
      Lam_split := hsplit
      zu := zu
      zu_norm := hznorm
      zu_orth := hzo
      zu_Lb := fun u => ⟨hzL u, fun a => hzo u a⟩
      Fu := Fu
      Fu_e := fun u => rfl
      flagZVector := fun u => rfl
      Fu_fixed := fun u => ⟨(VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular, ⟨hzL u, rfl⟩, ⟨fun P => ?_, hprim u⟩⟩ }⟩
  obtain ⟨cl, hcl0, hcl1, hcle⟩ := hloc P
  refine ⟨cl, hcl0, hcl1, ?_⟩
  show Formalism.HermitianLatticesTheory.localization₂ P.asIdeal ((VS D).L0 ⊓ (Submodule.span D.host.E (Set.range eX)).restrictScalars (𝓞 D.host.E)) = _
  rw [hXL]
  exact hcle

end D7main

end GlobalTheory.St.Lat

namespace GlobalTheory.St.Lat
open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

theorem latExists_of (hH : HypRep) (hU : Unram) (D : Formalism.BasicNotions.D7) (hI : IsoW D) : Formalism.L2.SG.SplitPrimeNormLemmas.LatExists D :=
  latExists_of_steps D (satBasis_of LatEx.satBasisV_holds) hH hI (ddG_of D hU LatEx.splitDiff_holds)

end GlobalTheory.St.Lat
