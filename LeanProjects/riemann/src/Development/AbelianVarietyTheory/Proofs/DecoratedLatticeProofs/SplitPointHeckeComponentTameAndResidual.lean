import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one' : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem sec_mul' (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idlU_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul' q x y
  rw [h, sec_one'] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idlU (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idlU_mul q _ _ x.mul_inv, idlU_mul q _ _ x.inv_mul⟩

theorem continuous_idlU : Continuous (idlU q) :=
  Units.continuous_iff.2 ⟨(q.cont_sec.comp Units.continuous_val).add continuous_const,
    (q.cont_sec.comp Units.continuous_coe_inv).add continuous_const⟩

theorem res_eq_locK {PP : Formalism.L2.DIV.Pl D.host.E} {H : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (hr : Formalism.IndefR.Links.IsRes H PP c) {a : D.host.E} (ha : IntAt PP a)
    (ha0 : a ≠ 0) (r : (Formalism.L2.DIV.kP PP)ˣ) (hra : (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a) :
    c r = H.locK PP (Units.mk0 a ha0) := by
  obtain ⟨r₀, s, hs, e⟩ := ha
  have hs0 : (algebraMap (𝓞 D.host.E) D.host.E s) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hs (zero_mem _))
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field PP.asIdeal
  have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hsp := Formalism.L2.Col.reduction_spec PP hs e
  have h1 := hr s (Units.mk0 _ hs0) (Units.mk0 _ hu) rfl rfl
  have h2 := hr r₀ (Units.mk0 _ hs0 * Units.mk0 _ ha0) (Units.mk0 _ hu * r) (by simp [e])
    (by simp [hra, hsp])
  rw [map_mul, map_mul, h1] at h2
  exact mul_left_cancel h2

end Place
end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem chi_idlU_rat {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {χ : (AE D)ˣ →* Circle}
    {H : Formalism.L2.Host.HChar D.host.E} (hχ : Formalism.IndefR.Links.ChrEq χ H) {a : D.host.E} (ha0 : a ≠ 0) (u : kˣ)
    (hu : (u : k) = (ofSplit q).pr a) : (χ (idlU q u) : ℂ) = H.locK PP (Units.mk0 a ha0) := by
  exact hχ.2 PP q.e ⟨h.1.1, by
      obtain ⟨ε, hε, hs⟩ := q.above
      exact ⟨q.v, ε, hε, Or.inl ⟨h.1.2.1, hs⟩⟩, h.2⟩ (Units.mk0 _ ha0) (idlU q u) (by
        change q.sec u + (1 - q.e) = 1 + q.e * (incA D a - 1)
        rw [hu]
        change q.sec (q.pr _) + _ = _
        rw [q.sec_pr]
        ring)

end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)
section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

def prOU : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem prOU_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (prOU q z) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : prOU q z ≠ 0 := (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k (prOU q z)) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem prOU_le {PP : Formalism.L2.DIV.Pl D.host.E} (hi : ∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ IntAt PP x)
    (z : 𝓞 D.host.E) : valuation k (prOU q z) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 ((hi _).2
    ⟨z, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)

end Place

theorem tame_and_res : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → DenseRange (ofSplit q).pr → ∀ (χ : (AE D)ˣ →* Circle) (H : Formalism.L2.Host.HChar D.host.E) (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (μ : kˣ →* ℂˣ), ChrEq χ H → IsRes H PP c → (ofSplit q).IsComp χ μ → IsTame μ ∧ ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), Formalism.L2.Col.IntAt PP a → (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
  intro D k _ _ _ _ q PP h hi hd χ H c μ hχ hr hμ
  have comp : ∀ x : kˣ, (μ x : ℂ) = χ (idlU q x) := fun x => hμ x (idlU q x) rfl
  have val : ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), IntAt PP a →
      (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
    intro a u r ha hra hu
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA D)).map_zero)
    apply Units.ext
    rw [comp u, chi_idlU_rat q h hχ ha0 u hu, res_eq_locK hr ha ha0 r hra]
  refine ⟨?_, val⟩
  have rat : ∀ (a : D.host.E) (y : kˣ), (y : k) = (ofSplit q).pr a → valuation k ((y : k) - 1) < 1 →
      χ (idlU q y) = 1 := by
    intro a y hy hy1
    have hv : valuation k (y : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hy1
    have ha : IntAt PP a := (hi a).1 (by rw [← hy, Valuation.mem_integer_iff, hv])
    have hred : Formalism.L2.Col.redP PP a = 1 := by
      obtain ⟨r₀, s, hs, e⟩ := ha
      have hsp := Formalism.L2.Col.reduction_spec PP hs e
      have e' : prOU q s * y = prOU q r₀ := by
        rw [hy]
        exact ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
      have hrs : r₀ - s ∈ PP.asIdeal := by
        rw [prOU_lt q h, map_sub, ← e', ← mul_sub_one, map_mul]
        calc valuation k (prOU q s) * valuation k ((y : k) - 1) ≤ 1 * valuation k ((y : k) - 1) :=
              by gcongr; exact prOU_le q hi s
          _ < 1 := by rwa [one_mul]
      haveI := PP.isMaximal
      letI := Ideal.Quotient.field PP.asIdeal
      have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have e2 : Ideal.Quotient.mk PP.asIdeal r₀ = Ideal.Quotient.mk PP.asIdeal s :=
        Ideal.Quotient.eq.2 hrs
      rw [e2] at hsp
      exact mul_left_cancel₀ hu (hsp.trans (mul_one _).symm)
    have h1 := val a y 1 ha (by rw [Units.val_one, hred]) hy
    rw [map_one] at h1
    have h2 := comp y
    rw [h1, Units.val_one] at h2
    exact Circle.coe_injective h2.symm
  intro x hx
  suffices hs : χ (idlU q x) = 1 by
    apply Units.ext
    rw [comp x, hs]
    simp
  by_contra hne
  have hc : Continuous fun y => χ (idlU q y) := hχ.1.1.comp (continuous_idlU q)
  have h1 : {y : kˣ | χ (idlU q y) ≠ 1} ∈ nhds x := (isOpen_ne_fun hc continuous_const).mem_nhds hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨W, hW, hW'⟩ := h1
  have h2 : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha1, ha2, ha3⟩ := hd.mem_nhds (Filter.inter_mem hW (Filter.inter_mem h2 (isOpen_ne.mem_nhds x.ne_zero)))
  refine hW' (a := Units.mk0 _ ha3) ha1 (rat a _ rfl ?_)
  have := Valuation.map_add_lt (valuation k) ha2 hx
  simpa using this

end GlobalTheory.LocMod.SplitHecke
