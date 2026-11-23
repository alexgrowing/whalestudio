import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SymChainAt
open GlobalTheory.FinPl (SplitPt idAt intAt)
open Formalism.L2.NTheta (IsIdemAt)
open Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem pr_e : q.pr q.e = 1 := by rw [← sec_one, q.pr_sec]

theorem pr_e_mul (x : AE D) : q.pr (q.e * x) = q.pr x := by rw [map_mul, pr_e, one_mul]

theorem place_facts {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pr_e_mul, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pr_e_mul]

def prO : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem prO_le {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) : valuation k (prO q z) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (((place_facts q h).1 _).2
    ⟨z, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)

theorem prO_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (prO q z) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : prO q z ≠ 0 := (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k (prO q z)) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem prO_eq_one {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {z : 𝓞 D.host.E} (hz : z ∉ PP.asIdeal) :
    valuation k (prO q z) = 1 := le_antisymm (prO_le q h z) (not_lt.1 (mt (prO_lt q h z).2 hz))

theorem sec_mul (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idl_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul q x y
  rw [h, sec_one] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idl (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idl_mul q _ _ x.mul_inv, idl_mul q _ _ x.inv_mul⟩

theorem continuous_idl : Continuous (idl q) :=
  Units.continuous_iff.2 ⟨(q.cont_sec.comp Units.continuous_val).add continuous_const,
    (q.cont_sec.comp Units.continuous_coe_inv).add continuous_const⟩

theorem unram_idl {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (x : kˣ) (hx : valuation k (x : k) = 1) :
    χ (idl q x) = 1 := by
  have one : finPart D 1 ∈ intAE D := by
    rw [map_one]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simp, 1, rfl⟩
  have key : ∀ y : k, valuation k y ≤ 1 → finPart D (q.sec y + (1 - q.e)) ∈ intAE D := fun y hy => by
    rw [RingHom.map_add, RingHom.map_sub, ← sec_one]
    exact add_mem ((q.int_iff y).1 hy) (sub_mem one ((q.int_iff 1).1 (one_mem _)))
  refine hχ _ ?_ (key _ hx.le) (key _ (by simp [hx]))
  have h1 : infPart D (q.sec x) = 0 := (GlobalTheory.FrameGlob.sec_mem_idAt q x).1
  have h2 : infPart D q.e = 0 := (GlobalTheory.FrameGlob.e_mem_idAt q).1
  change infPart D (q.sec x + (1 - q.e)) = 1
  rw [RingHom.map_add, RingHom.map_sub, h1, h2, RingHom.map_one, zero_add, sub_zero]

theorem res_idl {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {χ : (AE D)ˣ →* Circle} {H : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (hχ : Formalism.IndefR.Links.ChrEq χ H) (hr : Formalism.IndefR.Links.IsRes H PP c) (x : kˣ)
    (hx : valuation k ((x : k) - 1) < 1) : χ (idl q x) = 1 := by
  obtain ⟨hi, hd⟩ := place_facts q h
  have rat : ∀ (a : D.host.E) (y : kˣ), (y : k) = (ofSplit q).pr a → valuation k ((y : k) - 1) < 1 → χ (idl q y) = 1 := by
    intro a y hy hy1
    have hv : valuation k (y : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hy1
    obtain ⟨r, s, hs, e⟩ := (hi a).1 (by rw [← hy, Valuation.mem_integer_iff, hv])
    have e' : prO q s * y = prO q r := by
      rw [hy]
      exact ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
    have hrs : r - s ∈ PP.asIdeal := by
      rw [prO_lt q h, map_sub, ← e', ← mul_sub_one, map_mul, prO_eq_one q h hs, one_mul]
      exact hy1
    have hs0 : (s : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hs (zero_mem _))
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact y.ne_zero (hy.trans (q.pr.comp (incA D)).map_zero)
    haveI := PP.isMaximal
    letI := Ideal.Quotient.field PP.asIdeal
    have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := hr s (Units.mk0 _ hs0) (Units.mk0 _ hu) rfl rfl
    have h2 := hr r (Units.mk0 _ hs0 * Units.mk0 _ ha0) (Units.mk0 _ hu) e (Ideal.Quotient.eq.2 hrs).symm
    rw [map_mul, ← h1, left_eq_mul] at h2
    have h3 := hχ.2 PP q.e ⟨h.1.1, by
      obtain ⟨ε, hε, hs⟩ := q.above
      exact ⟨q.v, ε, hε, Or.inl ⟨h.1.2.1, hs⟩⟩, h.2⟩ (Units.mk0 _ ha0) (idl q y) (by
        change q.sec y + (1 - q.e) = 1 + q.e * (incA D a - 1)
        rw [hy]
        change q.sec (q.pr _) + _ = _
        rw [q.sec_pr]
        ring)
    rw [h2] at h3
    exact Circle.coe_injective h3
  by_contra hne
  have hc : Continuous fun y => χ (idl q y) := hχ.1.1.comp (continuous_idl q)
  have h1 : {y : kˣ | χ (idl q y) ≠ 1} ∈ nhds x := (isOpen_ne_fun hc continuous_const).mem_nhds hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨W, hW, hW'⟩ := h1
  have h2 : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha1, ha2, ha3⟩ := hd.mem_nhds (Filter.inter_mem hW (Filter.inter_mem h2 (isOpen_ne.mem_nhds x.ne_zero)))
  refine hW' (a := Units.mk0 _ ha3) ha1 (rat a _ rfl ?_)
  have := Valuation.map_add_lt (valuation k) ha2 hx
  simpa using this

theorem tame_comp {c : GlobalTheory.ChainOnto.Com D} (hc : c.Is) {PP : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ c.Pg) (h : IsIdemAt q.e PP)
    {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ} (hμ : (ofSplit q).IsComp (c.chS j)⁻¹ μ) : IsTame μ := by
  intro x hx
  have hv : valuation k (x : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨H, hH, hr⟩ := hc.res ⟨i, h2⟩
  have e1 := res_idl q h hH (hr PP hP) x hx
  have e2 := unram_idl q hc.chars.2.1 x hv
  have e3 : c.chS (i + 1) (idl q x) = 1 := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs
    · change c.μ (i + 1) (idl q x) * (c.η (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

end Place

theorem exists_symData_at : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), d.c.Is → PP ∈ d.c.Pg →
    Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar d.c.ψ ψk → HasConductor ψk 1 →
    ∀ s ρ : ℕ, s = 2 * ρ → ∃ S : SymData k s D.R.k, S.ψ = ψk ∧
      ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j) := by
  intro D u d k _ _ _ _ q PP hc hP h ψk _ hψ s ρ hs
  subst hs
  classical
  let μ : ℕ → kˣ →* ℂˣ := fun j =>
    if 1 ≤ j ∧ j ≤ D.R.m then Classical.choose (Witness.exists_isComp (ofSplit q) (d.c.chS j)⁻¹) else 1
  have hμ : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (μ j) := fun j h1 h2 => by
    simp only [μ, if_pos (And.intro h1 h2)]
    exact Classical.choose_spec (Witness.exists_isComp (ofSplit q) (d.c.chS j)⁻¹)
  have htame : ∀ j, IsTame (μ j) := fun j => by
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · exact tame_comp q hc hP h hj.1 hj.2 (hμ j hj.1 hj.2)
    · simp only [μ, if_neg hj]
      intro x _
      rfl
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using ht.symm)
  have hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif (Units.mk0 t ht0) := fun x => by
    rw [Units.val_mk0, ht]
    exact le_uniformizer_iff.symm
  obtain ⟨P, hP'⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel k ψk hψ _ hϖ ρ D.R.k (2 * ρ + 1)
  exact ⟨SymData.mk ψk (Units.mk0 t ht0) ρ P μ htame hψ hϖ rfl hP', rfl, hμ⟩

end GlobalTheory.LocMod.SymChainAt
