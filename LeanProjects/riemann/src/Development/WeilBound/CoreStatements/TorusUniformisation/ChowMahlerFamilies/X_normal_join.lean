import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XChartNoethFrac
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XCoherentGens
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.X_join_model
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_normal_join

open PositivityTheory.Xgn.A_coherent_gens (mem_spanOver spanOver_le)
open PositivityTheory.Xgn.A_chart_noeth_frac (mseg_join ratio_eq)
open ReciprocityTheory.ChartRestriction.G.Geo (exists_pow_mul_mem_chartRing div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

def intGrp (R : Subalgebra O Ω) : AddSubgroup Ω :=
  (integralClosure R Ω).toSubring.toAddSubgroup

theorem mem_intGrp {R : Subalgebra O Ω} {v : Ω} : v ∈ intGrp R ↔ IsIntegral R v := Iff.rfl

theorem isIntegral_of_mem {R : Subalgebra O Ω} {a : Ω} (ha : a ∈ R) : IsIntegral R a :=
  isIntegral_algebraMap (R := R) (A := Ω) (x := ⟨a, ha⟩)

theorem exists_pow_mul_isIntegral (R R' : Subalgebra O Ω) {r : Ω} (hr : IsIntegral R r)
    (h : ∀ a ∈ R', ∃ n : ℕ, IsIntegral R (r ^ n * a)) {v : Ω} (hv : IsIntegral R' v) :
    ∃ n : ℕ, IsIntegral R (r ^ n * v) := by
  obtain ⟨p, hp, hpv⟩ := hv
  choose m hm using fun i => h _ (p.coeff i).2
  let N := p.support.sup m
  let q : Polynomial Ω := Polynomial.C (r ^ N) * p.map (algebraMap R' Ω)
  have hq : q ∈ Polynomial.lifts (algebraMap (integralClosure R Ω) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine ⟨⟨q.coeff i, ?_⟩, rfl⟩
    show IsIntegral R (q.coeff i)
    simp only [q, Polynomial.coeff_C_mul, Polynomial.coeff_map]
    by_cases hi : i ∈ p.support
    · have hle : m i ≤ N := Finset.le_sup hi
      have e : r ^ N * algebraMap R' Ω (p.coeff i) = r ^ (N - m i) * (r ^ m i * (p.coeff i : Ω)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]; rfl
      rw [e]
      exact (hr.pow _).mul (hm i)
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero, mul_zero]
      exact isIntegral_zero
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).1 hq
  have h0 : Polynomial.aeval v Q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap Ω, hQ]
    simp only [q, map_mul, Polynomial.aeval_map_algebraMap]
    rw [Polynomial.aeval_def (R := R'), hpv, mul_zero]
  have h1 := isIntegral_leadingCoeff_smul Q v h0
  have h2 : algebraMap (integralClosure R Ω) Ω Q.leadingCoeff = r ^ N := by
    have hinj : Function.Injective (algebraMap (integralClosure R Ω) Ω) := Subtype.val_injective
    rw [← Polynomial.leadingCoeff_map_of_injective hinj, hQ]
    simp only [q]
    rw [(hp.map _).leadingCoeff_C_mul]
  rw [Algebra.smul_def, h2] at h1
  exact ⟨N, isIntegral_trans (A := integralClosure R Ω) _ h1⟩

theorem exists_span (R : Subalgebra O Ω) [h : Module.Finite R (integralClosure R Ω)] :
    ∃ S : Finset Ω, intGrp R = spanOver R (S : Set Ω) := by
  have hfg : (Subalgebra.toSubmodule (integralClosure R Ω)).FG :=
    Module.Finite.iff_fg.1 h
  obtain ⟨S, hS⟩ := hfg
  refine ⟨S, le_antisymm (fun v hv => ?_) (spanOver_le R (fun a ha v hv => ?_) fun e he => ?_)⟩
  · have hv' : v ∈ Submodule.span R (S : Set Ω) := by rw [hS]; exact hv
    obtain ⟨f, hf⟩ := (Submodule.mem_span_finset).1 hv'
    rw [← hf.2]
    exact sum_mem fun e he => AddSubgroup.subset_closure ⟨f e, (f e).2, e, he, rfl⟩
  · exact (isIntegral_of_mem ha).mul hv
  · have he' : e ∈ Submodule.span R (S : Set Ω) := Submodule.subset_span he
    rw [hS] at he'
    exact he'

theorem isIntegrallyClosedIn (R R' : Subalgebra O Ω) {u : Ω} (hu0 : u ≠ 0) (hu : IsIntegral R u)
    (h1 : ∀ a, IsIntegral R a → u⁻¹ * a ∈ R') (h2 : ∀ a ∈ R', ∃ n : ℕ, IsIntegral R (u ^ n * a)) :
    IsIntegrallyClosedIn R' Ω := by
  refine isIntegrallyClosedIn_iff.2 ⟨Subtype.val_injective, fun {v} hv => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral R R' hu h2 hv
  have hi : u⁻¹ ∈ R' := by simpa using h1 1 isIntegral_one
  have ha := mul_mem (pow_mem hi n) (h1 _ (hu.mul hn))
  have e : u⁻¹ ^ n * (u⁻¹ * (u * (u ^ n * v))) = v := by
    rw [inv_mul_cancel_left₀ hu0, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ hu0)]
  rw [e] at ha
  exact ⟨⟨v, ha⟩, rfl⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem fam (x : (Σ k, ι k) → Ω) : IsLatFamily O x fun c => intGrp (chartRing O (mseg x) c) := by
  refine ⟨fun s _ a ha v hv => (isIntegral_of_mem ha).mul hv, fun s t hs _ v hv => ?_⟩
  refine exists_pow_mul_isIntegral _ (chartRing O (mseg x) s)
    (isIntegral_of_mem (div_mem_chartRing (mseg x) t s)) (fun a ha => ?_) hv
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs ha
  exact ⟨n, isIntegral_of_mem hn⟩

end PositivityTheory.Xgn.A_normal_join

open PositivityTheory.Xgn.A_normal_join PositivityTheory.Xgn.A_coherent_gens PositivityTheory.Xgn.A_chart_noeth_frac in
theorem PositivityTheory.Xgn.t_normal_join : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ NormalCharts O (joinCoord x z) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ d hx htop
  obtain ⟨hK, hx0, hinj, hT⟩ := (PositivityTheory.Xgn.A_join_model.isModelOver_iff x d).1 hx
  obtain ⟨-, hfrac, hjoin⟩ := PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x
  have hfg : ∀ c, mseg x c ≠ 0 → ∃ S : Finset Ω, intGrp (chartRing O (mseg x) c) =
      spanOver (chartRing O (mseg x) c) (S : Set Ω) := by
    intro c hc
    have := hfrac htop c hc
    have : Algebra.FiniteType O (chartRing O (mseg x) c) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    have : Algebra.EssFiniteType (chartRing O (mseg x) c) Ω :=
      .of_isLocalization Ω (nonZeroDivisors _)
    have := GlobalTheory.finite_integralClosure_of_injective O (chartRing O (mseg x) c) Ω hinj
    exact exists_span _
  obtain ⟨a, ha⟩ := PositivityTheory.Xgn.t_coherent_gens O Ω K ι x Ω _ (fam x) hfg
  obtain ⟨M, v, hv⟩ := ha a le_rfl
  let z : (Σ _ : Unit, Fin M) → Ω := fun p => v p.2
  obtain ⟨hf, hle⟩ := hjoin Unit (fun _ => Fin M) z
  have hz : ∃ j, v j ≠ 0 := by
    by_contra hn
    push Not at hn
    choose c hc using hx0
    have hc' : mseg x c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
    have h1 : (1 : Ω) ∈ intGrp (chartRing O (mseg x) c) := isIntegral_one
    rw [hv c hc'] at h1
    have h2 := spanOver_le (L := ⊥) (chartRing O (mseg x) c)
      (S := Set.range fun j => (chartMon x c a)⁻¹ • v j)
      (fun a _ w hw => by rw [AddSubgroup.mem_bot.1 hw, smul_zero]; exact zero_mem _)
      (by rintro _ ⟨j, rfl⟩; simp [hn j]) h1
    exact one_ne_zero (AddSubgroup.mem_bot.1 h2)
  refine ⟨Unit, inferInstance, inferInstance, fun _ => Fin M, inferInstance, z, ?_, fun c' hc' => ?_⟩
  · refine (PositivityTheory.Xgn.A_join_model.isModelOver_iff (joinCoord x z) d).2 ⟨inferInstance, ?_, hinj, ?_⟩
    · rintro (k | k)
      · exact hx0 k
      · exact hz
    · rw [hf htop, ← htop]
      exact hT
  · obtain ⟨hc, hR⟩ := hle c' hc'
    have hj : ∀ t : ∀ k : K ⊕ Unit, Sum.elim ι (fun _ => Fin M) k,
        mseg (joinCoord x z) t = mseg x (restrictChart t) * v (t (.inr ())) := by
      intro t
      rw [mseg_join]
      simp [mseg, z]
    have hl : v (c' (.inr ())) ≠ 0 := by
      rw [hj] at hc'
      exact right_ne_zero_of_mul hc'
    have hm : chartMon x (restrictChart c') a ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ =>
        zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k))
    have hw : ∀ j, IsIntegral (chartRing O (mseg x) (restrictChart c'))
        ((chartMon x (restrictChart c') a)⁻¹ * v j) := by
      intro j
      rw [← mem_intGrp, hv _ hc]
      exact mem_spanOver _ ⟨j, rfl⟩
    refine isIntegrallyClosedIn (chartRing O (mseg x) (restrictChart c')) _
      (mul_ne_zero (inv_ne_zero hm) hl) (hw _) (fun b hb => ?_) (fun b hb => ?_)
    · rw [← mem_intGrp, hv _ hc] at hb
      refine spanOver_le (L := (chartRing O (mseg (joinCoord x z)) c').toSubring.toAddSubgroup.comap
        (AddMonoidHom.mulLeft ((chartMon x (restrictChart c') a)⁻¹ * v (c' (.inr ())))⁻¹)) _
        (fun r hr w hw => ?_) ?_ hb
      · show _ * (r * w) ∈ chartRing O (mseg (joinCoord x z)) c'
        rw [mul_left_comm]
        exact mul_mem (hR hr) hw
      · rintro _ ⟨j, rfl⟩
        show _ * (_ * v j) ∈ chartRing O (mseg (joinCoord x z)) c'
        have e : ((chartMon x (restrictChart c') a)⁻¹ * v (c' (.inr ())))⁻¹ *
            ((chartMon x (restrictChart c') a)⁻¹ * v j) = v j / v (c' (.inr ())) := by
          field_simp
        rw [e]
        have e2 := ratio_eq (joinCoord x z) c' hc' (.inr ()) j
        have e3 : v j / v (c' (.inr ())) =
            mseg (joinCoord x z) (Function.update c' (.inr ()) j) / mseg (joinCoord x z) c' := e2.symm
        rw [e3]
        exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
    · unfold chartRing at hb
      induction hb using Algebra.adjoin_induction with
      | mem b hb =>
        obtain ⟨t, rfl⟩ := hb
        refine ⟨1, ?_⟩
        have e : ((chartMon x (restrictChart c') a)⁻¹ * v (c' (.inr ()))) ^ 1 *
            (mseg (joinCoord x z) t / mseg (joinCoord x z) c') =
            (mseg x (restrictChart t) / mseg x (restrictChart c')) *
              ((chartMon x (restrictChart c') a)⁻¹ * v (t (.inr ()))) := by
          rw [hj, hj]
          field_simp
        simp only
        rw [e]
        exact (isIntegral_of_mem (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _)).mul (hw _)
      | algebraMap r =>
        exact ⟨0, isIntegral_of_mem (by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r)⟩
      | add b₁ b₂ _ _ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        refine ⟨n₁ + n₂, ?_⟩
        have h := (((hw (c' (.inr ()))).pow n₂).mul h₁).add (((hw (c' (.inr ()))).pow n₁).mul h₂)
        have e : ∀ u : Ω, u ^ (n₁ + n₂) * (b₁ + b₂) = u ^ n₂ * (u ^ n₁ * b₁) + u ^ n₁ * (u ^ n₂ * b₂) :=
          fun u => by ring
        rw [e]
        exact h
      | mul b₁ b₂ _ _ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        refine ⟨n₁ + n₂, ?_⟩
        have e : ∀ u : Ω, u ^ (n₁ + n₂) * (b₁ * b₂) = u ^ n₁ * b₁ * (u ^ n₂ * b₂) := fun u => by ring
        rw [e]
        exact h₁.mul h₂
