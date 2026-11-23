import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_snd_le {D : D7} {j N : ℕ} {β : Idx D j N →₀ ℕ} {q : (Idx D j N →₀ ℕ) × (Idx D j N →₀ ℕ)}
    (hq : q ∈ Finset.HasAntidiagonal.antidiagonal β) :
    (q.2.sum fun _ n => n) ≤ (β.sum fun _ n => n) := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Nat.le_add_left _ _

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j}
  {la : HeightOneSpectrum (𝓞 B.KO)} {N : ℕ} {w : Fin N → B.Cusp j wL}

theorem hasse_Op_smul (o : Op X la N) (x : ↥(HK X la w wF)) (β : Idx D j N →₀ ℕ) :
    hasse X la w β (((algebraMap (Op X la N) (Kp X la N) o • x : ↥(HK X la w wF))) : Lw X la w) =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β,
        algebraMap (Op X la N) (Kp X la N) (hasseOp X la N q.1 o) • hasse X la w q.2 (x : Lw X la w) := by
  have e1 : ((algebraMap (Op X la N) (Kp X la N) o • x : ↥(HK X la w wF)) : Lw X la w) =
      algebraMap (Rp X la N) (Lw X la w) (algebraMap (Op X la N) (Rp X la N) o) * (x : Lw X la w) := by
    rw [Submodule.coe_smul_of_tower, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w),
      ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  rw [e1]
  refine (hasse_mul X la w β _ _).trans (Finset.sum_congr rfl fun q _ => ?_)
  rw [Algebra.smul_def]
  congr 1
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lc X la w),
    ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  exact hasse_algebraMap_Op X la w q.1 o

theorem aaRep_holds : AARep := by
  unfold AARep
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw x hx
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  suffices key : ∃ x' : ↥(HK X la G.w wF),
      (∃ hx' : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
          hasse X la G.w β (x' : Lw X la G.w) ∈ HK X la G.w wF,
        ∀ β hβ, toA0K X la G.w wF ⟨_, hx' β hβ⟩ ∈ Q.A0) ∧
      toWK X la G.w wF (a0 D j T) x' = x by
    obtain ⟨x', ⟨_, h2⟩, h3⟩ := key
    exact ⟨x', h3, fun β hβ _ => h2 β hβ⟩
  unfold LocalPointData.AA LocalPointData.AAp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, ⟨hx0, hb0⟩, rfl⟩ := hy
    refine ⟨x0, ⟨hx0, fun β hβ => ?_⟩, rfl⟩
    unfold LocalPointData.A0
    rw [mem_ballO_iff Q.c hU hC.2.2]
    intro ζ
    have h := hb0 β hβ ζ
    simpa [LocalPointData.ordA] using h
  | zero =>
    have hz : ∀ β : Idx D j G.N →₀ ℕ,
        hasse X la G.w β ((0 : ↥(HK X la G.w wF)) : Lw X la G.w) = 0 := fun β => by
      exact map_zero (hasse X la G.w β)
    refine ⟨0, ⟨fun β _ => by rw [hz]; exact (HK X la G.w wF).zero_mem, fun β hβ => ?_⟩, map_zero _⟩
    convert Q.A0.zero_mem using 1
    rw [← map_zero (toA0K X la G.w wF)]
    exact congrArg _ (Subtype.ext (hz β))
  | add a b _ _ ha hb =>
    obtain ⟨xa, ⟨ha1, ha2⟩, rfl⟩ := ha
    obtain ⟨xb, ⟨hb1, hb2⟩, rfl⟩ := hb
    have hs : ∀ β : Idx D j G.N →₀ ℕ, hasse X la G.w β ((xa + xb : ↥(HK X la G.w wF)) : Lw X la G.w) =
        hasse X la G.w β (xa : Lw X la G.w) + hasse X la G.w β (xb : Lw X la G.w) := fun β => by
      exact map_add (hasse X la G.w β) _ _
    refine ⟨xa + xb, ⟨fun β hβ => by rw [hs]; exact add_mem (ha1 β hβ) (hb1 β hβ), fun β hβ => ?_⟩, map_add _ _ _⟩
    convert Q.A0.add_mem (ha2 β hβ) (hb2 β hβ) using 1
    rw [← map_add]
    exact congrArg _ (Subtype.ext (hs β))
  | smul o y _ ih =>
    classical
    obtain ⟨x0, ⟨h1, h2⟩, rfl⟩ := ih
    let g : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun q =>
      if h : hasse X la G.w q.2 (x0 : Lw X la G.w) ∈ HK X la G.w wF then ⟨_, h⟩ else 0
    have hg' : ∀ q : (Idx D j G.N →₀ ℕ) × (Idx D j G.N →₀ ℕ), ∀ hq : (q.2.sum fun _ n => n) ≤ a0 D j T - 1,
        g q = ⟨_, h1 q.2 hq⟩ := fun q hq => dif_pos (h1 q.2 hq)
    let F : (Idx D j G.N →₀ ℕ) → ↥(HK X la G.w wF) := fun β =>
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, algebraMap (Op X la G.N) (Kp X la G.N) (hasseOp X la G.N q.1 o) • g q
    have he : ∀ β : Idx D j G.N →₀ ℕ, (β.sum fun _ n => n) ≤ a0 D j T - 1 →
        hasse X la G.w β ((algebraMap (Op X la G.N) (Kp X la G.N) o • x0 : ↥(HK X la G.w wF)) : Lw X la G.w) =
          ((F β : ↥(HK X la G.w wF)) : Lw X la G.w) := by
      intro β hβ
      rw [hasse_Op_smul, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Submodule.coe_smul_of_tower, hg' q ((sum_snd_le hq).trans hβ)]
      rfl
    refine ⟨algebraMap (Op X la G.N) (Kp X la G.N) o • x0, ⟨fun β hβ => ?_, fun β hβ => ?_⟩, ?_⟩
    · rw [he β hβ]
      exact Submodule.coe_mem _
    · have hm : toA0K X la G.w wF (F β) ∈ Q.A0 := by
        rw [map_sum]
        refine Q.A0.sum_mem fun q hq => ?_
        rw [LinearMap.map_smul_of_tower, algebraMap_smul, hg' q ((sum_snd_le hq).trans hβ)]
        exact Q.A0.smul_mem _ (h2 q.2 ((sum_snd_le hq).trans hβ))
      convert hm using 1
      exact congrArg _ (Subtype.ext (he β hβ))
    · rw [LinearMap.map_smul_of_tower]
      rfl

end PoleLengthBounds
