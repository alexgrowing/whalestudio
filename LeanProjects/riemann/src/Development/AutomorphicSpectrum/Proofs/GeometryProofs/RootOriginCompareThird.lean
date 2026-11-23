import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogX
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.ALine

section Cross

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Cmp

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω]

theorem cross_mem (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) :
    (X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) +
        -(X (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) : MRing (joinIdx ι₁ ι₂)) ∈
      mCoordIdeal (joinVec y₁ y₂) := by
  classical
  have hl : ∀ a : ι₁ k₁, IsMultiHomog (X (joinInl ι₁ ι₂ ⟨k₁, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inl k₁) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a
  have hr : ∀ a : ι₂ k₂, IsMultiHomog (X (joinInr ι₁ ι₂ ⟨k₂, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inr k₂) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a
  refine Small.LineModel.mem_of_aeval _
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhAdd (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl a₁) (hr b₂))
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhNeg (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl b₁) (hr a₂)))) ?_
  simp only [map_add, map_neg, map_mul, aeval_X]
  show y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ + -(y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) = 0
  rw [h]; ring

theorem cross_eq (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) =
      z (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) := by
  have h0 := hz.2 _ (cross_mem y₁ y₂ a₁ b₁ a₂ b₂ h)
  simp only [map_add, map_neg, map_mul, aeval_X] at h0
  linear_combination h0

theorem hasVal_one (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ : ι₁ k₁) (a₂ : ι₂ k₂) (h : y₁ ⟨k₁, a₁⟩ = y₂ ⟨k₂, a₂⟩)
    (d : K₁ ⊕ K₂ → ℤ) (hd₁ : d (Sum.inl k₁) = 1) (hd₂ : d (Sum.inr k₂) = -1)
    (hd : ∀ k, k ≠ Sum.inl k₁ → k ≠ Sum.inr k₂ → d k = 0)
    {L : Type} [Field L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L)
    (hz : z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) ≠ 0) :
    Small.HasVal (joinVec y₁ y₂) d 1 z
      (z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) / z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) := by
  classical
  refine ⟨Pi.single (Sum.inl k₁) 1, Pi.single (Sum.inr k₂) 1, X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩),
    X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩), ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a₁,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a₂, fun k => ?_, ?_, ?_, ?_⟩
  · by_cases e₁ : k = Sum.inl k₁
    · subst e₁; simp [hd₁]
    · by_cases e₂ : k = Sum.inr k₂
      · subst e₂; simp [hd₂]
      · simp [hd k e₁ e₂, e₁, e₂]
  · simp only [aeval_X, one_mul]
    exact h
  · simpa only [aeval_X] using hz
  · simp only [aeval_X]
    field_simp

end Cross

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), ∀ v : ℂ, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 w v → M.A.h (fun p => w (Cmp.joinInl M.ι R.ι p)) = ‖v‖ * R.A.h (fun p => w (Cmp.joinInr M.ι R.ι p)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi
  classical
  have hy : ∀ a, M.y ⟨o.k₀, o.ix a⟩ = i (R.y ⟨o₀.k₀, o₀.ix a⟩) := fun a => by
    rw [o.y_eq, o₀.y_eq, ← hi]; rfl
  have hd₁ : Ht.joinDeg M R none (Sum.inl o.k₀) = 1 := o.A_deg.1
  have hd₂ : Ht.joinDeg M R none (Sum.inr o₀.k₀) = -1 := by
    show -(R.A.a o₀.k₀) = -1
    rw [o₀.A_deg.1]
  have hd : ∀ k, k ≠ Sum.inl o.k₀ → k ≠ Sum.inr o₀.k₀ → Ht.joinDeg M R none k = 0 := by
    rintro (k | k) h₁ h₂
    · exact o.A_deg.2 k fun e => h₁ (congrArg _ e)
    · show -(R.A.a k) = 0
      rw [o₀.A_deg.2 k fun e => h₂ (congrArg _ e), neg_zero]
  have hval : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L) (a : Fin (Fx.m + 1)),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 →
      Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 z
        (z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) / z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩)) :=
    fun L _ z a hz => hasVal_one M.y (fun p => i (R.y p)) (o.ix a) (o₀.ix a) (hy a) _ hd₁ hd₂ hd z hz
  have hcr : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a b : Fin (Fx.m + 1),
      z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) =
        z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) :=
    fun L _ z hz a b => cross_eq M.y (fun p => i (R.y p)) (o.ix a) (o.ix b) (o₀.ix a) (o₀.ix b) (by
      show M.y _ * i (R.y _) = M.y _ * i (R.y _)
      rw [hy a, hy b, mul_comm]) hz
  have hexR : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inr o₀.k₀)
    have e : o₀.ix (o₀.ix.symm p) = p := o₀.ix.apply_symm_apply p
    exact ⟨o₀.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : R.ι o₀.k₀ => z ⟨Sum.inr o₀.k₀, x⟩) e.symm).trans h0)⟩
  have hexM : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inl o.k₀)
    have e : o.ix (o.ix.symm p) = p := o.ix.apply_symm_apply p
    exact ⟨o.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : M.ι o.k₀ => z ⟨Sum.inl o.k₀, x⟩) e.symm).trans h0)⟩
  have hne : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a : Fin (Fx.m + 1),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 → z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz a ha h0
    obtain ⟨b, hb⟩ := hexM L z hz
    have h1 := hcr L z hz b a
    rw [h0, zero_mul] at h1
    exact mul_ne_zero hb ha h1
  refine ⟨fun L _ _ z hz => ?_, fun w hw v hv => ?_⟩
  · obtain ⟨a, ha⟩ := hexR L z hz
    exact ⟨_, div_ne_zero (hne L z hz a ha) ha, hval L z a ha⟩
  · obtain ⟨a, ha⟩ := hexR ℂ w hw
    have hv' := Small.LineModel.hasVal_unique _ _ _ hw hv (hval ℂ w a ha)
    have hvne : v ≠ 0 := hv' ▸ div_ne_zero (hne ℂ w hw a ha) ha
    have hblock : ∀ b : Fin (Fx.m + 1), w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) =
        v * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) := by
      intro b
      rw [hv', div_mul_eq_mul_div, eq_div_iff ha]
      exact hcr ℂ w hw b a
    obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at h1 h2
    let c : R.K → ℂ := fun k => if k = o₀.k₀ then v else 1
    have hc : ∀ k, c k ≠ 0 := by
      intro k
      by_cases hk : k = o₀.k₀
      · simpa [c, hk] using hvne
      · simp [c, hk]
    have e1 := o.A_h _ h1
    have e2 := o₀.A_h _ (mcPts_smul R.arith.2.1.2.1 c hc h2)
    have e3 := R.A.smul c (fun p => w (Cmp.joinInr M.ι R.ι p)) hc
    have e4 : (∏ k, ‖c k‖ ^ R.A.a k) = ‖v‖ := by
      rw [Finset.prod_eq_single o₀.k₀]
      · simp [c, o₀.A_deg.1]
      · intro k _ hk
        simp [c, hk, o₀.A_deg.2 k hk]
      · simp
    rw [e1, ← e4, ← e3, e2]
    congr 1
    funext b
    simpa [c] using hblock b

end GlobalTheory.CompanionTheory.Ar.Ht.ALine
