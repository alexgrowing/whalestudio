import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_letter_type_eq_ite [NeZero n] {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ} (i : ZMod n) :
    (arcOf b w S η up size).ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i) :=
  rfl

theorem arc_length_two_reduction [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂)
    (hArc : ArcCore W)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hFL : ArcFilLowCore W)
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK)
    (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false)
    {d₁ : ℕ} (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL)
    (hb₁ : IsHor W T₁ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) b₁ sol₁) (c₁ : Fin d₁ → O)
    (hlt : dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁ ∈ FilS W T₁ c 1 (size (c - 1)))
    (hpr : Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ ((arcOf b w S η up size).len c) b₁ c₁) =
      ((PD.p : LL) ^ (2 * (arcOf b w S η up size).σ PD.p)) •
        dv W T₂ ((arcOf b w S η up size).len c) bb (Pi.single k₀ 1)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 9 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  set A := arcOf b w S η up size with hA
  have hup1 : up (c - 1) = true := by
    cases h : up (c - 1) <;> simp_all
  have hty0 : A.ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    rw [hA, arc_letter_type_eq_ite, hup]; rfl
  have hty1 : A.ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    rw [hA, arc_letter_type_eq_ite, hup1]; rfl
  have hl5 : 5 ≤ PD.p := by have := hB.1; omega
  have hcase : Formalism.MainNotions.LiftingTheory.CaseA W := hB.2.1.1
  have hthick : ∀ s < A.len c, (A.ty (c - (s : ZMod n))).thick := by
    intro s _
    rw [hA, arc_letter_type_eq_ite]
    split_ifs <;> rfl
  have hden : nnDen W A c = ps W 1 ^ size (c - 1) := by
    simp only [nnDen, prodTy, hlen, Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      sub_zero, Nat.cast_one, hty0, hty1, pow_zero, one_mul]
  obtain ⟨hf1, hf2⟩ := hf
  have hL := liftsAt_thin_letter_type W A F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj hArc
    hW₁ hW₂ hbb ({1} : Finset ℕ) (by
      intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      refine ⟨by omega, size (c - 1), ?_⟩
      rw [Nat.cast_one, hty1]) b₁ sol₁ hb₁ c₁ (2 * A.σ PD.p) (by
      intro s hs bs hbs
      rw [Finset.mem_singleton] at hs
      subst hs
      rw [Nat.cast_one, hty1] at hbs
      cases hbs
      exact hlt) hpr f (by
      simpa [Nat.cast_one, hty1, ← hden] using hf1) (by
      intro s hs bs hbs
      obtain ⟨κ, x, hx⟩ := hf2 s hs bs hbs
      refine ⟨κ, x, ?_⟩
      simpa [Nat.cast_one, hty1, ← hden] using hx) (by
      intro s hs hs1 bs hbs
      have hs0 : s = 0 := by
        rw [Finset.mem_singleton] at hs1
        omega
      subst hs0
      rw [Nat.cast_zero, sub_zero, hty0] at hbs
      cases hbs)
  refine ⟨2 * A.σ PD.p + A.σ PD.p, ?_, hL⟩
  push_cast
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
