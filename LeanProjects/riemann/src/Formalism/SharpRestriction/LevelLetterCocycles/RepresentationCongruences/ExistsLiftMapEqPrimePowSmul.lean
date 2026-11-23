import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SmulEqZeroOfAevalProd
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LeValOneAddPowSub
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.StepIi
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.StepOneGG

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem existsLiftMapEqPrimePowSmul (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (i : ZMod n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ)

    (Ai ri : ℕ) (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))

    (bi S η : ℕ) (hU : Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T₁ i ((Set.Icc (bi : ℤ) (bi + S)) ∪ Set.Icc (-(η : ℤ)) η))
    (hb : 2 * (Ai + ri) + η + 1 ≤ bi)

    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))

    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))

    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hl0 : ((PD.p : ℕ) : O) ≠ 0)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))

    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    (hgN₂ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧ W.γ T₂ x - x = W.π₀ • y)

    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)

    (hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ (TruncatedCoefficientPoly cc bi S η (Ai + ri)) y))

    (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (lam : W.DD T₂)

    (hH1 : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (s • lam))
    (hH2 : ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ (Ai + ri)) • y) :
    ∃ x₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x₁ ∧
      W.map F x₁ = (((PD.p : ℕ) : LetA O n) ^ EG PD.p (Ai + ri) S η bi) • (s • lam) := by
  classical
  have : Fact (PD.p).Prime := ⟨PD.hp⟩
  have : IsDomain O := Function.Injective.isDomain (algebraMap O LL) hinj
  obtain ⟨hπ, -, -⟩ := lemG_units W hcase hP9 hc₁ hO hOv hinj

  have hdM : imgSub W F i ≤ (imgSub W F i).comap dop₂ := fun z hz =>
    dop_inImg W hπ F i dop₁ hd₁ dop₂ hd₂ hgN₁ hz
  have hpow : ∀ (k : ℕ) (z : W.DD T₂), (((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) ^ k)
      ((imgSub W F i).mkQ z) = (imgSub W F i).mkQ ((dop₂ ^ k) z) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        show ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) ((imgSub W F i).mkQ z) =
          (imgSub W F i).mkQ (dop₂ z) from rfl, ih]
  have haev : ∀ (p : O[X]) (z : W.DD T₂),
      aeval ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) p ((imgSub W F i).mkQ z) =
        (imgSub W F i).mkQ (aeval dop₂ p z) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => intro z; rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq, map_add]
    | monomial k c =>
      intro z
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, hpow,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

  suffices hmain : InImg W F i ((((PD.p : ℕ) : O) ^ EG PD.p (Ai + ri) S η bi) • (s • lam)) by
    obtain ⟨x₁, h1, h2⟩ := hmain
    refine ⟨x₁, h1, ?_⟩
    rw [h2, ← algebraMap_smul (LetA O n), map_pow, map_natCast]
  rcases Nat.eq_zero_or_pos (Ai + ri) with ha0 | ha
  · have h := q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr hH1
    rw [ha0, pow_zero, one_smul] at h
    exact inImg_smulO W F i _ h
  · have h₁ := step_i W hcase hP9 i F hc₁ hO hOv Ai ri hA hr bi (by omega) hgpi0 hA3 hA4 hl0 hinj hgN₁ hgN₂
      dop₁ hd₁ dop₂ hd₂ cc hcc s s' hs' hs lam hH1 hH2
    have h₂ := step_ii W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr dop₁ hd₁ dop₂ hd₂ (TruncatedCoefficientPoly cc bi S η (Ai + ri)) hCONS hH1
    have hu : v (algebraMap O LL ((W.χΓ W.gam : Oˣ) : O) - 1) = 1 := by
      rw [W.gam_gen, hcase.2.1, Nat.cast_one]
    have hcA := cc_assoc v PD.p hcase.2.2 W.v_l hO hOv hinj (W.χΓ W.gam) hu cc hcc
    have hS₂ : TruncationIndexSet bi S η (Ai + ri) ⊆
        Finset.Icc ((bi : ℤ) + 1) ((bi : ℤ) + S + (Ai + ri : ℕ)) ∪
          Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + (Ai + ri : ℕ)) := by
      intro y hy
      simp only [TruncationIndexSet, winU, Finset.mem_image, Finset.mem_product, Finset.mem_union, Finset.mem_Icc] at hy
      obtain ⟨⟨u, j⟩, ⟨hu | hu, hj⟩, rfl⟩ := hy
      · simp only [Finset.mem_union, Finset.mem_Icc]; left; push_cast; omega
      · simp only [Finset.mem_union, Finset.mem_Icc]; right; push_cast; omega
    have hE : ⌊(((3 * (Ai + ri) + S + 2 * η : ℕ) : ℝ) - 2) / ((PD.p : ℝ) - 1) +
        Real.logb PD.p ((bi : ℝ) + η - 1)⌋₊ ≤ EG PD.p (Ai + ri) S η bi := by
      unfold EG; push_cast; exact le_rfl
    have key := lemmaG_lagr PD.p ((imgSub W F i).mapQ (imgSub W F i) dop₂ hdM) cc hl0 hcA
      (Ai + ri) S η bi (EG PD.p (Ai + ri) S η bi) ha hb (TruncationIndexSet bi S η (Ai + ri)) hS₂
      ((imgSub W F i).mkQ (s • lam))
      (by rw [haev]; exact (Submodule.Quotient.mk_eq_zero _).2 h₁)
      (by rw [haev]; exact (Submodule.Quotient.mk_eq_zero _).2 h₂) hE
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at key
    exact key

end Formalism.MainNotions.N.FrobeniusPowerSeries
