import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AevalDopMap
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoefStep

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

variable (W : LocWach PD LL O v n)

theorem γA_comm_GG (g h : W.Gam) (a : LetA O n) : W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  funext k
  unfold LocWach.γA letγ
  change W.γ₀ g (W.γ₀ h (a k)) = W.γ₀ h (W.γ₀ g (a k))
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]

theorem γA_memAΔ_GG {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA W.gam a ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ (W.γA W.gam a) = W.γA W.gam a
  intro δ hδ
  rw [γA_comm_GG W, ha δ hδ]

theorem step_one_GG (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (i : ZMod n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : IsCrys PD T₁.ρ)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (Ai ri : ℕ) (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))
    (bi : ℕ)
    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))
    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))
    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hl0 : ((PD.p : ℕ) : O) ≠ 0) (hinj : Function.Injective (algebraMap O LL))
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)
    (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (lam : W.DD T₂)
    (hH2 : ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ (Ai + ri)) • y)
    (j : ℕ) (hj : j ≤ bi) (g : LetA O n) (hg : g ∈ W.AΔ) :
    ∃ h ∈ W.AΔ, InImg W F i (dop₂ ((qA W ^ j * g) • (s • lam)) -
      cc ((bi : ℤ) - j) • ((qA W ^ j * g) • (s • lam)) - (qA W ^ (j + 1) * h) • (s • lam)) := by
  obtain ⟨hπ, -, -⟩ := lemG_units W hcase hP9 hc₁ hO hOv hinj
  obtain ⟨h, hh, hcoef⟩ := coef_step W hcase hP9 hc₁ hgpi0 hA3 hA4 hl0 hinj cc hcc bi s s' hs' hs j hj g hg
  obtain ⟨y, hy, hyeq⟩ := hH2
  set f := qA W ^ j * g with hf
  set c := cc ((bi : ℤ) - j) with hcdef
  have hfΔ : f ∈ W.AΔ := mul_mem (pow_mem (qA_mem_AΔ W hcase hP9 hc₁).2 j) hg
  have hγf : W.γA W.gam f ∈ W.AΔ := γA_memAΔ_GG W hfΔ
  refine ⟨h, hh, ?_⟩
  set E := algebraMap (LetA O n) W.EE with hE
  have hfx : f • (s • lam) = (E f * s) • lam := by
    rw [← smul_assoc, Algebra.smul_def]
  have hγE : W.γE W.gam (E f * s) = E (W.γA W.gam f) * W.γE W.gam s := by
    rw [map_mul, hE, W.γE_ext]; rfl
  have key : W.γ T₂ (f • (s • lam)) - f • (s • lam) =
      W.π₀ • (c • (f • (s • lam)) + (qA W ^ (j + 1) * h) • (s • lam) +
        qA W ^ (Ai + ri) • (W.γA W.gam f • y)) := by
    have h1 : W.γ T₂ (f • (s • lam)) - f • (s • lam) =
        W.γE W.gam (E f * s) • (W.γ T₂ lam - lam) + (W.γE W.gam (E f * s) - E f * s) • lam := by
      rw [hfx]
      change W.γD T₂ W.gam ((E f * s) • lam) - _ = _
      rw [W.γD_smul, smul_sub, sub_smul]
      change _ = W.γE W.gam (E f * s) • W.γD T₂ W.gam lam - _ + _
      abel
    rw [h1, hcoef, hγE, mul_smul, hyeq, mul_smul (E _) s lam, hE, algebraMap_smul, algebraMap_smul]
    rw [← algebraMap_smul (LetA O n) c (f • (s • lam))]
    have e1 : W.π₀ * qA W ^ j * (algebraMap O (LetA O n) c * g + qA W * h) =
        W.π₀ * (algebraMap O (LetA O n) c * f) + W.π₀ * (qA W ^ (j + 1) * h) := by
      rw [hf]; ring
    have e2 : W.γA W.gam f * (W.π₀ * qA W ^ (Ai + ri)) = W.π₀ * (qA W ^ (Ai + ri) * W.γA W.gam f) := by
      ring
    simp only [smul_add, smul_smul]
    rw [e1, e2, add_smul]
    abel
  have hd := dop_eq W hπ T₂ dop₂ hd₂ key
  rw [hd]
  have himg : InImg W F i (qA W ^ (Ai + ri) • (W.γA W.gam f • y)) :=
    q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr (inNΔi_smulA W T₂ i hγf hy)
  convert himg using 1
  abel

theorem step_i (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (i : ZMod n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : IsCrys PD T₁.ρ)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (Ai ri : ℕ) (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))
    (bi : ℕ) (hab : Ai + ri ≤ bi)
    (hgpi0 : ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W))
    (hA3 : ∀ k ≥ 1, ∃ g ∈ W.AΔ, W.γA W.gam (ps W k) = ps W k * (1 + W.π₀ * qA W * g))
    (hA4 : ∃ g ∈ W.AΔ, W.γA W.gam (qA W) = ((W.χΓ W.gam : Oˣ) : O) • qA W + qA W ^ 2 * g)
    (hl0 : ((PD.p : ℕ) : O) ≠ 0) (hinj : Function.Injective (algebraMap O LL))
    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    (hgN₂ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧ W.γ T₂ x - x = W.π₀ • y)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (cc : ℤ → O) (hcc : ∀ m : ℤ, (-((PD.p : ℕ) : O)) * cc m = (((W.χΓ W.gam) ^ (-m) : Oˣ) : O) - 1)
    (s : W.EE) (s' : LetA O n) (hs' : s' ∈ Submonoid.closure {x | ∃ k ≥ 1, x = ps W k})
    (hs : algebraMap (LetA O n) W.EE (qA W ^ bi) * s = algebraMap (LetA O n) W.EE s')
    (lam : W.DD T₂)
    (hH1 : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (s • lam))
    (hH2 : ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ (Ai + ri)) • y) :
    InImg W F i (aeval dop₂ (∏ j ∈ Finset.range (Ai + ri), (X - C (cc ((bi : ℤ) - j)))) (s • lam)) := by
  obtain ⟨hπ, -, -⟩ := lemG_units W hcase hP9 hc₁ hO hOv hinj
  have main : ∀ k ≤ Ai + ri, ∃ g ∈ W.AΔ, InImg W F i
      (aeval dop₂ (∏ j ∈ Finset.range k, (X - C (cc ((bi : ℤ) - j)))) (s • lam) -
        (qA W ^ k * g) • (s • lam)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨1, one_mem _, ?_⟩
      simpa using inImg_zero W F i
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, himg⟩ := ih (by omega)
      obtain ⟨h, hh, hstep⟩ := step_one_GG W hcase hP9 i F hc₁ hO hOv Ai ri hA hr bi hgpi0 hA3 hA4 hl0 hinj
        dop₂ hd₂ cc hcc s s' hs' hs lam hH2 k (by omega) g hg
      refine ⟨h, hh, ?_⟩
      have himg2 := aeval_inImg W hπ F i dop₁ hd₁ dop₂ hd₂ hgN₁ (X - C (cc ((bi : ℤ) - k))) himg
      rw [Finset.prod_range_succ, mul_comm, map_mul, Module.End.mul_apply]
      set z := aeval dop₂ (∏ j ∈ Finset.range k, (X - C (cc ((bi : ℤ) - j)))) (s • lam)
      have hX : ∀ w : W.DD T₂, aeval dop₂ (X - C (cc ((bi : ℤ) - k))) w = dop₂ w - cc ((bi : ℤ) - k) • w := by
        intro w
        simp [Module.algebraMap_end_apply]
      rw [hX] at himg2 ⊢
      have e := inImg_add W F i hstep himg2
      convert e using 1
      simp only [map_sub, smul_sub]
      abel
  obtain ⟨g, hg, himg⟩ := main (Ai + ri) le_rfl
  have hq := q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr (inNΔi_smulA W T₂ i hg hH1)
  have e := inImg_add W F i himg hq
  convert e using 1
  rw [mul_smul]
  abel

end Formalism.MainNotions.N.FrobeniusPowerSeries
