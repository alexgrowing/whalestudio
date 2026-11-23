import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AevalDopMap

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

variable (W : LocWach PD LL O v n)

theorem step_ii (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) {T₁ T₂ : LocLat G Qp LL O}
    (hc₁ : IsCrys PD T₁.ρ)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL)) (F : LatHom T₁.L T₂.L) (i : ZMod n) (Ai ri : ℕ)
    (hA : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (W.π₀ ^ Ai)) (hr : Formalism.MainNotions.LiftingTheory.KillsΔ W F i (Formalism.MainNotions.LiftingTheory.lp W ri))
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (P : O[X])
    (hCONS : ∀ y : W.DD T₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (qA W ^ (Ai + ri) • y) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ P y))
    {x : W.DD T₂} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x) : InImg W F i (aeval dop₂ P x) := by
  have hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀) ∧ IsUnit (algebraMap (LetA O n) W.EE (qA W)) ∧
      IsUnit ((W.DelF.card : ℕ) : O) := by
    exact lemG_units W hcase hP9 hc₁ hO hOv hinj
  obtain ⟨hπ, hq, -⟩ := hU
  have hz : InImg W F i (qA W ^ (Ai + ri) • x) := by
    exact q_pow_inImg W hcase hP9 hc₁ hO hOv hinj F i Ai ri hA hr hx
  obtain ⟨z, hzN, hzx⟩ := hz
  set N := Ai + ri
  set e : W.EE := (↑hq.unit⁻¹ : W.EE) ^ N with he
  have key : algebraMap (LetA O n) W.EE (qA W ^ N) * e = 1 := by
    rw [he, map_pow, ← mul_pow, hq.mul_val_inv, one_pow]
  have hqy : qA W ^ N • (e • z) = z := by
    rw [← algebraMap_smul W.EE (qA W ^ N), smul_smul, key, one_smul]
  have hFy : W.map F (e • z) = x := by
    rw [LinearMap.map_smul, hzx, ← algebraMap_smul W.EE (qA W ^ N) x, smul_smul, mul_comm, key, one_smul]
  have hy : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (aeval dop₁ P (e • z)) := by
    apply hCONS
    rw [hqy]
    exact hzN
  exact ⟨aeval dop₁ P (e • z), hy, by rw [aeval_dop_map W hπ F dop₁ hd₁ dop₂ hd₂, hFy]⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
