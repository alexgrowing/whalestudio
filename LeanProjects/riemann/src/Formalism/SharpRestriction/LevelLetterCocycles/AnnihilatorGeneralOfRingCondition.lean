import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.SharpRestriction.LevelLetterCocycles.KillerSecondTheoremHolds
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section CoreW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem cancel_unit_mul_uniformizer_pow {w : (LetA O n)ˣ} {k : ℕ} {a b : LetA O n}
    (h : (w : LetA O n) * letπ ^ k * a = (w : LetA O n) * letπ ^ k * b) : a = b := by
  unfold letπ at h
  have h' : (fun _ => PowerSeries.X) ^ k * a = (fun _ => PowerSeries.X) ^ k * b := by
    have := congrArg (fun x => (↑w⁻¹ : LetA O n) * x) h
    simpa [← mul_assoc, Units.inv_mul] using this
  funext i
  have hi := congrFun h' i
  simp only [Pi.mul_apply, Pi.pow_apply] at hi
  ext m
  have hm := congrArg (PowerSeries.coeff (m + k)) hi
  rwa [mul_comm, PowerSeries.coeff_mul_X_pow, mul_comm, PowerSeries.coeff_mul_X_pow] at hm

theorem pi0Core_of (W : LocWach PD LL O v n) (w : (LetA O n)ˣ) (k : ℕ) (h1 : W.π₀ ∈ W.AΔ)
    (h3 : W.π₀ = (w : LetA O n) * letπ ^ k) : Pi0LatticeCondition W := by
  intro g
  obtain ⟨t, ht⟩ := Formalism.MainNotions.LiftingTheory.gamma_X_eq W g
  obtain ⟨Uc, hUc⟩ : ∃ Uc : LetA O n,
      Uc = fun _ => PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t := ⟨_, rfl⟩
  have hπ : W.γA g letπ = letπ * Uc := by
    funext i
    rw [hUc]
    show W.γ₀ g PowerSeries.X = PowerSeries.X * (PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t)
    exact ht
  obtain ⟨u, hu⟩ : ∃ u : LetA O n, u = (↑w⁻¹ : LetA O n) * W.γA g (w : LetA O n) * Uc ^ k :=
    ⟨_, rfl⟩
  have heq : W.γA g W.π₀ = W.π₀ * u := by
    rw [h3, map_mul, map_pow, hπ, hu,
      show (↑w : LetA O n) * letπ ^ k * (↑w⁻¹ * W.γA g ↑w * Uc ^ k) =
        (↑w * ↑w⁻¹) * (W.γA g ↑w * (letπ * Uc) ^ k) by ring,
      Units.mul_inv, one_mul]
  refine ⟨u, ?_, heq⟩
  have hmem : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := h1
  show ∀ δ ∈ W.DelF, W.γA δ u = u
  intro δ hδ
  have e1 : W.γA δ (W.γA g W.π₀) = W.γA g W.π₀ := by
    rw [Formalism.MainNotions.LiftingTheory.gammaA_comm W δ g, hmem δ hδ]
  rw [heq, map_mul, hmem δ hδ, h3] at e1
  exact cancel_unit_mul_uniformizer_pow e1

end CoreW

theorem finrank_K0_eq_one_of_le_Kur {l : ℕ} [Fact l.Prime] {K : FinExt l} (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    Module.finrank ↥(K0 K) ↥K.1 = 1 := by
  unfold K0
  rw [finrank_eq_one_iff_of_nonzero' (1 : ↥K.1) one_ne_zero]
  intro x
  refine ⟨⟨(x : Om l), IntermediateField.mem_inf.mpr ⟨x.2, hK x.2⟩⟩, ?_⟩
  first
    | exact Subtype.ext (mul_one _)
    | exact Subtype.ext (by simp)
    | rfl

theorem ring_condition_uniformizer_polynomial (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL h.2.2) 1 (((D.loc l).PD K).p - 1) ((HW l).W K 1 LL h.2.2).π₀
      (fun _ => Polynomial.X + Polynomial.C ((((D.loc l).PD K).p : ℕ) : ↥(OL LL))) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h9W := h9 l K 1 LL h.2.2
  have hp := h9W _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL h.2.2))
  refine ((hp ?_ ?_).2.2 ?_).1
  · exact (HW l).W_s K 1 LL h.2.2
  · rw [(D.loc l).PD_p K]
    exact h.2.1
  · exact finrank_K0_eq_one_of_le_Kur h.1

theorem gamma_uniformizer_divisible_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : UniformiserGammaTheorem D HW F := by
  intro h9 l _ K LL h _
  obtain ⟨h1, -, ⟨w, hw⟩, -⟩ := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  exact pi0Core_of _ w _ h1 hw

end Formalism.MainNotions.UnusedSlot80
