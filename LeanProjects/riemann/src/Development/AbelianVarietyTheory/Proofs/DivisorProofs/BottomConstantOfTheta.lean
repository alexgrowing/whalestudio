import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantNormalizedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationProportionalityRatioLeBottomPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraRest

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.BotConstPf

theorem gBig_imp {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | (apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem ..)

theorem lamC_div_norm {p : ℕ} [Fact p.Prime] {u₁ u₂ : ℂ} (h₁ : u₁ ∈ Qbar) (h₂ : u₂ ∈ Qbar)
    (n₁ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₁‖ = 1) (n₂ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₂‖ = 1) :
    u₁ / u₂ ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (u₁ / u₂)‖ = 1 := by
  have h3 : u₁ / u₂ ∈ Qbar := div_mem h₁ h₂
  refine ⟨h3, fun lam => ?_⟩
  have e : (⟨u₁ / u₂, h3⟩ : Qbar) = ⟨u₁, h₁⟩ / ⟨u₂, h₂⟩ := rfl
  have a := n₁ lam
  have b := n₂ lam
  rw [lamC, dif_pos h₁] at a
  rw [lamC, dif_pos h₂] at b
  rw [lamC, dif_pos h3, e, map_div₀, norm_div, a, b, div_one]

end GlobalTheory.SqTop.BotConstPf

namespace GlobalTheory.SqTop

open BotConstPf

theorem botConst_of_inputs : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  intro hPr hK hM hInp hS hL
  refine gBig_imp (Model.gBig_and (Model.gBig_and (GlobalTheory.T.bottom_triangle_constant_at hPr hK hM hInp hS hL) (GlobalTheory.T.bottom_triangle_constant_normalized hPr hK hM hInp hS)) hS) ?_
  intro D T Lc sc G μ₀ C x b hμ H
  obtain ⟨⟨H1, H2⟩, hGood, htw, hSm⟩ := H
  intro W S hψ hN i j t A A' WW X c0 δ t0 P₀ P₀' P P' z z' C' dl hX hc hB₀ hB hz hz' hz0 hz'0 hI
  obtain ⟨hct, hc0, γ, hγ⟩ := H1 W S hψ hN i j t A A' WW X c0 hX hc
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hγ
    exact hct hγ.symm
  refine ⟨γ, hγ0, hc0, hγ, fun w hw => ?_⟩
  obtain ⟨κ, hκ, H⟩ := H2 W S hψ hN i j A A' WW X c0 δ t0 hX hc
  obtain ⟨-, hQn1, hmod⟩ := Model.base_tuple G hμ
  obtain ⟨u₁, M, M', hu₁, hu₁q, hu₁n, hr₁⟩ := H t _ P P' hB
  obtain ⟨u₂, N₁, N₂, hu₂, hu₂q, hu₂n, hr₂⟩ := H μ₀ _ P₀ P₀' (hmod ▸ hB₀)
  obtain ⟨S', del, hE, hCo, -, rfl⟩ := hI
  obtain ⟨p, hp, hpw⟩ := exists_prime_under w
  haveI : Fact p.Prime := ⟨hp⟩
  have hpQ : ¬ p ∣ Qn G t := fun hd => hw (by
    obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpw)
  have hp1 : ¬ p ∣ Qn G μ₀ := by rw [hQn1]; exact hp.not_dvd_one
  obtain ⟨hv, hvn⟩ := lamC_div_norm hu₁q hu₂q (hu₁n p hpQ) (hu₂n p hp1)
  have hlev : padicValNat p (levQ G.pl * Qn G t) ≤ padicValNat p (levQ G.pl) := by
    have h0 : levQ G.pl ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ =>
      pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    rw [padicValNat.mul h0 (Model.Qn_ne_zero G t), padicValNat.eq_zero_of_not_dvd hpQ, add_zero]
  have e1 := hB.rank
  have e2 := hB₀.rank
  have s1 := hSm δ t0 _ P P' t i j _ hB
  have s2 := hSm δ t0 _ P₀ P₀' μ₀ i j _ hB₀
  refine GlobalTheory.T.valuation_proportionalityRatio_le_bottomPairs D (bigN D) (maxWt D sc.cGap) (levQ G.pl) S' del _ (hInp D) hE hCo D.what₂.LL D.what₂.embLL w p hpw δ t0
    (levQ G.pl * Qn G t) (levQ G.pl) hlev le_rfl P P' P₀ P₀' s1.1 s1.2 s2.1 s2.2 e1.2.2.2 e2.2.2.2
    (κ * u₁ * c0 t) (κ * u₂ * c0 μ₀) (u₁ / u₂) M N₂ (fun h T => (hr₁ e1.2.2.2 h).1 T)
    (fun h T' => (hr₂ e2.2.2.2 h).2 T') (mul_ne_zero (mul_ne_zero hκ hu₂) hc0) hv hvn γ z z' ?_ hz hz' hz0 hz'0
  rw [← hγ]
  field_simp

end GlobalTheory.SqTop

end
