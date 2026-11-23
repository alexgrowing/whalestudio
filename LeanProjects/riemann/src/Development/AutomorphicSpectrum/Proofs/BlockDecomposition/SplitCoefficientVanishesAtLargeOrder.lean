import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaBoundedIntegral
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexSupport

open ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem ord_nonneg_of_mem {x : F} (hx : x ≠ 0) (h : x ∈ 𝒪[F]) : 0 ≤ ord x := by
  have h0 := mem_valBall_iff_le_ord (n := 0) hx
  rw [mem_valBall_zero_iff] at h0
  exact h0.mp h

theorem ord_eq_zero_of_mem {u : Fˣ} (h₁ : (u : F) ∈ 𝒪[F]) (h₂ : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F]) :
    ord (u : F) = 0 := by
  have a := ord_nonneg_of_mem u.ne_zero h₁
  have b := ord_nonneg_of_mem (u⁻¹ : Fˣ).ne_zero h₂
  rw [ord_units_inv] at b
  omega

theorem exists_ord_lower [CharZero F] {S : Set F} (hS : IsCompact S) :
    ∃ A : ℤ, ∀ x ∈ S, x ≠ 0 → -A ≤ ord x := by
  obtain ⟨N, hN, H⟩ := GlobalTheory.CompanionTheory.ThetaBound.exists_nat_mul_mem hS
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  refine ⟨ord (N : F), fun x hx h0 => ?_⟩
  have := ord_nonneg_of_mem (mul_ne_zero hN' h0) (H x hx)
  rw [ord_mul hN' h0] at this
  omega

end Loc

end GlobalTheory.CompanionTheory.FexSupport

theorem GlobalTheory.CompanionTheory.FexSupport.fL_eq_zero : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ), ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v,
    fL L g (κ : K) (unifUnit (Qv v) ^ k * u) = 0 := by
  intro K _ _ h2 c v L hok hsp g κ
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨hne, hl, hc⟩ := hok
    haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
    have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
    have hχc := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
    have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
    have hf := (GlobalTheory.CompanionTheory.SplitPi.sPiRep (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) (cAt c v w₂)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₂) Φ ⟨hl, hc⟩ 1 g).2
    set f := GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g Φ with hfdef
    have hC : IsCompact (tsupport f) := hf.2
    obtain ⟨A₁, hA₁⟩ := GlobalTheory.CompanionTheory.FexSupport.exists_ord_lower (hC.image continuous_fst)
    obtain ⟨A₂, hA₂⟩ := GlobalTheory.CompanionTheory.FexSupport.exists_ord_lower (hC.image continuous_snd)
    obtain ⟨e₁, e₂, -⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have hκ : algebraMap K (Kv K w₁) (κ : K) ≠ 0 := (map_ne_zero _).2 κ.ne_zero
    have hκ' : algebraMap K (Kv K w₂) (κ : K) ≠ 0 := (map_ne_zero _).2 κ.ne_zero
    have hξ₁ : dg1 v w₁ (κ : K) ≠ 0 := fun h => hκ (by rw [← e₁, h, map_zero])
    have hξ₂ : dg1 v w₂ (κ : K) ≠ 0 := fun h => hκ' (by rw [← e₂, h, map_zero])
    refine ⟨(|A₁ + ord (dg1 v w₁ (κ : K))| + |A₂ + ord (dg1 v w₂ (κ : K))|).toNat, fun k hk u hu => ?_⟩
    set x : (Qv v)ˣ := unifUnit (Qv v) ^ k * u with hx
    have hu0 : ord (u : Qv v) = 0 := GlobalTheory.CompanionTheory.FexSupport.ord_eq_zero_of_mem hu.1 hu.2
    have ox : ord (x : Qv v) = k := by
      rw [hx, ord_units_mul, ord_unifUnit_zpow, hu0, add_zero]
    have ox' : ord ((x⁻¹ : (Qv v)ˣ) : Qv v) = -k := by rw [ord_units_inv, ox]
    have hval : (LM.tw (LM.sp w₁ w₂ Φ) x).val g (κ : K) =
        f ((dg1 v w₁ (κ : K), dg1 v w₂ (κ : K)) * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) :=
      GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) g Φ x _
    have hz : f ((dg1 v w₁ (κ : K), dg1 v w₂ (κ : K)) * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) = 0 := by
      by_contra hnz
      have hs := subset_tsupport f hnz
      have a₁ : -A₁ ≤ ord (dg1 v w₁ (κ : K) * (x : Qv v)) := hA₁ _ ⟨_, hs, rfl⟩ (mul_ne_zero hξ₁ x.ne_zero)
      have a₂ : -A₂ ≤ ord (dg1 v w₂ (κ : K) * ((x⁻¹ : (Qv v)ˣ) : Qv v)) :=
        hA₂ _ ⟨_, hs, rfl⟩ (mul_ne_zero hξ₂ (x⁻¹ : (Qv v)ˣ).ne_zero)
      rw [ord_mul hξ₁ x.ne_zero, ox] at a₁
      rw [ord_mul hξ₂ (x⁻¹ : (Qv v)ˣ).ne_zero, ox'] at a₂
      have b₁ := le_abs_self (A₁ + ord (dg1 v w₁ (κ : K)))
      have b₂ := neg_abs_le (A₁ + ord (dg1 v w₁ (κ : K)))
      have b₃ := le_abs_self (A₂ + ord (dg1 v w₂ (κ : K)))
      have b₄ := neg_abs_le (A₂ + ord (dg1 v w₂ (κ : K)))
      have hk' := lt_of_le_of_lt (Int.self_le_toNat _) hk
      rcases abs_cases k with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    simp only [fL]
    rw [hval, hz, mul_zero]
