import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

attribute [-instance] UpperTheory.V.Z.Sym.Glob.rpMul UpperTheory.V.Z.Sym.Glob.rpInv

theorem UpperTheory.V.Z.Sym.Dict.Br.integral_congr_of_forall_above :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), ∀ (y : DA B.Δ) (m₀ : ℕ), m₀ ≠ 0 → ∃ m : ℕ, m ≠ 0 ∧ ∀ (g : SA B.Δ) (v : Pl (Lp L)), (∀ w, un w = v → ∀ i j, ∃ a ∈ w.adicCompletionIntegers L, (mL w (B.bS g : UA L 2) - 1) i j = (m : Kw w) * a) → ∀ i j, ∃ a, IsIntegral (Ov v) a ∧ (mt ((y⁻¹ * g * y : DA B.Δ).1 v) - 1) i j = (m₀ : Lsq (Kv v) (cv v B.Δ)) * a := by
  intro L _ _ _ B y m₀ hm₀
  obtain ⟨N₁, hN₁, h₁⟩ := den_DA y
  obtain ⟨N₂, hN₂, h₂⟩ := den_DA y⁻¹
  have hm : m₀ * (N₁ * N₂) ≠ 0 := mul_ne_zero hm₀ (mul_ne_zero hN₁ hN₂)
  refine ⟨m₀ * (N₁ * N₂), hm, fun g v hg i j => ?_⟩
  generalize hmm : m₀ * (N₁ * N₂) = m at hm hg
  haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap (Lp L) (Kv v)).injective
  have hmK : (m : Kv v) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinv : (m : Lsq (Kv v) (cv v B.Δ)) * algebraMap (Kv v) (Lsq (Kv v) (cv v B.Δ)) (m : Kv v)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap (Kv v) (Lsq (Kv v) (cv v B.Δ))), ← map_mul, mul_inv_cancel₀ hmK, map_one]
  have hE : ∀ k l, ∃ b, IsIntegral (Ov v) b ∧
      (mt ((g : DA B.Δ).1 v) - 1) k l = (m : Lsq (Kv v) (cv v B.Δ)) * b := by
    intro k l
    refine ⟨algebraMap (Kv v) _ (m : Kv v)⁻¹ * (mt ((g : DA B.Δ).1 v) - 1) k l, ?_, ?_⟩
    · refine (B.ρ_int v _).2 fun w h => ?_
      subst h
      obtain ⟨a, ha, e⟩ := hg w rfl k l
      rw [B.bS_loc] at e
      have e2 : B.ρ _ w rfl ((mt ((g : DA B.Δ).1 (un w)) - 1) k l) = (m : Kw w) * a := by
        rw [← e]
        simp [Matrix.sub_apply, Matrix.one_apply, apply_ite (B.ρ _ w rfl)]
      have e3 : B.ρ _ w rfl (algebraMap (Kv (un w)) _ (m : Kv (un w))⁻¹) * (m : Kw w) = 1 := by
        rw [← map_natCast (B.ρ _ w rfl), ← map_mul, mul_comm, hinv, map_one]
      rw [map_mul, e2, ← mul_assoc, e3, one_mul]
      exact ha
    · rw [← mul_assoc, hinv, one_mul]
  choose E hE hE' using hE
  have hAB : mt ((y⁻¹ : DA B.Δ).1 v) * mt (y.1 v) = 1 := by
    have h : (y⁻¹ : DA B.Δ).1 v * y.1 v = 1 := inv_mul_cancel (y.1 v)
    exact congrArg Glob.mt h
  have hprod : mt ((y⁻¹ * g * y : DA B.Δ).1 v) = mt ((y⁻¹ : DA B.Δ).1 v) * mt ((g : DA B.Δ).1 v) * mt (y.1 v) := rfl
  refine ⟨∑ k, ∑ l, ((N₂ : Lsq (Kv v) (cv v B.Δ)) * mt ((y⁻¹ : DA B.Δ).1 v) i k) * E k l * ((N₁ : Lsq (Kv v) (cv v B.Δ)) * mt (y.1 v) l j),
    IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun l _ => ((h₂ v i k).mul (hE k l)).mul (h₁ v l j), ?_⟩
  have hsub : mt ((y⁻¹ * g * y : DA B.Δ).1 v) - 1 = mt ((y⁻¹ : DA B.Δ).1 v) * (mt ((g : DA B.Δ).1 v) - 1) * mt (y.1 v) := by
    rw [hprod, mul_sub, sub_mul, mul_one, hAB]
  rw [hsub]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hE', ← hmm]
  push_cast
  ring
