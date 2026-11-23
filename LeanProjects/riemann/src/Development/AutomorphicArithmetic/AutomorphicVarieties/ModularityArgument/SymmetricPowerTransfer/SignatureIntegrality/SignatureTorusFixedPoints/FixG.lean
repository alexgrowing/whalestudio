import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.DiagDC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ConjDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem sDom_of_valuation_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : kˣ) (h1 : valuation k (a : k) < 1) : SDom ![a, 1, a⁻¹] := by
  have hne : valuation k (a : k) ≠ 0 := ((valuation k).ne_zero_iff).mpr a.ne_zero
  have h2 : 1 < (valuation k (a : k))⁻¹ :=
    (one_lt_inv₀ (((valuation k).pos_iff).mpr a.ne_zero)).mpr h1
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact h1
  · exact h1.trans h2
  · exact h2

theorem UpperTheory.V.Z.Sym.Sig.fixG : UpperTheory.V.Z.Sym.Sig.FixG := by
  intro k _ _ _ _ V d hd x₁ y₁ z₁ hxz y
  have hF := thFacts k V
  have hth : ∀ g, th k 3 g = (Phi k)⁻¹ * th' k g * Phi k := fun g => by
    rw [mul_assoc, hF.2.2.2.2.2.2 g]
    group
  have hdom : Dom d := fun i j hij => by
    rcases hij.lt_or_eq with h | h
    · exact (hd i j h).le
    · rw [h]
  have hmul : ∀ {a b g : GL (Fin 3) k}, a ∈ V.J 3 → b ∈ V.J 3 → g ∈ V.DC d → a * g * b ∈ V.DC d := by
    intro a b g ha hb hg
    obtain ⟨p, hp, q, hq, rfl⟩ := hg
    exact ⟨a * p, (V.J 3).mul_mem ha hp, q * b, (V.J 3).mul_mem hq hb, by group⟩
  have hDC : ∀ {a b g : GL (Fin 3) k}, a ∈ V.J 3 → b ∈ V.J 3 → (a * g * b ∈ V.DC d ↔ g ∈ V.DC d) := by
    intro a b g ha hb
    refine ⟨fun h => ?_, hmul ha hb⟩
    have h2 := hmul ((V.J 3).inv_mem ha) ((V.J 3).inv_mem hb) h
    simpa [mul_assoc] using h2
  have hL : y⁻¹ * (dg ![x₁, y₁, z₁] * Phi k) * th k 3 y * (Phi k)⁻¹ = y⁻¹ * dg ![x₁, y₁, z₁] * th' k y := by
    rw [hth]
    group
  rw [hL]
  have key : ∀ (u : Fin 3 → kˣ) (j : GL (Fin 3) k), j ∈ V.J 3 → y = dg u * j →
      (y⁻¹ * dg ![x₁, y₁, z₁] * th' k y ∈ V.DC d ↔
        (x₁ / (u 0 * u 2) / d 0 ∈ V.H ∧ y₁ / u 1 ^ 2 / d 1 ∈ V.H ∧ z₁ / (u 0 * u 2) / d 2 ∈ V.H)) := by
    intro u j hj hy
    have hu3 : dg u = dg ![u 0, u 1, u 2] := by
      congr 1
      funext i
      fin_cases i <;> rfl
    have hc : (dg ![u 0, u 1, u 2])⁻¹ * dg ![x₁, y₁, z₁] * dg ![(u 2)⁻¹, (u 1)⁻¹, (u 0)⁻¹] =
        dg ![x₁ / (u 0 * u 2), y₁ / u 1 ^ 2, z₁ / (u 0 * u 2)] := by
      simp only [dg, ← map_inv, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [div_eq_mul_inv, sq, mul_comm, mul_left_comm, mul_assoc]
    have e1 : y⁻¹ * dg ![x₁, y₁, z₁] * th' k y =
        j⁻¹ * dg ![x₁ / (u 0 * u 2), y₁ / u 1 ^ 2, z₁ / (u 0 * u 2)] * th' k j := by
      rw [hy, map_mul, hu3, hF.2.2.1, ← hc]
      group
    rw [e1, hDC ((V.J 3).inv_mem hj) (hF.2.1 j hj), diagDC k V 3 d _ hdom]
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
  constructor
  · intro hg
    obtain ⟨j, hj, s, hs, hjs⟩ := contract k V 3 (th' k) hF.1 d hd _ hg
    obtain ⟨h, hh, rfl⟩ := hs
    have hhH : ∀ i, h i ∈ V.H := fun i => hh i (Set.mem_univ i)
    set g := y⁻¹ * dg ![x₁, y₁, z₁] * th' k y with hg_def
    have hD : dg ![x₁, y₁, z₁] * dg ![z₁⁻¹, y₁⁻¹, x₁⁻¹] = dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] := by
      simp only [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
    have A : g * th' k g = y⁻¹ * dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] * y := by
      have : g * th' k g = y⁻¹ * (dg ![x₁, y₁, z₁] * th' k (dg ![x₁, y₁, z₁])) * y := by
        rw [hg_def, map_mul, map_mul, map_inv, Pres.invol hF.1]
        simp only [mul_assoc, mul_inv_cancel_left]
      rw [this, hF.2.2.1, hD]
    set p := h 0 * d 0 / (h 2 * d 2) with hp
    have C : diagT k (Fin 3) h * dg d * th' k (diagT k (Fin 3) h * dg d) = dg ![p, 1, p⁻¹] := by
      have e : diagT k (Fin 3) h * dg d = dg ![h 0 * d 0, h 1 * d 1, h 2 * d 2] := by
        simp only [dg, ← map_mul]
        congr 1
        funext i
        fin_cases i <;> rfl
      rw [e, hF.2.2.1]
      simp only [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [hp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have B : (j⁻¹ * g * th' k j) * th' k (j⁻¹ * g * th' k j) = j⁻¹ * (g * th' k g) * j := by
      simp only [map_mul, map_inv, Pres.invol hF.1]
      group
    rw [hjs, C, A] at B
    have hconj : (y * j)⁻¹ * dg ![x₁ / z₁, 1, (x₁ / z₁)⁻¹] * (y * j) = dg ![p, 1, p⁻¹] := by
      rw [B]
      group
    have hp1 : valuation k (p : k) < 1 := by
      have e2 : p = h 0 / h 2 * (d 0 / d 2) := by
        rw [hp, div_mul_div_comm]
      have hv1 : valuation k ((h 0 / h 2 : kˣ) : k) = 1 := V.H_le (V.H.div_mem (hhH 0) (hhH 2))
      rw [e2, Units.val_mul, map_mul, hv1, one_mul, Units.val_div_eq_div_val, map_div₀]
      exact (div_lt_one₀ (((valuation k).pos_iff).mpr (d 2).ne_zero)).mpr (hd 0 2 (by decide))
    obtain ⟨-, u, hu⟩ := conjDiag k 3 _ _ (sDom_of_valuation_lt_one _ hxz) (sDom_of_valuation_lt_one _ hp1) (y * j) hconj
    have hy : y = dg u * j⁻¹ := by
      rw [← hu]
      group
    exact ⟨u, j⁻¹, (V.J 3).inv_mem hj, hy, (key u j⁻¹ ((V.J 3).inv_mem hj) hy).mp hg⟩
  · rintro ⟨u, j, hj, hy, hc⟩
    exact (key u j hj hy).mpr hc

end
