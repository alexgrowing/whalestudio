import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.AdmissibleTraceRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuaternionStableSideTraceIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuotSumCongr

open UpperTheory.V.Z.Sym.Glob

private theorem alg {g e c k : ℝ} (hc : 0 < c) (hk : 0 < k) {A B C S K : ℂ} (h1 : A = g * (S + e * K)) (h2 : B = c * S) (h3 : C = k * K) :
    A = ((g / c : ℝ) : ℂ) * B + ((g * e / k : ℝ) : ℂ) * C := by
  subst h1 h2 h3
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Sym.Glob.tFId0 : TFId0 := by
  unfold TFId0
  intro F iF iN Δ D hD x₀ hx
  obtain ⟨cG, hG⟩ := @sideG F iF iN Δ D hD
  obtain ⟨e, hG⟩ := hG
  obtain ⟨cK, hK⟩ := @sideK F iF iN Δ D hD
  obtain ⟨n, hS⟩ := @split_side_identity_unitary F iF iN Δ D hD x₀ hx
  obtain ⟨x, hS⟩ := hS
  obtain ⟨cS, hS⟩ := hS
  refine ⟨n, x, cG / cS, cG * e / cK, hS.1, hS.2.1, div_pos hG.1 hS.2.2.1, ?_⟩
  intro VG VS VK a1 a2 a3 a4 a5 a6 a7 a8 a9 ch BG s BS BK hBG hBS hBK t ht
  exact alg hS.2.2.1 hK.1 (@hG.2 VG a1 a2 a3 ch BG s hBG t ht) (@hS.2.2.2 VS a4 a5 a6 ch BS hBS t ht) (@hK.2 VK a7 a8 a9 ch BK hBK t ht)
