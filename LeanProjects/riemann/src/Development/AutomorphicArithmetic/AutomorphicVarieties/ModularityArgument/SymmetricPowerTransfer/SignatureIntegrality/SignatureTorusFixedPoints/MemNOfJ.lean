import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem ord_le_ord_of_valuation_le {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) : ord k y ≤ ord k x := by
  rw [val_ord, val_ord] at h
  exact (zpow_le_zpow_iff_right_of_lt_one₀ GlAx.unif_pos ValuativeRel.uniformizer_lt_one).1 h

private theorem ord_anti {d : Fin n → kˣ} (hd : Dom d) : Antitone fun i => ord k (d i) := fun i j hij => ord_le_ord_of_valuation_le (hd i j hij)

private theorem conjN {d : Fin n → kˣ} (hd : Dom d) {x : GL (Fin n) k} (hx : x ∈ (glIwa k n).N) :
    dg d * x * (dg d)⁻¹ ∈ (glIwa k n).N :=
  GlAx.conj_N (fun i => val_ord (d i)) (ord_anti hd) hx

private theorem conjNm {d : Fin n → kˣ} (hd : Dom d) {c : ℕ} {y : GL (Fin n) k} (hy : y ∈ (glIwa k n).Nm c) :
    (dg d)⁻¹ * y * dg d ∈ (glIwa k n).Nm c := by
  have h := GlAx.conj_Nm (t := d⁻¹) (a := fun i => ord k ((d⁻¹) i)) (fun i => val_ord _) (c := c) (c' := c) ?_ hy
  · rw [map_inv, inv_inv] at h
    exact h
  · intro i j hji
    have h1 : valuation k ((d j : k)) ≤ valuation k (d i : k) := hd j i hji.le
    have h2 : valuation k (((d⁻¹) i : kˣ) : k) ≤ valuation k (((d⁻¹) j : kˣ) : k) := by
      simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_anti₀ (zero_lt_iff.2 (by simp)) h1
    have h3 := ord_le_ord_of_valuation_le h2
    omega

private theorem DC_left (V : Lev k) {d : Fin n → kˣ} {j x : GL (Fin n) k} (hj : j ∈ V.J n) (hx : x ∈ V.DC d) :
    j * x ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨j * a, (V.J n).mul_mem hj ha, b, hb, by simp only [mul_assoc]⟩

private theorem DC_N (V : Lev k) {d : Fin n → kˣ} (hd : Dom d) {g : GL (Fin n) k} (hg : g ∈ V.DC d) :
    ∃ a ∈ (glIwa k n).N, ∃ b ∈ V.J n, g = a * dg d * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  obtain ⟨a', ha', s, hs, b', hb', rfl⟩ := (factJ k V n).1 a ha
  obtain ⟨t, -, hts⟩ := Subgroup.mem_map.1 hs
  have hcomm : s * dg d = dg d * s := by
    rw [← hts]
    show diagT k (Fin n) t * diagT k (Fin n) d = diagT k (Fin n) d * diagT k (Fin n) t
    rw [← map_mul, ← map_mul, mul_comm]
  refine ⟨a', ha', s * ((dg d)⁻¹ * b' * dg d) * b, ?_, ?_⟩
  · exact (V.J n).mul_mem ((V.J n).mul_mem (V.TH_le hs) (V.Nm_le (conjNm hd hb'))) hb
  · calc a' * s * b' * dg d * b = a' * (s * dg d) * (dg d)⁻¹ * b' * dg d * b := by group
      _ = a' * (dg d * s) * (dg d)⁻¹ * b' * dg d * b := by rw [hcomm]
      _ = a' * dg d * (s * ((dg d)⁻¹ * b' * dg d) * b) := by group

private theorem dom_mul {d d' : Fin n → kˣ} (hd : Dom d) (hd' : Dom d') : Dom (d * d') := fun i j h => by
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_le_mul' (hd i j h) (hd' i j h)

private theorem dg_mul (d d' : Fin n → kˣ) : dg (d * d') = dg d * dg d' := map_mul _ d d'

private theorem key (V : Lev k) {d d' : Fin n → kˣ} (hd : Dom d) (hd' : Dom d') {n₁ n₂ g : GL (Fin n) k}
    (h₁ : n₁ ∈ (glIwa k n).N) (h₂ : n₂ ∈ (glIwa k n).N)
    (g₁ : (n₁ * dg d)⁻¹ * g ∈ V.DC d') (g₂ : (n₂ * dg d)⁻¹ * g ∈ V.DC d') :
    (n₁ * dg d)⁻¹ * (n₂ * dg d) ∈ V.J n := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = (n₁ * dg d)⁻¹ * (n₂ * dg d) := ⟨_, rfl⟩
  rw [← hxdef]
  obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := DC_N V hd' g₁
  obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := DC_N V hd' g₂
  have hx : x = a₁ * dg d' * (b₁ * b₂⁻¹) * (dg d')⁻¹ * a₂⁻¹ := by
    have h0 : x = ((n₁ * dg d)⁻¹ * g) * ((n₂ * dg d)⁻¹ * g)⁻¹ := by rw [hxdef]; group
    rw [h0, e₁, e₂]
    group
  have hxu : x ∈ unipB k (Fin n) := by
    have hu : n₁⁻¹ * n₂ ∈ unipB k (Fin n) :=
      (glIwa k n).N_le ((glIwa k n).N.mul_mem ((glIwa k n).N.inv_mem h₁) h₂)
    have h0 := GlAx.conj_up (d⁻¹) hu
    rw [map_inv, inv_inv] at h0
    have h3 : x = (diagT k (Fin n) d)⁻¹ * (n₁⁻¹ * n₂) * diagT k (Fin n) d := by rw [hxdef]; group
    rw [h3]
    exact h0
  have hw : (dg d')⁻¹ * (a₁⁻¹ * x * a₂) * dg d' = b₁ * b₂⁻¹ := by rw [hx]; group
  have hwu : (dg d')⁻¹ * (a₁⁻¹ * x * a₂) * dg d' ∈ unipB k (Fin n) := by
    have h0 : a₁⁻¹ * x * a₂ ∈ unipB k (Fin n) :=
      (unipB k (Fin n)).mul_mem ((unipB k (Fin n)).mul_mem
        ((unipB k (Fin n)).inv_mem ((glIwa k n).N_le ha₁)) hxu) ((glIwa k n).N_le ha₂)
    have h3 := GlAx.conj_up (d'⁻¹) h0
    rw [map_inv, inv_inv] at h3
    exact h3
  obtain ⟨α, hα, s, hs, γ, hγ, eβ⟩ :=
    (factJ k V n).1 (b₁ * b₂⁻¹) ((V.J n).mul_mem hb₁ ((V.J n).inv_mem hb₂))
  obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hs
  rw [hw, eβ] at hwu
  have hγ0 : γ ∈ Subgroup.comap (GlobalTheory.CuspRep.invT n k) (unipB k (Fin n)) ⊓ Kc k n (V.c + 1) := hγ
  have hu2 := GlAx.uniq t ((unipB k (Fin n)).mul_mem ((unipB k (Fin n)).inv_mem hwu)
    ((glIwa k n).N_le hα)) (Subgroup.mem_inf.1 hγ0).1 (by group)
  have eα : α * diagT k (Fin n) t * γ = α := inv_mul_eq_one.1 hu2.1
  have key2 : a₁⁻¹ * x * a₂ = dg d' * α * (dg d')⁻¹ := by
    have h0 : (dg d')⁻¹ * (a₁⁻¹ * x * a₂) * dg d' = α := by rw [hw, eβ, eα]
    rw [← h0]
    group
  have hxN : x ∈ (glIwa k n).N := by
    have h0 : x = a₁ * (dg d' * α * (dg d')⁻¹) * a₂⁻¹ := by rw [← key2]; group
    rw [h0]
    exact (glIwa k n).N.mul_mem ((glIwa k n).N.mul_mem ha₁ (conjN hd' hα)) ((glIwa k n).N.inv_mem ha₂)
  exact V.N_le hxN

end UpperTheory.V.Z.Sym.Sig

open UpperTheory.V.Z.Sym.Sig in
theorem UpperTheory.V.Z.Sym.Sig.dCMul :
    UpperTheory.V.Z.Sym.Sig.DCMul := by
  intro k _ _ _ _ V n d d' hd hd' g
  have gen : ∀ p q : GL (Fin n) k, p ∈ V.DC d → p⁻¹ * g ∈ V.DC d' → q ∈ V.DC d → q⁻¹ * g ∈ V.DC d' →
      p⁻¹ * q ∈ V.J n := by
    intro p q hp hpg hq hqg
    obtain ⟨n₁, hn₁, b₁, hb₁, rfl⟩ := DC_N V hd hp
    obtain ⟨n₂, hn₂, b₂, hb₂, rfl⟩ := DC_N V hd hq
    have k1 : (n₁ * dg d)⁻¹ * g ∈ V.DC d' := by
      have e : (n₁ * dg d)⁻¹ * g = b₁ * ((n₁ * dg d * b₁)⁻¹ * g) := by group
      rw [e]
      exact DC_left V hb₁ hpg
    have k2 : (n₂ * dg d)⁻¹ * g ∈ V.DC d' := by
      have e : (n₂ * dg d)⁻¹ * g = b₂ * ((n₂ * dg d * b₂)⁻¹ * g) := by group
      rw [e]
      exact DC_left V hb₂ hqg
    have h0 := key V hd hd' hn₁ hn₂ k1 k2
    have e : (n₁ * dg d * b₁)⁻¹ * (n₂ * dg d * b₂) = b₁⁻¹ * ((n₁ * dg d)⁻¹ * (n₂ * dg d)) * b₂ := by group
    rw [e]
    exact (V.J n).mul_mem ((V.J n).mul_mem ((V.J n).inv_mem hb₁) h0) hb₂
  refine ⟨fun hg => ?_, fun y hy hyg => ?_⟩
  · obtain ⟨a, ha, b, hb, hgab⟩ := DC_N V (dom_mul hd hd') hg
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V.J n) (a * dg d)
    have P0 : (QuotientGroup.mk (a * dg d) : GL (Fin n) k ⧸ V.J n).out ∈ V.DC d ∧
        (QuotientGroup.mk (a * dg d) : GL (Fin n) k ⧸ V.J n).out⁻¹ * g ∈ V.DC d' := by
      rw [hh]
      refine ⟨⟨a, V.N_le ha, h, h.2, rfl⟩, ⟨(h : GL (Fin n) k)⁻¹, (V.J n).inv_mem h.2, b, hb, ?_⟩⟩
      rw [hgab, dg_mul]
      group
    refine ⟨QuotientGroup.mk (a * dg d), P0, fun y hy => ?_⟩
    rw [← Quotient.out_eq y, ← Quotient.out_eq (QuotientGroup.mk (a * dg d) : GL (Fin n) k ⧸ V.J n)]
    exact Quotient.sound (QuotientGroup.leftRel_apply.2 (gen _ _ hy.1 hy.2 P0.1 P0.2))
  · obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', e⟩ := hyg
    obtain ⟨α, hα, s, hs, γ, hγ, eβ⟩ := (factJ k V n).1 (b * a') ((V.J n).mul_mem hb ha')
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hs
    have hcomm : diagT k (Fin n) t * dg d' = dg d' * diagT k (Fin n) t := by
      show diagT k (Fin n) t * diagT k (Fin n) d' = diagT k (Fin n) d' * diagT k (Fin n) t
      rw [← map_mul, ← map_mul, mul_comm]
    have h2 : diagT k (Fin n) t = dg d' * diagT k (Fin n) t * (dg d')⁻¹ := by
      rw [← hcomm]
      group
    have hg : g = a * dg d * (b * a') * dg d' * b' := by
      have h0 : g = (a * dg d * b) * ((a * dg d * b)⁻¹ * g) := by group
      rw [h0, e]
      group
    rw [hg, eβ]
    refine ⟨a * (dg d * α * (dg d)⁻¹), (V.J n).mul_mem ha (V.N_le (conjN hd hα)),
      diagT k (Fin n) t * ((dg d')⁻¹ * γ * dg d') * b',
      (V.J n).mul_mem ((V.J n).mul_mem (V.TH_le hs) (V.Nm_le (conjNm hd' hγ))) hb', ?_⟩
    rw [dg_mul]
    nth_rewrite 1 [h2]
    group

end
