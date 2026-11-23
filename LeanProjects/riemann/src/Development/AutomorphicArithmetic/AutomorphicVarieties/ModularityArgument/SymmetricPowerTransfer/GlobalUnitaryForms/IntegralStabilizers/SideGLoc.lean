import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuoMulInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ModelMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FinprodSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.SelCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVals
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Stable

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Loc QuadraticAlgebra

private theorem two_add_ne {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) : 2 + τ ≠ 0 := by
  intro h0
  apply h
  have : τ ^ 2 - 4 = (2 + τ) * (τ - 2) := by ring
  rw [this, h0, zero_mul]

private theorem unit_one_add {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) :
    ((toUnit (1 + ω : Etau K τ) : (Etau K τ)ˣ) : Etau K τ) = 1 + ω := by
  have h' := two_add_ne h
  have : IsUnit (1 + ω : Etau K τ) := by
    refine IsUnit.of_mul_eq_one (⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ : Etau K τ) ?_
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  simp [toUnit, this]

private theorem unit_om {K : Type} [Field K] (τ : K) :
    ((toUnit (ω : Etau K τ) : (Etau K τ)ˣ) : Etau K τ) = ω := by
  have : IsUnit (ω : Etau K τ) := by
    refine IsUnit.of_mul_eq_one (⟨τ, -1⟩ : Etau K τ) ?_
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  simp [toUnit, this]

private theorem jstd_tr {K : Type} [Field K] (τ : K) : (jstd τ ω).trace = τ := by
  simp [jstd, Matrix.trace, Fin.sum_univ_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]

private theorem mem_int {F : Type} [Field F] [NumberField F] (v : Pl F) (y : F) (hy : v.valuation F y ≤ 1) :
    cv v y ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (y : v.adicCompletion F) ≤ 1
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

private theorem ae_int {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : Pl F in Filter.cofinite, cv v x ∈ (algebraMap (Ov v) (Kv v)).range := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) x).subset fun v hv => ?_
  by_contra hn
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  exact hv ⟨⟨_, mem_int v x hn⟩, rfl⟩

private theorem ae_unit {F : Type} [Field F] [NumberField F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v x := by
  filter_upwards [ae_int x, ae_int x⁻¹] with v ⟨a, ha⟩ ⟨b, hb⟩
  have : a * b = 1 := by
    apply Subtype.ext
    change algebraMap (Ov v) (Kv v) (a * b) = 1
    rw [map_mul, ha, hb, ← map_mul, mul_inv_cancel₀ hx, map_one]
  exact ⟨⟨a, b, this, by rw [mul_comm, this]⟩, ha⟩

private theorem fp_zero {I : Type} (S : Finset I) (g : I → ℂ) (hg : ∀ᶠ v in Filter.cofinite, g v = 1) (v₀ : I) (h₀ : v₀ ∉ S)
    (h : g v₀ = 0) : (∏ᶠ (v : I) (_ : v ∉ S), g v) = 0 := by
  classical
  have hg' : (Function.mulSupport fun v => ∏ᶠ (_ : v ∉ S), g v).Finite := by
    refine (show {v | ¬ g v = 1}.Finite from hg).subset fun v hv h => hv ?_
    simp [h]
  exact finprod_eq_zero _ v₀ (by simp [h₀, h]) hg'

private theorem loc_ne {F : Type} [Field F] [NumberField F] {τ : F} (h : τ ^ 2 - 4 ≠ 0) (v : Pl F) : cv v τ ^ 2 - 4 ≠ 0 := by
  have := (map_ne_zero (cv v)).2 h
  simpa [map_ofNat] using this

private theorem unr_one (O K : Type) [CommRing O] [Field K] [Algebra O K] : Unr O (1 : Kˣ →* ℂˣ) := fun _ => rfl

variable {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ)

theorem sg_vanish (hD : D.Ok) {τ : F} (h : τ ^ 2 - 4 ≠ 0) (hi : ¬ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) :
    D.nS τ = 0 ∧ D.nK τ = 0 := by
  push Not at hi
  obtain ⟨w, hw, hi⟩ := hi
  have ae : ∀ᶠ v : Pl F in Filter.cofinite, gOrb (Ov v) (jstd (cv v τ)) 1 (toUnit ω) = 1 ∧
      gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + ω)) = 1 := by
    filter_upwards [ae_unit h, ae_unit (two_add_ne h), ae_int τ, D.Sg.eventually_cofinite_notMem] with v h1 h2 h4 h3
    obtain ⟨a, b, -⟩ := gVals (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v h3) (loc_ne h v) h4 (jstd _) (D.χ v) (jstd_tr _) (hD.chi v).1
      _ (unit_om _) _ (unit_one_add (loc_ne h v))
    obtain ⟨-, b', -⟩ := gVals (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v h3) (loc_ne h v) h4 (jstd _) 1 (jstd_tr _) (unr_one _ _)
      _ (unit_om _) _ (unit_one_add (loc_ne h v))
    refine ⟨b' (by simpa [map_ofNat] using h1), ?_⟩
    rw [a (by simpa [map_ofNat] using h2), b (by simpa [map_ofNat] using h1)]
  constructor
  · refine fp_zero D.Sg _ (ae.mono fun _ h => h.1) w hw ?_
    by_contra hn
    exact hi (gVanish (Ov w) (Kv w) (cv w Δ) (cv w τ) (hD.off w hw) _ (jstd_tr _) _ _ (Or.inl (unit_om _)) hn)
  · refine fp_zero D.Sg _ (ae.mono fun _ h => h.2) w hw ?_
    by_contra hn
    exact hi (gVanish (Ov w) (Kv w) (cv w Δ) (cv w τ) (hD.off w hw) _ (jstd_tr _) _ _ (Or.inr (unit_one_add (loc_ne h w))) hn)

theorem sg_ev (hD : D.Ok) {τ c : F} {d m : EL Δ τ} (h : IsDat c d m) (hn : D.nL c d m ≠ 0) : D.Ev (c * (2 - τ)) := by
  intro w hw
  have hl : lcount (Ov w) (cv w c) (elmap (cv w) d) (elmap (cv w) m) ≠ 0 := by
    intro h0
    refine hn (fp_zero D.Sg _ ?_ w hw h0)
    filter_upwards [genPl F Δ D hD τ c d m h] with v hv
    have := hv 1
    rw [Units.val_one, one_smul] at this
    rw [this]
    exact if_pos (one_mem _)
  have := (vanish (Ov w) (Kv w) (cv w Δ) (cv w τ) (hD.off w hw) _ _ _ (modelMap F (Kv w) (cv w) Δ τ c d m h).1 hl).2
  rw [map_mul, map_sub, map_ofNat]
  exact this

theorem sg_stab (hD : D.Ok) {τ c : F} {d m : EL Δ τ} (h : IsDat c d m) (he : D.Ev (c * (2 - τ))) :
    (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), stabSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) = D.nS τ := by
  refine finprod_congr fun v => finprod_congr fun hv => ?_
  have e := he v hv
  rw [map_mul, map_sub, map_ofNat] at e
  exact stable (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v hv) _ _ _ (modelMap F (Kv v) (cv v) Δ τ c d m h).1 e _ (jstd_tr _) _
    (unr_one _ _) _ (unit_om _)

theorem sg_inner (hD : D.Ok) {τ : F} {e : ℝ} {d m : EL Δ τ} (hτ : IsCM τ) (hs : D.Spl τ) (h : IsDat 1 d m)
    (hk : ∀ c : F, TPos c → D.Ev (c * (2 - τ)) →
      (∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m)) = e * D.nK τ) :
    (Function.support fun x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ) =>
      one (x.1 ∈ D.Sel (2 - τ)) * (one (TPos (x.2.out : F)) * D.nL (x.1.out : F) d ((x.2.out : F) • m))).Finite ∧
    ∑ᶠ x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ),
      one (x.1 ∈ D.Sel (2 - τ)) * (one (TPos (x.2.out : F)) * D.nL (x.1.out : F) d ((x.2.out : F) • m)) =
      ((D.Sel 1).ncard : ℂ) * (1 / 2 * (D.nS τ + e * D.nK τ)) := by
  classical
  have hp : TPos (2 - τ) := fun σ => by
    have := hτ σ
    simp only [map_sub, map_pow, map_ofNat] at this ⊢
    nlinarith
  obtain ⟨hfin, hcard⟩ := (selCard F Δ D hD).2.2 _ hp
  have hd : ∀ c : Fˣ, IsDat (c : F) d m := fun c => { h with c_ne := c.ne_zero }
  have hT := fun c : Fˣ => sumT F Δ D hD τ c d m hτ hs (hd c)
  have hf : (Function.support fun x : (Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) × (Fˣ ⧸ NE τ) =>
      one (x.1 ∈ D.Sel (2 - τ)) * (one (TPos (x.2.out : F)) * D.nL (x.1.out : F) d ((x.2.out : F) • m))).Finite := by
    refine (hfin.biUnion fun c _ => (hT c.out).1.image (Prod.mk c)).subset ?_
    rintro ⟨c, u⟩ hx
    have h1 := left_ne_zero_of_mul hx
    have h2 := right_ne_zero_of_mul hx
    have h3 := left_ne_zero_of_mul h2
    simp only [Set.mem_iUnion]
    refine ⟨c, ?_, u, ⟨?_, right_ne_zero_of_mul h2⟩, rfl⟩
    · by_contra hn; exact h1 (if_neg hn)
    · by_contra hn; exact h3 (if_neg hn)
  refine ⟨hf, ?_⟩
  rw [finsum_curry _ hf, ← hcard]
  have e1 : ∀ c : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range, (∑ᶠ u : Fˣ ⧸ NE τ,
      one (c ∈ D.Sel (2 - τ)) * (one (TPos (u.out : F)) * D.nL (c.out : F) d ((u.out : F) • m))) =
      ∑ᶠ (_ : c ∈ D.Sel (2 - τ)), (1 / 2 * (D.nS τ + e * D.nK τ)) := fun c => by
    by_cases hc : c ∈ D.Sel (2 - τ)
    · have : one (c ∈ D.Sel (2 - τ)) = 1 := if_pos hc
      simp only [this, one_mul]
      rw [(hT c.out).2, sg_stab D hD (hd _) hc.2, hk _ hc.1 hc.2, finsum_eq_if, if_pos hc]
    · have : one (c ∈ D.Sel (2 - τ)) = 0 := if_neg hc
      simp only [this, zero_mul, finsum_zero]
      rw [finsum_eq_if, if_neg hc]
  rw [finsum_congr e1, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]

theorem sg_sigma {T : Type} [Finite T] {β : T → Type} (g : (Σ i, β i) → ℂ)
    (hg : ∀ i, (Function.support fun x => g ⟨i, x⟩).Finite) : ∑ᶠ j, g j = ∑ᶠ i, ∑ᶠ x, g ⟨i, x⟩ := by
  classical
  haveI := Fintype.ofFinite T
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.sigma fun i => (hg i).toFinset), Finset.sum_sigma, finsum_eq_sum_of_fintype]
  · exact Finset.sum_congr rfl fun i _ => (finsum_eq_sum _ (hg i)).symm
  · rintro ⟨i, x⟩ hx
    simpa using hx

section Scale

variable {K : Type} [Field K] {Δ τ : K}

private theorem ofE_mul' (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

private theorem ofE_inv (z : (Etau K τ)ˣ) : ofE Δ (z : Etau K τ) * ofE Δ ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
  rw [← ofE_mul', Units.mul_inv]
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private noncomputable def scaleEq (Δ : K) (s : Kˣ) (z : (Etau K τ)ˣ) : Sp Δ τ ≃ₗ[Lsq K Δ] Sp Δ τ where
  toFun x := (algebraMap K (Lsq K Δ) s * x.1, ofE Δ (z : Etau K τ) * x.2)
  invFun x := (algebraMap K (Lsq K Δ) (s⁻¹ : Kˣ) * x.1, ofE Δ ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2)
  map_add' x y := by simp [mul_add]
  map_smul' a x := by simp [mul_left_comm]
  left_inv x := by
    refine Prod.ext ?_ ?_
    · simp only []
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    · simp only []
      rw [← mul_assoc, mul_comm _ (ofE Δ (z : Etau K τ)), ofE_inv, one_mul]
  right_inv x := by
    refine Prod.ext ?_ ?_
    · simp only []
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    · simp only []
      rw [← mul_assoc, ofE_inv, one_mul]

private theorem sigL_ofE (z : Etau K τ) (x : EL Δ τ) : sigL (ofE Δ z * x) = ofE Δ z * sigL x := by
  ext <;> simp [ofE, sigL] <;> ring

private theorem ofE_norm (z : Etau K τ) (m : EL Δ τ) : QuadraticAlgebra.norm z • m = m * (ofE Δ z * star (ofE Δ z)) := by
  ext <;> simp [ofE, QuadraticAlgebra.norm_def] <;> ring

theorem sg_scale {c : K} {d m : EL Δ τ} {δ ι P} (h : Models c d m δ ι P) (s : Kˣ) (z : (Etau K τ)ˣ) :
    ∃ P', Models (c * s ^ 2) d (QuadraticAlgebra.norm (z : Etau K τ) • m) δ ι P' := by
  refine ⟨(scaleEq Δ s z).trans P, fun x y => ?_, fun x => ?_, fun w x => ?_⟩
  · simp only [LinearEquiv.trans_apply]
    rw [← h.form]
    change _ = algebraMap K (Lsq K Δ) c * (algebraMap K (Lsq K Δ) s * x.1) * star (algebraMap K (Lsq K Δ) s * y.1) +
      QuadraticAlgebra.trace (m * (ofE Δ (z : Etau K τ) * x.2) * star (sigL (ofE Δ (z : Etau K τ) * y.2)))
    have e : star (algebraMap K (Lsq K Δ) s) = algebraMap K (Lsq K Δ) s := by ext <;> simp
    rw [sigL_ofE, star_mul', star_mul', e, herm, ofE_norm, map_mul, map_pow]
    congr 1
    · ring
    · congr 1
      ring
  · simp only [LinearEquiv.trans_apply]
    rw [← h.semi]
    congr 1
    have e : star (algebraMap K (Lsq K Δ) s) = algebraMap K (Lsq K Δ) s := by ext <;> simp
    refine Prod.ext ?_ ?_
    · change algebraMap K (Lsq K Δ) s * star x.1 = star (algebraMap K (Lsq K Δ) s * x.1)
      rw [star_mul', e]
    · change ofE Δ (z : Etau K τ) * (d * sigL x.2) = d * sigL (ofE Δ (z : Etau K τ) * x.2)
      rw [sigL_ofE, mul_left_comm]
  · simp only [LinearEquiv.trans_apply]
    rw [← h.tor]
    congr 1
    refine Prod.ext rfl ?_
    change ofE Δ (z : Etau K τ) * (ofE Δ (quo w) * x.2) = ofE Δ (quo w) * (ofE Δ (z : Etau K τ) * x.2)
    rw [mul_left_comm]

theorem sg_out {c t : Kˣ} {d m : EL Δ τ} {δ ι P} (h : Models (c : K) d ((t : K) • m) δ ι P) :
    ∃ (x : (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) × (Kˣ ⧸ NE τ)), ∃ P',
      Models (x.1.out : K) d ((x.2.out : K) • m) δ ι P' := by
  obtain ⟨⟨_, s, rfl⟩, hs⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom 2 : Kˣ →* Kˣ).range c
  obtain ⟨⟨_, z, rfl⟩, hz⟩ := QuotientGroup.mk_out_eq_mul (NE τ) t
  obtain ⟨P', h'⟩ := sg_scale h s z
  refine ⟨(c, t), P', ?_⟩
  simp only [hs, hz]
  rw [smul_smul, mul_comm _ (t : K)] at h'
  exact h'

end Scale

end UpperTheory.V.Z.Sym.Glob
