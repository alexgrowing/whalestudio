import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.EvUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KappaZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVals
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsCast
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ChiVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.SigOneAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.QuoMulInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ModelMap

open NumberField IsDedekindDomain QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.V.Z.Sym.Glob

private theorem hs_sq {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {d : K} (hd : d ≠ 0) (hs' : IsSquare d) (x : K) : hs d x = 1 := by
  obtain ⟨r, rfl⟩ := hs'
  have hr : r ≠ 0 := fun h => hd (by simp [h])
  unfold hs
  rw [if_pos]
  exact ⟨(x + 1) / 2, (x - 1) / (2 * r), by field_simp; ring⟩

private theorem hs_pos (d x : ℝ) (hx : 0 < x) : hs d x = 1 := by
  unfold hs
  rw [if_pos]
  exact ⟨Real.sqrt x, 0, by rw [Real.sq_sqrt hx.le]; ring⟩

private theorem hs_neg (d x : ℝ) (hd : d < 0) (hx : x < 0) : hs d x = -1 := by
  unfold hs
  rw [if_neg]
  rintro ⟨a, b, h⟩
  nlinarith [sq_nonneg a, sq_nonneg b]

private theorem normL {K : Type} [Field K] (Δ : K) (x : Lsq K Δ) : QuadraticAlgebra.norm x = x.re ^ 2 - Δ * x.im ^ 2 := by
  simp [QuadraticAlgebra.norm_def]; ring

private theorem hs_iff {K : Type} [Field K] (Δ x : K) : (∃ lam : Lsq K Δ, QuadraticAlgebra.norm lam = x) → hs Δ x = 1 := by
  rintro ⟨lam, hl⟩
  unfold hs
  rw [if_pos ⟨lam.re, lam.im, by rw [← normL, hl]⟩]

private theorem hs_iff' {K : Type} [Field K] (Δ x : K) (h : hs Δ x = 1) : ∃ lam : Lsq K Δ, QuadraticAlgebra.norm lam = x := by
  unfold hs at h
  split_ifs at h with h'
  · obtain ⟨a, b, e⟩ := h'
    exact ⟨⟨a, b⟩, by rw [normL]; exact e⟩
  · norm_num at h

private theorem two_add_ne {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) : 2 + τ ≠ 0 := fun e =>
  h (by have : τ = -2 := by linear_combination e
        rw [this]; ring)

private theorem unit_one_add {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) :
    ((toUnit (1 + ω : Etau K τ) : (Etau K τ)ˣ) : Etau K τ) = 1 + ω := by
  have h' := two_add_ne h
  have : IsUnit (1 + ω : Etau K τ) := by
    refine IsUnit.of_mul_eq_one (⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ : Etau K τ) ?_
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  simp [toUnit, this]

private theorem unit_om {K : Type} [Field K] (τ : K) :
    ((toUnit (ω : Etau K τ) : (Etau K τ)ˣ) : Etau K τ) = ω := by
  have hu : IsUnit (ω : Etau K τ) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, isUnit_iff_ne_zero]
    have e : QuadraticAlgebra.norm (ω : Etau K τ) = 1 := by
      rw [QuadraticAlgebra.norm_def]
      simp
    rw [e]
    exact one_ne_zero
  unfold toUnit
  rw [dif_pos hu]
  rfl

private theorem jstd_tr {K : Type} [Field K] (τ : K) : (jstd τ ω).trace = τ := by
  simp [jstd, Matrix.trace, Fin.sum_univ_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]

private theorem inv_val {K : Type} [Field K] {τ : K} (h : τ ^ 2 - 4 ≠ 0) (z : (Etau K τ)ˣ) (hz : (z : Etau K τ) = 1 + ω) :
    ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ := by
  have h' := two_add_ne h
  apply Units.inv_eq_of_mul_eq_one_right
  rw [hz]
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring

private theorem elmap_dLam {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ τ : K} (h : τ ^ 2 - 4 ≠ 0) (h' : f τ ^ 2 - 4 ≠ 0) (lam : Lsq K Δ)
    (z : (Etau K τ)ˣ) (hz : (z : Etau K τ) = 1 + ω) (z' : (Etau K' (f τ))ˣ) (hz' : (z' : Etau K' (f τ)) = 1 + ω) :
    elmap f (dLam lam z) = dLam (lmap f Δ lam) z' := by
  have hi := inv_val h z hz
  have hi' := inv_val h' z' hz'
  unfold dLam
  rw [hi, hi']
  ext <;> simp [elmap, ofE, lmap, map_div₀, map_add, map_mul, map_neg, map_one, map_ofNat]

private theorem elmap_one {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ τ : K} :
    elmap f (1 : EL Δ τ) = 1 := by
  show (⟨lmap f Δ (1 : EL Δ τ).re, lmap f Δ (1 : EL Δ τ).im⟩ : EL (f Δ) (f τ)) = 1
  rw [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, map_one, map_zero]
  rfl

private theorem posF_one {F : Type} [Field F] [NumberField F] {Δ τ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (hτ : IsCM τ) :
    PosF (1 : F) (1 : EL Δ τ) := by
  intro x hx σ
  have key : (herm 1 (1 : EL Δ τ) x x).re =
      (x.1.re ^ 2 - Δ * x.1.im ^ 2) + 2 * (x.2.re.re ^ 2 - Δ * x.2.re.im ^ 2) + 2 * (x.2.im.re ^ 2 - Δ * x.2.im.im ^ 2)
        + 2 * τ * (x.2.re.re * x.2.im.re - Δ * x.2.re.im * x.2.im.im) := by
    simp [herm, sigL, QuadraticAlgebra.trace_def]
    ring
  rw [key]
  have hD := hΔ σ
  have hT : σ τ ^ 2 < 4 := by
    have h' := hτ σ
    rw [map_sub, map_pow, map_ofNat] at h'
    linarith
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  set D := σ Δ
  set T := σ τ
  set a1 := σ x.1.re with ha1
  set b1 := σ x.1.im with hb1
  set p1 := σ x.2.re.re with hp1
  set p2 := σ x.2.re.im with hp2
  set q1 := σ x.2.im.re with hq1
  set q2 := σ x.2.im.im with hq2
  by_contra hle
  push_neg at hle
  have t1 := sq_nonneg a1
  have t2 : 0 ≤ (-D) * b1 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have t3 : 0 ≤ (2 * p1 + T * q1) ^ 2 := sq_nonneg _
  have t4 : 0 ≤ (4 - T ^ 2) * q1 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have t5 : 0 ≤ (-D) * (2 * p2 + T * q2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have t6 : 0 ≤ (-D) * ((4 - T ^ 2) * q2 ^ 2) := mul_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg _))
  have hE : (a1 ^ 2 - D * b1 ^ 2) + 2 * (p1 ^ 2 - D * p2 ^ 2) + 2 * (q1 ^ 2 - D * q2 ^ 2)
      + 2 * T * (p1 * q1 - D * p2 * q2) = a1 ^ 2 + (-D) * b1 ^ 2 + (2 * p1 + T * q1) ^ 2 / 2
        + (4 - T ^ 2) * q1 ^ 2 / 2 + (-D) * (2 * p2 + T * q2) ^ 2 / 2 + (-D) * ((4 - T ^ 2) * q2 ^ 2) / 2 := by
    ring
  rw [hE] at hle
  have hDn : -D ≠ 0 := by linarith
  have hTn : 4 - T ^ 2 ≠ 0 := by linarith
  have e1 : a1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have e2 : b1 = 0 := by
    have : (-D) * b1 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hDn)
  have e3 : q1 = 0 := by
    have : (4 - T ^ 2) * q1 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hTn)
  have e4 : p1 = 0 := by
    have : (2 * p1 + T * q1) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff two_ne_zero |>.mp this
    rw [e3] at this
    linarith
  have e5 : q2 = 0 := by
    have : (-D) * ((4 - T ^ 2) * q2 ^ 2) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hDn
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hTn)
  have e6 : p2 = 0 := by
    have : (-D) * (2 * p2 + T * q2) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hDn)
    rw [e5] at this
    linarith
  apply hx
  rw [ha1, map_eq_zero] at e1
  rw [hb1, map_eq_zero] at e2
  rw [hp1, map_eq_zero] at e4
  rw [hp2, map_eq_zero] at e6
  rw [hq1, map_eq_zero] at e3
  rw [hq2, map_eq_zero] at e5
  exact Prod.ext (QuadraticAlgebra.ext e1 e2)
    (QuadraticAlgebra.ext (QuadraticAlgebra.ext e4 e6) (QuadraticAlgebra.ext e3 e5))

private theorem ae_unit {F : Type} [Field F] [NumberField F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v x := by
  have integ : ∀ y : F, ∀ᶠ v : Pl F in Filter.cofinite,
      cv v y ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    intro y
    simp only [Filter.eventually_cofinite, HeightOneSpectrum.mem_adicCompletionIntegers, not_le]
    refine (HeightOneSpectrum.Support.finite (𝓞 F) y).subset fun v hv => ?_
    simp only [Set.mem_setOf_eq] at hv
    show 1 < v.valuation F y
    have e : Valued.v (cv v y) = v.valuation F y :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y
    rw [← e]
    exact hv
  filter_upwards [integ x, integ x⁻¹] with v h1 h2
  refine ⟨⟨⟨cv v x, h1⟩, ⟨cv v x⁻¹, h2⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show cv v x * cv v x⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  · apply Subtype.ext
    show cv v x⁻¹ * cv v x = 1
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]

private theorem fp_mul {I : Type} (S : Finset I) (a b c g k : I → ℂ) (ha : {v | a v ≠ 1}.Finite) (hb : {v | b v ≠ 1}.Finite)
    (hc : {v | c v ≠ 1}.Finite) (hg : ∀ᶠ v in Filter.cofinite, g v = 1) (hS : ∀ v ∈ S, a v = 1 ∧ b v = 1 ∧ c v = 1)
    (hk : ∀ v ∉ S, k v = a v * b v * c v * g v) :
    (∏ᶠ (v : I) (_ : v ∉ S), k v) = (∏ᶠ v, a v) * (∏ᶠ v, b v) * (∏ᶠ v, c v) * ∏ᶠ (v : I) (_ : v ∉ S), g v := by
  have sub : Function.mulSupport (Set.mulIndicator {v | v ∉ S} g) ⊆ Function.mulSupport g := by
    rw [Set.mulSupport_mulIndicator]
    exact Set.inter_subset_right
  have hG : (Function.mulSupport (Set.mulIndicator {v | v ∉ S} g)).Finite :=
    (Filter.eventually_cofinite.mp hg).subset sub
  have hpt : ∀ v, Set.mulIndicator {v | v ∉ S} k v = a v * b v * c v * Set.mulIndicator {v | v ∉ S} g v := by
    intro v
    by_cases hv : v ∈ S
    · rw [Set.mulIndicator_of_notMem (by simpa using hv), Set.mulIndicator_of_notMem (by simpa using hv)]
      obtain ⟨h1, h2, h3⟩ := hS v hv
      rw [h1, h2, h3]
      ring
    · rw [Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hv),
        Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hv)]
      exact hk v hv
  change ∏ᶠ (v : I) (_ : v ∈ {v | v ∉ S}), k v =
    (∏ᶠ v, a v) * (∏ᶠ v, b v) * (∏ᶠ v, c v) * ∏ᶠ (v : I) (_ : v ∈ {v | v ∉ S}), g v
  rw [finprod_mem_def, finprod_mem_def, finprod_congr hpt]
  have hab : (Function.mulSupport fun v => a v * b v).Finite :=
    (ha.union hb).subset (Function.mulSupport_mul a b)
  have habc : (Function.mulSupport fun v => a v * b v * c v).Finite :=
    (hab.union hc).subset (Function.mulSupport_mul _ c)
  rw [finprod_mul_distrib habc hG, finprod_mul_distrib hab hc, finprod_mul_distrib ha hb]

private theorem fp_zero {I : Type} (S : Finset I) (g : I → ℂ) (hg : ∀ᶠ v in Filter.cofinite, g v = 1) (v₀ : I) (h₀ : v₀ ∉ S)
    (h : g v₀ = 0) : (∏ᶠ (v : I) (_ : v ∉ S), g v) = 0 := by
  have hfin : (Function.mulSupport g).Finite := Filter.eventually_cofinite.mp hg
  change ∏ᶠ (v : I) (_ : v ∈ {v | v ∉ S}), g v = 0
  rw [finprod_mem_def]
  apply finprod_eq_zero _ v₀
  · rw [Set.mulIndicator_of_mem (show v₀ ∈ {v | v ∉ S} from h₀)]
    exact h
  · refine hfin.subset ?_
    rw [Set.mulSupport_mulIndicator]
    exact Set.inter_subset_right

private theorem loc_ne {F : Type} [Field F] [NumberField F] {τ : F} (h : τ ^ 2 - 4 ≠ 0) (v : Pl F) : cv v τ ^ 2 - 4 ≠ 0 := by
  have h' : cv v (τ ^ 2 - 4) ≠ 0 := (map_ne_zero _).mpr h
  rwa [map_sub, map_pow, map_ofNat] at h'

private theorem ae_g {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) {τ : F} (h : τ ^ 2 - 4 ≠ 0)
    (hi : ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range) :
    ∀ᶠ v : Pl F in Filter.cofinite, gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + ω)) = 1 := by
  filter_upwards [ae_unit (two_add_ne h), ae_unit h, D.Sg.finite_toSet.eventually_cofinite_notMem]
    with v hu1 hu2 hvS
  obtain ⟨u1, e1⟩ := hu1
  obtain ⟨u2, e2⟩ := hu2
  have g := gVals (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v hvS) (loc_ne h v) (hi v hvS)
    (jstd (cv v τ)) (D.χ v) (jstd_tr _) (hD.chi v).1 (toUnit ω) (unit_om _) (toUnit (1 + ω))
    (unit_one_add (loc_ne h v))
  rw [g.1 ⟨u1, by rw [e1, map_add, map_ofNat]⟩, g.2.1 ⟨u2, by rw [e2, map_sub, map_pow, map_ofNat]⟩]

private theorem kap_one (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K) (L : IsLoc O Δ)
    (h : τ ^ 2 - 4 ≠ 0) (c : K) (d m : EL Δ τ) (H : ∀ t : Kˣ, lcount O c d ((t : K) • m) = one (t ∈ NE τ)) : kapSum O c d m = 1 := by
  unfold kapSum
  rw [finsum_eq_single _ (1 : Kˣ ⧸ NE τ)]
  · rw [H]
    have hmem : Quotient.out (1 : Kˣ ⧸ NE τ) ∈ NE τ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
    rw [(hsNE O K Δ τ L h _).mp hmem]
    simp [one, hmem]
  · intro t ht
    rw [H]
    have hnm : Quotient.out t ∉ NE τ := by
      intro hm
      apply ht
      rw [← QuotientGroup.out_eq' t]
      exact (QuotientGroup.eq_one_iff _).mpr hm
    simp [one, hnm]

private theorem ae_k {F : Type} [Field F] [NumberField F] {Δ : F} (D : Dat Δ) (hD : D.Ok) {τ c : F} {d m : EL Δ τ} (h : IsDat c d m) :
    ∀ᶠ v : Pl F in Filter.cofinite, kapSum (Ov v) (cv v c) (elmap (cv v) d) (elmap (cv v) m) = 1 := by
  filter_upwards [genPl F Δ D hD τ c d m h, D.Sg.eventually_cofinite_notMem] with v h1 h3
  exact kap_one _ _ _ _ (hD.off v h3) (loc_ne h.reg v) _ _ _ h1

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.basePt :
    UpperTheory.V.Z.Sym.Glob.BasePt := by
  intro F _ _ Δ D hD
  haveI := hD.real
  refine ⟨(-1 : ℝ) ^ Fintype.card (F →+* ℝ), ?_⟩
  intro τ hτ hspl hi
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
  let σ₀ : F →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w)
  have hreg : τ ^ 2 - 4 ≠ 0 := by
    intro h0
    have h' := hτ σ₀
    rw [h0, map_zero] at h'
    exact lt_irrefl _ h'
  have hΔ0 : Δ ≠ 0 := by
    intro h0
    have h' := hD.neg σ₀
    rw [h0, map_zero] at h'
    exact lt_irrefl _ h'
  have h2τ : 2 + τ ≠ 0 := two_add_ne hreg
  have two_ne : ∀ v : Pl F, (2 : Kv v) ≠ 0 := fun v => by
    have h' : cv v (2 : F) ≠ 0 := (map_ne_zero _).mpr two_ne_zero
    rwa [map_ofNat] at h'
  have hTb : ∀ σ : F →+* ℝ, σ τ ^ 2 < 4 := fun σ => by
    have h' := hτ σ
    rw [map_sub, map_pow, map_ofNat] at h'
    linarith
  by_cases hglob : ∃ lam : Lsq F Δ, QuadraticAlgebra.norm lam = 2 + τ
  · obtain ⟨lam0, hl0⟩ := hglob
    obtain ⟨lam, hl, htr⟩ : ∃ lam : Lsq F Δ, QuadraticAlgebra.norm lam = 2 + τ ∧
        2 + τ + QuadraticAlgebra.trace lam ≠ 0 := by
      by_cases h0 : 2 + τ + QuadraticAlgebra.trace lam0 = 0
      · refine ⟨-lam0, by rw [QuadraticAlgebra.norm_neg, hl0], ?_⟩
        rw [map_neg]
        intro h1
        apply h2τ
        linear_combination (h0 + h1) / 2
      · exact ⟨lam0, hl0, h0⟩
    refine ⟨dLam lam (toUnit (1 + ω)), 1,
      datLam F Δ τ 1 hreg one_ne_zero lam hl _ (unit_one_add hreg), posF_one hD.neg hτ, ?_⟩
    intro c hc hev
    have hc0 : c ≠ 0 := by
      intro h0
      have h' := hc σ₀
      rw [h0, map_zero] at h'
      exact lt_irrefl _ h'
    have hk : ∀ v ∉ D.Sg,
        kapSum (Ov v) (cv v c) (elmap (cv v) (dLam lam (toUnit (1 + ω)))) (elmap (cv v) (1 : EL Δ τ)) =
          hs (cv v (τ ^ 2 - 4)) (cv v (2 + τ + QuadraticAlgebra.trace lam)) *
            hs (cv v Δ) (cv v (2 + τ + QuadraticAlgebra.trace lam)) *
            hs (cv v (τ ^ 2 - 4)) (cv v (-c)) *
            gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + ω)) := by
      intro v hv
      have hl' := loc_ne hreg v
      rw [elmap_dLam (cv v) hreg hl' lam _ (unit_one_add hreg) _ (unit_one_add hl'), elmap_one]
      have hnorm : QuadraticAlgebra.norm (lmap (cv v) Δ lam) = 2 + cv v τ := by
        have e : QuadraticAlgebra.norm (lmap (cv v) Δ lam) = cv v (QuadraticAlgebra.norm lam) := by
          simp [QuadraticAlgebra.norm_def, lmap]
        rw [e, hl, map_add, map_ofNat]
      have htr' : QuadraticAlgebra.trace (lmap (cv v) Δ lam) = cv v (QuadraticAlgebra.trace lam) := by
        simp [QuadraticAlgebra.trace_def, lmap]
        left
        exact (map_ofNat (cv v) 2).symm
      have e2 : cv v (2 + τ + QuadraticAlgebra.trace lam) =
          2 + cv v τ + QuadraticAlgebra.trace (lmap (cv v) Δ lam) := by
        rw [htr', map_add, map_add, map_ofNat]
      have hX : 2 + cv v τ + QuadraticAlgebra.trace (lmap (cv v) Δ lam) ≠ 0 := by
        rw [← e2]
        exact (map_ne_zero _).mpr htr
      have hev' : EvenVal (Ov v) (cv v c * (2 - cv v τ)) := by
        have h' := hev v hv
        rwa [map_mul, map_sub, map_ofNat] at h'
      rw [kappa (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v hv) hl' (cv v c) hev' (lmap (cv v) Δ lam) hnorm hX
        _ (unit_one_add hl') (jstd (cv v τ)) (D.χ v) (jstd_tr _) (fun x x₀ hx => chiVal F Δ D hD v x x₀ hx)]
      rw [e2, map_neg, map_sub, map_pow, map_ofNat]
    have hS : ∀ v ∈ D.Sg, hs (cv v (τ ^ 2 - 4)) (cv v (2 + τ + QuadraticAlgebra.trace lam)) = 1 ∧
        hs (cv v Δ) (cv v (2 + τ + QuadraticAlgebra.trace lam)) = 1 ∧ hs (cv v (τ ^ 2 - 4)) (cv v (-c)) = 1 := by
      intro v hv
      have sq : IsSquare (cv v (τ ^ 2 - 4)) := by
        rw [map_sub, map_pow, map_ofNat]
        exact hspl v hv
      have n1 : cv v (τ ^ 2 - 4) ≠ 0 := (map_ne_zero _).mpr hreg
      have n2 : cv v Δ ≠ 0 := (map_ne_zero _).mpr hΔ0
      exact ⟨hs_sq (two_ne v) n1 sq _, hs_sq (two_ne v) n2 (hD.split v hv) _, hs_sq (two_ne v) n1 sq _⟩
    have rA := recip F (τ ^ 2 - 4) (2 + τ + QuadraticAlgebra.trace lam) hreg htr
    have rB := recip F Δ (2 + τ + QuadraticAlgebra.trace lam) hΔ0 htr
    have rC := recip F (τ ^ 2 - 4) (-c) hreg (neg_ne_zero.mpr hc0)
    rw [fp_mul D.Sg (fun v => hs (cv v (τ ^ 2 - 4)) (cv v (2 + τ + QuadraticAlgebra.trace lam)))
      (fun v => hs (cv v Δ) (cv v (2 + τ + QuadraticAlgebra.trace lam)))
      (fun v => hs (cv v (τ ^ 2 - 4)) (cv v (-c)))
      (fun v => gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + ω)))
      (fun v => kapSum (Ov v) (cv v c) (elmap (cv v) (dLam lam (toUnit (1 + ω)))) (elmap (cv v) (1 : EL Δ τ)))
      rA.1 rB.1 rC.1 (ae_g D hD hreg hi) hS hk]
    rw [rA.2, rB.2, rC.2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    have hloc : ∀ σ : F →+* ℝ, hs (σ (τ ^ 2 - 4)) (σ (2 + τ + QuadraticAlgebra.trace lam)) *
        hs (σ Δ) (σ (2 + τ + QuadraticAlgebra.trace lam)) * hs (σ (τ ^ 2 - 4)) (σ (-c)) = -1 := by
      intro σ
      have hn1 := hτ σ
      have hn2 := hD.neg σ
      have hcn : σ (-c) < 0 := by
        rw [map_neg]
        exact neg_neg_of_pos (hc σ)
      have hXn : σ (2 + τ + QuadraticAlgebra.trace lam) ≠ 0 := (map_ne_zero _).mpr htr
      rw [hs_neg _ _ hn1 hcn]
      rcases lt_or_gt_of_ne hXn with hlt | hgt
      · rw [hs_neg _ _ hn1 hlt, hs_neg _ _ hn2 hlt]
        ring
      · rw [hs_pos _ _ hgt, hs_pos _ _ hgt]
        ring
    rw [Finset.prod_congr rfl fun σ _ => hloc σ, Finset.prod_const, Finset.card_univ]
    unfold Dat.nK
    push_cast
    rfl
  · have hnot : hs Δ (2 + τ) ≠ 1 := fun h1 => hglob (hs_iff' Δ (2 + τ) h1)
    have hreal : ∀ σ : F →+* ℝ, hs (σ Δ) (σ (2 + τ)) = 1 := fun σ => by
      apply hs_pos
      rw [map_add, map_ofNat]
      nlinarith [hTb σ]
    obtain ⟨v, hv⟩ : ∃ v : Pl F, hs (cv v Δ) (cv v (2 + τ)) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hnot (hsHasse F Δ (2 + τ) hΔ0 h2τ hreal hcon)
    have hvS : v ∉ D.Sg := fun hvS => hv (hs_sq (two_ne v) ((map_ne_zero _).mpr hΔ0) (hD.split v hvS) _)
    have hnl : ¬ ∃ lam : Lsq (Kv v) (cv v Δ), QuadraticAlgebra.norm lam = 2 + cv v τ := by
      intro hex
      apply hv
      rw [map_add, map_ofNat]
      exact hs_iff _ _ hex
    obtain ⟨d, m, hdm, hpos⟩ := datEx F Δ D hD τ hτ hi
    refine ⟨d, m, hdm, hpos, ?_⟩
    intro c hc hev
    have hc0 : c ≠ 0 := by
      intro h0
      have h' := hc σ₀
      rw [h0, map_zero] at h'
      exact lt_irrefl _ h'
    have hdmc : IsDat c d m := ⟨hdm.reg, hc0, hdm.d_norm, hdm.m_unit, hdm.m_star, hdm.m_sig⟩
    have hloc := (modelMap F (Kv v) (cv v) Δ τ c d m hdmc).1
    have kz := kappaZero (Ov v) (Kv v) (cv v Δ) (cv v τ) (hD.off v hvS) (cv v c) _ _ hloc hnl
    have lhs : (∏ᶠ (u : Pl F) (_ : u ∉ D.Sg), kapSum (Ov u) (cv u c) (elmap (cv u) d) (elmap (cv u) m)) = 0 :=
      fp_zero D.Sg (fun u => kapSum (Ov u) (cv u c) (elmap (cv u) d) (elmap (cv u) m)) (ae_k D hD hdmc) v hvS kz.1
    have rhs : D.nK τ = 0 :=
      fp_zero D.Sg (fun u => gOrb (Ov u) (jstd (cv u τ)) (D.χ u) (toUnit (1 + ω))) (ae_g D hD hreg hi) v hvS
        (kz.2 (jstd (cv v τ)) (jstd_tr _) (D.χ v) (toUnit (1 + ω)) (unit_one_add (loc_ne hreg v)))
    rw [lhs, rhs, mul_zero]
