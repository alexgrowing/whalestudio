import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal TensorProduct

namespace GlobalTheory.CovHt.Link.DegreePolynomialContinuity
variable {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F}

theorem one_tmul_int (z : ℤ) (y : Y.Dv) : ((z : ℚ) ⊗ₜ[ℤ] y) = (1 : ℚ) ⊗ₜ[ℤ] (z • y) := by
  rw [← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]

theorem exists_int_eq (A : Adl C Y) (L b : Y.Dv) {r : ℚ} (hr : 0 < r)
    (h : qDiv A = (1 : ℚ) ⊗ₜ[ℤ] L - r ⊗ₜ[ℤ] b) :
    ∃ M a e : ℤ, 0 < M ∧ 0 < a ∧ (e : ℚ) / a = -r ∧ (a : ℚ) = M * ((A.n : ℕ) : ℚ) ∧ M • A.D = a • L + e • b := by
  set n : ℕ := (A.n : ℕ) with hn
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  have hd0 : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
  have e1 := congrArg (((r.den * n : ℕ) : ℚ) • ·) h
  simp only [qDiv, smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at e1
  have h1 : ((r.den * n : ℕ) : ℚ) * (n : ℚ)⁻¹ = ((r.den : ℤ) : ℚ) := by push_cast; field_simp
  have h2 : ((r.den * n : ℕ) : ℚ) = ((r.den * n : ℤ) : ℚ) := by push_cast; ring
  have h3 : ((r.den * n : ℕ) : ℚ) * r = ((r.num * n : ℤ) : ℚ) := by
    push_cast; rw [mul_comm, ← mul_assoc, Rat.mul_den_eq_num]
  rw [← hn, h1, h3, h2, one_tmul_int, one_tmul_int, one_tmul_int, ← TensorProduct.tmul_sub] at e1
  obtain ⟨q, hq, hq'⟩ := (one_tmul_eq_iff).1 e1
  refine ⟨q * r.den, q * (r.den * n), -(q * (r.num * n)), by positivity, by positivity, ?_, ?_, ?_⟩
  · push_cast
    rw [neg_div, neg_inj]
    field_simp
    rw [mul_comm, Rat.mul_den_eq_num]
  · push_cast; ring
  · rw [← natCast_zsmul, ← natCast_zsmul] at hq'
    rw [mul_smul, hq', smul_sub, ← mul_smul, ← mul_smul, neg_smul, ← sub_eq_add_neg]

variable (Y) in

noncomputable def degPoly (L b : Y.Dv) (x : ℝ) : ℝ :=
  ∑ S : Finset (Fin Y.dim), (∏ i, if i ∈ S then (1 : ℝ) else x) * (Y.inter (S.piecewise (fun _ => L) (fun _ => b)) : ℝ)

theorem inter_add_smul (L b : Y.Dv) (a e : ℤ) :
    (Y.inter (fun _ => a • L + e • b) : ℝ) = ∑ S : Finset (Fin Y.dim),
      (∏ i, if i ∈ S then (a : ℝ) else e) * (Y.inter (S.piecewise (fun _ => L) (fun _ => b)) : ℝ) := by
  have := Y.interForm.map_add_univ (fun _ => a • L) (fun _ => e • b)
  simp only [Var.interForm_apply] at this
  rw [show (fun _ : Fin Y.dim => a • L + e • b) = (fun _ => a • L) + (fun _ => e • b) from rfl, this]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  have hp : S.piecewise (fun _ => a • L) (fun _ => e • b) =
      fun i => (if i ∈ S then a else e) • S.piecewise (fun _ => L) (fun _ => b) i := by
    funext i; by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi]
  rw [hp, Var.inter_zsmul]
  push_cast
  congr 1

theorem deg_eq_degPoly (A : Adl C Y) (L b : Y.Dv) {M a e : ℤ} (hM0 : 0 < M) (ha : 0 < a)
    (han : (a : ℚ) = M * ((A.n : ℕ) : ℚ)) (hM : M • A.D = a • L + e • b) :
    A.deg = degPoly Y L b ((e : ℝ) / a) := by
  have e1 : (Y.inter (fun _ => M • A.D) : ℝ) = (M : ℝ) ^ Y.dim * Y.inter fun _ => A.D := by
    have := Y.inter_zsmul (fun _ => M) (fun _ => A.D)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  rw [hM, inter_add_smul] at e1
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have key : ∀ S : Finset (Fin Y.dim), (∏ i, if i ∈ S then (1 : ℝ) else (e : ℝ) / a) =
      (∏ i, if i ∈ S then (a : ℝ) else e) / (a : ℝ) ^ Y.dim := by
    intro S
    rw [show (a : ℝ) ^ Y.dim = ∏ _i : Fin Y.dim, (a : ℝ) by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · exact (div_self ha').symm
    · rfl
  have han' : (a : ℝ) = M * ((A.n : ℕ) : ℝ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) han
  unfold Adl.deg degPoly
  simp_rw [key, div_mul_eq_mul_div]
  rw [← Finset.sum_div, e1, han', mul_pow]
  have hM' : (M : ℝ) ^ Y.dim ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM0.ne')
  have hn' : ((A.n : ℕ) : ℝ) ^ Y.dim ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 A.n.ne_zero)
  rw [mul_div_mul_left _ _ hM']

theorem continuous_degPoly (L b : Y.Dv) : Continuous (degPoly Y L b) :=
  continuous_finset_sum _ fun S _ => (continuous_finset_prod _ fun i _ =>
    continuous_const.if_const _ continuous_id).mul continuous_const

theorem degPoly_zero (L b : Y.Dv) : degPoly Y L b 0 = (Y.inter fun _ => L : ℝ) := by
  unfold degPoly
  rw [Finset.sum_eq_single Finset.univ]
  · simp [Finset.piecewise_univ]
  · intro S _ hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra hc
      push_neg at hc
      exact hS (Finset.eq_univ_of_forall hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_mul]
  · simp

theorem tendsto_cast_zero : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  simpa using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds

theorem cast_div_eq {r : ℚ} {a e : ℤ} (hea : (e : ℚ) / a = -r) : (e : ℝ) / a = -(r : ℝ) := by
  have := congrArg (Rat.cast : ℚ → ℝ) hea
  push_cast at this
  exact this

theorem tendsto_deg (f : ℚ → Adl C Y) (L b : Y.Dv)
    (h : ∀ r : ℚ, 0 < r → qDiv (f r) = (1 : ℚ) ⊗ₜ[ℤ] L - r ⊗ₜ[ℤ] b) :
    Tendsto (fun r => (f r).deg) (𝓝[>] 0) (𝓝 (Y.inter fun _ => L : ℝ)) := by
  have hneg : Tendsto (fun r : ℚ => -(r : ℝ)) (𝓝[>] 0) (𝓝 0) := by simpa using tendsto_cast_zero.neg
  have := ((continuous_degPoly L b).tendsto 0).comp hneg
  rw [degPoly_zero] at this
  refine this.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
  obtain ⟨M, a, e, hM0, ha, hea, han, hM⟩ := exists_int_eq (f r) L b hr (h r hr)
  show degPoly Y L b (-(r : ℝ)) = (f r).deg
  rw [deg_eq_degPoly (f r) L b hM0 ha han hM, cast_div_eq hea]

theorem nef_of_eventually (f : ℚ → Adl C Y) (L b : Y.Dv)
    (h : ∀ r : ℚ, 0 < r → qDiv (f r) = (1 : ℚ) ⊗ₜ[ℤ] L - r ⊗ₜ[ℤ] b)
    (hn : ∀ᶠ r : ℚ in 𝓝[>] 0, Y.nef (f r).D) : Y.nef L := by
  refine Var.nef_iff.2 fun Z hZ => ?_
  have hle : ∀ᶠ r : ℚ in 𝓝[>] 0, (r : ℝ) * (Y.deg Z b : ℝ) ≤ (Y.deg Z L : ℝ) := by
    filter_upwards [hn, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
    obtain ⟨M, a, e, hM0, ha, hea, han, hM⟩ := exists_int_eq (f r) L b hr0 (h r hr0)
    have h1 := Var.nef_iff.1 hr Z hZ
    have h2 : Y.deg Z (M • (f r).D) = M * Y.deg Z (f r).D := hZ.deg_zsmul M _
    rw [hM, hZ.deg_add, hZ.deg_zsmul, hZ.deg_zsmul] at h2
    have h3 : (0 : ℝ) ≤ (a : ℝ) * Y.deg Z L + (e : ℝ) * Y.deg Z b := by
      have : (0 : ℤ) ≤ a * Y.deg Z L + e * Y.deg Z b := h2 ▸ mul_nonneg hM0.le h1
      exact_mod_cast this
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hea' : (e : ℝ) = -(r : ℝ) * a := by
      rw [← cast_div_eq hea]; field_simp
    rw [hea'] at h3
    have h4 : (0 : ℝ) ≤ (a : ℝ) * ((Y.deg Z L : ℝ) - r * Y.deg Z b) := by linarith
    exact sub_nonneg.1 ((mul_nonneg_iff_of_pos_left haR).1 h4)
  have ht : Tendsto (fun r : ℚ => (r : ℝ) * (Y.deg Z b : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_cast_zero.mul_const (Y.deg Z b : ℝ)
  exact_mod_cast le_of_tendsto ht hle

end GlobalTheory.CovHt.Link.DegreePolynomialContinuity

namespace GlobalTheory.CovHt.Link.DegreePolynomialContinuity

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j)

theorem exOf_rootLetter (L : CmList A) (u : AllWt.Weight S.Dw) (x : DV.Rt D.what₂.Tau N) :
    AllWt.exOf S.Dw u 0 (some (RootSum.rootLetter S x)) =
      (if (x.2 : ℕ) < S.Dw.p then 1 else -1) * u (L.ψ x.1) (Fin.cast S.rank_eq.symm x.2) := by
  have hr := S.rank_eq
  have hx := x.2.2
  have hψ : L.ψ x.1 = ⟨DV.tauEmb D x.1, A.cm x.1⟩ := Subtype.ext (L.ψ_val x.1)
  by_cases h : (x.2 : ℕ) < S.Dw.p
  · rw [RootSum.rootLetter, dif_pos h, if_pos h]
    rw [hψ, one_mul]
    simp only [AllWt.exOf, exZ]
    unfold AllWt.wtOf
    dsimp only
    rw [dif_pos (A.cm x.1), dif_pos h, sub_zero]
    rfl
  · rw [RootSum.rootLetter, dif_neg h, if_neg h]
    have h' : conjEmb (conjEmb (DV.tauEmb D x.1)) (A.H.rt : D.host.E) = A.H.rt0 := by
      rw [RootSum.conjEmb_conjEmb']; exact A.cm x.1
    have hi : S.Dw.p + S.Dw.q - 1 - (x.2 : ℕ) < S.Dw.q := by omega
    simp only [AllWt.exOf, exZ]
    unfold AllWt.wtOf
    dsimp only
    rw [dif_neg (RootSum.conj_tau_ne x.1), dif_pos h', dif_pos hi, sub_zero, neg_one_mul, neg_inj]
    congr 1
    · exact Subtype.ext ((RootSum.conjEmb_conjEmb' _).trans (L.ψ_val x.1).symm)
    · exact Fin.ext (by simp only [Fin.val_cast]; omega)

variable {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp)

theorem qL_wtR (L : CmList A) (u : AllWt.Weight S.Dw) :
    qL Φ k (fun τ i => ((u (L.ψ τ) (Fin.cast S.rank_eq.symm i) : ℤ) : ℚ)) = (1 : ℚ) ⊗ₜ[ℤ] (Φ.C k).Lw u := by
  rw [← DeKeyTrue.divOf_neg_exOf, divOf, qL,
    ← (Equiv.ofBijective _ (RootSum.rootLetter_bijective S)).sum_comp]
  simp only [Equiv.ofBijective_apply, TensorProduct.tmul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RootSum.divOf_root, exOf_rootLetter S L, one_tmul_int, ← TensorProduct.tmul_neg, smul_smul, ← neg_smul,
    mul_comm]
  split_ifs <;> simp

theorem qDiv_mbarOf_wtR {x : ToroidalCompactificationData s} (P : Mean4O.PolOf x Φ) (B : ℝ) (L : CmList A) (u : AllWt.Weight S.Dw)
    {r : ℚ} (hr : 0 < r) :
    qDiv (mbarOf P B (wtR L u) r k) = (1 : ℚ) ⊗ₜ[ℤ] (Φ.C k).Lw u - r ⊗ₜ[ℤ] P.bd k := by
  have e : wtR L u = fun τ i => (((u (L.ψ τ) (Fin.cast S.rank_eq.symm i) : ℤ) : ℚ) : ℝ) := by
    funext τ i; simp [wtR]
  rw [e, mbarOf_cast P B _ hr, PolDat.qDiv_mbarQ, qL_wtR]

end GlobalTheory.CovHt.Link.DegreePolynomialContinuity

namespace GlobalTheory.CovHt.Link

theorem tendsto_deg_mbarOf_and_nef : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (k : s.Comp), Tendsto (fun r : ℚ => (mbarOf P B (wtR L u) r k).deg) (𝓝[>] 0) (𝓝 ((Φ.C k).Y.inter fun _ => (Φ.C k).Lw u : ℝ)) ∧ ((∀ᶠ r : ℚ in 𝓝[>] 0, (Φ.C k).Y.nef (mbarOf P B (wtR L u) r k).D) → (Φ.C k).Y.nef ((Φ.C k).Lw u)) := by
  intro D A N j S κ s Φ L x P B u k
  have h := fun (r : ℚ) (hr : 0 < r) => DegreePolynomialContinuity.qDiv_mbarOf_wtR S Φ k P B L u hr
  exact ⟨DegreePolynomialContinuity.tendsto_deg _ _ _ h, DegreePolynomialContinuity.nef_of_eventually _ _ _ h⟩

end GlobalTheory.CovHt.Link
