import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TranslationZeroModeLift

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

def ucL (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : X.L →ₗ[ℤ] Vsp X.dim :=
  (AddMonoidHom.mk' (fun γ : X.L => uc (IR I) (γ : Vsp X.dim))
    (fun a b => by simp only [Submodule.coe_add]; exact uc_add _ _)).toIntLinearMap

theorem NIp_le_ker (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : NIp X I ≤ LinearMap.ker (ucL X I) := by
  intro x hx
  rw [LinearMap.mem_ker]
  exact uc_Ip hx

def uQ (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Qc X I →ₗ[ℤ] Vsp X.dim :=
  (NIp X I).liftQ (ucL X I) (NIp_le_ker X I)

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)}

theorem uQ_mk (γ : X.L) : uQ X I (Submodule.Quotient.mk γ) = uc (IR I) (γ : Vsp X.dim) := rfl

theorem uQ_out (c : Qc X I) : uQ X I c = uc (IR I) ((Quotient.out c : X.L) : Vsp X.dim) := by
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  calc uQ X I c = uQ X I (Submodule.Quotient.mk (Quotient.out c)) := by rw [e]
    _ = _ := uQ_mk _

theorem uQ_mem (c : Qc X I) : uQ X I c ∈ IR I := by
  rw [uQ_out]
  exact uc_mem _ _

theorem uQ_eq_zero {c : Qc X I} (h : uQ X I c = 0) : c = 0 := by
  have hγ : ((Quotient.out c : X.L) : Vsp X.dim) ∈ Ip X I := by
    rw [mem_Ip]
    refine ⟨(Quotient.out c).2, fun a ha => ?_⟩
    rw [← inner_uc (IR I) _ a (Submodule.subset_span ha), ← uQ_out, h, inner_zero_left]
  have e : (Submodule.Quotient.mk (Quotient.out c) : Qc X I) = c := Quotient.out_eq c
  rw [← e]
  exact (Submodule.Quotient.mk_eq_zero _).2 hγ

variable {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem uQ_sep {c : Qc X I} (h : c ≠ 0) : b0 (E := E) P.q P.R0 ≤ ‖uQ X I c‖ ^ 2 := by
  have hne : uQ X I c ≠ 0 := fun h0 => h (uQ_eq_zero h0)
  rw [uQ_out] at hne ⊢
  exact hI.sep _ (Quotient.out c).2 _ (isU_uc _) hne

theorem uQ_dist {c c' : Qc X I} (h : c ≠ c') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uQ X I c) (uQ X I c') := by
  have h1 := uQ_sep hI (sub_ne_zero.2 h)
  rw [dist_eq_norm, ← map_sub, ← Real.sqrt_sq (norm_nonneg (uQ X I (c - c')))]
  exact Real.sqrt_le_sqrt h1

theorem tailQ (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (a : ℝ) (ha : 0 < a)
    (hcond : (dK (IR I) : ℝ) + 1 ≤ a * P.q * b0 (E := E) P.q P.R0) :
    Summable (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
        Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2)) ∧
      ∑' c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, Real.exp (-(a * P.q) * ‖uQ X I c‖ ^ 2) ≤
        2 * 3 ^ (dK (IR I)) * Real.exp (-(a * P.q * b0 (E := E) P.q P.R0)) := by
  classical
  obtain ⟨ρ, -, hρ⟩ := hI.rank
  have hdK : dK (IR I) = 2 * (PT.f E * ρ) := by
    show Module.finrank ℝ (IR I) = 2 * (PT.f E * ρ)
    rw [hρ]; ring
  have hb0 : 0 < b0 (E := E) P.q P.R0 := cutoff_pos P
  have haqb : 0 < a * P.q * b0 (E := E) P.q P.R0 := by
    have : (0 : ℝ) ≤ dK (IR I) := Nat.cast_nonneg _
    linarith
  have haq : 0 < a * (P.q : ℝ) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [haqb, hb0, hneg]
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (a * P.q) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.sqrt_pos.2 haq
  have hs2 : s ^ 2 = a * P.q := by rw [hs_def]; exact Real.sq_sqrt haq.le
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = Real.sqrt (b0 (E := E) P.q P.R0) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ Real.sqrt_pos.2 hb0
  have hδ2 : δ ^ 2 = b0 (E := E) P.q P.R0 := by rw [hδ_def]; exact Real.sq_sqrt hb0.le
  have h4s : 0 < 4 * s := by positivity
  have hr0pos : 0 < 4 * s * δ := by positivity
  have hnorm : ∀ c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))}, δ ≤ ‖uQ X I c.1‖ := by
    intro c
    have hc : c.1 ≠ 0 := by simpa using c.2
    rw [hδ_def, ← Real.sqrt_sq (norm_nonneg (uQ X I c.1))]
    exact Real.sqrt_le_sqrt (uQ_sep hI hc)
  have hinj : Function.Injective
      (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} => uQ X I c.1) := by
    intro c c' hcc
    apply Subtype.ext
    have h0 : uQ X I (c.1 - c'.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hcc
    exact sub_eq_zero.1 (uQ_eq_zero h0)
  have key := hA {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} (fun c => 4 * s * ‖uQ X I c.1‖)
    (PT.f E * ρ) (4 * s * δ) hr0pos
    (by
      have e1 : (4 * s * δ) ^ 2 = 16 * (a * P.q * b0 (E := E) P.q P.R0) := by
        rw [mul_pow, mul_pow, hs2, hδ2]; ring
      have e2 : (dK (IR I) : ℝ) = 2 * ((PT.f E * ρ : ℕ) : ℝ) := by rw [hdK]; push_cast; ring
      rw [e1]; rw [e2] at hcond; linarith)
    (fun c => mul_le_mul_of_nonneg_left (hnorm c) h4s.le)
    (by
      intro R hR S hS
      have hcard : (S.image fun c => uQ X I c.1).card = S.card := Finset.card_image_of_injective _ hinj
      have hpk := pack_K hP (IR I) (S.image fun c => uQ X I c.1)
        (by
          intro u hu
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          exact uQ_mem c.1) δ (R / (4 * s)) hδ
        (by
          rw [le_div_iff₀ h4s]
          calc δ * (4 * s) = 4 * s * δ := by ring
            _ ≤ R := hR)
        (by
          intro u hu
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hu
          rw [le_div_iff₀ h4s]
          calc ‖uQ X I c.1‖ * (4 * s) = 4 * s * ‖uQ X I c.1‖ := by ring
            _ ≤ R := hS c hc)
        (by
          intro u hu v hv huv
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hu
          obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hv
          have hcc : c.1 ≠ c'.1 := fun e => huv (by simp only [e])
          rw [hδ_def]
          exact uQ_dist hI hcc)
      have e3 : 3 * (R / (4 * s)) / δ = 3 * R / (4 * s * δ) := by
        field_simp
      rw [e3, hdK, hcard] at hpk
      exact hpk)
  have hfun : (fun c : {c : Qc X I // c ∉ ({0} : Finset (Qc X I))} =>
      Real.exp (-(4 * s * ‖uQ X I c.1‖) ^ 2 / 16)) =
      fun c => Real.exp (-(a * P.q) * ‖uQ X I c.1‖ ^ 2) := by
    funext c
    congr 1
    rw [mul_pow, mul_pow, hs2]; ring
  have e9 : (9 : ℝ) ^ (PT.f E * ρ) = 3 ^ (dK (IR I)) := by rw [hdK, pow_mul (3 : ℝ) 2 (PT.f E * ρ)]; norm_num
  have er : -(4 * s * δ) ^ 2 / 16 = -(a * P.q * b0 (E := E) P.q P.R0) := by
    rw [mul_pow, mul_pow, hs2, hδ2]; ring
  rw [hfun, e9, er] at key
  exact key

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
