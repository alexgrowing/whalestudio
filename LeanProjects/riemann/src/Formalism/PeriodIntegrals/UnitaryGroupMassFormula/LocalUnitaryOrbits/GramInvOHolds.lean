import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

def oEvS : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)

theorem oEvS_fg : (oEvS (E := E) v).FG := by
  let g : 𝓞 E →+ (Fv F v ⊗[F] E) :=
    (inclR (F := F) (Fv F v)).toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom
  have hfg : (Submodule.map g.toIntLinearMap ⊤).FG := Submodule.FG.map _ Module.Finite.fg_top
  obtain ⟨t, ht⟩ := hfg
  have himg : (fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ =
      ↑(Submodule.map g.toIntLinearMap ⊤) := by
    ext y
    simp [g] <;> rfl
  refine ⟨t, ?_⟩
  unfold oEvS
  rw [himg, ← ht, Submodule.span_span_of_tower]

theorem oEv_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  exact Submodule.subset_span ⟨1, Set.mem_univ _, by simp⟩

theorem one_add_inv {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    ∃ m ∈ OEv (E := E) v, (1 + sc (E := E) v ϖ * x) * m = 1 := by
  have hϖi : ϖ ∈ v.adicCompletionIntegers F := by
    unfold IsUnif at hϖ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.coe_one,
      WithZero.coe_le_coe]
    show Multiplicative.ofAdd (-1 : ℤ) ≤ Multiplicative.ofAdd 0
    exact Multiplicative.ofAdd_le.mpr (by norm_num)
  have hsc : ∀ z : Fv F v ⊗[F] E,
      sc (E := E) v ϖ * z = (⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F) • z := by
    intro z
    unfold sc
    rw [Algebra.smul_def]
    rfl
  have hcomm : ∀ (r : v.adicCompletionIntegers F) (a b : Fv F v ⊗[F] E), a * (r • b) = r • (a * b) :=
    fun r a b => mul_smul_comm r a b
  let y := 1 + sc (E := E) v ϖ * x
  let N' : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Submodule.span (v.adicCompletionIntegers F) ((fun m => y * m) '' (OEv (E := E) v))
  have hN'sub : ∀ z ∈ N', ∃ m ∈ OEv (E := E) v, z = y * m := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, hm, rfl⟩ := hz
      exact ⟨m, hm, rfl⟩
    | zero => exact ⟨0, oEv_zero v, (mul_zero y).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨m1, hm1, rfl⟩ := ha
      obtain ⟨m2, hm2, rfl⟩ := hb
      exact ⟨m1 + m2, oEv_add v hm1 hm2, (mul_add y m1 m2).symm⟩
    | smul r a _ ha =>
      obtain ⟨m, hm, rfl⟩ := ha
      refine ⟨r • m, ?_, (hcomm r y m).symm⟩
      unfold OEv at hm ⊢
      exact Submodule.smul_mem _ r hm
  have hle : oEvS (E := E) v ≤ N' := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (oEvS_fg v)
      (IsLocalRing.maximalIdeal_le_jacobson _)
    intro m hm
    have hm' : m ∈ OEv (E := E) v := hm
    have hxm : x * m ∈ oEvS (E := E) v := oEv_mul v hx hm'
    have h1 : y * m ∈ N' := Submodule.subset_span ⟨m, hm', rfl⟩
    have h2 : (-(⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F)) • (x * m) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • oEvS (E := E) v := by
      apply Submodule.smul_mem_smul _ hxm
      apply neg_mem
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have hmul := congrArg (fun z : v.adicCompletionIntegers F => Valued.v (z : Fv F v)) u.mul_inv
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one, map_mul, map_one] at hmul
      have hui : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) ≤ 1 :=
        (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u⁻¹ : (v.adicCompletionIntegers F)ˣ).1.2
      rw [hu] at hmul
      unfold IsUnif at hϖ
      change Valued.v ϖ * _ = 1 at hmul
      rw [hϖ] at hmul
      have hlt : (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
        rw [← WithZero.coe_one, WithZero.coe_lt_coe]
        show Multiplicative.ofAdd (-1 : ℤ) < Multiplicative.ofAdd 0
        exact Multiplicative.ofAdd_lt.mpr (by norm_num)
      have hcon : (1 : WithZero (Multiplicative ℤ)) ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
        calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
          _ ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) * 1 := by gcongr
          _ = _ := mul_one _
      exact absurd hcon (not_le.mpr hlt)
    have hdecomp : m = y * m + (-(⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F)) • (x * m) := by
      rw [neg_smul, ← hsc]
      simp only [y]
      ring
    rw [hdecomp]
    exact Submodule.add_mem_sup h1 h2
  have h1 : (1 : Fv F v ⊗[F] E) ∈ N' := hle (oEv_one v)
  obtain ⟨m, hm, hm1⟩ := hN'sub 1 h1
  exact ⟨m, hm, hm1.symm⟩

section Main

variable (Λ : Set (Fin n → E)) (ψ : AddChar (AF F) ℂ)

def oEvR : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oEv_mul v
  one_mem' := oEv_one v
  add_mem' := oEv_add v
  zero_mem' := oEv_zero v
  neg_mem' := oEv_neg v

theorem det_sub_mem {a : ℕ} {ϖ : Fv F v} (hint : ϖ ∈ v.adicCompletionIntegers F)
    (A B : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ OEv (E := E) v)
    (hB : ∀ i j, B i j ∈ OEv (E := E) v) (hAB : ∀ i j, A i j - B i j ∈ PO (E := E) v ϖ) :
    A.det - B.det ∈ PO (E := E) v ϖ := by
  have hsc : sc (E := E) v ϖ ∈ OEv (E := E) v := by
    have h1 := oEv_one (E := E) v
    unfold OEv at h1 ⊢
    have h2 := Submodule.smul_mem _ (⟨ϖ, hint⟩ : v.adicCompletionIntegers F) h1
    convert h2 using 1
    simp [sc, Algebra.smul_def, Algebra.TensorProduct.one_def]
  let A' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨B i j, hB i j⟩
  let s : oEvR (E := E) v := ⟨sc (E := E) v ϖ, hsc⟩
  have hdA : ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = A.det := by
    calc ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = (oEvR (E := E) v).subtype A'.det := rfl
      _ = ((oEvR (E := E) v).subtype.mapMatrix A').det := RingHom.map_det _ _
      _ = A.det := rfl
  have hdB : ((B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = B.det := by
    calc ((B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) = (oEvR (E := E) v).subtype B'.det := rfl
      _ = ((oEvR (E := E) v).subtype.mapMatrix B').det := RingHom.map_det _ _
      _ = B.det := rfl
  have hmem : A'.det - B'.det ∈ Ideal.span {s} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨c, hc, hceq⟩ := hAB i j
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    show c * sc (E := E) v ϖ = A i j - B i j
    rw [hceq, mul_comm]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  show ∃ c ∈ OEv (E := E) v, A.det - B.det = sc (E := E) v ϖ * c
  refine ⟨b, b.2, ?_⟩
  rw [← hdA, ← hdB]
  calc ((A'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) - B'.det
      = ((A'.det - B'.det : oEvR (E := E) v) : Fv F v ⊗[F] E) := rfl
    _ = ((b * s : oEvR (E := E) v) : Fv F v ⊗[F] E) := by rw [hb]
    _ = sc (E := E) v ϖ * b := by
      show (b : Fv F v ⊗[F] E) * sc (E := E) v ϖ = _
      exact mul_comm _ _

theorem gramInvO_holds (a : ℕ) (Y : TupV (E := E) v n a) : GramInvO σ J v Λ ψ a Y := by
  intro hG ϖ hϖ y hy hd
  unfold GoodY at hG
  have hSD := hG.2.2.1
  have hy' : ∀ i, y i ∈ latLoc (E := E) v Λ := hy
  have hϖi : ϖ ∈ v.adicCompletionIntegers F := by
    unfold IsUnif at hϖ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖ, ← WithZero.coe_one,
      WithZero.coe_le_coe]
    show Multiplicative.ofAdd (-1 : ℤ) ≤ Multiplicative.ofAdd 0
    exact Multiplicative.ofAdd_le.mpr (by norm_num)
  have hsc : sc (E := E) v ϖ ∈ OEv (E := E) v := by
    have h1 := oEv_one (E := E) v
    unfold OEv at h1 ⊢
    have h2 := Submodule.smul_mem _ (⟨ϖ, hϖi⟩ : v.adicCompletionIntegers F) h1
    convert h2 using 1
    simp [sc, Algebra.smul_def, Algebra.TensorProduct.one_def]
  have hyI : ∀ i j, gramR (Fv F v) σ J y i j ∈ OEv (E := E) v := fun i j =>
    hR_mem_oEv (σ := σ) (J := J) (v := v) (Λ := Λ) hSD (hy' i) (hy' j)
  have hYI : ∀ i j, gramR (Fv F v) σ J Y i j ∈ OEv (E := E) v := by
    intro i j
    obtain ⟨c, hc, hceq⟩ := hd i j
    have e : gramR (Fv F v) σ J Y i j = gramR (Fv F v) σ J y i j + -(sc (E := E) v ϖ * c) := by
      rw [← hceq]
      ring
    rw [e]
    exact oEv_add v (hyI i j) (oEv_neg v (oEv_mul v hsc hc))
  obtain ⟨w, hw, -, hdw⟩ := hG.2.2.2.2.2.2
  obtain ⟨c, hc, hceq⟩ := det_sub_mem v hϖi (gramR (Fv F v) σ J y) (gramR (Fv F v) σ J Y) hyI hYI hd
  have hwc : w * c ∈ OEv (E := E) v := oEv_mul v hw hc
  obtain ⟨m, hm, hm1⟩ := one_add_inv v hϖ hwc
  have e1 : (gramR (Fv F v) σ J y).det =
      (gramR (Fv F v) σ J Y).det + sc (E := E) v ϖ * c := by
    rw [← hceq]
    ring
  have e2 : (gramR (Fv F v) σ J y).det =
      (gramR (Fv F v) σ J Y).det * (1 + sc (E := E) v ϖ * (w * c)) := by
    linear_combination e1 - (sc (E := E) v ϖ * c) * hdw
  have hdy1 : (m * w) * (gramR (Fv F v) σ J y).det = 1 := by
    calc (m * w) * (gramR (Fv F v) σ J y).det
        = (gramR (Fv F v) σ J Y).det * w * ((1 + sc (E := E) v ϖ * (w * c)) * m) := by
          rw [e2]
          ring
      _ = 1 := by rw [hdw, hm1, one_mul]
  let A' : Matrix (Fin a) (Fin a) (oEvR (E := E) v) := fun i j => ⟨gramR (Fv F v) σ J y i j, hyI i j⟩
  have hadj : ∀ i j, (gramR (Fv F v) σ J y).adjugate i j ∈ OEv (E := E) v := by
    intro i j
    have e : (gramR (Fv F v) σ J y).adjugate = (oEvR (E := E) v).subtype.mapMatrix A'.adjugate := by
      rw [RingHom.map_adjugate]
      rfl
    rw [e]
    exact (A'.adjugate i j).2
  refine ⟨(m * w) • (gramR (Fv F v) σ J y).adjugate, fun i j => ?_, ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact oEv_mul v (oEv_mul v hm hw) (hadj i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hdy1, one_smul]

end Main

end PI.OmLocU
