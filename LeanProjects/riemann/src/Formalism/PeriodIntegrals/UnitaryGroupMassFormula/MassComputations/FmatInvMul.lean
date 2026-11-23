import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MassDataMassesW.NLev

section Grp

variable {I : AutInst}

theorem Kset_Lf {x : I.Gf} (hx : x ∈ I.Kset) : ∀ v ∈ I.Lf, I.fmat x *ᵥ v ∈ I.Lf := by
  intro v hv
  have h : ∀ w, w ∈ I.Lf ↔ I.fmat x *ᵥ w ∈ I.Lf := hx
  exact (h v).1 hv

theorem Kset_inv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [InvMemClass.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem Kset_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  show ((x * y : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [MulMemClass.coe_mul]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.inv_mul]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.mul_inv]

def Tm (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v : VA I) : VA I :=
  Ai *ᵥ ((By - 1) *ᵥ (A *ᵥ v))

theorem Tm_add (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v + w) = Tm Ai By A v + Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_add]

theorem Tm_sub (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v - w) = Tm Ai By A v - Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_sub]

theorem Tm_smul (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (r : I.E ⊗[I.F] Af I.F) (v : VA I) :
    Tm Ai By A (r • v) = r • Tm Ai By A v := by
  simp only [Tm, Matrix.mulVec_smul]

theorem sub_one_Lf {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ v ∈ I.Lf, M *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, (M - 1) *ᵥ v ∈ I.Lf := by
  intro v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem (hM v hv) hv

theorem Tm_Lf {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf)
    (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, Tm Ai By A v ∈ I.Lf :=
  fun v hv => hAi _ (sub_one_Lf hBy _ (hA v hv))

theorem Tm_mL (m : ℕ) {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf) (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ mL I m, Tm Ai By A v ∈ mL I m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Tm_smul]
    exact Submodule.subset_span ⟨_, Tm_Lf hAi hBy hA x hx, rfl⟩
  | zero =>
    have h0 : Tm Ai By A 0 = 0 := by simp [Tm]
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Tm_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h1 : Tm Ai By A (a • x) = a • Tm Ai By A x := by
      rw [Subring.smul_def, Subring.smul_def, Tm_smul]
    rw [h1]
    exact Submodule.smul_mem _ a hx

end Grp

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sig_eq : (starRingEnd X.B.I.E) = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
  first
  | rfl
  | exact RingHom.ext fun _ => rfl

theorem hA_e_f (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.eX a) (X.fY b)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b))) = _
  rw [h, X.ef]
  split_ifs <;> simp

theorem hA_f_e (b a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.fY b) (X.eX a)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
  rw [h, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem key {c d : ℕ} (hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    {s : Set (Fin D.R.rS)} {w : VA X.B.I}
    (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
    (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
    ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
      Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
  classical
  obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
  have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
      ∑ b, l b • incl X.B.I (X.eR b) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _
  rw [hsum] at hdw ⊢
  have hcoef : ∀ b, ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
    intro b
    have h := hA_int X.B.I _ (hfL b) _ hdw
    rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
    simp only [hA_smul_right, hA_f_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    convert h using 1
    push_cast; ring
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : l b = 0
  · rw [hb, zero_smul, smul_zero]; exact zero_mem _
  have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
  have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
    rw [← smul_sub, ← smul_sub, sub_sub_cancel]
    simp only [smul_smul]
    congr 1; push_cast; ring
  rw [heq]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
  exact sm X.B.I (hcoef b) (sm X.B.I (natCast_int X.B.I c) (Submodule.subset_span ⟨b, hbs, rfl⟩))

theorem mults (u : D.what₂.Word) : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g) ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) ∧
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
      mL X.B.I X.B.g := by
  have h1 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.eR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).1
  have h2 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).2
  have h3 : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
        mL X.B.I X.B.g := X.xu_z u
  choose ce hce1 hce2 using h1
  choose cf hcf1 hcf2 using h2
  obtain ⟨cz, hcz1, hcz2⟩ := h3
  have hP : ∀ b, ce b * cf b ∣ ∏ a, ce a * cf a := fun b =>
    Finset.dvd_prod_of_mem (fun a => ce a * cf a) (Finset.mem_univ b)
  have hcop : Nat.Coprime ((∏ a, ce a * cf a) * cz) X.B.g :=
    Nat.Coprime.mul (Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul (hce1 a) (hcf1 a)) hcz1
  have hd1 : ∀ b, ce b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro (cf b) rfl).trans (hP b)) cz
  have hd2 : ∀ b, cf b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro_left (ce b) rfl).trans (hP b)) cz
  have hd3 : cz ∣ (∏ a, ce a * cf a) * cz := Dvd.intro_left _ rfl
  exact ⟨(∏ a, ce a * cf a) * cz, hcop, fun b => dvd_smul X.B.I (hd1 b) (hce2 b),
    fun b => dvd_smul X.B.I (hd2 b) (hcf2 b), dvd_smul X.B.I hd3 hcz2⟩

end MassDataMassesW.NLev
