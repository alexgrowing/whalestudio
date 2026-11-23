import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsUnitDetLeviM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.Transp

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  PI.UnitaryDimensionFormula.unitaryCongruence PI.UnitaryDimensionFormula.NormCutK

namespace PI.UnitaryDimensionFormula.FrameX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def E1 (e : Af X.B.I.F) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e

theorem idempotent_mul_self {e : Af X.B.I.F} (he : e * e = e) : E1 X e * E1 X e = E1 X e := by
  unfold E1; rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he]

theorem idempotent_conj_fixed (e : Af X.B.I.F) : sigA X.B.I (E1 X e) = E1 X e := by
  unfold E1; rw [sigA_tmul, star_one]

theorem tmul_int {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) :
    (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Or.inr ⟨⟨e, he⟩, rfl⟩)

theorem integral_circleChar {e : Af X.B.I.F} (he : e ∈ Formalism.UG.intAd X.B.I.F) : E1 X e ∈ IntAf X.B.I.F X.B.I.E :=
  tmul_int X he

theorem one_sub_idempotent {e t : Af X.B.I.F} (ht : 1 - e = (X.B.g : Af X.B.I.F) * t) :
    1 - E1 X e = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) := by
  unfold E1
  have h1 : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (X.B.g : Af X.B.I.F) := by
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  rw [h1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← ht, Algebra.TensorProduct.one_def,
    TensorProduct.tmul_sub]

variable {X}

theorem Zfix {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hc : c ∈ IntAf X.B.I.F X.B.I.E) (h : ZMod' X.B.I X.B.g (E1 X e * c)) : ZMod' X.B.I X.B.g c := by
  obtain ⟨t, ht, he1⟩ := hE.2.2.1
  have hs := one_sub_idempotent X he1
  have e2 : c = E1 X e * c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * c) := by
    linear_combination c * hs
  rw [e2]
  exact Z_add X.B.I X.B.g h ⟨_, mul_mem (tmul_int X ht) hc, rfl⟩

theorem idempotent_inv_coprime_nat (hJ : IdxDJacE) {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) (c : ℕ)
    (hc : Nat.Coprime c X.B.g) :
    ∃ y ∈ IntAf X.B.I.F X.B.I.E, E1 X e * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y = E1 X e := by
  have hcop : IsCoprime (c : ℤ) (X.B.g : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨y, hy, hyE⟩ := hJ X.B.I.F X.B.I.E X.B.g e hE (-(b : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))
    (neg_mem (intCast_mem _ b))
  refine ⟨(a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y, mul_mem (intCast_mem _ a) hy, ?_⟩
  have hab' : (a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (-(b : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
    have := congrArg (Int.cast : ℤ → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hab
    push_cast at this
    linear_combination this
  calc E1 X e * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y)
      = E1 X e * ((a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * y := by ring
    _ = E1 X e := by rw [hab']; exact hyE

theorem mL_le_Lf : ∀ v ∈ mL X.B.I X.B.g, v ∈ X.B.I.Lf := by
  intro v hv
  refine (Submodule.span_le (p := X.B.I.Lf)).2 ?_ hv
  rintro _ ⟨x, hx, rfl⟩
  have := X.B.I.Lf.smul_mem (⟨(X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), natCast_mem _ _⟩ : IntAf X.B.I.F X.B.I.E) hx
  rwa [Subring.smul_def] at this

theorem smul_int_mem {N : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I)} {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hc : c ∈ IntAf X.B.I.F X.B.I.E) {v : VA X.B.I} (hv : v ∈ N) : c • v ∈ N := by
  have := N.smul_mem (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) hv
  rwa [Subring.smul_def] at this

theorem congruence_on_idempotent (hJ : IdxDJacE) {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) {δ : VA X.B.I}
    (h : InAt X.B.I X.B.g X.B.g δ) : E1 X e • δ ∈ mL X.B.I X.B.g := by
  obtain ⟨c, hc, hcδ⟩ := h
  obtain ⟨y, hy, hyE⟩ := idempotent_inv_coprime_nat hJ hE c hc
  have e2 : E1 X e • δ = (E1 X e * y) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • δ) := by
    rw [smul_smul]
    conv_lhs => rw [← hyE]
    ring_nf
  rw [e2]
  exact smul_int_mem (mul_mem (integral_circleChar X hE.1) hy) hcδ

theorem hA_crd (x y : (VS D).V) :
    hA X.B.I (incl X.B.I (X.crd x)) (incl X.B.I (X.crd y)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((VS D).hT x y)) := by
  rw [hA_incl, tr_hT, RingEquiv.symm_apply_apply]
  congr 1
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]

variable (X)

def zv (u : D.what₂.Word) : VA X.B.I := X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)

theorem ev_fix (u : D.what₂.Word) (a : Fin D.R.rS) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) :=
  fixes_inv X (X.xu_fix u a).1

theorem fv_fix (u : D.what₂.Word) (a : Fin D.R.rS) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) :=
  fixes_inv X (X.xu_fix u a).2

theorem rel_ee (a b : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.eR b)) = 0 := by
  show hA X.B.I (incl X.B.I (X.crd (X.eX a))) (incl X.B.I (X.crd (X.eX b))) = 0
  rw [hA_crd, X.ee, map_zero, map_zero]

theorem rel_ff (a b : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (X.fR b)) = 0 := by
  show hA X.B.I (incl X.B.I (X.crd (X.fY a))) (incl X.B.I (X.crd (X.fY b))) = 0
  rw [hA_crd, X.ff, map_zero, map_zero]

theorem rel_ef (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  show hA X.B.I (incl X.B.I (X.crd (X.eX a))) (incl X.B.I (X.crd (X.fY b))) = _
  rw [hA_crd, X.ef]
  split_ifs <;> simp

theorem rel_ez (u : D.what₂.Word) (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (zv X u) = 0 := by
  rw [← ev_fix X u a, zv, hA_unit]
  show hA X.B.I (incl X.B.I (X.crd (X.eX a))) (incl X.B.I (X.crd (X.zu u))) = 0
  rw [hA_crd, (X.zu_orth u a).1, map_zero, map_zero]

theorem rel_fz (u : D.what₂.Word) (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (zv X u) = 0 := by
  rw [← fv_fix X u a, zv, hA_unit]
  show hA X.B.I (incl X.B.I (X.crd (X.fY a))) (incl X.B.I (X.crd (X.zu u))) = 0
  rw [hA_crd, (X.zu_orth u a).2, map_zero, map_zero]

end PI.UnitaryDimensionFormula.FrameX

namespace PI.UnitaryDimensionFormula.FrameX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def eh (e : Af X.B.I.F) (a : Fin D.R.rS) : VA X.B.I := E1 X e • incl X.B.I (X.eR a)
def fh (e : Af X.B.I.F) (a : Fin D.R.rS) : VA X.B.I := E1 X e • incl X.B.I (X.fR a)
def zh (e : Af X.B.I.F) (u : D.what₂.Word) : VA X.B.I := E1 X e • zv X u

def Qv (e : Af X.B.I.F) (u : D.what₂.Word) (y : VA X.B.I) : VA X.B.I :=
  FrameAlg.Q (sigA X.B.I) (JA X.B.I) (eh X e) (fh X e) (zh X e u) y

variable {X}

theorem hermitian_idempotent_smul {e : Af X.B.I.F} (he : e * e = e) (x y : VA X.B.I) :
    hA X.B.I (E1 X e • x) (E1 X e • y) = E1 X e * hA X.B.I x y := by
  rw [hA_smul_left, hA_smul_right, idempotent_conj_fixed, ← mul_assoc, idempotent_mul_self X he]

theorem hermitian_idempotent_smul_left (e : Af X.B.I.F) (x y : VA X.B.I) :
    hA X.B.I (E1 X e • x) y = E1 X e * hA X.B.I x y := by
  rw [hA_smul_left, idempotent_conj_fixed]

theorem idempotent_smul_idem {e : Af X.B.I.F} (he : e * e = e) (x : VA X.B.I) : E1 X e • (E1 X e • x) = E1 X e • x := by
  rw [smul_smul, idempotent_mul_self X he]

theorem sub_hA_left (x x' y : VA X.B.I) : hA X.B.I x y = hA X.B.I (x - x') y + hA X.B.I x' y := by
  rw [← hA_add_left, sub_add_cancel]

theorem Qv_perp (hS : IdxDSig) {e : Af X.B.I.F} (he : e * e = e) (u : D.what₂.Word) (y : VA X.B.I) :
    (∀ b, hA X.B.I (eh X e b) (Qv X e u y) = 0) ∧ (∀ b, hA X.B.I (fh X e b) (Qv X e u y) = 0) ∧
      hA X.B.I (zh X e u) (Qv X e u y) = 0 := by
  have hE := idempotent_mul_self X he
  refine FrameAlg.Q_perp_idem (sigA X.B.I) (JA X.B.I) (hS X.B.I).2 (hS X.B.I).1 (E1 X e) hE (idempotent_conj_fixed X e)
    (fun a => (idempotent_smul_idem he _).symm) (fun a => (idempotent_smul_idem he _).symm) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_) (fun a => ?_) (fun a => ?_) y
  · show hA X.B.I (eh X e a) (eh X e b) = 0
    rw [eh, eh, hermitian_idempotent_smul he, rel_ee, mul_zero]
  · show hA X.B.I (fh X e a) (fh X e b) = 0
    rw [fh, fh, hermitian_idempotent_smul he, rel_ff, mul_zero]
  · show hA X.B.I (eh X e a) (fh X e b) = _
    rw [eh, fh, hermitian_idempotent_smul he, rel_ef]
    split_ifs <;> simp
  · show hA X.B.I (eh X e a) (zh X e u) = 0
    rw [eh, zh, hermitian_idempotent_smul he, rel_ez, mul_zero]
  · show hA X.B.I (fh X e a) (zh X e u) = 0
    rw [fh, zh, hermitian_idempotent_smul he, rel_fz, mul_zero]

theorem fixV_perp (hS : IdxDSig) {e : Af X.B.I.F} (he : e * e = e) (u : D.what₂.Word) (y w : VA X.B.I)
    (hw : w ∈ fixV X u) : E1 X e * hA X.B.I w (Qv X e u y) = 0 := by
  obtain ⟨h1, h2, h3⟩ := Qv_perp hS he u y
  rw [← hermitian_idempotent_smul_left]
  rcases hw with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · exact h1 a
  · exact h2 a
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact h3

variable (hJ : IdxDJacE) {e : Af X.B.I.F} (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word)
include hJ hE

theorem eh_cong (a : Fin D.R.rS) : eh X e a - E1 X e • X.e0 a ∈ mL X.B.I X.B.g := by
  have := congruence_on_idempotent hJ hE (X.basisApprox a).1
  rw [smul_sub] at this
  have h2 := (mL X.B.I X.B.g).neg_mem this
  rw [neg_sub] at h2
  exact h2

theorem fh_cong (a : Fin D.R.rS) : fh X e a - E1 X e • X.f0 a ∈ mL X.B.I X.B.g := by
  have := congruence_on_idempotent hJ hE (X.basisApprox a).2
  rw [smul_sub] at this
  have h2 := (mL X.B.I X.B.g).neg_mem this
  rw [neg_sub] at h2
  exact h2

theorem zh_cong : zh X e u - E1 X e • X.z0 ∈ mL X.B.I X.B.g := by
  have := congruence_on_idempotent hJ hE (X.xu_z u)
  rw [smul_sub] at this
  exact this

theorem mem_of_cong {x x0 : VA X.B.I} (hx0 : x0 ∈ X.B.I.Lf) (h : x - E1 X e • x0 ∈ mL X.B.I X.B.g) :
    x ∈ X.B.I.Lf := by
  have h1 : E1 X e • x0 ∈ X.B.I.Lf := smul_int_mem (integral_circleChar X hE.1) hx0
  have := X.B.I.Lf.add_mem (mL_le_Lf _ h) h1
  rwa [sub_add_cancel] at this

theorem eh_Lf (a : Fin D.R.rS) : eh X e a ∈ X.B.I.Lf :=
  mem_of_cong hJ hE ((frame_Lf X).1 a) (eh_cong hJ hE a)
theorem fh_Lf (a : Fin D.R.rS) : fh X e a ∈ X.B.I.Lf :=
  mem_of_cong hJ hE ((frame_Lf X).2.1 a) (fh_cong hJ hE a)
theorem zh_Lf : zh X e u ∈ X.B.I.Lf :=
  mem_of_cong hJ hE (frame_Lf X).2.2.1 (zh_cong hJ hE u)

theorem Qv_Lf {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : Qv X e u y ∈ X.B.I.Lf := by
  unfold Qv FrameAlg.Q
  have hi : ∀ x w, x ∈ X.B.I.Lf → w ∈ X.B.I.Lf → Formalism.UG.hform (sigA X.B.I) (JA X.B.I) x w ∈ IntAf X.B.I.F X.B.I.E :=
    fun x w hx hw => hA_int X.B.I hx hw
  refine X.B.I.Lf.add_mem (smul_int_mem (neg_mem (hi _ _ (zh_Lf hJ hE u) (zh_Lf hJ hE u)))
    (X.B.I.Lf.sub_mem hy (Submodule.sum_mem _ fun a _ => X.B.I.Lf.add_mem ?_ ?_)))
    (smul_int_mem (hi _ _ (zh_Lf hJ hE u) hy) (zh_Lf hJ hE u))
  · exact smul_int_mem (hi _ _ (fh_Lf hJ hE a) hy) (eh_Lf hJ hE a)
  · exact smul_int_mem (hi _ _ (eh_Lf hJ hE a) hy) (fh_Lf hJ hE a)

omit hJ hE in
theorem Z_hA_mL' {d w : VA X.B.I} (hd : d ∈ mL X.B.I X.B.g) (hw : w ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I w d) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g (Z_hA_mL X hd hw)

omit hJ hE in

theorem Z_pair {x x' y y' : VA X.B.I} (hx : x - x' ∈ mL X.B.I X.B.g) (hy : y - y' ∈ mL X.B.I X.B.g)
    (hyL : y ∈ X.B.I.Lf) (hx'L : x' ∈ X.B.I.Lf) :
    ZMod' X.B.I X.B.g (hA X.B.I x y - hA X.B.I x' y') := by
  have e1 : hA X.B.I x y - hA X.B.I x' y' = hA X.B.I (x - x') y + hA X.B.I x' (y - y') := by
    rw [hA_sub_right, sub_hA_left x x' y]; ring
  rw [e1]
  exact Z_add X.B.I X.B.g (Z_hA_mL X hx hyL) (Z_hA_mL' hy hx'L)

theorem N_cong : ZMod' X.B.I X.B.g (hA X.B.I (zh X e u) (zh X e u) + E1 X e) := by
  have hz0 := (frame_Lf X).2.2.1
  have hc := zh_cong hJ hE u
  have h1 := Z_pair hc hc (zh_Lf hJ hE u) (smul_int_mem (integral_circleChar X hE.1) hz0)
  rw [hermitian_idempotent_smul hE.2.1] at h1
  have h2 := Z_smul X.B.I X.B.g (integral_circleChar X hE.1) X.formsAtZero.1
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  ring

theorem Qv_cong {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (he0 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) y))
    (hf0 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) y)) (hz0 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 y)) :
    Qv X e u y - E1 X e • y ∈ mL X.B.I X.B.g := by
  have hEi := integral_circleChar X hE.1
  have Zc : ∀ (x x0 : VA X.B.I), x - E1 X e • x0 ∈ mL X.B.I X.B.g → ZMod' X.B.I X.B.g (hA X.B.I x0 y) →
      ZMod' X.B.I X.B.g (hA X.B.I x y) := fun x x0 hc h0 => by
    rw [sub_hA_left x (E1 X e • x0) y, hermitian_idempotent_smul_left]
    exact Z_add X.B.I X.B.g (Z_hA_mL X hc hy) (Z_smul X.B.I X.B.g hEi h0)
  set N := hA X.B.I (zh X e u) (zh X e u)
  have hN : ZMod' X.B.I X.B.g (-N - E1 X e) := by
    have := Z_sub X.B.I X.B.g (Z_zero X.B.I X.B.g) (N_cong hJ hE u)
    convert this using 1; ring
  have hNi : N ∈ IntAf X.B.I.F X.B.I.E := hA_int X.B.I (zh_Lf hJ hE u) (zh_Lf hJ hE u)
  have e1 : Qv X e u y - E1 X e • y = (-N - E1 X e) • y +
      N • (∑ a, (hA X.B.I (fh X e a) y • eh X e a + hA X.B.I (eh X e a) y • fh X e a)) +
      hA X.B.I (zh X e u) y • zh X e u := by
    simp only [Qv, FrameAlg.Q]
    change (-N) • (y - ∑ a, (hA X.B.I (fh X e a) y • eh X e a + hA X.B.I (eh X e a) y • fh X e a)) +
      hA X.B.I (zh X e u) y • zh X e u - E1 X e • y = _
    simp only [smul_sub, sub_smul, neg_smul]
    abel
  rw [e1]
  refine (mL X.B.I X.B.g).add_mem ((mL X.B.I X.B.g).add_mem (Z_smul_mL X hN hy) (smul_int_mem hNi
    (Submodule.sum_mem _ fun a _ => (mL X.B.I X.B.g).add_mem ?_ ?_))) ?_
  · exact Z_smul_mL X (Zc _ _ (fh_cong hJ hE a) (hf0 a)) (eh_Lf hJ hE a)
  · exact Z_smul_mL X (Zc _ _ (eh_cong hJ hE a) (he0 a)) (fh_Lf hJ hE a)
  · exact Z_smul_mL X (Zc _ _ (zh_cong hJ hE u) hz0) (zh_Lf hJ hE u)

end PI.UnitaryDimensionFormula.FrameX

namespace PI.UnitaryDimensionFormula.FrameX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PI.UnitaryDimensionFormula

def FrGramS : Prop := ∀ (D : D7) (X : HidaSetting D) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
  ∀ G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), (∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E) →
  (∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then epsX X e else 0)) →
  ∃ y ∈ IntAf X.B.I.F X.B.I.E, epsX X e * G.det * y = epsX X e

variable {D : D7} {X : HidaSetting D}

theorem eps_eq (e : Af X.B.I.F) : epsX X e = E1 X e * X.ew := rfl

theorem int_adj {S : Subring (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)} {k : ℕ}
    {M : Matrix (Fin k) (Fin k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)} (h : ∀ i j, M i j ∈ S) (i j : Fin k) :
    M.adjugate i j ∈ S := by
  let M' : Matrix (Fin k) (Fin k) S := fun i j => ⟨M i j, h i j⟩
  have e1 : M = S.subtype.mapMatrix M' := by ext i j; rfl
  rw [e1, ← RingHom.map_adjugate]
  exact ((M'.adjugate) i j).2

variable {e : Af X.B.I.F}

theorem eps_int (hE : EgProp X.B.I.F X.B.g e) : epsX X e ∈ IntAf X.B.I.F X.B.I.E := mul_mem (integral_circleChar X hE.1) X.ew_int

theorem eps_idem (he : e * e = e) : epsX X e * epsX X e = epsX X e := by
  rw [eps_eq]
  have h1 := idempotent_mul_self X he
  have h2 := X.ew_idem
  linear_combination (X.ew * X.ew) * h1 + E1 X e * h2

theorem sig_eps : sigA X.B.I (epsX X e) = E1 X e * sigA X.B.I X.ew := by
  rw [eps_eq, map_mul, idempotent_conj_fixed]

theorem eps_orth : epsX X e * sigA X.B.I (epsX X e) = 0 := by
  rw [sig_eps, eps_eq]
  have h2 := X.ew_orth
  linear_combination (E1 X e * E1 X e) * h2

theorem epsilon_idempotent_mul (he : e * e = e) : epsX X e * E1 X e = epsX X e := by
  rw [eps_eq]; linear_combination X.ew * idempotent_mul_self X he

theorem eps_ew : epsX X e * X.ew = epsX X e := by
  rw [eps_eq]; linear_combination E1 X e * X.ew_idem

def bv (e : Af X.B.I.F) (u : D.what₂.Word) (j : Fin D.R.k) : VA X.B.I := epsX X e • Qv X e u (X.bw j)
def cv (e : Af X.B.I.F) (u : D.what₂.Word) (l : Fin D.R.k) : VA X.B.I :=
  sigA X.B.I (epsX X e) • Qv X e u (X.bwd l)

theorem Qbw_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (j : Fin D.R.k) : Qv X e u (X.bw j) - E1 X e • X.bw j ∈ mL X.B.I X.B.g :=
  Qv_cong hJ hE u ((frame_Lf X).2.2.2.1 j) (fun a => ((X.weightVectorsIntegral j).2.2 a).1) (fun a => ((X.weightVectorsIntegral j).2.2 a).2.1)
    (X.weightVectorsIntegral j).1

theorem Qbwd_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l : Fin D.R.k) : Qv X e u (X.bwd l) - E1 X e • X.bwd l ∈ mL X.B.I X.B.g :=
  Qv_cong hJ hE u ((frame_Lf X).2.2.2.2 l) (fun a => ((X.weightVectorsIntegral l).2.2 a).2.2.1)
    (fun a => ((X.weightVectorsIntegral l).2.2 a).2.2.2) (X.weightVectorsIntegral l).2.1

theorem bv_Lf (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (j : Fin D.R.k) : bv e u j ∈ X.B.I.Lf :=
  smul_int_mem (eps_int hE) (Qv_Lf hJ hE u ((frame_Lf X).2.2.2.1 j))

theorem cv_Lf (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l : Fin D.R.k) : cv e u l ∈ X.B.I.Lf :=
  smul_int_mem (sigA_mem X.B.I (eps_int hE)) (Qv_Lf hJ hE u ((frame_Lf X).2.2.2.2 l))

theorem G_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (cv e u l) (bv e u j) - if l = j then epsX X e else 0) := by
  have hp := Z_pair (Qbwd_cong hJ hE u l) (Qbw_cong hJ hE u j) (Qv_Lf hJ hE u ((frame_Lf X).2.2.2.1 j))
    (smul_int_mem (integral_circleChar X hE.1) ((frame_Lf X).2.2.2.2 l))
  rw [hermitian_idempotent_smul hE.2.1] at hp
  have h1 := Z_smul X.B.I X.B.g (eps_int hE) hp
  have h2 := Z_smul X.B.I X.B.g (eps_int hE) (X.bw_dual l j)
  have e1 : hA X.B.I (cv e u l) (bv e u j) = epsX X e * hA X.B.I (Qv X e u (X.bwd l)) (Qv X e u (X.bw j)) := by
    rw [cv, bv, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, eps_idem hE.2.1]
  rw [e1]
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  have h3 := epsilon_idempotent_mul hE.2.1
  have h4 : epsX X e * X.ew = epsX X e := eps_ew
  split_ifs
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3 + h4
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3

theorem cbw_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (l j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (cv e u l) (X.bw j) - if l = j then epsX X e else 0) := by
  have hp : ZMod' X.B.I X.B.g (hA X.B.I (Qv X e u (X.bwd l)) (X.bw j) - hA X.B.I (E1 X e • X.bwd l) (X.bw j)) := by
    rw [sub_hA_left (Qv X e u (X.bwd l)) (E1 X e • X.bwd l) (X.bw j), add_sub_cancel_right]
    exact Z_hA_mL X (Qbwd_cong hJ hE u l) ((frame_Lf X).2.2.2.1 j)
  rw [hermitian_idempotent_smul_left] at hp
  have h1 := Z_smul X.B.I X.B.g (eps_int hE) hp
  have h2 := Z_smul X.B.I X.B.g (eps_int hE) (X.bw_dual l j)
  have e1 : hA X.B.I (cv e u l) (X.bw j) = epsX X e * hA X.B.I (Qv X e u (X.bwd l)) (X.bw j) := by
    rw [cv, hA_smul_left, sigA_sigA]
  rw [e1]
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  have h3 := epsilon_idempotent_mul hE.2.1
  have h4 : epsX X e * X.ew = epsX X e := eps_ew
  split_ifs
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3 + h4
  · linear_combination (hA X.B.I (X.bwd l) (X.bw j)) * h3

theorem bwdb_cong (hJ : IdxDJacE) (hE : EgProp X.B.I.F X.B.g e) (u : D.what₂.Word) (i j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (bv e u j) - if i = j then epsX X e else 0) := by
  have hp : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (Qv X e u (X.bw j)) - hA X.B.I (X.bwd i) (E1 X e • X.bw j)) := by
    rw [← hA_sub_right]
    exact Z_hA_mL' (Qbw_cong hJ hE u j) ((frame_Lf X).2.2.2.2 i)
  rw [hA_smul_right] at hp
  have h1 := Z_smul X.B.I X.B.g (eps_int hE) hp
  have h2 := Z_smul X.B.I X.B.g (eps_int hE) (X.bw_dual i j)
  have e1 : hA X.B.I (X.bwd i) (bv e u j) = epsX X e * hA X.B.I (X.bwd i) (Qv X e u (X.bw j)) := by
    rw [bv, hA_smul_right]
  rw [e1]
  have := Z_add X.B.I X.B.g h1 h2
  convert this using 1
  have h3 := epsilon_idempotent_mul hE.2.1
  have h4 : epsX X e * X.ew = epsX X e := eps_ew
  split_ifs
  · linear_combination (hA X.B.I (X.bwd i) (X.bw j)) * h3 + h4
  · linear_combination (hA X.B.I (X.bwd i) (X.bw j)) * h3

theorem to_ew (hE : EgProp X.B.I.F X.B.g e) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop) [Decidable b]
    (h : ZMod' X.B.I X.B.g (c - if b then epsX X e else 0)) : ZMod' X.B.I X.B.g (c - if b then X.ew else 0) := by
  refine Zfix hE (sub_mem hc (by split_ifs; exacts [X.ew_int, zero_mem _])) ?_
  have h1 := Z_smul X.B.I X.B.g (integral_circleChar X hE.1) h
  convert h1 using 1
  have h3 : E1 X e * epsX X e = epsX X e := by rw [mul_comm]; exact epsilon_idempotent_mul hE.2.1
  split_ifs
  · rw [mul_sub, mul_sub, h3, eps_eq]
  · ring

end PI.UnitaryDimensionFormula.FrameX
