import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeAverageIdentity

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.KernelScalingBack

section Diag

variable {K : Type} [CommRing K] {n : ℕ}

def DG (d : Fin n → Kˣ) : GL (Fin n) K :=
  ⟨diagonal fun b => ((d b : Kˣ) : K), diagonal fun b => (((d b)⁻¹ : Kˣ) : K),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem DG_coe (d : Fin n → Kˣ) :
    ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun b => ((d b : Kˣ) : K) := rfl

theorem DG_inv_coe (d : Fin n → Kˣ) :
    (((DG d)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun b => (((d b)⁻¹ : Kˣ) : K) := rfl

def cj (d : Fin n → Kˣ) (g : GL (Fin n) K) : GL (Fin n) K := (DG d)⁻¹ * g * DG d

theorem cj_apply (d : Fin n → Kˣ) (g : GL (Fin n) K) (a b : Fin n) :
    ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      (((d a)⁻¹ : Kˣ) : K) * (g : Matrix (Fin n) (Fin n) K) a b * ((d b : Kˣ) : K) := by
  unfold cj
  rw [Units.val_mul, Units.val_mul, DG_coe, DG_inv_coe, mul_diagonal, diagonal_mul]

theorem cj_mul (d : Fin n → Kˣ) (g g' : GL (Fin n) K) : cj d (g * g') = cj d g * cj d g' := by
  unfold cj; group

theorem cj_inv (d : Fin n → Kˣ) (g : GL (Fin n) K) : cj d g⁻¹ = (cj d g)⁻¹ := by
  unfold cj; group

theorem cj_back (d : Fin n → Kˣ) (g : GL (Fin n) K) : cj d (DG d * g * (DG d)⁻¹) = g := by
  unfold cj; group

theorem entry_back (d : Fin n → Kˣ) (g : GL (Fin n) K) (a b : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) a b = ((d a : Kˣ) : K) *
      ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * (((d b)⁻¹ : Kˣ) : K) := by
  rw [cj_apply]
  have h1 : ((d a : Kˣ) : K) * (((d a)⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
  have h2 : ((d b : Kˣ) : K) * (((d b)⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
  linear_combination (-(g : Matrix (Fin n) (Fin n) K) a b * ((d b : Kˣ) : K) * (((d b)⁻¹ : Kˣ) : K)) * h1
    - (g : Matrix (Fin n) (Fin n) K) a b * h2

theorem isUpUni_cj (d : Fin n → Kˣ) (g : GL (Fin n) K) :
    IsUpUni ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ↔
      IsUpUni (g : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [entry_back d, h.1 hab]; simp
    · rw [entry_back d, h.2 a]; simp
  · intro h
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [cj_apply, h.1 hab]; simp
    · rw [cj_apply, h.2 a]; simp

theorem isLowUni_cj (d : Fin n → Kˣ) (g : GL (Fin n) K)
    (h : IsLowUni (g : Matrix (Fin n) (Fin n) K)) :
    IsLowUni ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [cj_apply, h.1 hab]; simp
  · rw [cj_apply, h.2 a]; simp

theorem isInt_cj (R : Subring K) (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (g : GL (Fin n) K) :
    IsInt R ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ↔
      IsInt R (g : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro h a b
    rw [entry_back d]
    exact R.mul_mem (R.mul_mem (hd a).1 (h a b)) (hd b).2
  · intro h a b
    rw [cj_apply]
    exact R.mul_mem (R.mul_mem (hd a).2 (h a b)) (hd b).1

theorem isInt_mul_DG (R : Subring K) (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (Z : Matrix (Fin n) (Fin n) K) :
    IsInt R (Z * ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ IsInt R Z := by
  constructor
  · intro h a b
    have h1 := h a b
    rw [DG_coe, mul_diagonal] at h1
    have h2 : Z a b = Z a b * ((d b : Kˣ) : K) * (((d b)⁻¹ : Kˣ) : K) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [h2]
    exact R.mul_mem h1 (hd b).2
  · intro h a b
    rw [DG_coe, mul_diagonal]
    exact R.mul_mem (h a b) (hd b).1

end Diag

section Scale

variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)

def dg (b : Fin S.sum) : Kˣ := c (blk S b)

theorem pt_scale :
    pt S (T * c) = pt S T * ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) := by
  ext a b
  rw [DG_coe, mul_diagonal]
  simp only [pt]
  split_ifs with hb
  · rw [dg, hb, Formalism.DoubleCosetMeasures.P.Phase.blk_revIn S a a.2]; simp
  · simp

theorem mem_lowW_scale {g : GL (Fin S.sum) K} (hg : g ∈ lowW K S T) : g ∈ lowW K S (T * c) := by
  obtain ⟨h1, x, hx, e⟩ := hg
  have hxd : x.det = 1 := isLowUni_det K hx
  refine ⟨h1, ((cj (dg S c) (A5x8.sec_gl x hxd) : GL (Fin S.sum) K) :
    Matrix (Fin S.sum) (Fin S.sum) K), isLowUni_cj _ _ hx, ?_⟩
  rw [pt_scale, ← Matrix.mul_assoc, e]
  unfold cj
  rw [Units.val_mul, Units.val_mul, A5x8.sec_gl_coe]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K),
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem mem_lowW_scale_iff {g : GL (Fin S.sum) K} : g ∈ lowW K S (T * c) ↔ g ∈ lowW K S T := by
  refine ⟨fun hg => ?_, mem_lowW_scale S T c⟩
  have := mem_lowW_scale S (T * c) c⁻¹ hg
  rwa [mul_inv_cancel_right] at this

def fm (p : lowW K S T × upUniG K S.sum) : lowW K S (T * c) × upUniG K S.sum :=
  (⟨p.1.1, mem_lowW_scale S T c p.1.2⟩, ⟨cj (dg S c) p.2.1, (isUpUni_cj _ _).2 p.2.2⟩)

theorem fm_surj : Function.Surjective (fm S T c) := by
  rintro ⟨⟨v, hv⟩, ⟨u, hu⟩⟩
  refine ⟨(⟨v, (mem_lowW_scale_iff S T c).1 hv⟩, ⟨DG (dg S c) * u * (DG (dg S c))⁻¹, ?_⟩), ?_⟩
  · have : IsUpUni ((cj (dg S c) (DG (dg S c) * u * (DG (dg S c))⁻¹) : GL (Fin S.sum) K) :
        Matrix (Fin S.sum) (Fin S.sum) K) := by rw [cj_back]; exact hu
    exact (isUpUni_cj _ _).1 this
  · unfold fm
    simp only [cj_back]

theorem orbZ_fm (p : lowW K S T × upUniG K S.sum) :
    orbZ ((S, T * c) : Point K) (fm S T c p) = orbZ ((S, T) : Point K) p *
      ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) := by
  show ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) * pt S (T * c) *
      ((cj (dg S c) p.2.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) =
    ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) * pt S T *
      ((p.2.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) *
      ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)
  rw [pt_scale]
  unfold cj
  rw [Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K),
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

variable (hc : ∀ b, ((c b : Kˣ) : K) ∈ R ∧ (((c b)⁻¹ : Kˣ) : K) ∈ R)

include hc in
theorem toCos_fm_iff (p p₁ : lowW K S T × upUniG K S.sum) :
    A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c p) =
        A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c p₁) ↔
      A5x8.toCos R (w := ((S, T) : Point K)) p = A5x8.toCos R (w := ((S, T) : Point K)) p₁ := by
  unfold A5x8.toCos
  rw [Prod.mk.injEq, Prod.mk.injEq]
  refine and_congr ?_ ?_
  · rw [Quotient.eq, Quotient.eq, QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    exact Iff.rfl
  · rw [QuotientGroup.eq, QuotientGroup.eq, A5x7.mem_intSub, A5x7.mem_intSub]
    have e : (((fm S T c p).2⁻¹ * (fm S T c p₁).2 : upUniG K S.sum) : GL (Fin S.sum) K) =
        cj (dg S c) ((p.2⁻¹ * p₁.2 : upUniG K S.sum) : GL (Fin S.sum) K) := by
      show (cj (dg S c) p.2.1)⁻¹ * cj (dg S c) p₁.2.1 = cj (dg S c) (p.2.1⁻¹ * p₁.2.1)
      rw [cj_mul, cj_inv]
    have hd : ∀ b, ((dg S c b : Kˣ) : K) ∈ R ∧ (((dg S c b)⁻¹ : Kˣ) : K) ∈ R := fun b => hc _
    show IsInt R ((((fm S T c p).2⁻¹ * (fm S T c p₁).2 : upUniG K S.sum) : GL (Fin S.sum) K) :
        Matrix (Fin S.sum) (Fin S.sum) K) ∧
      IsInt R (((((fm S T c p).2⁻¹ * (fm S T c p₁).2 : upUniG K S.sum) : GL (Fin S.sum) K)⁻¹ :
        GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) ↔ _
    rw [e, ← cj_inv, isInt_cj R _ hd, isInt_cj R _ hd]

include hc in
theorem fm_bij : Function.Bijective (fun q : Cos R ((S, T) : Point K) =>
    A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c (rep R q))) := by
  constructor
  · intro q q' h
    have h1 := (toCos_fm_iff R S T c hc _ _).1 h
    rwa [A5x8.inv_toCos_rep, A5x8.inv_toCos_rep] at h1
  · intro q₁
    obtain ⟨p, hp⟩ := fm_surj S T c (rep R q₁)
    refine ⟨A5x8.toCos R (w := ((S, T) : Point K)) p, ?_⟩
    show A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c (rep R (A5x8.toCos R (w := ((S, T) : Point K)) p))) = q₁
    rw [(toCos_fm_iff R S T c hc _ p).2 (A5x8.inv_toCos_rep R _), hp, A5x8.inv_toCos_rep]

end Scale

section Typ

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem latZ_mul_DG (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (Z : Matrix (Fin n) (Fin n) K) :
    latZ R Z = latZ R (Z * ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  ext x
  rw [Formalism.DoubleCosetMeasures.P.mem_latZ, Formalism.DoubleCosetMeasures.P.mem_latZ]
  constructor
  · rintro ⟨t, e⟩
    refine ⟨fun b => ⟨_, (hd b).2⟩ * t b, ?_⟩
    rw [← e, ← Matrix.mulVec_mulVec]
    congr 1
    funext b
    rw [DG_coe, mulVec_diagonal, Formalism.DoubleCosetMeasures.P.coeLin_apply, Formalism.DoubleCosetMeasures.P.coeLin_apply]
    simp
  · rintro ⟨t, e⟩
    refine ⟨fun b => ⟨_, (hd b).1⟩ * t b, ?_⟩
    rw [← e, ← Matrix.mulVec_mulVec]
    congr 1
    funext b
    rw [DG_coe, mulVec_diagonal, Formalism.DoubleCosetMeasures.P.coeLin_apply, Formalism.DoubleCosetMeasures.P.coeLin_apply]
    simp

theorem iso_mul_DG (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : ∀ j b : Fin n, j.val + 1 = n → ((((d j)⁻¹ : Kˣ) : K) - 1) * Z⁻¹ j b ∈ R) :
    Submodule.quotEquivOfEq _ _ (latZ_mul_DG R d hd Z) ∈
      isoZZ R Z (Z * ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  refine ⟨rfl, fun v v' hv => ?_⟩
  rw [Submodule.quotEquivOfEq_mk] at hv
  rw [← A5x4.lamLin_mk_eq R _ hv, Formalism.DoubleCosetMeasures.P.lamLin_apply, Formalism.DoubleCosetMeasures.P.lamLin_apply,
    Submodule.mkQ_apply, Submodule.mkQ_apply, A5x3.mk_eq_mk, Matrix.mul_inv_rev,
    ← Matrix.coe_units_inv, DG_inv_coe, ← Matrix.mulVec_mulVec, Formalism.DoubleCosetMeasures.P.lastCoord_apply,
    Formalism.DoubleCosetMeasures.P.lastCoord_apply, ← Finset.sum_sub_distrib]
  refine R.sum_mem fun j _ => ?_
  split_ifs with hj
  · rw [mulVec_diagonal, ← sub_one_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine R.sum_mem fun b _ => ?_
    rw [← mul_assoc, Formalism.DoubleCosetMeasures.P.coeLin_apply]
    exact R.mul_mem (hA j b hj) (v b).2
  · simp

theorem sUp_cj_sub (d : Fin n → Kˣ) (y : GL (Fin n) K)
    (hB : ∀ (j : Fin n) (hj : j.val + 1 < n),
      ((((d j)⁻¹ : Kˣ) : K) * ((d ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ ∈ R) :
    sUp ((cj d y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      sUp (y : Matrix (Fin n) (Fin n) K) ∈ R := by
  unfold sUp
  rw [← Finset.sum_sub_distrib]
  refine R.sum_mem fun j _ => ?_
  split_ifs with hj
  · rw [cj_apply]
    have := hB j hj
    have e : (((d j)⁻¹ : Kˣ) : K) * (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ *
        ((d ⟨j.val + 1, hj⟩ : Kˣ) : K) - (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ =
        ((((d j)⁻¹ : Kˣ) : K) * ((d ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ := by ring
    rw [e]; exact this
  · simp

theorem sUp_inv (u : upUniG K n) :
    sUp (((u⁻¹ : upUniG K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      - sUp ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 := A5x9.grp_sUp_mul u u⁻¹
  rw [mul_inv_cancel, A5x9.grp_sUp_one] at h1
  linear_combination -h1

end Typ

section Main

variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)

theorem phase_fm (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (p : lowW K S T × upUniG K S.sum)
    (hB : ∀ (j : Fin S.sum) (hj : j.val + 1 < S.sum),
      ((((dg S c j)⁻¹ : Kˣ) : K) * ((dg S c ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) j
          ⟨j.val + 1, hj⟩ ∈ R) :
    phase ψ (w := ((S, T * c) : Point K)) (fm S T c p) = phase ψ (w := ((S, T) : Point K)) p := by
  have h1 := sUp_cj_sub R (dg S c) ((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) hB
  have e1 : cj (dg S c) ((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) =
      (((fm S T c p).2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) := by
    show cj (dg S c) (p.2.1⁻¹) = (cj (dg S c) p.2.1)⁻¹
    rw [cj_inv]
  rw [e1, sUp_inv, sUp_inv] at h1
  show ψ (sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp (((fm S T c p).2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)) =
    ψ (sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp ((p.2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K))
  have e2 : sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp ((p.2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) =
      (sLow ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) +
      sUp (((fm S T c p).2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)) +
      (-sUp (((fm S T c p).2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) -
        -sUp ((p.2 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)) := by ring
  conv_rhs => rw [e2, AddChar.map_add_eq_mul, hψ _ h1, mul_one]

theorem Kp_scale (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1)
    (hc : ∀ b, ((c b : Kˣ) : K) ∈ R ∧ (((c b)⁻¹ : Kˣ) : K) ∈ R)
    (hA : ∀ p : lowW K S T × upUniG K S.sum, IsInt R (orbZ ((S, T) : Point K) p) →
      ∀ j b : Fin S.sum, j.val + 1 = S.sum →
        ((((dg S c j)⁻¹ : Kˣ) : K) - 1) * (orbZ ((S, T) : Point K) p)⁻¹ j b ∈ R)
    (hB : ∀ p : lowW K S T × upUniG K S.sum, IsInt R (orbZ ((S, T) : Point K) p) →
      ∀ (j : Fin S.sum) (hj : j.val + 1 < S.sum),
      ((((dg S c j)⁻¹ : Kˣ) : K) * ((dg S c ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) j
          ⟨j.val + 1, hj⟩ ∈ R)
    (w' : Point K) :
    Kp R ψ ((S, T * c) : Point K) w' = Kp R ψ ((S, T) : Point K) w' := by
  have hd : ∀ b, ((dg S c b : Kˣ) : K) ∈ R ∧ (((dg S c b)⁻¹ : Kˣ) : K) ∈ R := fun b => hc _
  rw [A5x8.Kp_eq_section R ψ hψ ((S, T * c) : Point K) w' (Cos R ((S, T) : Point K)) (Cos R w')
    (fun q => fm S T c (rep R q)) (fun q => rep R q) (fm_bij R S T c hc)
    (by simp only [A5x8.inv_toCos_rep]; exact Function.bijective_id)]
  unfold Kp
  refine finsum_congr fun q => ?_
  show A5x8.Gterm R ψ ((S, T * c) : Point K) w' (fm S T c (rep R q.1)) (rep R q.2) =
    A5x8.Gterm R ψ ((S, T) : Point K) w' (rep R q.1) (rep R q.2)
  generalize rep R q.1 = p
  generalize rep R q.2 = p'
  unfold A5x8.Gterm
  by_cases hZ : IsInt R (orbZ ((S, T) : Point K) p)
  · rw [phase_fm R S T c ψ hψ p (hB p hZ), orbZ_fm,
      ← A5x4.card_isoZZ_congr R (iso_mul_DG R (dg S c) hd _ (hA p hZ)) (A5x4.isoZZ_refl R _)]
    have hi := (isInt_mul_DG R (dg S c) hd (orbZ ((S, T) : Point K) p)).2 hZ
    by_cases h' : IsInt R (orbZ w' p')
    · rw [if_pos ⟨hi, h'⟩, if_pos ⟨hZ, h'⟩]
    · rw [if_neg (fun h => h' h.2), if_neg (fun h => h' h.2)]
  · have hZ' : ¬ IsInt R (orbZ ((S, T * c) : Point K) (fm S T c p)) := by
      intro h1
      rw [orbZ_fm] at h1
      exact hZ ((isInt_mul_DG R (dg S c) hd _).1 h1)
    rw [if_neg (fun h => hZ' h.1), if_neg (fun h => hZ h.1)]
    simp

end Main

section Block

variable {K : Type} [CommRing K] (R : Subring K)

theorem inv_entry {n : ℕ} {Z : Matrix (Fin n) (Fin n) K} (hZ : IsInt R Z) {x : K}
    (hx : x * Ring.inverse Z.det ∈ R) (a b : Fin n) : x * Z⁻¹ a b ∈ R := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
  exact R.mul_mem hx (Formalism.DoubleCosetMeasures.P.isInt_adjugate R hZ a b)

theorem blk_last_iff (l : List ℕ) (s j : ℕ) (hj : j < (l ++ [s]).sum) :
    blk (l ++ [s]) j = l.length ↔ l.sum ≤ j := by
  have hsum : (l ++ [s]).sum = l.sum + s := by simp
  constructor
  · intro h
    by_contra hlt'
    have hlt := not_le.1 hlt'
    rw [A5x5.blk_append_lt l s j hlt] at h
    exact (A5x5.blk_lt l j hlt).ne h
  · intro h
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
    exact A5x5.blk_append_ge l s i (by omega)

theorem dg_ge (l : List ℕ) (s : ℕ) (k : Kˣ) (j : Fin (l ++ [s]).sum) (hj : l.sum ≤ j.val) :
    dg (l ++ [s]) (Function.update (1 : ℕ → Kˣ) l.length k) j = k := by
  unfold dg
  rw [(blk_last_iff l s j j.2).2 hj, Function.update_self]

theorem dg_lt (l : List ℕ) (s : ℕ) (k : Kˣ) (j : Fin (l ++ [s]).sum) (hj : j.val < l.sum) :
    dg (l ++ [s]) (Function.update (1 : ℕ → Kˣ) l.length k) j = 1 := by
  unfold dg
  rw [Function.update_of_ne (fun h => absurd ((blk_last_iff l s j j.2).1 h) (by omega))]
  rfl

theorem Kp_block (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (h : Point K) (s : ℕ) (hs : 1 ≤ s)
    (z k : Kˣ) (hk : (k : K) ∈ R) (hki : ((k⁻¹ : Kˣ) : K) ∈ R)
    (h1 : (((k⁻¹ : Kˣ) : K) - 1) *
      Ring.inverse (pt (addBlock h s z).1 (addBlock h s z).2).det ∈ R)
    (h2 : ((k : K) - 1) * (z : K) *
      Ring.inverse (pt (addBlock h s z).1 (addBlock h s z).2).det ∈ R) (w' : Point K) :
    Kp R ψ (addBlock h s (z * k)) w' = Kp R ψ (addBlock h s z) w' := by
  have e : addBlock h s (z * k) = ((h.1 ++ [s], Function.update h.2 h.1.length z *
      Function.update (1 : ℕ → Kˣ) h.1.length k) : Point K) := by
    unfold addBlock
    congr 1
    funext b
    by_cases hb : b = h.1.length
    · subst hb; simp
    · simp [Function.update_of_ne hb]
  have hsum : (h.1 ++ [s]).sum = h.1.sum + s := by simp
  have hlast : h.1.sum + s - 1 < (h.1 ++ [s]).sum := by omega
  rw [e]
  show _ = Kp R ψ ((h.1 ++ [s], Function.update h.2 h.1.length z) : Point K) w'
  refine Kp_scale R _ _ _ ψ hψ ?_ ?_ ?_ w'
  · intro b
    by_cases hb : b = h.1.length
    · subst hb; simp [hk, hki]
    · simp [Function.update_of_ne hb, R.one_mem]
  · intro p hZ j b hj
    rw [dg_ge h.1 s k j (by omega)]
    apply inv_entry R hZ
    rw [A5x5.det_orbZ]
    exact h1
  · intro p hZ j hj
    by_cases c1 : j.val + 1 < h.1.sum
    · rw [dg_lt h.1 s k j (by omega), dg_lt h.1 s k ⟨j.val + 1, hj⟩ c1]
      simp [R.zero_mem]
    · by_cases c2 : h.1.sum ≤ j.val
      · rw [dg_ge h.1 s k j c2, dg_ge h.1 s k ⟨j.val + 1, hj⟩ (by simp; omega)]
        simp [R.zero_mem]
      · rw [dg_lt h.1 s k j (by omega), dg_ge h.1 s k ⟨j.val + 1, hj⟩ (by simp; omega)]
        have hL := (Formalism.FourierDecayAlt.P.inverse_last_column_formula K h s z hs
          ((p.1 : GL (Fin (h.1 ++ [s]).sum) K) : Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)
          ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) : Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)
          p.1.2.1 p.2.2 j ⟨h.1.sum + s - 1, hlast⟩ ⟨j.val + 1, hj⟩
          (by show h.1.sum + s - 1 + 1 = (h.1 ++ [s]).sum; omega)
          (by show j.val + 1 = h.1.sum; omega)).1
        have hZ' := inv_entry R hZ (x := ((k : K) - 1) * (z : K))
          (by rw [A5x5.det_orbZ]; exact h2) j ⟨h.1.sum + s - 1, hlast⟩
        have e3 : (orbZ ((h.1 ++ [s], Function.update h.2 h.1.length z) : Point K) p)⁻¹ j
            ⟨h.1.sum + s - 1, hlast⟩ = ((z⁻¹ : Kˣ) : K) *
            ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩ := hL
        rw [e3] at hZ'
        rw [Subgroup.coe_inv, Matrix.coe_units_inv]
        have e4 : ((k : K) - 1) * (z : K) * (((z⁻¹ : Kˣ) : K) *
            ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩) =
            ((((1 : Kˣ)⁻¹ : Kˣ) : K) * (k : K) - 1) *
            ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩ := by
          have hz : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
          simp only [inv_one, Units.val_one, one_mul]
          linear_combination ((k : K) - 1) * ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩ * hz
        rw [← e4]
        exact hZ'

end Block

section Det

variable {K : Type} [CommRing K]

theorem det_pt_eq (s : List ℕ) : ∃ e : Kˣ, ∀ t : ℕ → Kˣ,
    (pt s t).det = (∏ a : Fin s.sum, ((t (blk s a) : Kˣ) : K)) * (e : K) := by
  let σ : Equiv.Perm (Fin s.sum) :=
    ⟨Formalism.DoubleCosetMeasures.P.Phase.revF s, Formalism.DoubleCosetMeasures.P.Phase.revF s, Formalism.DoubleCosetMeasures.P.Phase.revF_revF s,
      Formalism.DoubleCosetMeasures.P.Phase.revF_revF s⟩
  have e : ∀ t : ℕ → Kˣ,
      pt s t = diagonal (fun a : Fin s.sum => ((t (blk s a) : Kˣ) : K)) * σ.permMatrix K := by
    intro t
    ext a c
    rw [diagonal_mul]
    simp only [pt, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, mul_ite, mul_one, mul_zero]
    congr 1
    simp only [σ, Equiv.coe_fn_mk, Fin.ext_iff, Formalism.DoubleCosetMeasures.P.Phase.revF_val, eq_iff_iff]
    exact eq_comm
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact ⟨1, fun t => by rw [e, det_mul, det_diagonal, det_permutation, h]; simp⟩
  · exact ⟨-1, fun t => by rw [e, det_mul, det_diagonal, det_permutation, h]; simp⟩

theorem det_addBlock (h : Point K) (s : ℕ) : ∃ c0 : Kˣ, ∀ z : Kˣ,
    (pt (addBlock h s z).1 (addBlock h s z).2).det = ((c0 * z ^ s : Kˣ) : K) := by
  obtain ⟨e, he⟩ := det_pt_eq (K := K) (h.1 ++ [s])
  refine ⟨(∏ a : Fin h.1.sum, h.2 (blk h.1 a)) * e, fun z => ?_⟩
  have h1 : (pt (addBlock h s z).1 (addBlock h s z).2).det =
      (∏ a : Fin (addBlock h s z).1.sum,
        (((addBlock h s z).2 (blk (addBlock h s z).1 a) : Kˣ) : K)) * (e : K) := he _
  rw [h1, A5x5.prod_addBlock]
  push_cast
  ring

end Det

section Top

variable {K : Type} [CommRing K] (R : Subring K)

theorem inv_mem_of_near (ϖ : K) (hϖ : ϖ ∈ R) (hu : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R) (x : Kˣ)
    (r : K) (hr : r ∈ R) (hx : (x : K) = 1 + ϖ * r) : ((x⁻¹ : Kˣ) : K) ∈ R := by
  have hy : ((x⁻¹ : Kˣ) : K) = 1 - ϖ * r * ((x⁻¹ : Kˣ) : K) := by
    have := Units.mul_inv x
    rw [hx] at this
    linear_combination this
  have key : ∀ m : ℕ, ϖ ^ m * ((x⁻¹ : Kˣ) : K) ∈ R → ((x⁻¹ : Kˣ) : K) ∈ R := by
    intro m
    induction m with
    | zero => intro h; simpa using h
    | succ m ih =>
      intro h
      apply ih
      have e : ϖ ^ m * ((x⁻¹ : Kˣ) : K) = ϖ ^ m - r * (ϖ ^ (m + 1) * ((x⁻¹ : Kˣ) : K)) := by
        rw [pow_succ]
        linear_combination ϖ ^ m * hy
      rw [e]
      exact R.sub_mem (R.pow_mem hϖ m) (R.mul_mem hr h)
  obtain ⟨m, hm⟩ := hu ((x⁻¹ : Kˣ) : K)
  exact key m hm

theorem inv_bdd [TopologicalSpace K] [IsTopologicalRing K] (ho : IsOpen (R : Set K)) (ϖ : Kˣ)
    (hϖ : (ϖ : K) ∈ R) (hu : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (Om : Set K)
    (hOm : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ N : ℕ, ∀ z : Kˣ, (z : K) ∈ Om → (ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K) ∈ R := by
  refine hOm.induction_on
    (p := fun s => ∃ N : ℕ, ∀ z : Kˣ, (z : K) ∈ s → (ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K) ∈ R)
    ?_ ?_ ?_ ?_
  · exact ⟨0, fun z hz => absurd hz (Set.notMem_empty _)⟩
  · rintro s t hst ⟨N, hN⟩
    exact ⟨N, fun z hz => hN z (hst hz)⟩
  · rintro s t ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, fun z hz => ?_⟩
    rcases hz with hz | hz
    · rw [pow_add, mul_comm ((ϖ : K) ^ N), mul_assoc]
      exact R.mul_mem (R.pow_mem hϖ M) (hN z hz)
    · rw [pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem hϖ N) (hM z hz)
  · intro x hx
    obtain ⟨z0, rfl⟩ := hU x hx
    obtain ⟨m, hm⟩ := hu ((z0⁻¹ : Kˣ) : K)
    refine ⟨{z | ((z0⁻¹ : Kˣ) : K) * ((ϖ⁻¹ : Kˣ) : K) * (z - (z0 : K)) ∈ R},
      mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_), m, fun z hz => ?_⟩
    · exact ho.preimage (continuous_const.mul (continuous_id.sub continuous_const))
    · simp [R.zero_mem]
    · have h0 : ((z0⁻¹ : Kˣ) : K) * (z0 : K) = 1 := Units.inv_mul z0
      have h1 : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := Units.mul_inv ϖ
      have h2 := inv_mem_of_near R ϖ hϖ hu (z0⁻¹ * z) _ hz (by
        rw [Units.val_mul]
        linear_combination h0 -
          (((z0⁻¹ : Kˣ) : K) * ((z : K) - (z0 : K))) * h1)
      have e : (ϖ : K) ^ m * ((z⁻¹ : Kˣ) : K) =
          ((ϖ : K) ^ m * ((z0⁻¹ : Kˣ) : K)) * (((z0⁻¹ * z)⁻¹ : Kˣ) : K) := by
        rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
        linear_combination (-(ϖ : K) ^ m * ((z⁻¹ : Kˣ) : K)) * h0
      rw [e]
      exact R.mul_mem hm h2

end Top

end Formalism.FourierDecayAlt.P.KernelScalingBack

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.KernelScalingBack

theorem phase_locally_constant : Formalism.FourierDecayAlt.A6.LocConst := by
  intro K _ _ _ R ψ hD _ s h Om hs hOm hU
  obtain ⟨ϖ, hϖ, hu⟩ := hD.unif
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A5x3.psi_of_mem hD.selfDual hr
  obtain ⟨N, hN⟩ := inv_bdd R hD.isOpen ϖ hϖ hu Om hOm hU
  obtain ⟨c0, hc0⟩ := det_addBlock h s
  obtain ⟨N0, hN0⟩ := hu ((c0⁻¹ : Kˣ) : K)
  have hlat := A5x5.lat_mulR hD.isOpen hD.isCompact (ϖ ^ (1 + N + N0 + s * N))
  refine ⟨mulR R ((ϖ ^ (1 + N + N0 + s * N) : Kˣ) : K), ⟨hlat.op, hlat.cp⟩, ?_⟩
  intro z z' hz hl w'
  obtain ⟨r, hr, hrl⟩ := hl
  have hr' : r ∈ R := hr
  have hrl' : (ϖ : K) ^ (1 + N + N0 + s * N) * r = (z' : K) - (z : K) := by
    rw [← hrl]; simp
  have hy := hN z hz
  have hzy : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
  have hk1 : ((z⁻¹ * z' : Kˣ) : K) = 1 + (ϖ : K) *
      ((ϖ : K) ^ (N0 + s * N) * r * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K))) := by
    rw [Units.val_mul]
    have e : (ϖ : K) ^ (1 + N + N0 + s * N) = (ϖ : K) * (ϖ : K) ^ (N0 + s * N) * (ϖ : K) ^ N := by
      ring
    rw [e] at hrl'
    linear_combination (-((z⁻¹ : Kˣ) : K)) * hrl' + hzy
  have hρ : (ϖ : K) ^ (N0 + s * N) * r * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) ∈ R :=
    R.mul_mem (R.mul_mem (R.pow_mem hϖ _) hr') hy
  have hk : ((z⁻¹ * z' : Kˣ) : K) ∈ R := by
    rw [hk1]; exact R.add_mem R.one_mem (R.mul_mem hϖ hρ)
  have hki : (((z⁻¹ * z')⁻¹ : Kˣ) : K) ∈ R := inv_mem_of_near R ϖ hϖ hu _ _ hρ hk1
  have hkk : ((z⁻¹ * z' : Kˣ) : K) * (((z⁻¹ * z')⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
  have hinv : Ring.inverse (pt (addBlock h s z).1 (addBlock h s z).2).det =
      ((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s := by
    rw [hc0, Ring.inverse_unit, mul_inv, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val]
  have hzk : z' = z * (z⁻¹ * z') := by group
  have hkz : ((z⁻¹ * z' : Kˣ) : K) = ((z⁻¹ : Kˣ) : K) * (z' : K) := Units.val_mul _ _
  rw [hzk]
  refine Kp_block R ψ hψ h s hs z (z⁻¹ * z') hk hki ?_ ?_ w'
  · rw [hinv]
    have e : ((((z⁻¹ * z')⁻¹ : Kˣ) : K) - 1) * (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) =
        -(((z⁻¹ * z')⁻¹ : Kˣ) : K) * ((ϖ : K) * r * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) *
          ((ϖ : K) ^ N0 * ((c0⁻¹ : Kˣ) : K)) * ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) ^ s) := by
      have e1 : (ϖ : K) ^ (1 + N + N0 + s * N) = (ϖ : K) * (ϖ : K) ^ N * (ϖ : K) ^ N0 *
          ((ϖ : K) ^ N) ^ s := by ring
      rw [e1] at hrl'
      rw [hkz] at hkk
      rw [mul_pow]
      linear_combination (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hkk +
        ((((z⁻¹ * z')⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) * ((c0⁻¹ : Kˣ) : K) *
          ((z⁻¹ : Kˣ) : K) ^ s) * hrl' -
        ((((z⁻¹ * z')⁻¹ : Kˣ) : K) * ((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hzy
    rw [e]
    exact R.mul_mem (R.neg_mem hki) (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem hϖ hr') hy) hN0)
      (R.pow_mem hy s))
  · rw [hinv]
    have e : (((z⁻¹ * z' : Kˣ) : K) - 1) * (z : K) * (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) =
        (ϖ : K) ^ (1 + N) * r * ((ϖ : K) ^ N0 * ((c0⁻¹ : Kˣ) : K)) *
          ((ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K)) ^ s := by
      have e1 : (ϖ : K) ^ (1 + N + N0 + s * N) = (ϖ : K) ^ (1 + N) * (ϖ : K) ^ N0 *
          ((ϖ : K) ^ N) ^ s := by ring
      rw [e1] at hrl'
      rw [hkz, mul_pow]
      linear_combination ((z' : K) * ((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hzy -
        (((c0⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) ^ s) * hrl'
    rw [e]
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.pow_mem hϖ _) hr') hN0) (R.pow_mem hy s)

end Formalism.FourierDecayAlt.P
