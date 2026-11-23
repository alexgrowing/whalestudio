import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

noncomputable section

open Matrix MeasureTheory
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp
namespace AltPf

variable {n : ℕ}

section Blocks

variable {R : Type} [CommRing R]

lemma pM_mul (a d a' d' : GL (Fin n) R) (b b' : Matrix (Fin n) (Fin n) R) :
    pM a d b * pM a' d' b' = pM (a * a') (d * d') (a.1 * b' + b * d'.1) := by
  apply Units.ext
  simp [pM, fromBlocks_multiply]

lemma pM_one : pM (1 : GL (Fin n) R) 1 0 = 1 := by
  apply Units.ext
  simp [pM]

lemma map_nU {S : Type} [CommRing S] (f : R →+* S) (y : Matrix (Fin n) (Fin n) R) :
    Matrix.GeneralLinearGroup.map f (nU y) = nU (y.map f) := by
  apply Units.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [nU, Matrix.GeneralLinearGroup.map, Matrix.one_apply, apply_ite f]

end Blocks

lemma lowerRightBlock_parabolic_mul {k : Type} [Field k] (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k)
    (g : GL (Ix n) k) : dBlk (pM a d b * g) = d.1 * dBlk g := by
  have hg : g.1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂ :=
    (fromBlocks_toBlocks g.1).symm
  unfold dBlk
  rw [Units.val_mul]
  conv_lhs => rw [hg]
  simp [pM, fromBlocks_multiply, toBlocks_fromBlocks₂₂]

lemma iD_pM_mul {k : Type} [Field k] (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k)
    (g : GL (Ix n) k) : iD (pM a d b * g) = iD g := by
  unfold iD
  rw [lowerRightBlock_parabolic_mul, Matrix.rank_mul_eq_right_of_isUnit_det]
  exact (Matrix.isUnit_iff_isUnit_det _).1 d.isUnit

section Height

variable {O L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L]
  [IsFractionRing O L]

lemma h_pM_mul (hIw : JpIw) {nv : Lˣ →* ℝ≥0} {h : GL (Ix n) L → ℝ≥0} (hh : IsHgt (O := O) nv h)
    (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (x : GL (Ix n) L) :
    h (pM a d b * x) = nv (Matrix.GeneralLinearGroup.det a) / nv (Matrix.GeneralLinearGroup.det d) * h x := by
  obtain ⟨a', d', b', κ, rfl⟩ := hIw O L n x
  rw [← mul_assoc, pM_mul, hh, hh, map_mul, map_mul, map_mul, map_mul, mul_div_mul_comm]

lemma h_inL {nv : Lˣ →* ℝ≥0} {h : GL (Ix n) L → ℝ≥0} (hh : IsHgt (O := O) nv h) (κ : GL (Ix n) O) :
    h (inL κ) = 1 := by
  have := hh 1 1 0 κ
  simpa [pM_one] using this

lemma h_mul_inL (hIw : JpIw) {nv : Lˣ →* ℝ≥0} {h : GL (Ix n) L → ℝ≥0} (hh : IsHgt (O := O) nv h)
    (x : GL (Ix n) L) (κ : GL (Ix n) O) : h (x * inL κ) = h x := by
  obtain ⟨a, d, b, κ₀, rfl⟩ := hIw O L n x
  rw [mul_assoc, ← map_mul, hh, hh]

lemma scM_val (w : Lˣ) : (scM (n := n) w).1 = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
  ext i j
  simp [scM, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

lemma tau_nU (w : Lˣ) (y : Matrix (Fin n) (Fin n) L) :
    tauM w * nU y = nU ((w⁻¹ : Lˣ).1 • y) * tauM w := by
  apply Units.ext
  simp [tauM, pM, nU, fromBlocks_multiply, scM_val, Matrix.smul_mul, smul_smul]

lemma h_key (hIw : JpIw) (hHgt : JpHgt) [Fintype (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {w : Lˣ} (hw : (w : L) = algebraMap O L ϖ) {nv : Lˣ →* ℝ≥0} (hnv : NvOK (O := O) nv w)
    {h : GL (Ix n) L → ℝ≥0} (hh : IsHgt (O := O) nv h) (κ κ' : GL (Ix n) O)
    (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L)
    (e : inL κ * tauM w = pM a d b * inL κ') (y : Matrix (Fin n) (Fin n) O) :
    h (inL κ * nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L))) *
        (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (resK κ')) =
      (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (resK (κ' * nU y))) := by
  set q : ℝ≥0 := (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) with hq
  set C : ℝ≥0 := nv (Matrix.GeneralLinearGroup.det a) / nv (Matrix.GeneralLinearGroup.det d) with hC
  have hq0 : q ≠ 0 := by
    simp [hq, Fintype.card_ne_zero]
  have e1 : (inL κ : GL (Ix n) L) = pM a d b * (inL κ' * (tauM w)⁻¹) := by
    rw [← mul_assoc, ← e, mul_inv_cancel_right]
  have e2 : (inL κ * nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)) : GL (Ix n) L) =
      pM a d b * (inL (κ' * nU y) * (tauM w)⁻¹) := by
    have t := tau_nU w (y.map (algebraMap O L))
    have t' : (nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)) : GL (Ix n) L) =
        tauM w * nU (y.map (algebraMap O L)) * (tauM w)⁻¹ := by
      rw [t, mul_inv_cancel_right]
    rw [t', map_mul, map_nU, ← mul_assoc, ← mul_assoc, ← mul_assoc, e, mul_assoc _ (inL κ')]
  have h1 : (1 : ℝ≥0) = C * (q ^ (2 * iD (resK κ')) / q ^ n) := by
    have := h_inL (L := L) hh κ
    rw [e1, h_pM_mul hIw hh, hHgt O L n ϖ hϖ w hw nv hnv h hh κ'] at this
    exact this.symm
  have h2 : h (inL κ * nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L))) =
      C * (q ^ (2 * iD (resK (κ' * nU y))) / q ^ n) := by
    rw [e2, h_pM_mul hIw hh, hHgt O L n ϖ hϖ w hw nv hnv h hh]
  rw [h2]
  calc C * (q ^ (2 * iD (resK (κ' * nU y))) / q ^ n) * q ^ (2 * iD (resK κ'))
      = q ^ (2 * iD (resK (κ' * nU y))) * (C * (q ^ (2 * iD (resK κ')) / q ^ n)) := by
        simp only [div_eq_mul_inv]; ring
    _ = _ := by rw [← h1, mul_one]

lemma h_red (hIw : JpIw) (hHgt : JpHgt) [Fintype (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {w : Lˣ} (hw : (w : L) = algebraMap O L ϖ) {nv : Lˣ →* ℝ≥0} (hnv : NvOK (O := O) nv w)
    {h : GL (Ix n) L → ℝ≥0} (hh : IsHgt (O := O) nv h) {ℓ : IsLocalRing.ResidueField O → O}
    (hℓ : ∀ a, IsLocalRing.residue O (ℓ a) = a) (κ : GL (Ix n) O)
    (hb : GL (Ix n) (IsLocalRing.ResidueField O)) (hr : IsRed (O := O) w κ hb)
    (Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) :
    h (inL κ * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) *
        (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD hb) =
      (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (hb * nU Y)) := by
  obtain ⟨a, d, b, κ', e, rfl⟩ := hr
  have key := h_key hIw hHgt hϖ hw hnv hh κ κ' a d b e (Y.map ℓ)
  have hY : (Y.map ℓ).map (IsLocalRing.residue O) = Y := by
    ext i j
    simp [hℓ]
  have hres : resK (κ' * nU (Y.map ℓ)) = resK κ' * nU Y := by
    rw [map_mul, map_nU, hY]
  rw [hres] at key
  exact key

lemma exists_conj_mat {ϖ : O} {w : Lˣ} (hw : (w : L) = algebraMap O L ϖ) (y : Matrix (Fin n) (Fin n) O)
    (γ : GL (Ix n) O) (hγ : γ ∈ Gam2 (n := n) ϖ) :
    ∃ B : Matrix (Ix n) (Ix n) O, (algebraMap O L).mapMatrix B =
      (((nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)))⁻¹ * inL γ *
        nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)) : GL (Ix n) L)).1 := by
  classical
  have hent : ∀ i j, ∃ a : O, a * ϖ ^ 2 = γ.1 i j - (1 : Matrix (Ix n) (Ix n) O) i j := by
    intro i j
    have h1 : (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) γ) = 1 := hγ
    have h2 := congrArg (fun u : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => u.1 i j) h1
    have h3 : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) (γ.1 i j) =
        Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 : Matrix (Ix n) (Ix n) O) i j) := by
      simpa [Matrix.GeneralLinearGroup.map, Matrix.one_apply, apply_ite (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))] using h2
    exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h3)
  choose A hA using hent
  let A' : Matrix (Ix n) (Ix n) O := Matrix.of A
  have hγ' : γ.1 = 1 + (ϖ ^ 2) • A' := by
    ext i j
    simp [A', hA, mul_comm]
  let f := (algebraMap O L).mapMatrix (m := Ix n)
  set x := (w⁻¹ : Lˣ).1 • y.map (algebraMap O L) with hx
  let Ep : Matrix (Ix n) (Ix n) O := fromBlocks (ϖ • 1) y 0 (ϖ • 1)
  let Em : Matrix (Ix n) (Ix n) O := fromBlocks (ϖ • 1) (-y) 0 (ϖ • 1)
  have hwx : (w : L) • x = y.map (algebraMap O L) := by
    simp [hx, smul_smul]
  have hs : ∀ c : O, (c • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O L) =
      (algebraMap O L c) • (1 : Matrix (Fin n) (Fin n) L) := by
    intro c
    ext i j
    simp [Matrix.one_apply, apply_ite (algebraMap O L)]
  have hEp : f Ep = (w : L) • (nU x).1 := by
    rw [show (nU x).1 = fromBlocks 1 x 0 1 from rfl, Matrix.fromBlocks_smul, hwx, hw]
    simp only [f, Ep, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, hs]
    simp
  have hEm : f Em = (w : L) • ((nU x)⁻¹).1 := by
    rw [show ((nU x)⁻¹).1 = fromBlocks 1 (-x) 0 1 from rfl, Matrix.fromBlocks_smul, smul_neg, hwx, hw]
    have hneg : (-y).map (algebraMap O L) = -(y.map (algebraMap O L)) := by
      ext i j
      simp
    simp only [f, Em, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, hs, hneg]
    simp
  have hγL : (inL γ : GL (Ix n) L).1 = 1 + (algebraMap O L ϖ) ^ 2 • f A' := by
    have : (inL γ : GL (Ix n) L).1 = f γ.1 := rfl
    rw [this, hγ', map_add, map_one]
    congr 1
    ext i j
    simp [f]
  have hXX : ((nU x)⁻¹).1 * (nU x).1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel]
    rfl
  refine ⟨1 + Em * A' * Ep, ?_⟩
  rw [Units.val_mul, Units.val_mul, hγL, map_add, map_one, map_mul, map_mul, hEp, hEm,
    mul_add, add_mul, mul_one, hXX, ← hw]
  congr 1
  simp [f, smul_smul, pow_two, Matrix.mul_assoc]

lemma exists_conj {ϖ : O} {w : Lˣ} (hw : (w : L) = algebraMap O L ϖ) (y : Matrix (Fin n) (Fin n) O)
    (γ : GL (Ix n) O) (hγ : γ ∈ Gam2 (n := n) ϖ) :
    ∃ γ' : GL (Ix n) O, (inL γ' : GL (Ix n) L) =
      (nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)))⁻¹ * inL γ *
        nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)) := by
  obtain ⟨B, hB⟩ := exists_conj_mat (L := L) hw y γ hγ
  obtain ⟨B', hB'⟩ := exists_conj_mat (L := L) hw y γ⁻¹ (inv_mem hγ)
  have inj : Function.Injective ((algebraMap O L).mapMatrix (m := Ix n)) :=
    Matrix.map_injective (IsFractionRing.injective O L)
  refine ⟨⟨B, B', inj ?_, inj ?_⟩, Units.ext hB⟩
  · rw [map_mul, hB, hB', ← Units.val_mul, map_one, map_inv]
    have : ∀ X g : GL (Ix n) L, X⁻¹ * g * X * (X⁻¹ * g⁻¹ * X) = 1 := fun X g => by group
    rw [this]
    rfl
  · rw [map_mul, hB, hB', ← Units.val_mul, map_one, map_inv]
    have : ∀ X g : GL (Ix n) L, X⁻¹ * g⁻¹ * X * (X⁻¹ * g * X) = 1 := fun X g => by group
    rw [this]
    rfl

lemma h_gam (hIw : JpIw) {ϖ : O} {w : Lˣ} (hw : (w : L) = algebraMap O L ϖ) {nv : Lˣ →* ℝ≥0}
    {h : GL (Ix n) L → ℝ≥0} (hh : IsHgt (O := O) nv h) (y : Matrix (Fin n) (Fin n) O)
    (κ γ : GL (Ix n) O) (hγ : γ ∈ Gam2 (n := n) ϖ) :
    h (inL (κ * γ) * nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L))) =
      h (inL κ * nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L))) := by
  obtain ⟨γ', hγ'⟩ := exists_conj (L := L) hw y γ hγ
  have : (inL (κ * γ) * nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)) : GL (Ix n) L) =
      inL κ * nU ((w⁻¹ : Lˣ).1 • y.map (algebraMap O L)) * inL γ' := by
    rw [hγ', map_mul]
    group
  rw [this, h_mul_inL hIw hh]

end Height

lemma cpow_key {q : ℕ} (hq : 0 < q) (H : ℝ≥0) (a b : ℕ) (u : ℂ)
    (e : H * (q : ℝ≥0) ^ (2 * b) = (q : ℝ≥0) ^ (2 * a)) :
    ((H : ℝ) : ℂ) ^ u = (q : ℂ) ^ (((a : ℂ) - b) * (2 * u)) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have e' : (H : ℝ) * (q : ℝ) ^ (2 * b) = (q : ℝ) ^ (2 * a) := by exact_mod_cast e
  have hH : (H : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e'
    exact (pow_pos hqr _).ne e'
  have hlog : Real.log H = (2 * (a : ℝ) - 2 * b) * Real.log q := by
    have := congrArg Real.log e'
    rw [Real.log_mul hH (pow_pos hqr _).ne', Real.log_pow, Real.log_pow] at this
    push_cast at this
    linarith
  have hHc : ((H : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hH
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Complex.cpow_def_of_ne_zero hHc, Complex.cpow_def_of_ne_zero hqc]
  congr 1
  rw [← Complex.ofReal_log H.coe_nonneg, hlog, show (q : ℂ) = ((q : ℝ) : ℂ) by simp,
    ← Complex.ofReal_log hqr.le]
  push_cast
  ring

section Residue

variable {k : Type} [Field k] [Fintype k]

def Wz (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (z : ℂ) (g : GL (Ix n) k) : ℂ :=
  ∑ Y : Matrix (Fin n) (Fin n) k, coY ψ₀ β Y *
    (Fintype.card k : ℂ) ^ (((iD (g * nU Y) : ℂ) - iD g) * (2 * z + n))

def cZ (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (z : ℂ) : ℂ :=
  sumG (fun g => (Fintype.card k : ℂ) ^ (2 * n * iD g) * Wz ψ₀ β z g) /
    sumG (fun g : GL (Ix n) k => (Fintype.card k : ℂ) ^ (2 * n * iD g))

lemma Wz_left (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (z : ℂ) (a d : GL (Fin n) k)
    (b : Matrix (Fin n) (Fin n) k) (g : GL (Ix n) k) : Wz ψ₀ β z (pM a d b * g) = Wz ψ₀ β z g := by
  unfold Wz
  simp only [mul_assoc, iD_pM_mul]

lemma sumG_den_ne : sumG (fun g : GL (Ix n) k => (Fintype.card k : ℂ) ^ (2 * n * iD g)) ≠ 0 := by
  haveI : Fintype (GL (Ix n) k) := Fintype.ofFinite _
  unfold sumG
  rw [finsum_eq_sum_of_fintype]
  have e : ∑ g : GL (Ix n) k, (Fintype.card k : ℂ) ^ (2 * n * iD g) =
      ((∑ g : GL (Ix n) k, (Fintype.card k : ℝ) ^ (2 * n * iD g) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e]
  have hq : (0 : ℝ) < Fintype.card k := by exact_mod_cast Fintype.card_pos
  have : 0 < ∑ g : GL (Ix n) k, (Fintype.card k : ℝ) ^ (2 * n * iD g) :=
    Finset.sum_pos (fun g _ => pow_pos hq _) Finset.univ_nonempty
  exact_mod_cast this.ne'

lemma diff_cZ (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) : Differentiable ℂ (cZ ψ₀ β) := by
  haveI : Fintype (GL (Ix n) k) := Fintype.ofFinite _
  have hq : (Fintype.card k : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hW : ∀ g : GL (Ix n) k, Differentiable ℂ (fun z => Wz ψ₀ β z g) := by
    intro g
    unfold Wz
    refine Differentiable.fun_sum (fun Y _ => ?_)
    refine Differentiable.const_mul ?_ _
    refine Differentiable.const_cpow ?_ (Or.inl hq)
    fun_prop
  unfold cZ sumG
  simp only [finsum_eq_sum_of_fintype]
  refine Differentiable.div_const ?_ _
  refine Differentiable.fun_sum (fun g _ => ?_)
  exact (hW g).const_mul _

lemma cZ_ne (hPos : JpPos) {r t : ℕ} (hrt : r + t = n) (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1)
    (β : Matrix (Fin n) (Fin n) k) (hβ : β.rank = r) : cZ ψ₀ β ((t : ℂ) / 2) ≠ 0 := by
  have hq : (Fintype.card k : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨x, hx, hsum⟩ := hPos k n r (n + t) ψ₀ hψ β hβ (by omega)
  have hnum : (fun g : GL (Ix n) k => (Fintype.card k : ℂ) ^ (2 * n * iD g) * Wz ψ₀ β ((t : ℂ) / 2) g) =
      fun g => ∑ Y : Matrix (Fin n) (Fin n) k, (Fintype.card k : ℂ) ^ (r * iD g) * coY ψ₀ β Y *
        (Fintype.card k : ℂ) ^ ((n + t) * iD (g * nU Y)) := by
    funext g
    unfold Wz
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    have e1 : (Fintype.card k : ℂ) ^ (((iD (g * nU Y) : ℂ) - iD g) * (2 * ((t : ℂ) / 2) + n)) *
        (Fintype.card k : ℂ) ^ ((n + t) * iD g) = (Fintype.card k : ℂ) ^ ((n + t) * iD (g * nU Y)) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq]
      congr 1
      push_cast
      ring
    have e2 : (Fintype.card k : ℂ) ^ (2 * n * iD g) =
        (Fintype.card k : ℂ) ^ (r * iD g) * (Fintype.card k : ℂ) ^ ((n + t) * iD g) := by
      rw [← pow_add]
      congr 1
      have : 2 * n = r + (n + t) := by omega
      rw [this, add_mul]
    rw [e2, ← e1]
    ring
  unfold cZ
  rw [hnum, hsum]
  exact div_ne_zero (by exact_mod_cast hx.ne') sumG_den_ne

end Residue

end AltPf

open AltPf in

theorem jpAlt_of_steps : JpIw → JpHgt → JpUnif → JpCmp → JpPos → JpCondition := by
  intro hIw hHgt hUnif hCmp hPos
  intro O L _ _ _ _ _ _ _ n r t hrt hr ψ₀ hψ β hβ
  refine ⟨cZ ψ₀ β, diff_cZ ψ₀ β, cZ_ne hPos hrt ψ₀ hψ β hβ, ?_⟩
  intro ϖ hϖ w hw ℓ hℓ nv hnv h hh X _ _ _ ν _ _ ρ hρ hmeas z
  have hT : ∀ κ : GL (Ix n) O, ∃ hb, IsRed (O := O) w κ hb := by
    intro κ
    obtain ⟨a, d, b, κ', e⟩ := hIw O L n (inL κ * tauM w)
    exact ⟨resK κ', a, d, b, κ', e, rfl⟩
  choose T hTr using hT
  have hF : ∀ (κ : GL (Ix n) O) (Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
      (((h (inL κ * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) =
        (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^
          (((iD (T κ * nU Y) : ℂ) - iD (T κ)) * (2 * z + n)) := by
    intro κ Y
    rw [cpow_key Fintype.card_pos _ _ _ (z + (n : ℂ) / 2)
      (h_red hIw hHgt hϖ hw hnv hh hℓ κ (T κ) (hTr κ) Y)]
    congr 2
    ring
  have hW : ∀ κ : GL (Ix n) O, Wz ψ₀ β z (T κ) =
      ∑ Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), coY ψ₀ β Y *
        (((h (inL κ * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) := by
    intro κ
    unfold Wz
    exact Finset.sum_congr rfl (fun Y _ => by rw [hF])
  have hinv : ∀ κ : GL (Ix n) O, ∀ γ ∈ Gam2 (n := n) ϖ,
      Wz ψ₀ β z (T (κ * γ)) = Wz ψ₀ β z (T κ) := by
    intro κ γ hγ
    rw [hW, hW]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    have := h_gam (L := L) hIw hw hh (Y.map ℓ) κ γ hγ
    unfold liftM
    rw [this]
  have hint : (fun x : X => ∑ Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), coY ψ₀ β Y *
      (((h (inL (ρ x) * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2)) =
      fun x => (fun κ => Wz ψ₀ β z (T κ)) (ρ x) := by
    funext x
    exact (hW (ρ x)).symm
  have h1 := hUnif O n ϖ hϖ X ν ρ hρ hmeas (fun κ => Wz ψ₀ β z (T κ)) hinv
  have h2 := hCmp O L n ϖ hϖ w hw (Wz ψ₀ β z) (Wz_left ψ₀ β z) T hTr
  rw [hint]
  exact h1.trans h2

end GlobalTheory.CompanionTheory.Jp
end
