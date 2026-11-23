import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem BK.X_pow_natDegree_mem {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
  simp only [map_add, map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X] at h
  have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i ∈
      Ideal.span {(l : bk.S)} := by
    refine Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    rw [hc, map_mul, map_natCast, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [BK.E, h]; ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hs)

set_option maxHeartbeats 1000000 in

theorem BK.hom_eq_of_X_C {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B)
    (hX : BK.hf f X = BK.hf g X) (hC : ∀ w, BK.hf f (C w) = BK.hf g (C w)) : f = g := by
  have hpoly : ∀ p : Polynomial (Wq l bk.a), BK.hf f (p : bk.S) = BK.hf g (p : bk.S) := by
    have e : (BK.hf f).comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
        (BK.hf g).comp Polynomial.coeToPowerSeries.ringHom :=
      Polynomial.ringHom_ext (fun a => by simpa using hC a) (by simpa using hX)
    exact fun p => RingHom.congr_fun e p
  have hle : Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} ≤
      (Ideal.span {(l : B.A)} ⊔ B.I).comap (BK.hf f) := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_sup_right (f.f_I _ (Ideal.mem_span_singleton_self _))
  have hXe : BK.hf f X ^ bk.Ep.natDegree ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
    rw [← map_pow]; exact hle bk.X_pow_natDegree_mem
  refine Hom.ext' (RingHom.ext fun (s : bk.S) => ?_)
  show BK.hf f s = BK.hf g s
  haveI : IsAdicComplete (Ideal.span {(l : B.A)} ⊔ B.I) B.A := B.complete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : B.A)} ⊔ B.I) B.A) _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ : (X : bk.S) ^ (bk.Ep.natDegree * n) ∣ s - (trunc (bk.Ep.natDegree * n) s : bk.S) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, coeff_trunc, hm]
  have e : s = (trunc (bk.Ep.natDegree * n) s : bk.S) + X ^ (bk.Ep.natDegree * n) * r := by
    rw [← hr]; ring
  have hd : BK.hf f s - BK.hf g s = BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) := by
    rw [e]
    simp only [map_add, map_mul, map_pow]
    rw [hpoly (trunc (bk.Ep.natDegree * n) s), ← hX]; ring
  have h2 : BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) ∈
      (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by
    rw [pow_mul]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXe n)
  have h3 : BK.hf f s - BK.hf g s ∈ (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by rw [hd]; exact h2
  rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact h3

theorem BK.galHom_comp_ι_of_fixFlat {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (hg : bk.FixFlat g) :
    (ainfHom K g).comp bk.ι = bk.ι := by
  refine BK.hom_eq_of_X_C bk _ _ ?_ ?_
  · change Per.σA (g : GQ l) (bk.ev X) = bk.ev X
    rw [bk.ev_X]
    exact (GlobalTheory.RingIface.sigA_teich l _ _).trans (congrArg _ hg)
  · intro w
    change Per.σA (g : GQ l) (bk.ev (C w)) = bk.ev (C w)
    rw [bk.ev_C, bk.gal_w]

theorem MReal.gal_of_fixFlat {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {T : Matrix (Fin d) (Fin d) (WCb l)} (h : MReal S ρ T)
    (g : ↥(GK K)) (hg : bk.FixFlat g) : zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
  have e := h.gal g
  rw [BK.galHom_comp_ι_of_fixFlat bk g hg, S.ε_refl] at e
  exact e.trans ((congrArg (T * ·) (Matrix.map_one (inclW l) (map_zero _) (map_one _))).trans (Matrix.mul_one T))

theorem MReal.exists_fixed_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d)
    (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) →
    ∃ X : Matrix (Fin d') (Fin d) (WCb l), T' * X = zW f * T ∧
      (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) ∧
      bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨u, hu⟩ := hT'.unit
  have cancel : ∀ M N : Matrix (Fin d') (Fin d) (WCb l), T' * M = T' * N → M = N := by
    intro M N h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * T) with hXm
  have hX : T' * Xm = zW f * T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine ⟨Xm, hX, fun g hg => ?_, ?_⟩
  · let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * T'.map G = T' := hT'.gal_of_fixFlat g hg
    have a2 : zW (ρ g) * T.map G = T := hT.gal_of_fixFlat g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc T' * Xm.map G = zW (ρ' g) * (T'.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = T' * Xm := by rw [a2, hX]
  · let F : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map F = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ S.a • T.map F = T * S.A.map bk.evW := hT.φ
    have b2 : bk.evW bk.E ^ S'.a • T'.map F = T' * S'.A.map bk.evW := hT'.φ
    change bk.evW bk.E ^ S.a • (S'.A.map bk.evW * Xm.map F) = bk.evW bk.E ^ S'.a • (Xm * S.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map F) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

end GlobalTheory.BSP
