import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCar
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ParCols
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.NormCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FrameCongSec

theorem coef_of_inMod (I : Formalism.MainNotions.S.AutInst) (m : ℕ) {ι : Type} [Fintype ι] (v : ι → VA I) (S : Set ι) (x : VA I)
    (h : InMod I m (v '' S) x) :
    ∃ t : ι → I.E ⊗[I.F] Af I.F, (∀ i, t i ∈ IntAf I.F I.E) ∧ (∀ i, i ∉ S → t i = 0) ∧
      x - ∑ i, t i • v i ∈ mL I m := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hy
  refine ⟨fun i => (l i : I.E ⊗[I.F] Af I.F), fun i => (l i).2, fun i hi => ?_, ?_⟩
  · have h0 : l i = 0 := (Finsupp.mem_supported' _ _).1 hl i hi
    simp [h0]
  · have e : Finsupp.linearCombination (IntAf I.F I.E) v l = ∑ i, (l i : I.E ⊗[I.F] Af I.F) • v i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; exact zero_smul _ _
    rw [e, add_sub_cancel_left]
    exact hw

variable {D : D7}

theorem frame_congruence_holds : FrameCongC := by
  intro D X Y u u' ρ ρ' γ σ hRL hκ
  obtain ⟨hE0, -, hZ0, -, -⟩ := frame_Lf X
  have hTF : FrameTie X u u' (X.Fu u) (X.Fu u') := Formalism.L2.SG.Full.Full.frameTie u u'
  set g1 : X.B.I.Gf := ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u with hg1
  set g2 : X.B.I.Gf := ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u' with hg2
  have haC : aC (Y.cs u) ρ = g1 := rfl
  rw [haC]
  set κ := kOf X u u' ((Y.cs u).h ρ : X.B.I.Gf) ((Y.cs u').h ρ' : X.B.I.Gf) γ with hκd
  have hκ' : κ = g1⁻¹ * γ.2 * g2 := rfl
  obtain ⟨hκK, hcE, hcZ, -⟩ := hκ
  have hg0 : 0 < X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  set e0v : Fin (D.R.rS + 1) → VA X.B.I := Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 with he0v
  have he0vL : ∀ a, e0v a ∈ X.B.I.Lf := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, Fin.snoc_last]; exact hZ0
    · simp only [he0v, Fin.snoc_castSucc]; exact hE0 i

  have hcol : ∀ c : Fin (D.R.rS + 1), ∃ t : Fin (D.R.rS + 1) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F,
      (∀ a, t a ∈ IntAf X.B.I.F X.B.I.E) ∧ t c = 1 ∧ (∀ a, c < a → t a = 0) ∧
      X.B.I.fmat κ *ᵥ e0v c - ∑ a, t a • e0v a ∈ mL X.B.I X.B.g := by
    intro c
    cases c using Fin.lastCases with
    | last =>
      have hZ' : InMod X.B.I X.B.g (X.e0 '' Set.univ) ((X.B.I.fmat κ - 1) *ᵥ X.z0) := by
        rw [Set.image_univ]; exact hcZ
      obtain ⟨τ, hτI, -, hτ⟩ := coef_of_inMod X.B.I X.B.g X.e0 Set.univ _ hZ'
      refine ⟨Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) τ 1, fun a => ?_, ?_, fun a ha => ?_, ?_⟩
      · cases a using Fin.lastCases with
        | last => simp only [Fin.snoc_last]; exact one_mem _
        | cast j => simp only [Fin.snoc_castSucc]; exact hτI j
      · simp only [Fin.snoc_last]
      · exact absurd ha (not_lt.2 (Fin.le_last a))
      · have e : X.B.I.fmat κ *ᵥ e0v (Fin.last _) -
            ∑ a, (Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) τ 1 a) • e0v a =
            (X.B.I.fmat κ - 1) *ᵥ X.z0 - ∑ j, τ j • X.e0 j := by
          simp only [Fin.sum_univ_castSucc, he0v, Fin.snoc_castSucc, Fin.snoc_last, one_smul, Matrix.sub_mulVec,
            Matrix.one_mulVec]
          abel
        rw [e]; exact hτ
    | cast b =>
      obtain ⟨τ, hτI, hτ0, hτ⟩ := coef_of_inMod X.B.I X.B.g X.e0 {j | j.1 < b.1} _ (hcE b)
      have hτb : τ b = 0 := hτ0 b (fun h => lt_irrefl (b : ℕ) h)
      refine ⟨Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun j => τ j + if j = b then 1 else 0) 0,
        fun a => ?_, ?_, fun a ha => ?_, ?_⟩
      · cases a using Fin.lastCases with
        | last => simp only [Fin.snoc_last]; exact zero_mem _
        | cast j =>
          simp only [Fin.snoc_castSucc]
          refine add_mem (hτI j) ?_
          split_ifs
          · exact one_mem _
          · exact zero_mem _
      · simp [Fin.snoc_castSucc, hτb]
      · cases a using Fin.lastCases with
        | last => simp only [Fin.snoc_last]
        | cast j =>
          have hbj : b < j := Fin.castSucc_lt_castSucc_iff.1 ha
          have hj : τ j = 0 := hτ0 j (fun h => lt_asymm hbj h)
          have hjb : j ≠ b := fun h => by subst h; exact lt_irrefl _ hbj
          simp only [Fin.snoc_castSucc, hj, if_neg hjb, add_zero]
      · have e : X.B.I.fmat κ *ᵥ e0v (Fin.castSucc b) -
            ∑ a, (Fin.snoc (α := fun _ => X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
              (fun j => τ j + if j = b then 1 else 0) 0 a) • e0v a =
            (X.B.I.fmat κ - 1) *ᵥ X.e0 b - ∑ j, τ j • X.e0 j := by
          simp only [Fin.sum_univ_castSucc, he0v, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero, add_smul,
            Finset.sum_add_distrib, ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
            Matrix.sub_mulVec, Matrix.one_mulVec]
          abel
        rw [e]; exact hτ
  choose t htI ht1 ht0 htm using hcol

  set s : D.host.E → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
    fun x => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) with hs
  have happ : ∀ c a, ∃ ξ : 𝓞 D.host.E, ∃ y ∈ IntAf X.B.I.F X.B.I.E,
      t c a = s (ξ : D.host.E) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y := by
    intro c a
    obtain ⟨a', y, hy, he⟩ := PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g hg0 (t c a) (htI c a)
    have hint : IsIntegral ℤ (X.ιE (a' : X.B.I.E)) := (a'.2 : IsIntegral ℤ (a' : X.B.I.E)).map X.ιE.toRingHom.toIntAlgHom
    refine ⟨⟨X.ιE (a' : X.B.I.E), hint⟩, y, hy, ?_⟩
    show t c a = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (X.ιE (a' : X.B.I.E))) + _
    rw [RingEquiv.symm_apply_apply]
    exact he
  choose ξ0 y0 hy0 hξ0 using happ
  set ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E) :=
    fun a c => if a < c then ξ0 c a else if a = c then 1 else 0 with hξd
  have hsI : ∀ a c, s (ξ a c : D.host.E) ∈ IntAf X.B.I.F X.B.I.E := fun a c => inclE_int X (ξ a c)
  have hrel : ∀ a c, ∃ y ∈ IntAf X.B.I.F X.B.I.E,
      t c a = s (ξ a c : D.host.E) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * y := by
    intro a c
    rcases lt_trichotomy a c with h | h | h
    · refine ⟨y0 c a, hy0 c a, ?_⟩
      simp only [hξd, if_pos h]
      exact hξ0 c a
    · subst h
      refine ⟨0, zero_mem _, ?_⟩
      simp only [hξd, lt_irrefl, if_false, if_pos rfl, ht1, mul_zero, add_zero, hs]
      simp
    · refine ⟨0, zero_mem _, ?_⟩
      have hna : ¬ a < c := not_lt.2 h.le
      have hne : a ≠ c := ne_of_gt h
      simp only [hξd, if_neg hna, if_neg hne, ht0 c a h, mul_zero, add_zero, hs]
      simp
  refine ⟨ξ, fun a b hab => ?_, fun a => ?_, fun b => ?_⟩
  · simp only [hξd, if_neg (not_lt.2 hab.le), if_neg (ne_of_gt hab)]
  · simp [hξd]

  set Yv : Fin (D.R.rS + 1) → VA X.B.I := fun a => X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd ((X.Fu u).fvec a)) with hY
  set Yv' : Fin (D.R.rS + 1) → VA X.B.I := fun c => X.B.I.fmat g2⁻¹ *ᵥ incl X.B.I (X.crd ((X.Fu u').fvec c))
    with hY'
  have fixE : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w) (a : Fin D.R.rS),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) :=
    fun w h a => fixes_inv X (fixes_mul X (h.2 _ (Or.inl (Or.inl ⟨a, rfl⟩))) ((X.xu_fix w a).1))
  have fixZ : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) =
        X.B.I.fmat (X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) := by
    intro w h
    have hz : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = incl X.B.I (X.crd (X.zu w)) :=
      fixes_inv X (h.2 _ (Or.inr rfl))
    rw [_root_.mul_inv_rev, fmat_mul, ← Matrix.mulVec_mulVec, hz]
  have hYa : ∀ a, InAt X.B.I X.B.g X.B.g (e0v a - Yv a) := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, hY, Fin.snoc_last, FlagG.fvec, hTF.2.1, hg1, fixZ]
      have := InAt_neg X (X.xu_z u)
      rwa [neg_sub] at this
    · simp only [he0v, hY, Fin.snoc_castSucc, FlagG.fvec, hTF.1 i, hg1, fixE]
      exact (X.basisApprox i).1
  have hY'a : ∀ c, InAt X.B.I X.B.g X.B.g (e0v c - Yv' c) := by
    intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [he0v, hY', Fin.snoc_last, FlagG.fvec, hTF.2.2.2, hg2, fixZ]
      have := InAt_neg X (X.xu_z u')
      rwa [neg_sub] at this
    · simp only [he0v, hY', Fin.snoc_castSucc, FlagG.fvec, hTF.2.2.1 i, hg2, fixE]
      exact (X.basisApprox i).1

  have e : X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (σ (frame (lf D (X.Fu u')) b) -
      frameAct (frame (lf D (X.Fu u))) ξ b)) = X.B.I.fmat κ *ᵥ Yv' b - ∑ a, s (ξ a b : D.host.E) • Yv a := by
    simp only [frameAct, crd_sub', crd_sum', crd_smul', incl_sub', incl_sum', incl_smul', Matrix.mulVec_sub,
      mulVec_fsum, Matrix.mulVec_smul, ratLink_incl X hRL]
    congr 1
    simp only [hY', Matrix.mulVec_mulVec, hκ', ← fmat_mul]
    congr 2
    group
  rw [e]
  have split : X.B.I.fmat κ *ᵥ Yv' b - ∑ a, s (ξ a b : D.host.E) • Yv a =
      (X.B.I.fmat κ *ᵥ e0v b - ∑ a, t b a • e0v a) - X.B.I.fmat κ *ᵥ (e0v b - Yv' b) +
        ∑ a, (t b a - s (ξ a b : D.host.E)) • e0v a + ∑ a, s (ξ a b : D.host.E) • (e0v a - Yv a) := by
    simp only [Matrix.mulVec_sub, smul_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [split]
  have inAt_mL : ∀ w : VA X.B.I, w ∈ mL X.B.I X.B.g → InAt X.B.I X.B.g X.B.g w := fun w hw =>
    ⟨1, Nat.coprime_one_left _, by rw [Nat.cast_one, one_smul]; exact hw⟩
  refine InAt_add X (InAt_add X (InAt_sub X (inAt_mL _ (htm b)) (InAt_K X hκK (hY'a b)))
    (InAt_sum X _ _ fun a _ => inAt_mL _ ?_)) (InAt_sum X _ _ fun a _ => InAt_smul X (hsI a b) (hYa a))
  obtain ⟨y, hy, hty⟩ := hrel a b
  rw [hty, add_sub_cancel_left, mul_smul]
  have hyL : y • e0v a ∈ X.B.I.Lf := by
    have : y • e0v a = (⟨y, hy⟩ : IntAf X.B.I.F X.B.I.E) • e0v a := rfl
    rw [this]; exact Submodule.smul_mem _ _ (he0vL a)
  exact Formalism.L2.SG.Pf.unitaryCongruence.smul_mem_mL X.B.I hyL

end FrameCongSec

end Formalism.L2.SG.Pf.RegroupPf
