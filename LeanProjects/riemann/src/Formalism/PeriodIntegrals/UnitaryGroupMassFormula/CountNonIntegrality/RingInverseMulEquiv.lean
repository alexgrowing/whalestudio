import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Development

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocGen : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D) (m : ℕ), ∃ x : D.host.E,
      x ∈ ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧ star x = x ∧
      ∃ w ∈ (D.s.atP p).O,
        Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ m) =
          w * (D.s.atP p).ιE x

theorem ringInverse_mulEquiv {R S : Type*} [MonoidWithZero R] [MonoidWithZero S] (f : R ≃* S) (x : R) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  have f0 : f 0 = 0 := by
    calc f 0 = f (0 * f.symm 0) := by rw [zero_mul]
      _ = f 0 * f (f.symm 0) := map_mul f _ _
      _ = 0 := by rw [f.apply_symm_apply, mul_zero]
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    have e : f u = ((Units.map f.toMonoidHom u : Sˣ) : S) := rfl
    rw [Ring.inverse_unit, e, Ring.inverse_unit]
    rfl
  · have hf : ¬ IsUnit (f x) := fun hu => h (by simpa using hu.map f.symm)
    rw [Ring.inverse_non_unit x h, Ring.inverse_non_unit _ hf]
    exact f0

theorem iE_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) (o : 𝓞 D.host.E) : (D.s.atP p).ιE (o : D.host.E) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h1 : IsIntegral ℤ ((D.s.atP p).ιE (o : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (D.s.atP p).ιE.toIntAlgHom
  exact h1.tower_top

theorem cj_frFac (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a : Fin (D.R.rS + 1)) :
    (D.s.atP p).cj (frFac δ p a) = frFac δ p a := by
  unfold frFac
  rw [show ∀ x, (D.s.atP p).cj (Ring.inverse x) = Ring.inverse ((D.s.atP p).cj x) from
    fun x => ringInverse_mulEquiv (D.s.atP p).cj.toMulEquiv x]
  rw [map_pow, map_mul, AlgEquiv.commutes, (D.s.atP p).cj_ιE, map_ratCast]

theorem frame_mem {D : Formalism.BasicNotions.D7} {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (VS D) D.R.rS T) (hX : XLam Λ F = XS D F.fl) (hz : F.fl.z ∈ Λ) (a : Fin (D.R.rS + 1))
    (x : D.host.E)
    (hx : x ∈ ((ddS D) ^ (-((D.R.rS - a.val : ℕ) : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) :
    x • F.fl.fvec a ∈ Λ := by
  have hXS : XS D F.fl ≤ Λ := by
    rw [← hX]
    unfold XLam
    exact inf_le_left
  induction a using Fin.lastCases with
  | last =>
    unfold FlagG.fvec
    rw [Fin.snoc_last]
    simp only [Fin.val_last, Nat.sub_self, Nat.cast_zero, neg_zero, zpow_zero] at hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    rw [algebraMap_smul]
    exact Λ.smul_mem o hz
  | cast b =>
    have e1 : (-((D.R.rS - (Fin.castSucc b).val : ℕ) : ℤ)) = -((D.R.rS : ℤ) - ((b : ℕ) : ℤ)) := by
      rw [Fin.coe_castSucc, Nat.cast_sub b.isLt.le]
    rw [e1] at hx
    have hmem : x • F.fl.e b ∈ XS D F.fl := by
      unfold XS
      apply Submodule.subset_span
      exact ⟨b, x, hx, rfl⟩
    unfold FlagG.fvec
    rw [Fin.snoc_castSucc]
    exact hXS hmem

theorem intL_of (hG : LocGen) : IntL := by
  intro D δ M hA u u' hT F0 what₂ hR Λ hΛ Z F' hF' p hs a b
  obtain ⟨hTerm, -, -, hOK, hZ⟩ := hF'
  obtain ⟨-, -, hreps, -⟩ := hR
  obtain ⟨-, ⟨-, hU, hz0, -⟩, hX0⟩ := hreps.1 Λ hΛ
  have hz' : F'.fl.z ∈ Λ := hTerm.1.1
  obtain ⟨xa, hxa, hsa, wa, hwa, hfa⟩ := hG D δ M hA p (D.R.rS - a.val)
  obtain ⟨xb, hxb, -, wb, hwb, hfb⟩ := hG D δ M hA p (D.R.rS - b.val)
  have ma : xa • F0.fvec a ∈ Λ := frame_mem Λ (lf D F0) hX0 hz0.1 a xa hxa
  have mb : xb • F'.fl.fvec b ∈ Λ := frame_mem Λ F' hOK.2 hz' b xb hxb
  have hd : xb • F'.fl.fvec b ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
    have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
    rw [hU']
    exact mb
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hd
  rw [Submodule.mem_iInf] at hd
  have hd2 := hd (xa • F0.fvec a)
  rw [Submodule.mem_iInf] at hd2
  have hint := hd2 ma
  rw [Submodule.mem_comap] at hint
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hint
  have hpair : (VS D).hT (xa • F0.fvec a) (xb • F'.fl.fvec b) = xa * xb * Z a b := by
    rw [← hZ]
    simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul]
    rw [starRingEnd_apply, hsa]
    show xb * (xa * (VS D).hT (F0.fvec a) (F'.fl.fvec b)) = xa * xb * brS (VS D) (F'.fl.fvec b) (F0.fvec a)
    simp only [brS]
    ring
  have hO : (M p).L.O = (D.s.atP p).O := (hA p).2.2.2.1
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  show frFac δ p b * (M p).L.cj (frFac δ p a) * (D.s.atP p).ιE (Z a b) ∈ (M p).L.O
  rw [hcj, cj_frFac, hO]
  have e2 : frFac δ p b * frFac δ p a * (D.s.atP p).ιE (Z a b) =
      (wb * wa) * (D.s.atP p).ιE (xa * xb * Z a b) := by
    unfold frFac
    rw [hfa, hfb, map_mul, map_mul]
    ring
  rw [e2, ← hpair]
  simp only [LinearMap.coe_restrictScalars] at ho
  rw [← ho]
  exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem hwb hwa) (iE_mem_O D p o)

theorem notIntAll_of_gen (hL : LocGen) (hG : IntG) : PI.CntLocalParts.NotIntAll :=
  notIntAll_of_LG (intL_of hL) hG

end PI.CntNotIntW
