import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.LocPhiUnit

section Fixed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
  (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

theorem exists_inclPlus_half (z : k ⊗[maximalRealSubfield E] Fld Q) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q,
      inclPlus Q k a = ((1 : k) ⊗ₜ[maximalRealSubfield E] (2⁻¹ : Fld Q)) * (z + involBase Q k z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨(y + invol Q y) / 2, ?_⟩, ?_⟩
    · change invol Q _ = _
      simp only [map_div₀, map_add, invol_invol, map_ofNat, AlgHom.id_apply, add_comm]
    · change s ⊗ₜ[maximalRealSubfield E] ((y + invol Q y) / 2) = _ * (s ⊗ₜ y + s ⊗ₜ invol Q y)
      rw [← TensorProduct.tmul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_inv_mul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb, map_add]
    ring

theorem exists_inclPlus_of_fixed {z : k ⊗[maximalRealSubfield E] Fld Q} (hz : involBase Q k z = z) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q, inclPlus Q k a = z := by
  obtain ⟨a, ha⟩ := exists_inclPlus_half Q k z
  refine ⟨a, ?_⟩
  have h2 : (2 : k ⊗[maximalRealSubfield E] Fld Q) = (1 : k) ⊗ₜ[maximalRealSubfield E] (2 : Fld Q) :=
    (map_ofNat (Algebra.TensorProduct.includeRight :
      Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q) 2).symm
  rw [ha, hz, ← two_mul, ← mul_assoc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    inv_mul_cancel₀ two_ne_zero, ← Algebra.TensorProduct.one_def, one_mul]

theorem inclPlus_injective : Function.Injective (inclPlus Q k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (plus Q).val.toLinearMap
    Subtype.val_injective

theorem exists_unit_of_fixed {y : k ⊗[maximalRealSubfield E] Fld Q} (hu : IsUnit y)
    (hy : involBase Q k y = y) :
    ∃ x : (k ⊗[maximalRealSubfield E] plus Q)ˣ,
      inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = y := by
  obtain ⟨u, rfl⟩ := hu
  have hinv : involBase Q k ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) :
      k ⊗[maximalRealSubfield E] Fld Q) = (u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) := by
    have h1 : (u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
        ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.mul_inv, map_one]
    calc _ = ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) *
          ((u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
            ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q)) := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [h1, mul_one]
  obtain ⟨a, ha⟩ := exists_inclPlus_of_fixed Q k hy
  obtain ⟨b, hb⟩ := exists_inclPlus_of_fixed Q k hinv
  have hab : a * b = 1 := inclPlus_injective Q k (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Fixed

section Matrix

theorem aeval_mul_of_intertwine {K : Type} [Field K] {n : ℕ} {B C H : Matrix (Fin n) (Fin n) K}
    (h : B * H = H * C) (g : K[X]) : aeval B g * H = H * aeval C g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]
  | monomial d a =>
    have e : B ^ d * H = H * C ^ d :=
      (((show SemiconjBy H C B from h.symm).pow_right d).eq).symm
    rw [aeval_monomial, aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_assoc, e]

theorem cT_mul {K : Type} [Field K] (s : K →+* K) {n : ℕ} (B C : Matrix (Fin n) (Fin n) K) :
    cT s (B * C) = cT s C * cT s B := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

end Matrix

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem involBase_locPhi (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    {r : ℕ} (Q : SelfRecip E r) {r₀ : E[X]} (hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0)
    (f : (w.adicCompletion E)[X]) :
    involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q f) =
      locPhi hU w hw v hv Q ((f.map (cj w)).comp (atPl w r₀)) := by
  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (inclBase Q k).toRingHom.comp (locJ hU w hw v hv).toRingHom
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (locJ hU w hw v hv y)) =
      inclBase Q k (locJ hU w hw v hv (cj w y))
    rw [locJ_cj]
    generalize locJ hU w hw v hv y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (involBase Q k).toRingHom
  have hR : locPhi hU w hw v hv Q (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [locPhi_atPl]
    congr 1
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at hr
    exact eq_inv_of_mul_eq_one_right hr
  have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
  have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    change (1 : k) ⊗ₜ invol Q (alpha Q) = _
    rw [invol_alpha]
  change ib (eval₂ ι _ f) = eval₂ ι _ _
  rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
  exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm

end Local

theorem locPhi_mem_units_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ hH hdet h3 m hM hMdet r Q hQ
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
  obtain ⟨A, hA⟩ : ∃ A, A = γ₀.val.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H, H = H₀.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  rw [← hA, ← hHd] at hM hMdet
  obtain ⟨M, hMd⟩ : ∃ M, M = aeval A m := ⟨_, rfl⟩
  rw [← hMd] at hM hMdet
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := by rw [hA]; exact Matrix.charpoly_map _ _
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hHh : cT (cj w) H = H := by
    rw [hHd, ← cT_map hU w hw]
    exact congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hH
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h3
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    rw [hA, hHd]
    exact this
  have hint : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hH0 : IsUnit H := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at *
    exact (left_ne_zero_of_mul hMdet).isUnit
  have hM0 : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [Matrix.det_mul] at hMdet
    exact (right_ne_zero_of_mul hMdet).isUnit
  have hfix : M = aeval A ((m.map (cj w)).comp (atPl w r₀)) := by
    have h1 : cT (cj w) M * H = H * M := by
      have := hM
      rw [IsHerm, cT_mul, hHh] at this
      exact this
    rw [hMd, GlobalTheory.NormInert.cT_aeval, aeval_mul_of_intertwine hint, ← aeval_comp, ← hMd] at h1
    exact (hH0.mul_left_cancel h1).symm
  have hdiv : A.charpoly ∣ (m.map (cj w)).comp (atPl w r₀) - m :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by rw [map_sub, ← hfix, ← hMd, sub_self])
  have hΦ0 : locPhi hU w hw v hv Q A.charpoly = 0 := by
    rw [hAP, locPhi_atPl]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hy : involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q m) =
      locPhi hU w hw v hv Q m := by
    obtain ⟨t, ht⟩ := hdiv
    rw [involBase_locPhi hU w hw v hv Q hr, ← sub_eq_zero, ← map_sub, ht, map_mul, hΦ0, zero_mul]
  obtain ⟨u, hu⟩ := hM0
  have hcomm : Commute A (u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hu, hMd]
    have := congrArg (aeval A) (mul_comm (X : (w.adicCompletion E)[X]) m)
    rw [map_mul, map_mul, aeval_X] at this
    exact this
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A
    ((u⁻¹ : (Matrix (Fin n) (Fin n) (w.adicCompletion E))ˣ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    hAsep hcomm.units_inv_right.eq
  have hdiv2 : A.charpoly ∣ m * g - 1 :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by
      rw [map_sub, map_mul, ← hg, ← hMd, ← hu, Units.mul_inv, map_one, sub_self])
  have hone : locPhi hU w hw v hv Q m * locPhi hU w hw v hv Q g = 1 := by
    obtain ⟨t, ht⟩ := hdiv2
    rw [← map_mul, ← sub_eq_zero, ← map_one (locPhi hU w hw v hv Q), ← map_sub, ht, map_mul, hΦ0,
      zero_mul]
  exact exists_unit_of_fixed Q _ (isUnit_iff_exists_inv.2 ⟨_, hone⟩) hy

end GlobalTheory.CompanionTheory.LocPhiUnit

end
