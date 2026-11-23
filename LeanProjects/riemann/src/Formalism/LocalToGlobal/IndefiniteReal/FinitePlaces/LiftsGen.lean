import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

noncomputable section

namespace Formalism.IndefR.Fin.Lifts

section Gen

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.L2.Herm Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem span_dualSet_eq (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    ((Submodule.span (𝓞 E) (dualSet σ J L) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = dualSet σ J L := by
  refine Set.Subset.antisymm ?_ Submodule.subset_span
  intro v hv
  rw [SetLike.mem_coe] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    unfold dualSet
    intro w _
    refine ⟨0, ?_⟩
    unfold hform
    simp
  | add x y hx' hy' hx hy =>
    clear hx' hy'
    unfold dualSet at hx hy ⊢
    intro w hw
    obtain ⟨a, ha⟩ := hx w hw
    obtain ⟨b, hb⟩ := hy w hw
    clear hx hy hw
    refine ⟨a + b, ?_⟩
    unfold hform at ha hb ⊢
    rw [map_add, ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Pi.add_apply, mul_add]
  | smul c x hx' hx =>
    clear hx'
    unfold dualSet at hx ⊢
    intro w hw
    obtain ⟨a, ha⟩ := hx w hw
    refine ⟨c * a, ?_⟩
    unfold hform at ha ⊢
    rw [map_mul, ha, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Pi.smul_apply, Algebra.smul_def]
    ring

theorem exists_gramS_sd (hc : CMData F E) {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {β : GL (Fin n) (E ⊗[F] Af F)} (hJ : IsUnit J.det) (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hsd : dualSet (hc.sig : E →+* E) J L = (L : Set (Fin n → E))) (hβ : IsFrame β L) :
    ∃ G : GL (Fin n) (intAf F E),
      (G : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype = gramA hc J β := by
  have hint : ∀ x ∈ L, ∀ z ∈ L, IsIntegral ℤ (((1 : ℤ) : E) * hform (hc.sig : E →+* E) J x z) := by
    intro x hx z hz
    have hz' : z ∈ dualSet (hc.sig : E →+* E) J L := by rw [hsd]; exact hz
    obtain ⟨a, ha⟩ := hz' x hx
    rw [Int.cast_one, one_mul, ← ha]
    exact RingOfIntegers.isIntegral_coe a
  have hG1 : ∀ i j, gramA hc J β i j ∈ intAf F E := by
    intro i j
    have := Formalism.UG.P.csScale_latS hc.sig J L 1 hint (frame_mulVec_mem hβ _ (single_mem_intAf i))
      (frame_mulVec_mem hβ _ (single_mem_intAf j))
    rw [Int.cast_one, map_one, one_mul, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single] at this
    exact this
  have hJu : IsUnit (J.map (inclE (F := F) (Af F))) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have : (J.map (inclE (F := F) (Af F))).det = inclE (F := F) (Af F) J.det :=
      (RingHom.map_det (inclE (F := F) (Af F)) J).symm
    rw [this]
    exact hJ.map _
  obtain ⟨Ju, hJu'⟩ := hJu
  let cβ : GL (Fin n) (E ⊗[F] Af F) :=
    ⟨cT (sigR hc.sig (Af F)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)),
      cT (sigR hc.sig (Af F)) ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)),
      by rw [← cT_mul, Units.inv_mul, cT_one], by rw [← cT_mul, Units.mul_inv, cT_one]⟩
  set Gu : GL (Fin n) (E ⊗[F] Af F) := cβ * Ju * β with hGu
  have hGv : (Gu : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) = gramA hc J β := by
    rw [hGu, Units.val_mul, Units.val_mul, hJu']
    rfl
  have hG2 : ∀ i j, ((Gu⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j ∈ intAf F E := by
    intro i j
    set u : Fin n → E ⊗[F] Af F :=
      ((Gu⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ Pi.single j 1 with hu
    have hw : (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ u ∈ hatL (F := F) L := by
      refine hat_selfdual hc.sig J L hspan hsd _ fun l hl => ?_
      set y : Fin n → E ⊗[F] Af F :=
        ((β⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ
          (fun i => inclE (F := F) (Af F) (l i)) with hy
      have hyS : ∀ i, y i ∈ intAf F E :=
        (hβ _).1 (Submodule.subset_span ⟨l, hl, rfl⟩)
      have e : (fun i => inclE (F := F) (Af F) (l i)) = (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ y := by
        rw [hy, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e, Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_eq_dot]
      have e2 : (cT (sigR hc.sig (Af F)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *
          J.map (inclE (F := F) (Af F)) * (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))) *ᵥ u = Pi.single j 1 := by
        have : (cT (sigR hc.sig (Af F)) (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *
          J.map (inclE (F := F) (Af F)) * (β : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))) =
            (Gu : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) := hGv.symm
        rw [this, hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e2, dotProduct_single, mul_one]
      exact Formalism.UG.P.csScale_sigR_mem hc.sig (hyS j)
    have h3 := (hβ _).1 hw i
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, hu, Matrix.mulVec_single_one] at h3
    exact h3
  obtain ⟨G, hG⟩ := Formalism.UG.P.levelaf_mem_range_of_integral (intAf F E) Gu
    ⟨fun i j => ⟨(Gu : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j, by rw [hGv]; exact hG1 i j⟩, by ext i j; rfl⟩
    ⟨fun i j => ⟨((Gu⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) i j, hG2 i j⟩,
      by ext i j; rfl⟩
  refine ⟨G, ?_⟩
  rw [← hGv, ← hG]
  rfl

theorem redSurj_sd (hc : CMData F E) {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {β : GL (Fin n) (E ⊗[F] Af F)} (T : Finset (Pl E)) (hJh : Formalism.UG.IsHerm (hc.sig : E →+* E) J) (hJ : IsUnit J.det)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hsd : dualSet (hc.sig : E →+* E) J L = (L : Set (Fin n → E))) (hβ : IsFrame β L) (hT : IsSplitSet T)
    (y : ∀ PP : ↥T, GL (Fin n) (kP PP.1)) : ∃ x ∈ UA hc J ⊓ St β, ∀ PP : ↥T, redFn β PP.1 x = y PP := by
  obtain ⟨G, hG⟩ := exists_gramS_sd hc hJ hspan hsd hβ
  obtain ⟨z, hz, hzy⟩ := exists_unitary_lift hc G (gramS_herm hc hJh hG) T hT y
  refine ⟨frGL β z, ⟨(frGL_mem_UA_iff hc hG z).2 hz, ⟨z, rfl⟩⟩, fun PP => ?_⟩
  rw [redFn_frGL]
  exact hzy PP

end Gen

end Formalism.IndefR.Fin.Lifts

end
