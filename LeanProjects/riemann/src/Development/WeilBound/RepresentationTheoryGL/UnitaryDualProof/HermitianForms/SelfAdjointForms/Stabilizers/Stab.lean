import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.ExistsBallPf
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.ConjCircleEqOne
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.VmvMulVecApply

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

private theorem exists_tr_lemma {n : ℕ} (C D : AddSubgroup (Fin n → k)) (hC : IsCompact (C : Set (Fin n → k)))
    (hD : IsOpen (D : Set (Fin n → k))) :
    ∃ T : Finset (Fin n → k), IsTr C D T ∧ T.card = D.relIndex C := by
  classical
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hfin : Finite (C ⧸ D.addSubgroupOf C) :=
    AddSubgroup.quotient_finite_of_isOpen _ (hD.preimage continuous_subtype_val)
  have := Fintype.ofFinite (C ⧸ D.addSubgroupOf C)
  let f : (C ⧸ D.addSubgroupOf C) → Fin n → k := fun q => ((Quotient.out q : C) : Fin n → k)
  have hf : Function.Injective f := by
    intro q q' e
    have e' : Quotient.out q = Quotient.out q' := Subtype.ext e
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', e']
  refine ⟨Finset.univ.image f, ⟨fun t ht => ?_, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    exact (Quotient.out q).2
  · set q : C ⧸ D.addSubgroupOf C := QuotientAddGroup.mk ⟨a, ha⟩ with hqd
    have hq : -(Quotient.out q) + ⟨a, ha⟩ ∈ D.addSubgroupOf C :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' q)
    refine ⟨f q, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have hm := AddSubgroup.mem_addSubgroupOf.1 hq
      have e : a - f q = -((Quotient.out q : C) : Fin n → k) + a := by
        simp only [f]
        abel
      rw [e]
      simpa using hm
    · rintro y ⟨hy, hyd⟩
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy
      congr 1
      rw [← QuotientAddGroup.out_eq' q', hqd]
      apply QuotientAddGroup.eq.2
      rw [AddSubgroup.mem_addSubgroupOf]
      have e : -((Quotient.out q' : C) : Fin n → k) + a = a - f q' := by
        simp only [f]
        abel
      simpa [e] using hyd
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, AddSubgroup.relIndex, AddSubgroup.index_eq_card,
      Nat.card_eq_fintype_card]

theorem key' (hB : Lv ψ h π s B) (K : Subgroup (GL (Fin (m + 1)) k)) (D : Set (Fin (m + 1) → k))
    (hDK : ∀ η ∈ D, ∃ g ∈ K, nabs k (Matrix.GeneralLinearGroup.det g) = 1 ∧
      (∀ s : kˣ, pre g⁻¹ (ball (m + 1) s) = ball (m + 1) s) ∧
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η)
    {A₀ A : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) (hA : IsLat A) (h0 : A₀ ≤ A) (hAD : (ann ψ A : Set _) ⊆ D)
    (r : kˣ) (hAr : A ≤ ball (m + 1) r) (hr : IsLat (ball (m + 1) r)) (v w : V) (hv : FixK (by omega) π K v)
    (hw : FixK (by omega) π K w) :
    ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
      ((A₀.relIndex (ball (m + 1) r) : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := by
  obtain ⟨T, hT, hTc⟩ := exists_tr_lemma (ball (m + 1) r) A hr.1 hA.2
  have hAc := ann_isLat_pf hB.cont hB.ne hA
  have hrc := ann_isLat_pf hB.cont hB.ne hr
  obtain ⟨R, hR, -⟩ := exists_tr_lemma (ann ψ A) (ann ψ (ball (m + 1) r)) hAc.1 hrc.2
  have hdec := avg_decomp_pf (h := h) (π := π) hB.cont hB.ne hB.smooth (xi0 k m) hA hr hAr hR hT v
  have hterm : ∀ η ∈ R, B (avg ψ h π (xi0 k m + η) (ball (m + 1) r) v) w =
      B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := by
    intro η hη
    obtain ⟨g, hg, hdet, hpre, hxi⟩ := hDK η (hAD (hR.1 η hη))
    have hc := avg_conj (h := h) hB.cont hB.smooth g (xi0 k m) hr v
    rw [hxi, hpre r, hv g hg] at hc
    calc B (avg ψ h π (xi0 k m + η) (ball (m + 1) r) v) w
        = B (π (blkAt k (m + 1) N (by omega) g) (avg ψ h π (xi0 k m) (ball (m + 1) r) v))
            (π (blkAt k (m + 1) N (by omega) g) w) := by rw [hc, hw g hg]
      _ = B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := form_inv hB g hdet _ _
  have e := congrArg (fun x => B x w) hdec
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    smul_eq_mul] at e
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at e
  have hR0 : (R.card : ℂ) ≠ 0 := by
    obtain ⟨t, ⟨ht, -⟩, -⟩ := hR.2 0 (ann ψ A).zero_mem
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem ht)
  have e2 : B (avg ψ h π (xi0 k m) A v) w = (T.card : ℂ) * B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := by
    apply mul_left_cancel₀ hR0
    rw [e]
    ring
  rw [e2, hTc, ← mul_assoc, ← Nat.cast_mul, AddSubgroup.relIndex_mul_relIndex _ _ _ h0 hAr]

theorem stab' (hB : Lv ψ h π s B) (K : Subgroup (GL (Fin (m + 1)) k)) (hK : IsOpen (K : Set (GL (Fin (m + 1)) k)))
    {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) :
    ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v → FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
      ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
        ((A₀.relIndex A₁ : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A₁ v) w := by
  obtain ⟨D, hD, hDK⟩ := good_nbhd_pf K hK
  obtain ⟨A₁, hA₁, h01, hA₁D⟩ := exists_big_pf hB.cont hB.ne D hD hA₀
  refine ⟨A₁, hA₁, h01, fun v w hv hw A hA h1A => ?_⟩
  obtain ⟨r, hAr, hr⟩ := exists_ball_pf hA
  rw [key' hB K D hDK hA₀ hA (h01.trans h1A) (fun x hx => hA₁D (ann_anti h1A hx)) r hAr hr v w hv hw,
    key' hB K D hDK hA₀ hA₁ h01 hA₁D r (h1A.trans hAr) hr v w hv hw]

end

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
