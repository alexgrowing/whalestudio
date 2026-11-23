import Formalism.CharacterColumnKernels.StatementColKer
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerSmulLe
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange

open Finset

noncomputable section

namespace Formalism.NG

namespace ColumnGeneratorDecomposition

variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ι → ℕ}

abbrev fNu (l : ι) : ColFreeJ A r χ E ι j := colGenJ 0 l 1 0 0

abbrev fSig (l : ι) (a : Fin (j l)) : ColFreeJ A r χ E ι j := colGenJ 0 l 0 (Pi.single a 1) 0

abbrev fSig0 (l : ι) : ColFreeJ A r χ E ι j := colGenJ 0 l 0 0 1

lemma colGenJ_decomp (y : Ymod r χ E) (l : ι) (c : A) (s : Fin (j l) → A) (c₀ : A) :
    colGenJ y l c s c₀ = ((y, 0) : ColFreeJ A r χ E ι j) + c • fNu l +
      ∑ a, s a • fSig l a + c₀ • fSig0 l := by
  refine Prod.ext ?_ ?_
  · simp [colGenJ, Prod.fst_sum]
  · funext l'
    by_cases h : l' = l
    · subst h
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [colGenJ, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
      · funext b
        simp [colGenJ, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [colGenJ, Prod.snd_sum, Finset.sum_apply]
    · simp [colGenJ, Prod.snd_sum, Finset.sum_apply, Pi.single_eq_of_ne h]

lemma free_decomp [Fintype ι] (z : ColFreeJ A r χ E ι j) :
    z = ((z.1, 0) : ColFreeJ A r χ E ι j) +
      ∑ l, colGenJ 0 l (z.2 l).1 (z.2 l).2.1 (z.2 l).2.2 := by
  refine Prod.ext ?_ ?_
  · simp [colGenJ, Prod.fst_sum]
  · simp only [colGenJ, Prod.snd_add, Prod.snd_sum, zero_add, Prod.mk.eta]
    exact (Finset.univ_sum_single z.2).symm

variable {M : Type*} [AddCommGroup M] [Module A M]

lemma map_colGenJ (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (y : Ymod r χ E) (l : ι) (c : A)
    (s : Fin (j l) → A) (c₀ : A) :
    ψ (colGenJ y l c s c₀) = ψ (y, 0) + c • ψ (fNu l) + ∑ a, s a • ψ (fSig l a) +
      c₀ • ψ (fSig0 l) := by
  rw [colGenJ_decomp]
  simp only [map_add, map_sum, map_smul]

lemma map_sigRel (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (l : ι) (a : Fin (j l)) (t : A) :
    ψ (colGenJ 0 l 0 (Pi.single a t) 0) = t • ψ (fSig l a) := by
  have h0 : ψ ((0 : Ymod r χ E), 0) = 0 := map_zero ψ
  rw [map_colGenJ]
  simp [Pi.single_apply, h0]

lemma map_sig0Rel (ψ : ColFreeJ A r χ E ι j →ₗ[A] M) (l : ι) (t : A) :
    ψ (colGenJ 0 l 0 0 t) = t • ψ (fSig0 l) := by
  have h0 : ψ ((0 : Ymod r χ E), 0) = 0 := map_zero ψ
  rw [map_colGenJ]
  simp [h0]

lemma eq_zero_of_gens [Fintype ι] {e₁ : A} {δ : T'} {D : ι → Subgroup G}
    {Kc : ∀ l, Fin (j l) → G → A} {k0 : ι → G → A}
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M)
    (hY : ∀ y : Ymod r χ E, φ (Submodule.Quotient.mk ((y, 0) : ColFreeJ A r χ E ι j)) = 0)
    (hν : ∀ l, φ (Submodule.Quotient.mk (fNu l)) = 0)
    (hσ : ∀ l a, φ (Submodule.Quotient.mk (fSig l a)) = 0)
    (hσ₀ : ∀ l, φ (Submodule.Quotient.mk (fSig0 l)) = 0) : φ = 0 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    let ψ := φ ∘ₗ (colRelJ r χ E e₁ δ D j Kc k0).mkQ
    have : ψ z = 0 := by
      have h0 : ψ ((0 : Ymod r χ E), 0) = 0 := map_zero ψ
      rw [free_decomp z, map_add, map_sum]
      refine (congrArg₂ (· + ·) (hY z.1) (Finset.sum_eq_zero fun l _ => ?_)).trans (add_zero 0)
      rw [map_colGenJ]
      have h1 : ψ (fNu l) = 0 := hν l
      have h2 : ∀ a, ψ (fSig l a) = 0 := hσ l
      have h3 : ψ (fSig0 l) = 0 := hσ₀ l
      simp only [h0, h1, h2, h3, smul_zero, Finset.sum_const_zero, add_zero]
    simpa [ψ] using this

end ColumnGeneratorDecomposition

open ColumnGeneratorDecomposition

theorem colKer : StatColKer := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ D j Kc k0 ℓ e' hE hk0 hδ heq hlift
  obtain ⟨eqv⟩ := heq
  set R1 := LinearMap.range (DistribSMul.toLinearMap O (d → KO O) e₁) with hR1
  let K := kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0
  let q : ColFreeJ A r χ E ι j →ₗ[A] ColNNJ r χ E e₁ δ D j Kc k0 := Submodule.mkQ _
  have hval : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) (z : ColFreeJ A r χ E ι j),
      z ∈ colRelJ r χ E e₁ δ D j Kc k0 → (φ ∘ₗ q) z = 0 := fun φ z hz => by
    rw [LinearMap.comp_apply, show q z = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  have hKY : ∀ φ ∈ K, ∀ y : Ymod r χ E, φ (q (y, 0)) = 0 := fun φ hφ y =>
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hφ y)
  have hσmem : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l a, φ (q (fSig l a)) ∈ R1 := by
    intro φ l a
    have h := hval φ (colGenJ 0 l 0 (Pi.single a (1 - e₁)) 0)
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨l, a, rfl⟩))))
    rw [map_sigRel, sub_smul, one_smul, sub_eq_zero] at h
    exact ⟨_, by rw [DistribSMul.toLinearMap_apply]; exact h.symm⟩
  have hσ0 : ∀ (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] (d → KO O)) l,
      φ (q (fSig0 l)) ∈ LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := by
    intro φ l
    have h := hval φ (colGenJ 0 l 0 0 (algebraMap T' A δ - E))
      (Submodule.subset_span (Or.inl (Or.inr ⟨l, rfl⟩)))
    rw [map_sig0Rel, sub_smul, hδ, hE, sub_zero] at h
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
    exact h
  have hg : ∀ φ ∈ K, ∀ l (g : D l), colDO (O := O) r χ (D l) (φ (q (fNu l))) g =
      ∑ a, Kc l a g • (δO • φ (q (fSig l a))) := by
    intro φ hφ l g
    have h := hval φ _ (Submodule.subset_span (Or.inr ⟨l, g, g.2, rfl⟩))
    rw [map_colGenJ] at h
    obtain ⟨b, hb⟩ := hk0 l g
    simp only [LinearMap.comp_apply, hKY φ hφ, zero_add, hb, neg_smul, mul_smul, hE, smul_zero,
      neg_zero, add_zero, hδ, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] at h
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g) • φ (q (fNu l)) - φ (q (fNu l)) = _
    rw [sub_smul, one_smul] at h
    rw [h]
    exact Finset.sum_congr rfl fun a _ => (smul_comm _ _ _).symm
  have hlift' : ∀ φ ∈ K, ∀ l a, ((ℓ : O) ^ e' l) • (δO • φ (q (fSig l a))) = 0 := by
    intro φ hφ l a
    exact hlift l (fun a => δO • φ (q (fSig l a))) (fun a => R1.smul_mem δO (hσmem φ l a))
      ⟨φ (q (fNu l)), funext fun g => hg φ hφ l g⟩ a
  let evK : ColNNJ r χ E e₁ δ D j Kc k0 → (K →ₗ[O] (d → KO O)) := fun x => evalO x ∘ₗ K.subtype
  let sR : ∀ l (a : Fin (j l)), K →ₗ[O] R1 := fun l a =>
    LinearMap.codRestrict R1 (evK (q (fSig l a))) (fun φ => hσmem φ.1 l a)
  have hsk : ∀ l a (φ : K), eqv (sR l a φ) ∈
      LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' l * δO)) := by
    intro l a φ
    rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, ← map_smul]
    have : ((ℓ : O) ^ e' l * δO) • sR l a φ = 0 := Subtype.ext (by
      rw [Submodule.coe_smul, mul_smul, Submodule.coe_zero]
      exact hlift' φ.1 φ.2 l a)
    rw [this, map_zero]
  let sK : ∀ l (a : Fin (j l)), K →ₗ[O]
      LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' l * δO)) := fun l a =>
    LinearMap.codRestrict _ (eqv.toLinearMap ∘ₗ sR l a) (hsk l a)
  let s0K : ∀ l, K →ₗ[O] LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δO) := fun l =>
    LinearMap.codRestrict _ (evK (q (fSig0 l))) (fun φ => hσ0 φ.1 l)
  let Φ : K →ₗ[O] ((l : ι) → ColData O ℓ δO (e' l) (j l) Unit d) :=
    LinearMap.pi fun l => (LinearMap.pi fun a => sK l a).prod ((0 : K →ₗ[O] Unit).prod (s0K l))
  have hΦ0 : ∀ φ : K, Φ φ = 0 →
      (∀ l a, φ.1 (q (fSig l a)) = 0) ∧ (∀ l, φ.1 (q (fSig0 l)) = 0) := by
    intro φ h
    refine ⟨fun l a => ?_, fun l => ?_⟩
    · have h1 : sK l a φ = 0 := congrFun (congrArg Prod.fst (congrFun h l)) a
      have h2 : sR l a φ = 0 := eqv.map_eq_zero_iff.mp (congrArg Subtype.val h1)
      exact congrArg Subtype.val h2
    · have h1 : s0K l φ = 0 := congrArg Prod.snd (congrArg Prod.snd (congrFun h l))
      exact congrArg Subtype.val h1
  have hΘmem : ∀ l (φ : LinearMap.ker Φ), evK (q (fNu l)) φ.1 ∈
      LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l)) := by
    intro l φ
    obtain ⟨hs, _⟩ := hΦ0 φ.1 (LinearMap.mem_ker.mp φ.2)
    rw [LinearMap.mem_ker]
    funext g
    show colDO (O := O) r χ (D l) (φ.1.1 (q (fNu l))) g = 0
    rw [hg φ.1.1 φ.1.2 l g]
    simp [hs]
  let Θ : LinearMap.ker Φ →ₗ[O]
      ((l : ι) → LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) :=
    LinearMap.pi fun l =>
      LinearMap.codRestrict _ (evK (q (fNu l)) ∘ₗ (LinearMap.ker Φ).subtype) (hΘmem l)
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ h
    have hν : ∀ l, φ.1.1 (q (fNu l)) = 0 := fun l => congrArg Subtype.val (congrFun h l)
    obtain ⟨hs, hs0⟩ := hΦ0 φ.1 (LinearMap.mem_ker.mp φ.2)
    have : φ.1.1 = 0 := eq_zero_of_gens φ.1.1 (hKY φ.1.1 φ.1.2) hν hs hs0
    exact Subtype.ext (Subtype.ext this)
  have h1 : Module.length O (LinearMap.ker Φ) ≤
      ∑ l, Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) :=
    (Module.length_le_of_injective Θ hΘ).trans_eq (Module.length_pi_of_fintype O _)
  have h2 : Module.length O (LinearMap.range Φ) ≤
      ∑ l, (((j l : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' l : ℕ∞) +
          IsDiscreteValuationRing.addVal O δO) + 0) +
        (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO) :=
    calc Module.length O (LinearMap.range Φ)
        ≤ Module.length O ((l : ι) → ColData O ℓ δO (e' l) (j l) Unit d) :=
          Module.length_le_of_injective (LinearMap.range Φ).subtype Subtype.val_injective
      _ = ∑ l, Module.length O (ColData O ℓ δO (e' l) (j l) Unit d) :=
          Module.length_pi_of_fintype O _
      _ ≤ _ := Finset.sum_le_sum fun l _ =>
          KernelLengthBounds.length_colData_le ℓ δO (e' l) (j l) Unit d 0 (by rw [Module.length_eq_zero])
  rw [IdempotentNormalFormsRhoFacts.length_eq_ker_add_range Φ]
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := by
      simp only [add_zero, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring

theorem blockRhoColumn : StatBlockRhoColumn := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0 ℓ
    hE hk0 hδ heq hlift ρM Ψ hΨ hcob what₂ F lenRow Q s cols eO vδ N h0 hrows hcols hQ hsel
  have hk := colKer O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
    Kc k0 ℓ (fun l => e' (colIdx l)) hE hk0 hδ heq hlift
  rw [← hΨ] at hk
  refine blockRhoAbs O G d ρM _ Ψ δO hcob ι' what₂ cols D F lenRow Q s ℓ e' j h0 hrows hcols hQ
    hsel (le_of_le_of_eq hk ?_)
  simp only [cols, h0]
  rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy), Finset.card_image_of_injective _ hinj,
    Finset.card_univ]

end Formalism.NG
