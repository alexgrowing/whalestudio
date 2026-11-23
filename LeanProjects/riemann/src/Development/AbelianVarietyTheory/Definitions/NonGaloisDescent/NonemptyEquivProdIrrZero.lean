import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL.Tests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_parInd_zero {d : Fin 0 → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prodIrr x hd)) :=
  nonempty_equiv_parInd_zero _ _ (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm

theorem empty_spec : IsZ (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ∧
    IsL (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  have ho : IsOrderedForm (k := k) (Fin.elim0 : Fin 0 → Segment k) 0 := ⟨rfl, fun i => i.elim0⟩
  exact ⟨⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isSocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩,
    ⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩⟩

theorem IsL_deg {N : ℕ} {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) :
    (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, rfl, ⟨Δ, ⟨rfl, -⟩, hΔ⟩, -⟩ := h
  rw [Multiset.map_map]
  exact Finset.sum_congr rfl fun i _ => (hΔ i).deg_eq

theorem eq_of_isZSeg_single {ρ x : IrrGL k} (hρ : ρ.IsCusp) (h : IsZSeg (.single ρ hρ) x.rep) : x = ρ := by
  obtain ⟨n, c⟩ := x
  obtain ⟨d, c'⟩ := ρ
  obtain rfl : d = n := (one_mul d).symm.trans h.deg_eq
  exact congrArg _ (irrCl_eq_iff.2 ((single_spec hρ).1.unique h))

theorem eq_of_embeds {e : (Σ _ : Fin 2, Fin 1) ≃ Fin 2} {χ : Fin 2 → kˣ →* ℂˣ} {ψ : kˣ →* ℂˣ}
    (h : Embeds (detRep (Fin 2) ψ) (multiProd e fun a => detRep (Fin 1) (χ a))) : χ 1 = χ 0 * absPow k 1 := by
  obtain ⟨f, hf⟩ := h
  have h1 : ∀ g : GL (Fin 2) k, (f 1).1.1 g = (ψ (GeneralLinearGroup.det g) : ℂ) • (f 1).1.1 1 := fun g => by
    have := congrArg (fun φ => φ.1.1 1) (f.isIntertwining _ _ g 1)
    have h2 : detRep (Fin 2) ψ g 1 = (ψ (GeneralLinearGroup.det g) : ℂ) • (1 : ℂ) := ofChar_apply _ _ _
    simp only [h2, map_smul] at this
    rw [← one_mul g]
    exact this.symm.trans (by rw [one_mul]; rfl)
  have h0 : (f 1).1.1 1 ≠ 0 := fun h0 => one_ne_zero (hf (by
    rw [map_zero]
    exact Subtype.ext (Subtype.ext (funext fun g => by rw [h1, h0, smul_zero]; rfl))))
  have key : ∀ (g : Levi k fun _ : Fin 2 => Fin 1) y, piTensor (fun a => detRep (Fin 1) (χ a)) g y =
      ((∏ a, χ a (GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ) • y := by
    intro g y
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | smul_tprod c x =>
      rw [map_smul, smul_comm, piTensor_tprod, Units.coe_prod, ← MultilinearMap.map_smul_univ]
      congr 2
  have law : ∀ g : Levi k fun _ : Fin 2 => Fin 1, ψ (∏ a, GeneralLinearGroup.det (g a)) =
      deltaHalf k _ g * ∏ a, χ a (GeneralLinearGroup.det (g a)) := fun g => by
    have := parInd_law e _ (f 1) ⟨_, leviEmb_mem_parab k e g⟩ 1
    rw [mul_one, leviProj_leviEmb, key, h1, smul_smul, det_leviEmb] at this
    exact Units.ext (smul_left_injective ℂ h0 this)
  refine MonoidHom.ext fun z => ?_
  have hz : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [GeneralLinearGroup.scalar]
  have a := law ![GeneralLinearGroup.scalar (Fin 1) z, 1]
  have b := law ![1, GeneralLinearGroup.scalar (Fin 1) z]
  rw [deltaHalf_apply] at a b
  simp only [Fin.prod_univ_two, modExp_fin (fun _ : Fin 2 => Fin 1) (fun _ => by simp), Matrix.cons_val_zero,
    Matrix.cons_val_one, hz, map_one, mul_one, one_mul] at a b
  have c : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by rw [← absPow_add]; norm_num
  have d : absPow k (-1 / 2) = (absPow k (1 / 2))⁻¹ := by rw [← absPow_neg, neg_div]
  norm_num at a b
  rw [← neg_div, d, a] at b
  rw [c, MonoidHom.mul_apply, MonoidHom.mul_apply]
  rw [MonoidHom.inv_apply, eq_inv_mul_iff_mul_eq] at b
  rw [← b, mul_comm ((χ 0) z), mul_assoc]

theorem eq_of_embeds_prodIrr {c : Fin 2 → kˣ →* ℂˣ} {ψ : kˣ →* ℂˣ} (hc : ∀ a, IsSmoothChar (c a)) {x : Fin 2 → IrrGL k}
    (hx : x = fun a => IrrGL.ofChar (c a) (hc a)) {hd : ∑ a, (x a).1 = 2}
    (h : Embeds (detRep (Fin 2) ψ) (prodIrr x hd)) : c 1 = c 0 * absPow k 1 := by
  subst hx
  let φ := multiProdEquiv (stdBlocks (fun _ : Fin 2 => 1) hd) fun a => equivRep (IrrRep.det (Fin 1) (c a) (hc a))
  exact eq_of_embeds (h.trans (.of_equiv φ.symm))

theorem not_isZ_pair {χ ψ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ¬ IsZ {.single _ (IrrGL.isCusp_ofChar χ hχ), .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)} (detRep (Fin 2) ψ) := by
  rintro ⟨h, x, hd, ⟨Δ, ⟨hm, ho⟩, hΔ⟩, hs⟩
  obtain rfl : h = 2 := by simpa using congrArg Multiset.card hm
  have hm' : ({Δ 0, Δ 1} : Multiset (Segment k)) = _ := hm
  have hp := single_precedes χ hχ
  have h01 : Δ 0 = .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1) ∧ Δ 1 = .single _ (IrrGL.isCusp_ofChar χ hχ) := by
    rcases Multiset.cons_eq_cons.1 hm' with ⟨a, b⟩ | ⟨-, s, a, b⟩
    · exact absurd hp.1 (by rw [← a, ← Multiset.singleton_inj.1 b]; exact ho 0 1 (by decide))
    · obtain rfl : s = 0 := by simpa using congrArg Multiset.card a
      exact ⟨(Multiset.singleton_inj.1 b).symm, Multiset.singleton_inj.1 a⟩
  let c : Fin 2 → kˣ →* ℂˣ := ![χ * absPow k 1, χ]
  have hc : ∀ a, IsSmoothChar (c a) := Fin.forall_fin_two.2 ⟨hχ.mul (isSmoothChar_absPow 1), hχ⟩
  have hx : x = fun a => IrrGL.ofChar (c a) (hc a) := by
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · exact (eq_of_isZSeg_single _ (h01.1 ▸ hΔ 0)).trans (IrrGL.tw_ofChar _ _ _ _)
    · exact eq_of_isZSeg_single _ (h01.2 ▸ hΔ 1)
  have := eq_of_embeds_prodIrr hc hx hs.embeds
  have h2 : χ = χ * absPow k 1 * absPow k 1 := this
  rw [mul_assoc, ← absPow_add, left_eq_mul] at h2
  have h3 : (2 : ℝ) = 0 := (absPow_ofReal_eq_one (k := k)).1 (by rw [← h2]; norm_num)
  norm_num at h3

theorem not_isGeneric_detRep (χ : kˣ →* ℂˣ) : ¬ IsGeneric (detRep (Fin 2) χ) := by
  rintro ⟨ψ, -, hψ, h⟩
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra! h; exact hψ (AddChar.ext _ _ h)
  let u : GL (Fin 2) k := GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by simp)
  have hu : u ∈ unipB k (Fin 2) := (mem_unipB k).2 ⟨fun i j hij => by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) i j = 0
    fin_cases i <;> fin_cases j <;> simp at hij ⊢, fun i => by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) i i = 1
    fin_cases i <;> simp⟩
  have hw : (whitChar ψ 2 ⟨u, hu⟩ : ℂ) = ψ t := by
    show ((ψ (∑ p : Fin 2 × Fin 2 with (p.2 : ℕ) = p.1 + 1, (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) p.1 p.2) : Circle) : ℂ) = _
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hdet : GeneralLinearGroup.det u = 1 := by ext; simp [u]
  refine Submodule.Quotient.nontrivial_iff.1 h (eq_top_iff.2 fun v _ => ?_)
  have hne : (1 : ℂ) - ψ t ≠ 0 := sub_ne_zero.2 fun e => ht (Circle.ext e.symm)
  refine Submodule.subset_span ⟨⟨u, hu⟩, v / (1 - ψ t), ?_⟩
  rw [hw]
  show v = ofChar _ u _ - _
  rw [ofChar_apply, detChar_apply, hdet, map_one]
  simp only [Units.val_one, smul_eq_mul]
  field_simp

theorem linked_tests (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (Segment.icc _ (IrrGL.isCusp_ofChar χ hχ) 0 1 (by decide)).Precedes (.icc _ (IrrGL.isCusp_ofChar χ hχ) 1 2 (by decide)) ∧
    ¬ (Segment.icc _ (IrrGL.isCusp_ofChar χ hχ) 0 2 (by decide)).Linked (.icc _ (IrrGL.isCusp_ofChar χ hχ) 1 1 (by decide)) := by
  have inj : ∀ a b : ℤ, (IrrGL.ofChar χ hχ).nu a = (IrrGL.ofChar χ hχ).nu b → a = b := fun a b h => by
    exact_mod_cast (IrrGL.nu_ofChar_inj χ hχ (s := a) (t := b)).1 (by simpa using h)
  refine ⟨⟨⟨⟨.icc _ (IrrGL.isCusp_ofChar χ hχ) 0 2 (by decide), ?_⟩, fun h => ?_, fun h => ?_⟩, 1, one_pos, ?_⟩,
    fun h => h.2.2 fun x hx => ?_⟩
  · ext x
    simp only [Set.mem_union, Segment.mem_icc]
    constructor
    · rintro ⟨a, h1, h2, rfl⟩
      rcases le_or_gt a 1 with h | h
      exacts [Or.inl ⟨a, h1, h, rfl⟩, Or.inr ⟨a, h.le, h2, rfl⟩]
    · rintro (⟨a, h1, h2, rfl⟩ | ⟨a, h1, h2, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩
  · obtain ⟨a, h1, -, h2⟩ := Segment.mem_icc.1 (h (Segment.mem_icc.2 ⟨0, by decide, by decide, rfl⟩))
    have := inj _ _ h2; omega
  · obtain ⟨a, -, h1, h2⟩ := Segment.mem_icc.1 (h (Segment.mem_icc.2 ⟨2, by decide, by decide, rfl⟩))
    have := inj _ _ h2; omega
  · simp [Segment.icc]
  · obtain ⟨a, h1, h2, rfl⟩ := Segment.mem_icc.1 hx
    exact Segment.mem_icc.2 ⟨a, by omega, by omega, rfl⟩

end GlobalTheory.LocGL.Tests
