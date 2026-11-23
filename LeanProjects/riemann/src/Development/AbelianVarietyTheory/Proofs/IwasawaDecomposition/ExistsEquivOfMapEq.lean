import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

namespace Unram

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem exists_eigenbasis {f : End ℂ V} (hf : f.IsSemisimple) :
    ∃ (b : Basis (Fin (finrank ℂ V)) ℂ V) (c : Fin (finrank ℂ V) → ℂ), ∀ i, f (b i) = c i • b i := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℂ (⋃ α, (f.eigenspace α : Set V))
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : s → V)) := by
    rw [Subtype.range_coe, hspan, Submodule.span_iUnion, ← hf.iSup_eigenspace_eq_top]
    simp
  let b0 : Basis s ℂ V := Basis.mk hli htop
  let b := b0.reindex (b0.indexEquiv (finBasis ℂ V))
  have hb : ∀ i, ∃ α : ℂ, f (b i) = α • b i := by
    intro i
    have : b i ∈ s := by
      simp only [b, b0, Basis.reindex_apply, Basis.mk_apply]
      exact Subtype.prop _
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp (hs this)
    exact ⟨α, End.mem_eigenspace_iff.mp hα⟩
  choose c hc using hb
  exact ⟨b, c, hc⟩

theorem apply_of_eigen {a : WDRep h V} (ha : a.Unr) {v : V} {c : ℂˣ}
    (hv : a.ρ (frob h) v = (c : ℂ) • v) (σ : Weil h) : a.ρ σ v = (c : ℂ) ^ deg σ • v := by
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  have hinv : a.ρ (frob h)⁻¹ v = (c : ℂ)⁻¹ • v := by
    have := congrArg (a.ρ (frob h)⁻¹) hv
    rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply, map_smul] at this
    rw [eq_inv_smul_iff₀ hc, ← this]
  have hk : ∀ k : ℤ, a.ρ (frob h ^ k) v = (c : ℂ) ^ k • v := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, End.mul_apply, hv, map_smul, ih, smul_smul, zpow_add_one₀ hc,
        mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, End.mul_apply, hinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc,
        mul_comm]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  conv_lhs => rw [hτ]
  rw [map_mul, ha.2, mul_one, hk]

theorem mk_eq_diag {ι : Type*} [Finite ι] {a : WDRep h V} (ha : a.Unr) (b : Basis ι ℂ V)
    (c : ι → ℂˣ) (hb : ∀ i, a.ρ (frob h) (b i) = (c i : ℂ) • b i) :
    WD.mk a = WD.mk (WDRep.diag h c) := by
  classical
  refine WD.sound ⟨b.equivFun, fun σ v => ?_, fun v => by simp [ha.1]⟩
  have : b.equivFun.toLinearMap ∘ₗ a.ρ σ = (WDRep.diag h c).ρ σ ∘ₗ b.equivFun.toLinearMap := by
    refine b.ext fun i => funext fun j => ?_
    by_cases hij : i = j
    · subst hij; simp [apply_of_eigen ha (hb i)]
    · simp [apply_of_eigen ha (hb i), hij]
  exact LinearMap.congr_fun this v

theorem exists_diag {x : WD h} (hx : x.unr) :
    ∃ (n : ℕ) (c : Fin n → ℂˣ), x = WD.mk (WDRep.diag h c) := by
  induction x using WD.ind with
  | hP n a =>
    obtain ⟨b, c, hc⟩ := exists_eigenbasis (a.semisimple (frob h))
    have h0 : ∀ i, c i ≠ 0 := by
      intro i hi
      have := congrArg (a.ρ (frob h)⁻¹) (hc i)
      rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply, hi, zero_smul,
        map_zero] at this
      exact b.ne_zero i this
    exact ⟨_, fun i => Units.mk0 (c i) (h0 i), mk_eq_diag ((WD.unr_mk a).mp hx) b _ hc⟩

theorem exists_equiv_of_map_eq {ι κ α : Type*} [Fintype ι] [Fintype κ] {c : ι → α} {d : κ → α}
    (hcd : Finset.univ.val.map c = Finset.univ.val.map d) : ∃ e : ι ≃ κ, ∀ i, d (e i) = c i := by
  classical
  have : ∀ z, Nonempty ({i // c i = z} ≃ {k // d k = z}) := by
    intro z
    rw [← Fintype.card_eq, Fintype.card_subtype, Fintype.card_subtype]
    have := congrArg (Multiset.count z) hcd
    rw [Multiset.count_map, Multiset.count_map] at this
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this
  exact ⟨Equiv.ofFiberEquiv fun z => (this z).some, Equiv.ofFiberEquiv_map _⟩

theorem diag_eq_diag {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → ℂˣ} {d : κ → ℂˣ}
    (hcd : (Finset.univ.val.map fun i => (c i : ℂ)) = Finset.univ.val.map fun k => (d k : ℂ)) :
    WD.mk (WDRep.diag h c) = WD.mk (WDRep.diag h d) := by
  obtain ⟨e, he⟩ := exists_equiv_of_map_eq hcd.symm
  refine WD.sound ⟨LinearEquiv.funCongrLeft ℂ ℂ e, fun σ v => funext fun k => ?_, fun v => by simp⟩
  simp [he]

theorem diag_frob_basisFun {ι : Type*} [Finite ι] (c : ι → ℂˣ) (i : ι) :
    (WDRep.diag h c).ρ (frob h) (Pi.basisFun ℂ ι i) = (c i : ℂ) • Pi.basisFun ℂ ι i := by
  classical
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

end Unram

namespace WD

open Unram

theorem lpUnr_spec (m : Multiset ℂ) (hm : (0 : ℂ) ∉ m) :
    unr (lpUnr h m) ∧ frobEig (lpUnr h m) = m ∧ lpDim (lpUnr h m) = Multiset.card m := by
  classical
  refine ⟨(unr_mk _).mpr (WDRep.unr_diag _), ?_, ?_⟩
  · rw [lpUnr, frobEig_diag]
    conv_rhs => rw [← Multiset.map_univ_coe m]
    refine Multiset.map_congr rfl fun i _ => coe_unitOf fun h0 => hm ?_
    rw [← h0]; exact Multiset.coe_mem
  · simp [lpUnr]

theorem unr_sum (a b : WD h) : unr (lpSum a b) ↔ unr a ∧ unr b := by
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
    simp only [lpSum_mk, unr_mk, WDRep.Unr, WDRep.sum_N, WDRep.sum_ρ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨LinearMap.ext fun v => congrArg Prod.fst (LinearMap.congr_fun h1 (v, 0)),
        fun σ => LinearMap.ext fun v => congrArg Prod.fst (LinearMap.congr_fun (h2 σ) (v, 0))⟩,
        LinearMap.ext fun v => congrArg Prod.snd (LinearMap.congr_fun h1 (0, v)),
        fun σ => LinearMap.ext fun v => congrArg Prod.snd (LinearMap.congr_fun (h2 σ) (0, v))⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by rw [h1, h3, LinearMap.prodMap_zero],
        fun σ => by rw [h2, h4]; exact LinearMap.prodMap_one⟩

theorem unr_tw (a : WD h) (s : ℝ) : unr (lpTw a s) ↔ unr a := by
  induction a using ind with
  | hP n a => simp [WDRep.Unr]

theorem unr_lpChar (a χ : WD h) (ha : unr a) (hχ : unr χ) : unr (lpChar a χ) := by
  induction a using ind with
  | hP n a =>
  induction χ using ind with
  | hP m b =>
    rw [unr_mk] at ha hχ
    rw [lpChar_mk, unr_mk]
    exact ⟨by simp [ha.1, hχ.1], fun σ => by
      rw [WDRep.tensor_ρ, ha.2, hχ.2, TensorProduct.map_one]⟩

theorem frobEig_lpSum (a b : WD h) : frobEig (lpSum a b) = frobEig a + frobEig b := by
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
    rw [lpSum_mk, frobEig_mk, frobEig_mk, frobEig_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap,
      roots_mul (mul_ne_zero (LinearMap.charpoly_monic _).ne_zero
        (LinearMap.charpoly_monic _).ne_zero)]

theorem frobEig_tw (a : WD h) (s : ℝ) (ha : unr a) :
    frobEig (lpTw a s) = (frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) := by
  obtain ⟨n, c, rfl⟩ := exists_diag ha
  have : mk ((WDRep.diag h c).tw s) = mk (WDRep.diag h fun i => c i * qPow w s) :=
    sound ⟨.refl _ _, fun σ v => funext fun i => by simp [mul_zpow]; ring, fun v => rfl⟩
  rw [lpTw_mk, this, frobEig_diag, frobEig_diag, Multiset.map_map]
  simp

theorem lpChar_diag {ι κ : Type*} [Finite ι] [Finite κ] (c : ι → ℂˣ) (d : κ → ℂˣ) :
    lpChar (mk (WDRep.diag h c)) (mk (WDRep.diag h d)) =
      mk (WDRep.diag h fun p : ι × κ => c p.1 * d p.2) := by
  classical
  have hu := unr_lpChar _ _ ((unr_mk _).mpr (WDRep.unr_diag (h := h) c))
    ((unr_mk _).mpr (WDRep.unr_diag (h := h) d))
  rw [lpChar_mk] at hu ⊢
  refine mk_eq_diag ((unr_mk _).mp hu) ((Pi.basisFun ℂ ι).tensorProduct (Pi.basisFun ℂ κ)) _ ?_
  rintro ⟨i, k⟩
  rw [Basis.tensorProduct_apply, WDRep.tensor_ρ, TensorProduct.map_tmul, diag_frob_basisFun,
    diag_frob_basisFun, TensorProduct.smul_tmul_smul, Units.val_mul]

theorem frobEig_char (a χ : WD h) (z : ℂ) (ha : unr a) (hχ : unr χ) (hz : frobEig χ = {z}) :
    frobEig (lpChar a χ) = (frobEig a).map (· * z) := by
  obtain ⟨n, c, rfl⟩ := exists_diag ha
  obtain ⟨m, d, rfl⟩ := exists_diag hχ
  have h0 : z ≠ 0 := by
    rintro rfl
    rw [frobEig_diag] at hz
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp (hz ▸ Multiset.mem_singleton_self (0 : ℂ))
    exact (d i).ne_zero hi
  have e : mk (WDRep.diag h d) = mk (WDRep.diag h fun _ : Unit => Units.mk0 z h0) :=
    diag_eq_diag (by rw [← frobEig_diag (h := h), hz]; simp)
  rw [e, lpChar_diag, frobEig_diag, frobEig_diag, Multiset.map_map,
    ← Finset.map_univ_equiv (Equiv.prodPUnit (Fin n)).symm]
  rw [Finset.map_val, Multiset.map_map]
  rfl

theorem lpZero_unr : unr (lpZero h) := (unr_mk _).mpr (WDRep.unr_diag _)

theorem frobEig_zero : frobEig (lpZero h) = 0 := by
  rw [lpZero, frobEig_diag]; simp

theorem frobEig_ne_zero (a : WD h) (ha : unr a) : (0 : ℂ) ∉ frobEig a := by
  obtain ⟨n, c, rfl⟩ := exists_diag ha
  rw [frobEig_diag]
  simp

theorem unr_eq_lpUnr (a : WD h) (ha : unr a) : a = lpUnr h (frobEig a) := by
  classical
  have h1 := (lpUnr_spec (h := h) _ (frobEig_ne_zero a ha)).2.1
  obtain ⟨n, c, hc⟩ := exists_diag ha
  rw [lpUnr] at h1 ⊢
  refine hc.trans (diag_eq_diag ?_)
  rw [← frobEig_diag (h := h), ← frobEig_diag (h := h), h1, hc]

theorem unr_mono0 (a : WD h) (ha : unr a) : mono0 a := by
  induction a using ind with
  | hP n a => exact (monodromyZero_ofWeilDeligneRepClass_iff a).mpr ((unr_mk a).mp ha).1

theorem tempered_unr (a : WD h) (ha : unr a) : tempered a ↔ ∀ α ∈ frobEig a, ‖α‖ = 1 := by
  obtain ⟨n, c, rfl⟩ := exists_diag ha
  rw [tempered_mk, tempered_diag_iff, frobEig_diag]
  simp

theorem unr_iff_ine (a : WD h) :
    unr a ↔ mono0 a ∧ ∀ σ ∈ Ine (F := E) A, inePol a σ = (X - 1) ^ lpDim a := by
  induction a using ind with
  | hP n a =>
    rw [unr_mk, monodromyZero_ofWeilDeligneRepClass_iff, lpDim_mk]
    refine and_congr Iff.rfl ⟨fun h1 σ hσ => ?_, fun h1 σ => ?_⟩
    · rw [inePol_of_mem_Ine _ hσ, charPol_mk, h1, LinearMap.charpoly_one]
    · have h2 := h1 σ σ.2
      rw [inePol_of_mem_Ine _ σ.2, charPol_mk] at h2
      have h3 := LinearMap.aeval_self_charpoly (a.ρ (ineIncl h σ))
      erw [h2] at h3
      rw [map_pow, map_sub, aeval_X, map_one] at h3
      have h4 : End.IsSemisimple (a.ρ (ineIncl h σ) - algebraMap ℂ (End ℂ (Fin n → ℂ)) 1) :=
        End.isSemisimple_sub_algebraMap_iff.mpr (a.semisimple _)
      rw [map_one] at h4
      exact sub_eq_zero.mp (End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h3⟩ h4)

variable (h) in

theorem unramified_laws :
    (∀ m : Multiset ℂ, (0 : ℂ) ∉ m → unr (lpUnr h m) ∧ frobEig (lpUnr h m) = m ∧
      lpDim (lpUnr h m) = Multiset.card m) ∧
    (∀ a b : WD h, unr (lpSum a b) ↔ unr a ∧ unr b) ∧
    (∀ (a : WD h) (s : ℝ), unr (lpTw a s) ↔ unr a) ∧
    (∀ a χ : WD h, lpDim χ = 1 → unr a → unr χ → unr (lpChar a χ)) ∧
    (∀ a b : WD h, unr a → unr b → frobEig (lpSum a b) = frobEig a + frobEig b) ∧
    (∀ (a : WD h) (s : ℝ), unr a →
      frobEig (lpTw a s) = (frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ))) ∧
    (∀ (a χ : WD h) (c : ℂ), unr a → unr χ → lpDim χ = 1 → frobEig χ = {c} →
      frobEig (lpChar a χ) = (frobEig a).map (· * c)) ∧
    unr (lpZero h) ∧
    frobEig (lpZero h) = 0 ∧
    (∀ a : WD h, unr a → a = lpUnr h (frobEig a)) ∧
    (∀ a : WD h, unr a → mono0 a) ∧
    (∀ a : WD h, unr a → (0 : ℂ) ∉ frobEig a) ∧
    (∀ a : WD h, unr a → Multiset.card (frobEig a) = lpDim a) ∧
    (∀ a : WD h, unr a → (tempered a ↔ ∀ α ∈ frobEig a, ‖α‖ = 1)) ∧
    (∀ a : WD h, unr a ↔ mono0 a ∧ ∀ σ ∈ Ine (F := E) A, inePol a σ = (X - 1) ^ lpDim a) :=
  ⟨lpUnr_spec, unr_sum, unr_tw, fun a χ _ => unr_lpChar a χ, fun a b _ _ => frobEig_lpSum a b,
    frobEig_tw, fun a χ c ha hχ _ => frobEig_char a χ c ha hχ, lpZero_unr, frobEig_zero,
    unr_eq_lpUnr, unr_mono0, frobEig_ne_zero, fun a _ => card_eig a _, tempered_unr, unr_iff_ine⟩

end WD

end GlobalTheory.WeilDeligne
