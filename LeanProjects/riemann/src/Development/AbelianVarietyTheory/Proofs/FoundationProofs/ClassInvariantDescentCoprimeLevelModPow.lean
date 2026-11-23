import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZModStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarModStatement

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.CoprimeDescent

theorem exists_cocycle {Q A : Type} [Group Q] [CommGroup A] (φ : Q →* MulAut A) (m : ℕ) (f : A)
    (hf : ∀ q, ∃ g, φ q f = f * g ^ m) (htor : ∀ a : A, a ^ m = 1 → ∀ q, φ q a = a)
    (hQ : ∀ (E : Type) [Group E] (π : E →* Q), Function.Surjective π → π.ker ≤ Subgroup.center E →
      (∀ x ∈ π.ker, x ^ m = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2) :
    ∃ c : Q → A, (∀ q q', c (q * q') = c q * φ q (c q')) ∧ ∀ q, φ q (f ^ 2) = f ^ 2 * c q ^ m := by
  let E : Subgroup (A ⋊[φ] Q) :=
    { carrier := {x | φ x.right f = f * x.left ^ m}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        simp only [SemidirectProduct.mul_right, SemidirectProduct.mul_left, map_mul, MulAut.mul_apply, hy, hx,
          map_pow, mul_pow, mul_assoc]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        simp only [SemidirectProduct.inv_right, SemidirectProduct.inv_left]
        have h := congrArg (φ x.right⁻¹) hx
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply, map_mul, map_pow] at h
        rw [map_inv (φ x.right⁻¹), inv_pow, eq_mul_inv_iff_mul_eq]
        exact h.symm }
  have hE : ∀ x, x ∈ E ↔ φ x.right f = f * x.left ^ m := fun x => Iff.rfl
  let π : E →* Q := SemidirectProduct.rightHom.comp E.subtype
  have hπ : ∀ x : E, π x = x.1.right := fun x => rfl
  have hker : ∀ x : E, x ∈ π.ker → x.1.right = 1 ∧ x.1.left ^ m = 1 := by
    intro x hx
    have h1 : x.1.right = 1 := hx
    have h2 := (hE x.1).1 x.2
    rw [h1, map_one, MulAut.one_apply] at h2
    exact ⟨h1, by simpa using h2.symm⟩
  have hpow : ∀ x : E, x ∈ π.ker → ∀ k : ℕ, (x ^ k).1.left = x.1.left ^ k := by
    intro x hx k
    have : x.1 = SemidirectProduct.inl x.1.left := by
      ext
      · simp
      · simp [(hker x hx).1]
    rw [SubgroupClass.coe_pow, this, ← map_pow, SemidirectProduct.left_inl, SemidirectProduct.left_inl]
  choose g hg using hf
  let s : Q → E := fun q => ⟨⟨g q, q⟩, hg q⟩
  obtain ⟨ψ, hψ1, hψ2⟩ := hQ E π (fun q => ⟨s q, rfl⟩)
    (by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h1, h2⟩ := hker x hx
      apply Subtype.ext
      ext
      · simp [h1, htor _ h2, mul_comm]
      · simp [h1])
    (by
      intro x hx
      apply Subtype.ext
      ext
      · rw [hpow x hx, (hker x hx).2]; rfl
      · exact (hker _ (π.ker.pow_mem hx m)).1)
  let χ : E → A := fun x => (ψ x).1.left
  have hχ : ∀ x y, χ (x * y) = χ x * χ y := by
    intro x y
    simp [χ, (hker _ (hψ1 x)).1]
  have hχm : ∀ x, χ x ^ m = 1 := fun x => (hker _ (hψ1 x)).2
  let C : E → A := fun x => x.1.left ^ 2 * (χ x)⁻¹
  have hC : ∀ x y, C (x * y) = C x * φ x.1.right (C y) := by
    intro x y
    simp only [C, hχ, Subgroup.coe_mul, SemidirectProduct.mul_left, map_mul, map_pow, map_inv, htor _ (hχm y),
      mul_pow, _root_.mul_inv_rev]
    rw [mul_comm (χ y)⁻¹, mul_mul_mul_comm]
  have hC1 : ∀ x ∈ π.ker, C x = 1 := by
    intro x hx
    simp only [C, χ, hψ2 x hx, hpow x hx, mul_inv_cancel]
  have hCs : ∀ x : E, C x = C (s x.1.right) := by
    intro x
    have hk : x * (s x.1.right)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact mul_inv_cancel _
    have := hC (x * (s x.1.right)⁻¹) (s x.1.right)
    rw [hC1 _ hk, (hker _ hk).1, inv_mul_cancel_right] at this
    simpa using this
  refine ⟨fun q => C (s q), fun q q' => ?_, fun q => ?_⟩
  · have := hC (s q) (s q')
    rw [hCs] at this
    exact this
  · have h : (s q).1.left = g q := rfl
    simp only [C, mul_pow, inv_pow, hχm, h, map_pow, hg q, inv_one, mul_one]
    rw [← pow_mul, ← pow_mul, mul_comm m 2]

theorem exists_invariant {Q F : Type} [Group Q] [Finite Q] [Field F] [CharZero F] (τ : Q → F →+* F)
    (hτ : ∀ q q' a, τ (q * q') a = τ q' (τ q a)) (m : ℕ) (f : Fˣ)
    (hf : ∀ q, ∃ g : Fˣ, τ q f = f * (g : F) ^ m) (htor : ∀ a : F, a ^ m = 1 → ∀ q, τ q a = a)
    (hsq : ∀ q, (∀ a, τ q a = a) → q * q = 1)
    (hQ : ∀ (E : Type) [Group E] (π : E →* Q), Function.Surjective π → π.ker ≤ Subgroup.center E →
      (∀ x ∈ π.ker, x ^ m = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2) :
    ∃ h : Fˣ, ∀ q, τ q ((f : F) ^ 4 * (h : F) ^ m) = (f : F) ^ 4 * (h : F) ^ m := by
  have h1 : ∀ a, τ 1 a = a := by
    intro a
    have e := hτ 1 1 a
    rw [mul_one] at e
    exact (τ 1).injective e.symm
  let φ0 : Q → MulAut Fˣ := fun q =>
    { toFun := Units.map (τ q⁻¹ : F →* F)
      invFun := Units.map (τ q : F →* F)
      left_inv := fun a => Units.ext (by simp [← hτ, h1])
      right_inv := fun a => Units.ext (by simp [← hτ, h1])
      map_mul' := map_mul _ }
  have hφ0 : ∀ q a, (φ0 q a : F) = τ q⁻¹ a := fun q a => rfl
  let φ : Q →* MulAut Fˣ := MonoidHom.mk' φ0 (by
    intro q q'
    ext a
    simp only [MulAut.mul_apply, hφ0, _root_.mul_inv_rev, hτ])
  have hφ : ∀ q a, (φ q a : F) = τ q⁻¹ a := fun q a => rfl
  obtain ⟨c, hc1, hc2⟩ := exists_cocycle φ m f
    (fun q => by
      obtain ⟨g, hg⟩ := hf q⁻¹
      exact ⟨g, Units.ext (by rw [hφ, hg]; simp)⟩)
    (fun a ha q => Units.ext (by
      rw [hφ]
      exact htor _ (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]) _)) hQ
  have hc0 : c 1 = 1 := by
    have := hc1 1 1
    simpa using this
  obtain ⟨h, hh⟩ := GlobalTheory.exists_unit_of_cocycle_rightAction_charZero F Q τ hτ (fun q => c q⁻¹ ^ 2)
    (fun q q' => by
      rw [_root_.mul_inv_rev, hc1]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, hφ, inv_inv, map_pow]
      ring)
    (fun q hq => by
      have e := hc1 q⁻¹ q⁻¹
      rw [← _root_.mul_inv_rev, hsq q hq, inv_one, hc0] at e
      have e2 : φ q⁻¹ (c q⁻¹) = c q⁻¹ := Units.ext (by rw [hφ, inv_inv, hq])
      rw [e2] at e
      rw [sq, ← e])
  refine ⟨h⁻¹, fun q => ?_⟩
  have e := congrArg Units.val (hc2 q⁻¹)
  rw [hφ, inv_inv] at e
  simp only [Units.val_pow_eq_pow_val, Units.val_mul] at e
  have e4 : (f : F) ^ 4 = ((f : F) ^ 2) ^ 2 := by ring
  have hc := (c q⁻¹).ne_zero
  have hh0 := h.ne_zero
  rw [map_mul, map_pow (τ q) _ m, Units.val_inv_eq_inv_val, map_inv₀, hh q, e4, map_pow, e]
  simp only [Units.val_pow_eq_pow_val, mul_inv, mul_pow, inv_pow]
  have : ((c q⁻¹ : F) ^ 2) ^ m = ((c q⁻¹ : F) ^ m) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [this]
  field_simp

theorem mem_gamma_iff {M : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma M ↔ ∀ i j, (M : ℤ) ∣ γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Fin.forall_fin_two]
  simp [sub_eq_zero, and_assoc]

theorem gamma_mono {M N : ℕ} (h : M ∣ N) : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [mem_gamma_iff] at hγ ⊢
  exact fun i j => (Int.natCast_dvd_natCast.2 h).trans (hγ i j)

theorem gamma_inf {M N : ℕ} (h : Nat.Coprime M N) {γ : SL(2, ℤ)} (h1 : γ ∈ CongruenceSubgroup.Gamma M)
    (h2 : γ ∈ CongruenceSubgroup.Gamma N) : γ ∈ CongruenceSubgroup.Gamma (M * N) := by
  rw [mem_gamma_iff] at h1 h2 ⊢
  intro i j
  push_cast
  exact (Nat.isCoprime_iff_coprime.2 h).mul_dvd (h1 i j) (h2 i j)

theorem exists_lift {M N : ℕ} (h : Nat.Coprime M N) (q : SL(2, ZMod N)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma M, SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ = q := by
  let e := ZMod.chineseRemainder h
  let B : Matrix (Fin 2) (Fin 2) (ZMod M × ZMod N) :=
    Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (ZMod M)) i j, q i j)
  have hB : B.det = 1 := by
    have := q.det_coe
    rw [Matrix.det_fin_two] at this ⊢
    ext
    · simp [B]
    · simpa [B] using this
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective (M * N)
    (SpecialLinearGroup.map (e.symm : ZMod M × ZMod N →+* ZMod (M * N)) ⟨B, hB⟩)
  have key : ∀ i j, ((γ i j : ℤ) : ZMod M × ZMod N) = B i j := by
    intro i j
    have h1 : ((γ i j : ℤ) : ZMod (M * N)) = e.symm (B i j) := congrArg (fun x : SL(2, ZMod (M * N)) => x i j) hγ
    have h2 := congrArg e h1
    rwa [map_intCast, RingEquiv.apply_symm_apply] at h2
  refine ⟨γ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [B] using congrArg Prod.fst (key 0 0)
    · simpa [B] using congrArg Prod.fst (key 0 1)
    · simpa [B] using congrArg Prod.fst (key 1 0)
    · simpa [B] using congrArg Prod.fst (key 1 1)
  · ext i j
    simpa [B] using congrArg Prod.snd (key i j)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def levSub (X : Tower Ω ε) (M : ℕ) : Subfield X.K where
  carrier := {f | Lev X M f}
  mul_mem' := fun ha hb γ hγ => by rw [map_mul, ha γ hγ, hb γ hγ]
  one_mem' := fun γ _ => map_one _
  add_mem' := fun ha hb γ hγ => by rw [map_add, ha γ hγ, hb γ hγ]
  zero_mem' := fun γ _ => map_zero _
  neg_mem' := fun ha γ hγ => by rw [map_neg, ha γ hγ]
  inv_mem' := fun a ha γ hγ => by rw [map_inv₀, ha γ hγ]

theorem lev_sl (X : Tower Ω ε) {M : ℕ} {f : X.K} (hf : Lev X M f) (γ : SL(2, ℤ)) :
    Lev X M (X.sl (ofSL γ) f) := by
  intro δ hδ
  have h := hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)
  rw [← X.sl_mul, ← map_mul]
  conv_rhs => rw [← h]
  rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]

noncomputable def levAct (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) : levSub X M →+* levSub X M :=
  RingHom.codRestrict ((X.sl (ofSL γ) : X.K →+* X.K).comp (levSub X M).subtype) (levSub X M)
    fun a => lev_sl X a.2 γ

theorem coe_levAct (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) (a : levSub X M) :
    (levAct X M γ a : X.K) = X.sl (ofSL γ) a := rfl

theorem sl_root [IsAlgClosed Ω] (X : Tower Ω ε) {m : ℕ} (hm : 0 < m) {a : X.K} (ha : a ^ m = 1) (g : GQ) :
    X.sl g a = a := by
  have hi : IsIntegral Ω a := IsIntegral.of_pow hm (ha ▸ isIntegral_one)
  obtain ⟨b, rfl⟩ := minpoly.mem_range_of_degree_eq_one Ω a
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact AlgEquiv.commutes _ b

theorem descent : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n Ma Mb : ℕ), l.Prime → 0 < Ma → 0 < Mb → 6 * l ∣ Ma → Nat.Coprime Ma Mb → ∀ f : X.Kˣ, Lev X (Ma * Mb) f → (∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∃ g : X.Kˣ, Lev X (Ma * Mb) g ∧ X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ h : X.Kˣ, Lev X Ma ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n Ma Mb hl hMa hMb h6 hco f hf hinv
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  haveI : NeZero Mb := ⟨hMb.ne'⟩
  let ρ : SL(2, ℤ) →* SL(2, ZMod Mb) := SpecialLinearGroup.map (Int.castRingHom (ZMod Mb))
  choose s hs1 hs2 using exists_lift hco
  have hs2' : ∀ q, ρ (s q) = q := hs2
  have hact : ∀ γ ∈ CongruenceSubgroup.Gamma Ma, ∀ a : X.K, Lev X (Ma * Mb) a →
      X.sl (ofSL (s (ρ γ))) a = X.sl (ofSL γ) a := by
    intro γ hγ a ha
    have hm : s (ρ γ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma (Ma * Mb) := by
      refine gamma_inf hco (Subgroup.mul_mem _ (hs1 _) (Subgroup.inv_mem _ hγ)) ?_
      show ρ (s (ρ γ) * γ⁻¹) = 1
      rw [map_mul, map_inv, hs2', mul_inv_cancel]
    conv_rhs => rw [← ha _ hm]
    rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]
  let u : ∀ g : X.Kˣ, Lev X (Ma * Mb) g → (levSub X (Ma * Mb))ˣ := fun g hg =>
    Units.mk0 ⟨g, hg⟩ (fun h => g.ne_zero (congrArg Subtype.val h))
  obtain ⟨h, hh⟩ := exists_invariant (Q := SL(2, ZMod Mb)) (fun q => levAct X (Ma * Mb) (s q))
    (fun q q' a => Subtype.ext (by
      rw [coe_levAct, coe_levAct, coe_levAct, ← X.sl_mul, ← map_mul,
        ← hact _ (Subgroup.mul_mem _ (hs1 q) (hs1 q')) _ a.2, map_mul, hs2', hs2']))
    (l ^ n) (u f hf)
    (fun q => by
      obtain ⟨g, hg1, hg2⟩ := hinv _ (hs1 q)
      exact ⟨u g hg1, Subtype.ext hg2⟩)
    (fun a ha q => Subtype.ext (sl_root X (pow_pos hl.pos n) (congrArg Subtype.val ha) _))
    (fun q hq => by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.jTranslates_level_and_scalar_mod ε X Mb hMb
      obtain ⟨e1, e2, e3⟩ := h2 (s q) (fun g hg =>
        congrArg Subtype.val (hq ⟨_, fun γ hγ => h1 g hg γ (gamma_mono (dvd_mul_left Mb Ma) hγ)⟩))
      have key : ∀ i j, (en (s q) i j : ZMod Mb) = q i j := fun i j =>
        congrArg (fun x : SL(2, ZMod Mb) => x i j) (hs2 q)
      simp only [key] at e1 e2 e3
      have hd := q.det_coe
      rw [Matrix.det_fin_two, e1, e2] at hd
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, e1, e2] <;>
        first | (simpa [e3] using hd))
    (GlobalTheory.T.exists_hom_to_kernel_sq_centralExtension_slTwoZMod l n Mb hl hMb (Nat.Coprime.coprime_dvd_right h6 hco.symm))
  refine ⟨Units.map (levSub X (Ma * Mb)).subtype.toMonoidHom h, fun γ hγ => ?_⟩
  have e := congrArg Subtype.val (hh (ρ γ))
  have hw : ∀ w : levSub X (Ma * Mb), Lev X (Ma * Mb) (w : X.K) := fun w => w.2
  rw [coe_levAct, hact γ hγ _ (hw _)] at e
  exact e

end GlobalTheory.KZ.ES.CoprimeDescent
