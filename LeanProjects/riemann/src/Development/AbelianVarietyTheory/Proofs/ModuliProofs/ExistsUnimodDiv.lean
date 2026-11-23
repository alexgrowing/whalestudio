import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdMulOfIdem

open scoped nonZeroDivisors

namespace GlobalTheory.HeckeTate

theorem exists_local_iso {R : Type} [CommRing R] [IsDedekindDomain R] {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R M'] (hr : Module.finrank R M = Module.finrank R M') (P : Ideal R) [P.IsPrime] :
    ∃ (φ : M →ₗ[R] M') (φ' : M' →ₗ[R] M) (s : R), s ∉ P ∧ (∀ a, φ' (φ a) = s • a) ∧ ∀ y, φ (φ' y) = s • y := by
  have hle : P.primeCompl ≤ R⁰ := P.primeCompl_le_nonZeroDivisors
  have : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Flat R M' := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : Module.FinitePresentation R M' := Module.finitePresentation_of_finite R M'
  let S := Localization.AtPrime P
  let N := LocalizedModule P.primeCompl M
  let N' := LocalizedModule P.primeCompl M'
  let j : M →ₗ[R] N := LocalizedModule.mkLinearMap P.primeCompl M
  let j' : M' →ₗ[R] N' := LocalizedModule.mkLinearMap P.primeCompl M'
  have : Module.Free S N := Module.free_of_flat_of_isLocalRing
  have : Module.Free S N' := Module.free_of_flat_of_isLocalRing
  have hr' : Module.finrank S N = Module.finrank S N' := by
    rw [IsLocalization.finrank_eq S P.primeCompl hle, IsLocalization.finrank_eq S P.primeCompl hle,
      IsLocalizedModule.finrank_eq P.primeCompl j hle, IsLocalizedModule.finrank_eq P.primeCompl j' hle, hr]
  let θ : N ≃ₗ[R] N' := (LinearEquiv.ofFinrankEq N N' hr').restrictScalars R
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule P.primeCompl j'
    (θ.toLinearMap ∘ₗ j)
  obtain ⟨φ', s', hφ'⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule P.primeCompl j
    (θ.symm.toLinearMap ∘ₗ j')
  have h1 : ∀ a, j' (φ a) = (s : R) • θ (j a) := fun a => LinearMap.congr_fun hφ a
  have h2 : ∀ a, j (φ' a) = (s' : R) • θ.symm (j' a) := fun a => LinearMap.congr_fun hφ' a
  have hj : Function.Injective j := (IsLocalizedModule.injective_iff_isRegular P.primeCompl j).2
    fun c => IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero (hle c.2))
  have hj' : Function.Injective j' := (IsLocalizedModule.injective_iff_isRegular P.primeCompl j').2
    fun c => IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero (hle c.2))
  refine ⟨φ, φ', (s * s' : P.primeCompl), (s * s').2, fun a => hj ?_, fun y => hj' ?_⟩
  · rw [h2, h1, map_smul, map_smul, LinearEquiv.symm_apply_apply, smul_smul, mul_comm]; rfl
  · rw [h1, h2, map_smul, map_smul, LinearEquiv.apply_symm_apply, smul_smul]; rfl

theorem mem_of_orth {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (B : M →+ M →+ ℤ)
    (hB : Function.Bijective B) {m c : ℕ} (hm : m ≠ 0) (hg : m ^ Module.finrank ℤ M = c * c) (C : AddSubgroup M)
    (hC : (nsmulAddMonoidHom (α := M) m).range ≤ C)
    (hc : (nsmulAddMonoidHom (α := M) m).range.relIndex C = c)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (x : M) (hx : ∀ y ∈ C, (m : ℤ) ∣ B x y) : x ∈ C := by
  classical
  have : NeZero m := ⟨hm⟩
  set K := (nsmulAddMonoidHom (α := M) m).range with hK
  have hKi : K.index = c * c := by rw [hK, AddSubgroup.index_range_nsmul, hg]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ hm (by simpa using hg)
  have hCi : C.index = c := by
    have := AddSubgroup.relIndex_mul_index hC
    rw [hc, hKi] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) this
  have : C.FiniteIndex := ⟨hCi ▸ hc0⟩
  let D : AddSubgroup M :=
    { carrier := {x | ∀ y ∈ C, (m : ℤ) ∣ B x y}
      add_mem' := fun {a b} ha hb y hy => by
        rw [map_add, AddMonoidHom.add_apply]; exact (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => by simp
      neg_mem' := fun {a} ha y hy => by
        rw [map_neg, AddMonoidHom.neg_apply]; exact (ha y hy).neg_right }
  have hCD : C ≤ D := fun x hx => hiso x hx
  let f : D → (M ⧸ C →+ ZMod m) := fun x =>
    QuotientAddGroup.lift C ((Int.castAddHom (ZMod m)).comp (B x)) fun y hy =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (x.2 y hy)
  have hf : ∀ (x : D) (y : M), f x (y : M ⧸ C) = (B x y : ZMod m) := fun _ _ => rfl
  let F : D →+ (M ⧸ C →+ ZMod m) := AddMonoidHom.mk' f fun a b => by
    ext y
    simp [hf]
  have hker : F.ker = K.addSubgroupOf D := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h
      have h1 : ∀ y, (m : ℤ) ∣ B x y := fun y =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by rw [← hf]; exact DFunLike.congr_fun h _)
      choose t ht using h1
      have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
      obtain ⟨z, hz⟩ := hB.2 (AddMonoidHom.mk' t fun a b => mul_left_cancel₀ hm' (by
        rw [← ht, map_add, ht, ht, mul_add]))
      refine ⟨z, hB.1 (AddMonoidHom.ext fun y => ?_)⟩
      rw [ht, nsmulAddMonoidHom_apply, map_nsmul, hz]
      simp
    · rintro ⟨z, hz⟩
      ext y
      change f x y = 0
      rw [hf, ← hz, nsmulAddMonoidHom_apply, map_nsmul]
      simp
  have := Fintype.ofFinite (M ⧸ C)
  let T : (M ⧸ C →+ ZMod m) → AddChar (M ⧸ C) ℂ := fun φ => ZMod.stdAddChar.compAddMonoidHom φ
  have hT : Function.Injective T := fun φ ψ h => AddMonoidHom.ext fun x =>
    ZMod.injective_stdAddChar (DFunLike.congr_fun h x)
  have : Finite (M ⧸ C →+ ZMod m) := Finite.of_injective T hT
  have h1 : K.relIndex D ≤ c := by
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker]
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
      ((Nat.card_le_card_of_injective T hT).trans_eq ?_)
    rw [← hCi, AddSubgroup.index, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have h2 := AddSubgroup.relIndex_mul_relIndex K C D hC hCD
  have h3 : C.relIndex D ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have h4 : C.relIndex D = 1 := by
    rw [hc] at h2
    have := Nat.pos_of_ne_zero hc0
    have := Nat.pos_of_ne_zero h3
    nlinarith
  exact (AddSubgroup.relIndex_eq_one.1 h4) hx

theorem exists_unimod_div {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {σ : R ≃+* R}
    {B : M →+ M →+ ℤ} (h : IsUnimod σ B) {m : ℕ} (hm : m ≠ 0) (C : Submodule R M) (hC : ∀ a, m • a ∈ C)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (horth : ∀ x, (∀ y ∈ C, (m : ℤ) ∣ B x y) → x ∈ C) :
    ∃ B' : C →+ C →+ ℤ, IsUnimod σ B' ∧ ∀ x y : C, B x y = m * B' x y := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  choose t ht using fun x y : C => hiso x x.2 y y.2
  let B' : C →+ C →+ ℤ := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (t x) fun a b => mul_left_cancel₀ hm' (by
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add]))
    fun a b => AddMonoidHom.ext fun y => mul_left_cancel₀ hm' (by
      change m * t (a + b) y = m * (t a y + t b y)
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add, AddMonoidHom.add_apply])
  have hB' : ∀ x y : C, B x y = m * B' x y := ht
  refine ⟨B', ⟨fun x y => mul_left_cancel₀ hm' ?_, fun a x y => mul_left_cancel₀ hm' ?_, ?_, fun f => ?_⟩, hB'⟩
  · rw [mul_neg, ← hB', ← hB', h.skew]
  · rw [← hB', ← hB', Submodule.coe_smul, Submodule.coe_smul, h.adj]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    apply (injective_iff_map_eq_zero _).1 h.bij.1
    ext a
    have := hB' x ⟨m • a, hC a⟩
    rw [hx, map_nsmul] at this
    simpa [hm] using this
  · let u : M →+ C := AddMonoidHom.mk' (fun a => ⟨m • a, hC a⟩) fun a b => Subtype.ext (smul_add _ _ _)
    obtain ⟨x, hx⟩ := h.bij.2 (f.comp u)
    have key : ∀ y : C, B x y = m * f y := fun y => by
      rw [hx, ← nsmul_eq_mul, ← map_nsmul]
      rfl
    refine ⟨⟨x, horth x fun y hy => ⟨_, key ⟨y, hy⟩⟩⟩, AddMonoidHom.ext fun y => mul_left_cancel₀ hm' ?_⟩
    rw [← hB', key]

end GlobalTheory.HeckeTate
