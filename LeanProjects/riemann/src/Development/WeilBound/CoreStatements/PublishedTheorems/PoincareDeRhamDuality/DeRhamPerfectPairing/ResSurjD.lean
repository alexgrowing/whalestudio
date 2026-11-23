import Mathlib

set_option autoImplicit false

open TensorProduct

namespace CrystallinePoints.Pd

theorem surjective_of_sup_smulD {R : Type} [CommRing R] {H M : Type*} [AddCommGroup H] [Module R H]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (γ : H →ₗ[R] M)
    (h : ∀ m : Ideal R, m.IsMaximal → LinearMap.range γ ⊔ m • (⊤ : Submodule R M) = ⊤) :
    Function.Surjective γ := by
  set P := LinearMap.range γ
  have key : ∀ m : Ideal R, m.IsMaximal → ∃ r : R, r - 1 ∈ m ∧ ∀ x : M, r • x ∈ P := by
    intro m hm
    have hin : (⊤ : Submodule R (M ⧸ P)) ≤ m • ⊤ := by
      have e := congrArg (Submodule.map P.mkQ) (h m hm)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ,
        Submodule.mkQ_map_self, bot_sup_eq] at e
      exact e.symm.le
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _
      (Module.Finite.fg_top) hin
    refine ⟨r, hr, fun x ↦ ?_⟩
    have := hr' (Submodule.Quotient.mk x) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  let J : Ideal R :=
    { carrier := {r | ∀ x : M, r • x ∈ P}
      add_mem' := fun ha hb x ↦ by rw [add_smul]; exact P.add_mem (ha x) (hb x)
      zero_mem' := fun x ↦ by rw [zero_smul]; exact P.zero_mem
      smul_mem' := fun c r hr x ↦ by rw [smul_eq_mul, mul_smul]; exact P.smul_mem c (hr x) }
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal J hne
    obtain ⟨r, hr, hr'⟩ := key m hm
    have h1 : r ∈ m := hle hr'
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h1 hr))
  intro x
  have : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
  have hx : x ∈ P := by simpa using this x
  exact hx

theorem finrank_res {R : Type} [CommRing R] (m : Ideal R) [hm : m.IsMaximal] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.rankAtStalk M (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have h := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ m) (⊥ : PrimeSpectrum (R ⧸ m))
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  rw [show Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = _ from h]
  congr 1
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

theorem oneT_iff {R : Type} [CommRing R] (m : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (y : M) : (1 : R ⧸ m) ⊗ₜ[R] y = 0 ↔ y ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff, ← Submodule.Quotient.mk_eq_zero]
  have : TensorProduct.quotTensorEquivQuotSMul M m ((1 : R ⧸ m) ⊗ₜ[R] y) = Submodule.Quotient.mk y := by
    have := TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) m 1 y
    rwa [map_one, one_smul] at this
  rw [this]

theorem resSurj_coreD.{u} :
  ∀ (R : Type) [CommRing R] (H : Type 1) [AddCommGroup H] [Module R H] (M : Type u) [AddCommGroup M] [Module R M]
    (g : ℕ) (F N : Submodule R H), IsCompl F N → Module.Finite R H → Module.Projective R H →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk H p = 2 * g) → Module.Finite R F → Module.Projective R F →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk F p = g) → Module.Finite R M → Module.Projective R M →
    (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = g) → ∀ γ : H →ₗ[R] M,
    (∀ m : Ideal R, m.IsMaximal → ∀ q : H, γ q ∈ m • (⊤ : Submodule R M) → q ∈ F ⊔ m • (⊤ : Submodule R H)) →
    Function.Surjective γ := by
  intro R _ H _ _ M _ _ g F N hc fH pH rH fF pF rF fM pM rM γ hγ
  refine surjective_of_sup_smulD γ fun m hm ↦ ?_
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  let π : H →ₗ[R] N := Submodule.linearProjOfIsCompl N F hc.symm
  have hπ : ∀ n : N, π n = n := fun n ↦ Submodule.linearProjOfIsCompl_apply_left hc.symm n
  have hπF : ∀ x ∈ F, π x = 0 := fun x hx ↦ Submodule.linearProjOfIsCompl_apply_right' hc.symm hx
  haveI : Module.Finite R N := Module.Finite.of_surjective π fun n ↦ ⟨n, hπ n⟩
  have d1 := finrank_res m H
  have d2 := finrank_res m F
  have d3 := finrank_res m M
  rw [rH] at d1
  rw [rF] at d2
  rw [rM] at d3
  have d4 : Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N) = g := by
    have e : (R ⧸ m) ⊗[R] H ≃ₗ[R ⧸ m] ((R ⧸ m) ⊗[R] F) × ((R ⧸ m) ⊗[R] N) :=
      (LinearEquiv.baseChange R (R ⧸ m) _ _ (Submodule.prodEquivOfIsCompl F N hc).symm).trans
        (TensorProduct.prodRight R (R ⧸ m) (R ⧸ m) F N)
    have := e.finrank_eq
    rw [Module.finrank_prod, d1, d2] at this
    omega
  have su : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  let δ := (γ ∘ₗ N.subtype).baseChange (R ⧸ m)
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, rfl⟩ := TensorProduct.mk_surjective R N (R ⧸ m) su z
    have h1 : γ n ∈ m • (⊤ : Submodule R M) := (oneT_iff m _).1 hz
    obtain ⟨f, hf, w, hw, e⟩ := Submodule.mem_sup.1 (hγ m hm n h1)
    refine (oneT_iff m n).2 ?_
    have e2 : n = π w := by rw [← hπ n, ← e, map_add, hπF f hf, zero_add]
    rw [e2]
    have : π w ∈ Submodule.map π (m • ⊤) := Submodule.mem_map_of_mem hw
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hs : Function.Surjective δ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (d4.trans d3.symm)).1 hinj
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz⟩ := hs ((1 : R ⧸ m) ⊗ₜ y)
  obtain ⟨n, rfl⟩ := TensorProduct.mk_surjective R N (R ⧸ m) su z
  have h2 : y - γ n ∈ m • (⊤ : Submodule R M) := by
    refine (oneT_iff m _).1 ?_
    rw [TensorProduct.tmul_sub, ← hz]
    exact sub_self _
  exact Submodule.mem_sup.2 ⟨γ n, ⟨n, rfl⟩, _, h2, add_sub_cancel _ _⟩

end CrystallinePoints.Pd
