import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PDivisibleGroupsOverOC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleDifferentialsTorsionFreeStatement

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SatForm

section General

variable {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
  {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]

omit [IsDomain O] in

theorem isLocalizedModule_mk (M : Type) [AddCommGroup M] [Module O M] :
    IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O C M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) C _).2 (TensorProduct.isBaseChange O M C)

theorem exists_smul_eq_tmul (z : C ⊗[O] M) :
    ∃ (s : O) (m : M), s ≠ 0 ∧ s • z = (1 : C) ⊗ₜ m := by
  haveI := isLocalizedModule_mk (O := O) (C := C) M
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors O) (TensorProduct.mk O C M 1) z
  exact ⟨s, m, nonZeroDivisors.ne_zero s.2, hs⟩

theorem one_tmul_eq_zero_iff (n : N) : (1 : C) ⊗ₜ[O] n = 0 ↔ ∃ c : O, c ≠ 0 ∧ c • n = 0 := by
  constructor
  · intro h
    haveI := isLocalizedModule_mk (O := O) (C := C) N
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O)
      (f := TensorProduct.mk O C N 1) (x₁ := n) (x₂ := 0) (by simpa using h)
    have hc' : (c : O) • n = (c : O) • 0 := hc
    exact ⟨c, nonZeroDivisors.ne_zero c.2, by rw [hc', smul_zero]⟩
  · rintro ⟨c, hc, hn⟩
    have h1 : algebraMap O C c • ((1 : C) ⊗ₜ[O] n) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hn, TensorProduct.tmul_zero]
    exact (smul_eq_zero.1 h1).resolve_left
      ((map_ne_zero_iff _ (IsFractionRing.injective O C)).2 hc)

theorem baseChange_one_tmul_eq_zero_iff (L : M →ₗ[O] N)
    (hN : ∀ (c : O) (n : N), c ≠ 0 → c • n = 0 → n = 0) (m : M) :
    L.baseChange C ((1 : C) ⊗ₜ m) = 0 ↔ L m = 0 := by
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    exact hN c _ hc h
  · intro h
    exact ⟨1, one_ne_zero, by rw [h, smul_zero]⟩

theorem baseChange_eq_zero_iff (L : M →ₗ[O] N)
    (hN : ∀ (c : O) (n : N), c ≠ 0 → c • n = 0 → n = 0) (z : C ⊗[O] M) {s : O} {m : M}
    (hs : s ≠ 0) (h : s • z = (1 : C) ⊗ₜ m) : L.baseChange C z = 0 ↔ L m = 0 := by
  have hs' : algebraMap O C s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O C)).2 hs
  rw [← baseChange_one_tmul_eq_zero_iff (C := C) L hN, ← h, ← algebraMap_smul C s z, map_smul,
    smul_eq_zero, or_iff_right hs']

theorem one_tmul_mem_span_iff (W : Submodule O M)
    (hW : ∀ (c : O) (x : M), c ≠ 0 → c • x ∈ W → x ∈ W) (y : M) :
    (1 : C) ⊗ₜ[O] y ∈ Submodule.span C (TensorProduct.mk O C M 1 '' W) ↔ y ∈ W := by
  constructor
  · intro hy
    have key : ∀ z ∈ Submodule.span C (TensorProduct.mk O C M 1 '' W),
        ∃ (s : O) (w : M), s ≠ 0 ∧ w ∈ W ∧ s • z = (1 : C) ⊗ₜ w := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨w, hw, rfl⟩ := hx
        exact ⟨1, w, one_ne_zero, hw, by simp⟩
      | zero => exact ⟨1, 0, one_ne_zero, W.zero_mem, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, w, hs, hw, hsx⟩ := hx
        obtain ⟨t, u, ht, hu, hty⟩ := hy
        refine ⟨s * t, t • w + s • u, mul_ne_zero hs ht,
          W.add_mem (W.smul_mem _ hw) (W.smul_mem _ hu), ?_⟩
        have e1 : (s * t) • x = (1 : C) ⊗ₜ (t • w) := by
          rw [mul_comm, mul_smul, hsx, TensorProduct.tmul_smul]
        have e2 : (s * t) • y = (1 : C) ⊗ₜ (s • u) := by
          rw [mul_smul, hty, TensorProduct.tmul_smul]
        rw [smul_add, e1, e2, TensorProduct.tmul_add]
      | smul a x _ hx =>
        obtain ⟨s, w, hs, hw, hsx⟩ := hx
        obtain ⟨⟨b, d⟩, hbd⟩ := IsLocalization.surj (nonZeroDivisors O) a
        refine ⟨(d : O) * s, b • w, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs,
          W.smul_mem _ hw, ?_⟩
        rw [smul_comm, mul_smul, hsx, ← algebraMap_smul C (d : O), smul_smul, hbd,
          algebraMap_smul, TensorProduct.tmul_smul]
    obtain ⟨s, w, hs, hw, h⟩ := key _ hy
    rw [← TensorProduct.tmul_smul] at h
    haveI := isLocalizedModule_mk (O := O) (C := C) M
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O)
      (f := TensorProduct.mk O C M 1) (x₁ := s • y) (x₂ := w) h
    have hc' : (c : O) • s • y = (c : O) • w := hc
    refine hW ((c : O) * s) y (mul_ne_zero (nonZeroDivisors.ne_zero c.2) hs) ?_
    rw [mul_smul, hc']
    exact W.smul_mem _ hw
  · intro hy
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end General

theorem scholzeWeinsteinB_of_subspaces (hPD : GlobalTheory.Published.PrismaticDieudonneHodge)
    (hC : GlobalTheory.Published.PDivisibleGroupsOverOC) : GlobalTheory.Published.ScholzeWeinsteinB := by
  intro p _ C _ _ _ v O _ _ hv _ _ _
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : IsFractionRing O C := hv.isFractionRing
  have tf : ∀ G : GlobalTheory.PDivGroup p O, ∀ (c : O) (w : G.dual.omega), c ≠ 0 → c • w = 0 → w = 0 :=
    fun G => GlobalTheory.T.p_divisible_differentials_torsion_free hPD p C v O hv G.dual
  obtain ⟨h1, h2⟩ := hC p C v O hv
  refine ⟨fun G H f hf => h1 G H f ?_, fun h W hW => ?_⟩
  · intro x hx
    rw [GlobalTheory.Published.hodgeTateSubspace, LinearMap.mem_ker] at hx ⊢
    obtain ⟨s, m, hs, hsm⟩ := exists_smul_eq_tmul (C := C) x
    have hm : G.hodgeTateLinear m = 0 := (baseChange_eq_zero_iff _ (tf G) x hs hsm).1 hx
    refine (baseChange_eq_zero_iff (C := C) _ (tf H) _ hs ?_).2 (hf m hm)
    rw [← LinearMap.map_smul_of_tower, hsm, LinearMap.baseChange_tmul]
  · obtain ⟨G, e, he⟩ := h2 h (Submodule.span C (TensorProduct.mk O C _ 1 '' W))
    refine ⟨G, e, fun x => ?_⟩
    have hx := he ((1 : C) ⊗ₜ x)
    rw [GlobalTheory.Published.hodgeTateSubspace, LinearMap.mem_ker, baseChange_one_tmul_eq_zero_iff _ (tf G),
      LinearMap.baseChange_tmul, one_tmul_mem_span_iff W hW] at hx
    exact hx

end GlobalTheory.SatForm
