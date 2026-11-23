import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.SliceFinDim

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem glide {T ι : Type} (Z : T → Submodule ℂ V) (hZ : ∀ t, FiniteDimensional ℂ (Z t))
    (s : T → ι → V) (hs : ∀ t y, s t y ∈ Z t)
    (H : ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → ∃ t y, s t y ∉ W) :
    ∃ (t : ℕ → T) (y : ℕ → ι) (β : ℕ → Module.Dual ℂ V), (∀ n, β n (s (t n) (y n)) = 1) ∧
      (∀ n m, n < m → ∀ v ∈ Z (t n), β m v = 0) ∧ (∀ v, ∀ᶠ n in atTop, β n v = 0) := by
  choose tt yy hty using H
  let step : {W : Submodule ℂ V // FiniteDimensional ℂ W} → {W : Submodule ℂ V // FiniteDimensional ℂ W} :=
    fun A => ⟨A.1 ⊔ Z (tt A.1 A.2), by haveI := A.2; haveI := hZ (tt A.1 A.2); infer_instance⟩
  let acc : ℕ → {W : Submodule ℂ V // FiniteDimensional ℂ W} :=
    fun n => Nat.rec ⟨⊥, inferInstance⟩ (fun _ A => step A) n
  have hacc : ∀ n, (acc (n + 1)).1 = (acc n).1 ⊔ Z (tt (acc n).1 (acc n).2) := fun n => rfl
  let Wn : ℕ → Submodule ℂ V := fun n => (acc n).1
  let t : ℕ → T := fun n => tt (acc n).1 (acc n).2
  let y : ℕ → ι := fun n => yy (acc n).1 (acc n).2
  have hnot : ∀ n, s (t n) (y n) ∉ Wn n := fun n => hty (acc n).1 (acc n).2
  have hmono : Monotone Wn := monotone_nat_of_le_succ fun n => by
    show (acc n).1 ≤ (acc (n + 1)).1
    rw [hacc]; exact le_sup_left
  have hZle : ∀ n, Z (t n) ≤ Wn (n + 1) := fun n => by
    show Z (t n) ≤ (acc (n + 1)).1
    rw [hacc]; exact le_sup_right
  let Winf : Submodule ℂ V := ⨆ n, Wn n
  have hWle : ∀ n, Wn n ≤ Winf := fun n => le_iSup Wn n
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl Winf
  have hnot' : ∀ n, s (t n) (y n) ∉ Wn n ⊔ Q := by
    intro n hmem
    obtain ⟨w, hw, q, hq, hwq⟩ := Submodule.mem_sup.1 hmem
    have hh : s (t n) (y n) ∈ Winf := hWle (n + 1) (hZle n (hs _ _))
    have hqW : q ∈ Winf := by
      have : q = s (t n) (y n) - w := by rw [← hwq]; abel
      rw [this]; exact Winf.sub_mem hh (hWle n hw)
    have hq0 : q = 0 := (Submodule.disjoint_def.1 hQ.disjoint) q hqW hq
    apply hnot n
    rw [← hwq, hq0, add_zero]; exact hw
  have key : ∀ n, ∃ b : Module.Dual ℂ V, b (s (t n) (y n)) = 1 ∧ ∀ v ∈ Wn n ⊔ Q, b v = 0 := by
    intro n
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (hnot' n) inferInstance
    refine ⟨(f (s (t n) (y n)))⁻¹ • f, ?_, fun v hv => ?_⟩
    · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
    · have h1 : f v ∈ (Wn n ⊔ Q).map f := Submodule.mem_map_of_mem hv
      rw [hmap] at h1
      rw [LinearMap.smul_apply, (Submodule.mem_bot ℂ).1 h1, smul_zero]
  choose β hβ1 hβ0 using key
  refine ⟨t, y, β, hβ1, fun n m hnm v hv => hβ0 m v (Submodule.mem_sup_left (hmono hnm (hZle n hv))), fun v => ?_⟩
  have hv : v ∈ Winf ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, q, hq, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed Wn hmono.directed_le).1 hw
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  rw [map_add, hβ0 n w (Submodule.mem_sup_left (hmono hn hN)), hβ0 n q (Submodule.mem_sup_right hq), add_zero]

noncomputable def triSol (c : ℕ → ℕ → ℂ) : ℕ → ℂ
  | n => (n : ℂ) - ∑ m : Fin n, triSol c m * c n m
decreasing_by exact m.2

theorem triSol_sum (c : ℕ → ℕ → ℂ) (hc : ∀ n, c n n = 1) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), triSol c m * c n m = n := by
  rw [Finset.sum_range_succ, hc, mul_one]
  conv_lhs => rw [triSol]
  rw [Fin.sum_univ_eq_sum_range (fun m => triSol c m * c n m) n]
  ring

theorem support_finite_of_eventually {u : ℕ → ℂ} (h : ∀ᶠ n in atTop, u n = 0) (a : ℕ → ℂ) :
    (Function.support fun n => a n * u n).Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine (Set.finite_Iio N).subset fun n hn => ?_
  by_contra hc
  exact hn (show a n * u n = 0 by rw [hN n (not_lt.1 hc), mul_zero])

end Abstract

section Slices

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def slice (y : κ → Ainf F) : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ) where
  toFun Φ z := Φ (fun i => GlobalTheory.HeisSchA.mk (y i) (z i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem slice_pureA (y : κ → Ainf F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → Af F) → ℂ) :
    slice F y (pureA F f g) = f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) • g := by
  funext z
  rfl

theorem slices_finDim (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) :
    ∃ W : Submodule ℂ ((κ → Af F) → ℂ), FiniteDimensional ℂ W ∧ ∀ y, slice F y Φ ∈ W := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨ℂ ∙ g, inferInstance, fun y => ?_⟩
    rw [slice_pureA]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self g)
  | zero => exact ⟨⊥, inferInstance, fun y => by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨W, hW, hxW⟩ := hx
    obtain ⟨W', hW', hxW'⟩ := hx'
    exact ⟨W ⊔ W', inferInstance, fun y => by
      rw [map_add]; exact Submodule.add_mem_sup (hxW y) (hxW' y)⟩
  | smul a x _ hx =>
    obtain ⟨W, hW, hxW⟩ := hx
    exact ⟨W, hW, fun y => by rw [map_smul]; exact Submodule.smul_mem _ _ (hxW y)⟩

end Slices

theorem slices_of_bounded : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : Type) (Ψ : T → (κ → AF F) → ℂ), (∀ t, Ψ t ∈ schA F κ) →
    (∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) →
    ∃ W : Submodule ℂ ((κ → Af F) → ℂ), FiniteDimensional ℂ W ∧
      ∀ t (y : κ → Ainf F), (fun z : κ → Af F => Ψ t (fun i => GlobalTheory.HeisSchA.mk (y i) (z i))) ∈ W := by
  intro F _ _ κ _ T Ψ hΨ hb
  by_contra hne
  push Not at hne
  choose Z hZ hZs using fun t => slices_finDim F (Ψ t) (hΨ t)
  obtain ⟨t, y, β, h1, h2, h3⟩ := glide Z hZ (fun t y => slice F y (Ψ t)) hZs
    (fun W hW => by obtain ⟨t, y, h⟩ := hne W hW; exact ⟨t, y, h⟩)

  have hev : ∀ Φ ∈ schA F κ, ∀ᶠ n in atTop, β n (slice F (y n) Φ) = 0 := by
    intro Φ hΦ
    obtain ⟨W, hW, hyW⟩ := slices_finDim F Φ hΦ
    obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional W).2 hW
    have hS' : ∀ᶠ n in atTop, ∀ x ∈ S, β n x = 0 := (Filter.eventually_all_finset S).2 fun x _ => h3 x
    filter_upwards [hS'] with n hn
    have hle : W ≤ LinearMap.ker (β n) := by
      rw [← hS, Submodule.span_le]
      exact fun x hx => hn x hx
    exact hle (hyW (y n))
  let c : ℕ → ℕ → ℂ := fun n m => β m (slice F (y m) (Ψ (t n)))
  let a : ℕ → ℂ := triSol c
  let l₀ : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ∑ᶠ n, a n * β n (slice F (y n) Φ.1)
      map_add' := fun Φ Φ' => by
        simp only [Submodule.coe_add, map_add, mul_add]
        exact finsum_add_distrib (support_finite_of_eventually (hev Φ.1 Φ.2) a)
          (support_finite_of_eventually (hev Φ'.1 Φ'.2) a)
      map_smul' := fun r Φ => by
        simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [mul_finsum]
        exact finsum_congr fun n => by ring }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  have hlv : ∀ Φ (hΦ : Φ ∈ schA F κ), l Φ = ∑ᶠ n, a n * β n (slice F (y n) Φ) :=
    fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩

  have hadm : l ∈ (adeleClass F).adm κ := by
    intro g hg
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h3 g)
    let pt : ℕ → κ → mixedEmbedding.mixedSpace F := fun n i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y n i)
    refine ⟨∑ n ∈ Finset.range N, (a n * β n g) •
      (BoundedContinuousFunction.evalCLM ℂ (pt n)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
    have hmem : pureA F (⇑f) g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
    rw [hlv _ hmem, ContinuousLinearMap.sum_apply]
    have hterm : ∀ n, a n * β n (slice F (y n) (pureA F (⇑f) g)) = (a n * β n g) * f (pt n) := fun n => by
      rw [slice_pureA, map_smul, smul_eq_mul]; ring
    simp_rw [hterm]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
        SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
    · intro n hn
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      exact hn (show a n * β n g * f (pt n) = 0 by rw [hN n (not_lt.1 hc), mul_zero, zero_mul])

  have hval : ∀ n, l (Ψ (t n)) = n := by
    intro n
    rw [hlv _ (hΨ (t n))]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
    · exact triSol_sum c (fun n => h1 n) n
    · intro m hm
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      exact hm (show a m * β m (slice F (y m) (Ψ (t n))) = 0 by
        rw [h2 n m (by omega) _ (hZs (t n) (y m)), mul_zero])
  obtain ⟨C, hC⟩ := hb l hadm
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC (t n)
  rw [hval, Complex.norm_natCast] at this
  linarith

end GlobalTheory.SliceFinDim
