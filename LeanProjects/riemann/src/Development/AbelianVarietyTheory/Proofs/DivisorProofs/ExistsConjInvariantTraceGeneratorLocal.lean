import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.RealTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_algebraMap (H : Host E) (r : 𝓞 (maximalRealSubfield E)) :
    H.bar (algebraMap _ (𝓞 E) r) = algebraMap _ (𝓞 E) r := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  have h1 : ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E) : E) =
      algebraMap (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) r) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E]
    exact (IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E r).symm
  rw [h1]
  exact (IsCMField.complexConj E).commutes _

theorem sub_bar_mem_pow_succ (H : Host E) (𝔭 : Ideal (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ c, c - H.bar c ∈ 𝔭 ^ n) (c : 𝓞 E) : c - H.bar c ∈ 𝔭 ^ (n + 1) := by
  haveI := H.unram
  let L : 𝓞 E →ₗ[𝓞 (maximalRealSubfield E)] (𝓞 E ⧸ 𝔭 ^ (n + 1)) :=
    { toFun := fun c => Ideal.Quotient.mk _ (c - H.bar c)
      map_add' := fun a b => by rw [← map_add, map_add H.bar]; congr 1; ring
      map_smul' := fun r a => by
        rw [Algebra.smul_def, map_mul, bar_algebraMap, ← mul_sub, RingHom.id_apply, Algebra.smul_def, map_mul,
          Ideal.Quotient.mk_algebraMap] }
  let D : Derivation (𝓞 (maximalRealSubfield E)) (𝓞 E) (𝓞 E ⧸ 𝔭 ^ (n + 1)) :=
    Derivation.mk' L fun a b => by
      show Ideal.Quotient.mk _ (a * b - H.bar (a * b)) =
        a • Ideal.Quotient.mk _ (b - H.bar b) + b • Ideal.Quotient.mk _ (a - H.bar a)
      rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, ← map_add,
        Ideal.Quotient.eq]
      have hab : (a - H.bar a) * (b - H.bar b) ∈ 𝔭 ^ (n + 1) :=
        Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) (by rw [pow_add]; exact Ideal.mul_mem_mul (h a) (h b))
      have : a * b - H.bar (a * b) - (a * (b - H.bar b) + b * (a - H.bar a)) = -((a - H.bar a) * (b - H.bar b)) := by
        rw [map_mul]; ring
      rw [this]; exact neg_mem hab
  have hD : D c = 0 := by
    rw [← Derivation.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D _ _ c) 0, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 hD

theorem exists_sub_bar_notMem (H : Host E) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭 ≠ ⊤) : ∃ c, c - H.bar c ∉ 𝔭 := by
  by_contra! h
  have key : ∀ n : ℕ, ∀ c, c - H.bar c ∈ 𝔭 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih => exact sub_bar_mem_pow_succ H 𝔭 (n + 1) (by omega) ih
  have h0 : H.rt - H.bar H.rt = 0 := by
    have hm : H.rt - H.bar H.rt ∈ ⨅ i, 𝔭 ^ i :=
      Ideal.mem_iInf.2 fun i => Ideal.pow_le_pow_right (Nat.le_succ i) (key i _)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭, Ideal.mem_bot] at hm
  rw [GlobalTheory.CharRank.bar_rt_neg, sub_neg_eq_add, ← two_mul] at h0
  have hrt : H.rt = 0 := (mul_eq_zero.1 h0).resolve_left two_ne_zero
  have hd := H.rt_sq
  rw [hrt, zero_pow two_ne_zero, zero_eq_neg, Nat.cast_eq_zero] at hd
  exact H.d_prime.ne_zero hd

end GlobalTheory.RealTheta

namespace GlobalTheory.RealTheta

open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_trace_eq (ψ : 𝓞 E →+ ℤ) : ∃ δ : E, ∀ u : 𝓞 E, ((ψ u : ℤ) : ℚ) = Algebra.trace ℚ E (δ * u) := by
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => (ψ (RingOfIntegers.basis E i) : ℚ))
  obtain ⟨δ, hδ⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective f
  refine ⟨δ, fun u => ?_⟩
  have h1 : Algebra.trace ℚ E (δ * u) = f u := by
    rw [← hδ, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]
  rw [h1]
  have h2 : ((Int.castAddHom ℚ).comp ψ).toIntLinearMap =
      (f.toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom).toIntLinearMap := by
    refine (RingOfIntegers.basis E).ext fun i => ?_
    simp [f, ← integralBasis_apply]
  exact (LinearMap.congr_fun h2 u)

open FractionalIdeal in

theorem exists_local_gen {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0) {𝔭 : Ideal (𝓞 E)} {δ : E} (hδ : δ ∈ M)
    (hδ' : δ ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M) :
    ∃ s : 𝓞 E, s ∉ 𝔭 ∧ ∀ x ∈ M, ∃ t : 𝓞 E, (s : E) * x = δ * t := by
  set I := spanSingleton (𝓞 E)⁰ δ * M⁻¹ with hI
  have hIM : I * M = spanSingleton (𝓞 E)⁰ δ := by
    rw [hI, mul_assoc, inv_mul_cancel₀ hM, mul_one]
  have hI1 : I ≤ 1 := by
    rw [← mul_inv_cancel₀ hM, hI]
    exact mul_le_mul_left (spanSingleton_le_iff_mem.2 hδ) _
  have hnot : ¬ I ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro h
    apply hδ'
    have : spanSingleton (𝓞 E)⁰ δ ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := hIM ▸ mul_le_mul_left h M
    exact spanSingleton_le_iff_mem.1 this
  obtain ⟨y, hyI, hy𝔭⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨s, rfl⟩ := (mem_one_iff _).1 (hI1 hyI)
  refine ⟨s, fun hs => hy𝔭 ((mem_coeIdeal _).2 ⟨s, hs, rfl⟩), fun x hx => ?_⟩
  have : algebraMap (𝓞 E) E s * x ∈ spanSingleton (𝓞 E)⁰ δ := hIM ▸ mul_mem_mul hyI hx
  obtain ⟨t, ht⟩ := (mem_spanSingleton _).1 this
  exact ⟨t, by rw [← ht, Algebra.smul_def, mul_comm]⟩

open FractionalIdeal in

theorem exists_mem_notMem_mul {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭 ≠ ⊤) :
    ∃ x ∈ M, x ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
  by_contra! h
  have hle : M ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := fun x hx => h x hx
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ 𝔭 := by
    have := mul_le_mul_left hle M⁻¹
    rwa [mul_assoc, mul_inv_cancel₀ hM, mul_one] at this
  rw [← coeIdeal_top, coeIdeal_le_coeIdeal E] at h1
  exact h𝔭 (top_le_iff.1 h1)

theorem fi_add_mem (N : FractionalIdeal (𝓞 E)⁰ E) {x y : E} (hx : x ∈ N) (hy : y ∈ N) : x + y ∈ N :=
  FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hy))

theorem fi_sub_mem (N : FractionalIdeal (𝓞 E)⁰ E) {x y : E} (hx : x ∈ N) (hy : y ∈ N) : x - y ∈ N :=
  FractionalIdeal.mem_coe.1 (Submodule.sub_mem _ (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hy))

theorem fi_mul_mem (N : FractionalIdeal (𝓞 E)⁰ E) (a : 𝓞 E) {y : E} (hy : y ∈ N) : (a : E) * y ∈ N := by
  have := Submodule.smul_mem (N : Submodule (𝓞 E) E) a (FractionalIdeal.mem_coe.2 hy)
  rw [Algebra.smul_def] at this
  exact FractionalIdeal.mem_coe.1 this

theorem exists_real_notMem (H : Host E) {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0)
    (hconj : ∀ x ∈ M, IsCMField.complexConj E x ∈ M) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ δ ∈ M, IsCMField.complexConj E δ = δ ∧ δ ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
  obtain ⟨x, hx, hx'⟩ := exists_mem_notMem_mul hM h𝔭.ne_top
  obtain ⟨c, hc⟩ := exists_sub_bar_notMem H h𝔭.ne_top
  have hcc : ∀ y, IsCMField.complexConj E (IsCMField.complexConj E y) = y := IsCMField.complexConj_apply_apply E
  have hbar : IsCMField.complexConj E (c : E) = (H.bar c : E) := (H.bar_eq c).symm
  by_cases h1 : x + IsCMField.complexConj E x ∈ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M
  · refine ⟨(c : E) * x + IsCMField.complexConj E ((c : E) * x), fi_add_mem _ (fi_mul_mem M c hx)
      (hconj _ (fi_mul_mem M c hx)), by rw [map_add, hcc, add_comm], fun h2 => hx' ?_⟩
    have h3 : ((c - H.bar c : 𝓞 E) : E) * x ∈ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
      have := fi_sub_mem _ h2 (fi_mul_mem _ (H.bar c) h1)
      convert this using 1
      rw [map_mul, hbar]; push_cast; ring
    obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv hc
    have hyi' := congrArg (fun z : 𝓞 E => (z : E)) hyi
    push_cast at hyi'
    have : x = (y : E) * (((c - H.bar c : 𝓞 E) : E) * x) + (i : E) * x := by
      push_cast; linear_combination (-x) * hyi'
    rw [this]
    exact fi_add_mem _ (fi_mul_mem _ y h3)
      (FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨i, hi, rfl⟩) hx)
  · exact ⟨x + IsCMField.complexConj E x, fi_add_mem _ hx (hconj x hx), by rw [map_add, hcc, add_comm], h1⟩

theorem trace_conj (y : E) : Algebra.trace ℚ E (IsCMField.complexConj E y) = Algebra.trace ℚ E y :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y

theorem conj_mem_dual (H : Host E) {x : E} (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    IsCMField.complexConj E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)] at hx ⊢
  intro a ha
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  have := hx _ ((FractionalIdeal.mem_one_iff _).2 ⟨H.bar b, rfl⟩)
  rw [Algebra.traceForm_apply] at this ⊢
  convert this using 1
  rw [← trace_conj, map_mul, IsCMField.complexConj_apply_apply]
  exact congrArg (fun y => Algebra.trace ℚ E (x * y)) (H.bar_eq b).symm

end GlobalTheory.RealTheta

namespace GlobalTheory.RealTheta

open scoped nonZeroDivisors

theorem exists_bar_inv_trace_gen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
  intro E _ _ _ H 𝔭 h𝔭
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set M : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hMdef
  have hM : M ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h10
  obtain ⟨δ, hδM, hδc, hδ⟩ := exists_real_notMem H hM (fun x hx => conj_mem_dual H hx) h𝔭
  have hint : ∀ x ∈ M, ∀ u : 𝓞 E, ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ E (x * u) := by
    intro x hx u
    rw [hMdef, FractionalIdeal.mem_dual h10] at hx
    obtain ⟨z, hz⟩ := hx _ ((FractionalIdeal.mem_one_iff _).2 ⟨u, rfl⟩)
    exact ⟨z, by rw [← Algebra.traceForm_apply, ← hz]; simp⟩
  choose z hz using hint δ hδM
  let θ : 𝓞 E →+ ℤ := AddMonoidHom.mk' z fun a b => Int.cast_injective (α := ℚ) (by
    push_cast; rw [hz, hz, hz]; push_cast; rw [mul_add, map_add])
  have hθ : ∀ u, ((θ u : ℤ) : ℚ) = Algebra.trace ℚ E (δ * u) := hz
  have hmemψ : ∀ ψ : 𝓞 E →+ ℤ, ∃ x ∈ M, ∀ u : 𝓞 E, ((ψ u : ℤ) : ℚ) = Algebra.trace ℚ E (x * u) := by
    intro ψ
    obtain ⟨x, hx⟩ := exists_trace_eq ψ
    refine ⟨x, (FractionalIdeal.mem_dual h10).2 fun a ha => ?_, hx⟩
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    exact ⟨ψ b, by rw [Algebra.traceForm_apply]; simpa using (hx b)⟩
  obtain ⟨s, hs, hsM⟩ := exists_local_gen hM hδM hδ
  have hθbar : ∀ t, θ (H.bar t) = θ t := by
    intro t
    apply Int.cast_injective (α := ℚ)
    rw [hθ, hθ, H.bar_eq, ← hδc, ← map_mul, trace_conj, hδc]
  have hPs : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
    intro ψ
    obtain ⟨x, hx, hψ⟩ := hmemψ ψ
    obtain ⟨t, ht⟩ := hsM x hx
    refine ⟨t, fun u => Int.cast_injective (α := ℚ) ?_⟩
    rw [hψ, hθ]
    push_cast
    rw [← mul_assoc, mul_comm x, ht, mul_assoc]
  have hPbar : ∀ s : 𝓞 E, (∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) →
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (H.bar s * u) = θ (t * u) := by
    intro s hs ψ
    obtain ⟨t, ht⟩ := hs (ψ.comp (H.bar : 𝓞 E →+* 𝓞 E).toAddMonoidHom)
    refine ⟨H.bar t, fun u => ?_⟩
    have := ht (H.bar u)
    simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingHom.coe_coe,
      map_mul, bar_bar] at this
    rw [this, ← hθbar (t * H.bar u), map_mul, bar_bar]
  refine ⟨θ, hθbar, ?_⟩
  by_cases hb : H.bar s ∈ 𝔭
  · have hsb : s + H.bar s ∉ 𝔭 := fun h => hs (by have := sub_mem h hb; rwa [add_sub_cancel_right] at this)
    refine ⟨s + H.bar s, hsb, by rwa [map_add, bar_bar, add_comm], fun ψ => ?_⟩
    obtain ⟨t, ht⟩ := hPs ψ
    obtain ⟨t', ht'⟩ := hPbar s hPs ψ
    exact ⟨t + t', fun u => by rw [add_mul, map_add, ht, ht', add_mul, map_add]⟩
  · exact ⟨s, hs, hb, hPs⟩

end GlobalTheory.RealTheta
