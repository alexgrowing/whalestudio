import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrSep

noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

variable {E : Type} [Field E] [NumberField E]

theorem natCast_ne_zero_int (M : ℕ) (hM : M ≠ 0) : ((M : ℕ) : 𝓞 E) ≠ 0 := by
  intro h
  apply hM
  have := congrArg (algebraMap (𝓞 E) E) h
  simpa using this

theorem ideal_gen (M : ℕ) (hM : M ≠ 0) (J : Ideal (𝓞 E)) :
    ∃ a ∈ J, ∀ j ∈ J, ∃ c : 𝓞 E, ∃ j' ∈ J, j = c * a + (M : 𝓞 E) * j' := by
  by_cases hJ : J = ⊥
  · refine ⟨0, zero_mem _, fun j hj => ⟨0, 0, zero_mem _, ?_⟩⟩
    rw [hJ, Ideal.mem_bot] at hj
    simp [hj]
  · have hM' := natCast_ne_zero_int (E := E) M hM
    have hle : Ideal.span {((M : ℕ) : 𝓞 E)} * J ≤ J := Ideal.mul_le.2 (fun r _ s hs => J.mul_mem_left r hs)
    have hne : Ideal.span {((M : ℕ) : 𝓞 E)} * J ≠ 0 := by
      intro h
      rw [Ideal.zero_eq_bot, Ideal.mul_eq_bot] at h
      rcases h with h | h
      · exact hM' (Ideal.span_singleton_eq_bot.1 h)
      · exact hJ h
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    have haJ : a ∈ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    refine ⟨a, haJ, fun j hj => ?_⟩
    rw [← ha, Submodule.mem_sup] at hj
    obtain ⟨i, hi, s, hs, rfl⟩ := hj
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.1 hi
    exact ⟨c, z, hz, by ring⟩

theorem clear_fg (P : Submodule (𝓞 E) E) (hP : P.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ p ∈ P, ∃ q : 𝓞 E, (d : E) * p = q := by
  obtain ⟨s, rfl⟩ := hP
  obtain ⟨⟨b, hb⟩, hbs⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) s
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun p hp => ?_⟩
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨q, hq⟩ := hbs p hp
    refine ⟨q, ?_⟩
    have hq' : (q : E) = (b : E) * p := by
      have := hq
      rw [Algebra.smul_def] at this
      exact this
    exact hq'.symm
  | zero => exact ⟨0, by simp⟩
  | add p p' _ _ h h' =>
    obtain ⟨q, hq⟩ := h
    obtain ⟨q', hq'⟩ := h'
    exact ⟨q + q', by push_cast; linear_combination hq + hq'⟩
  | smul a p _ h =>
    obtain ⟨q, hq⟩ := h
    refine ⟨a * q, ?_⟩
    show (b : E) * ((a : E) * p) = ((a * q : 𝓞 E) : E)
    push_cast
    linear_combination (a : E) * hq

theorem sub_gen (M : ℕ) (hM : M ≠ 0) (P : Submodule (𝓞 E) E) (hP : P.FG) :
    ∃ a ∈ P, ∀ p ∈ P, ∃ c : 𝓞 E, ∃ p' ∈ P, p = c • a + (M : E) • p' := by
  obtain ⟨d, hd, hdP⟩ := clear_fg P hP
  have hd' : (d : E) ≠ 0 := by
    intro h; apply hd; exact_mod_cast h
  let J : Ideal (𝓞 E) :=
    { carrier := {q | ∃ p ∈ P, (q : E) = (d : E) * p}
      add_mem' := by
        rintro q q' ⟨p, hp, hq⟩ ⟨p', hp', hq'⟩
        exact ⟨p + p', add_mem hp hp', by push_cast; linear_combination hq + hq'⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c q ⟨p, hp, hq⟩
        refine ⟨c • p, Submodule.smul_mem _ c hp, ?_⟩
        show ((c * q : 𝓞 E) : E) = (d : E) * ((c : E) * p)
        push_cast
        linear_combination (c : E) * hq }
  obtain ⟨a', ⟨pa, hpa, ha'⟩, hgen⟩ := ideal_gen M hM J
  refine ⟨pa, hpa, fun p hp => ?_⟩
  obtain ⟨q, hq⟩ := hdP p hp
  obtain ⟨c, j', ⟨pj, hpj, hj'⟩, hcj⟩ := hgen q ⟨p, hp, hq.symm⟩
  refine ⟨c, pj, hpj, ?_⟩
  have h1 : (d : E) * p = (d : E) * ((c : E) * pa + (M : E) * pj) := by
    have h3 : (q : E) = (c : E) * (a' : E) + (M : E) * (j' : E) := by rw [hcj]; push_cast; ring
    linear_combination hq + h3 + (c : E) * ha' + (M : E) * hj'
  have h2 := mul_left_cancel₀ hd' h1
  rw [h2, Algebra.smul_def, smul_eq_mul]

def snoc0 (r : ℕ) : (Fin r → E) →ₗ[E] (Fin (r + 1) → E) where
  toFun y i := if h : (i : ℕ) < r then y ⟨i, h⟩ else 0
  map_add' y y' := by
    funext i
    by_cases h : (i : ℕ) < r <;> simp [h]
  map_smul' c y := by
    funext i
    by_cases h : (i : ℕ) < r <;> simp [h]

theorem snoc_zero_castSucc (r : ℕ) (y : Fin r → E) (j : Fin r) : snoc0 r y j.castSucc = y j := by
  simp [snoc0]

theorem snoc_zero_last (r : ℕ) (y : Fin r → E) : snoc0 r y (Fin.last r) = 0 := by
  simp [snoc0]

theorem snoc_zero_injective (r : ℕ) : Function.Injective (snoc0 (E := E) r) := by
  intro y y' h
  funext j
  have := congrFun h j.castSucc
  rwa [snoc_zero_castSucc, snoc_zero_castSucc] at this

theorem genMod_fg (M : ℕ) (hM : M ≠ 0) : ∀ (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → GenMod Λ M := by
  intro r
  induction r with
  | zero =>
    intro Λ _
    refine ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun x _ => ⟨0, 0, zero_mem _, ?_⟩⟩
    exact Subsingleton.elim _ _
  | succ r ih =>
    intro Λ hΛ
    haveI : IsNoetherian (𝓞 E) Λ := isNoetherian_of_fg_of_noetherian _ hΛ

    let Λ0 : Submodule (𝓞 E) (Fin r → E) := Λ.comap ((snoc0 r).restrictScalars (𝓞 E))
    let φ : Λ0 →ₗ[𝓞 E] Λ :=
      { toFun := fun x => ⟨snoc0 r (x : Fin r → E), x.2⟩
        map_add' := fun x y => by ext1; simp
        map_smul' := fun a x => by
          ext1
          show snoc0 r (a • (x : Fin r → E)) = a • snoc0 r (x : Fin r → E)
          rw [← algebraMap_smul E a (x : Fin r → E), map_smul, algebraMap_smul] }
    have hφ : Function.Injective φ := by
      intro x y h
      exact Subtype.ext (snoc_zero_injective r (congrArg Subtype.val h))
    haveI : IsNoetherian (𝓞 E) Λ0 := isNoetherian_of_injective φ hφ
    have hΛ0 : Λ0.FG := (Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤)
    obtain ⟨b0, hb0, hgen0⟩ := ih Λ0 hΛ0

    let P : Submodule (𝓞 E) E := Λ.map ((LinearMap.proj (Fin.last r) : (Fin (r + 1) → E) →ₗ[E] E).restrictScalars (𝓞 E))
    obtain ⟨a, ⟨xa, hxa, hxae⟩, hgenP⟩ := sub_gen M hM P (hΛ.map _)
    simp only [LinearMap.coe_restrictScalars, LinearMap.coe_proj, Function.eval] at hxae
    refine ⟨Fin.lastCases xa (fun j => snoc0 r (b0 j)), fun i => ?_, fun x hx => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.lastCases_last]; exact hxa
      · simp only [Fin.lastCases_castSucc]; exact hb0 j
    · obtain ⟨c, p', ⟨xj, hxj, hxje⟩, hce⟩ := hgenP (x (Fin.last r)) ⟨x, hx, rfl⟩
      simp only [LinearMap.coe_restrictScalars, LinearMap.coe_proj, Function.eval] at hxje
      set y : Fin (r + 1) → E := x - c • xa - (M : E) • xj with hy
      have hyΛ : y ∈ Λ := by
        refine sub_mem (sub_mem hx (Submodule.smul_mem _ c hxa)) ?_
        have : (M : E) • xj = ((M : ℕ) : 𝓞 E) • xj := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        rw [this]
        exact Submodule.smul_mem _ _ hxj
      have hylast : y (Fin.last r) = 0 := by
        rw [hy]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hce, hxae, hxje, Algebra.smul_def, Algebra.smul_def]
        simp
      set y0 : Fin r → E := fun j => y j.castSucc with hy0
      have hyy : snoc0 r y0 = y := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [snoc_zero_last, hylast]
        · rw [snoc_zero_castSucc]
      have hy0Λ : y0 ∈ Λ0 := by
        show snoc0 r y0 ∈ Λ
        rw [hyy]; exact hyΛ
      obtain ⟨c', z0, hz0, hz0e⟩ := hgen0 y0 hy0Λ
      refine ⟨Fin.lastCases c c', xj + snoc0 r z0, add_mem hxj hz0, ?_⟩
      have hx' : x = c • xa + (M : E) • xj + snoc0 r y0 := by
        rw [hyy, hy]; abel
      rw [hx', hz0e, Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, map_add, map_sum, smul_add]
      have hs : ∀ j, snoc0 r (c' j • b0 j) = c' j • snoc0 r (b0 j) := by
        intro j
        rw [← algebraMap_smul E (c' j) (b0 j), map_smul, algebraMap_smul]
      simp only [hs, map_smul]
      abel

theorem genMod (M : ℕ) (hM : M ≠ 0) {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Module.Finite (𝓞 E) Λ) :
    GenMod Λ M :=
  genMod_fg M hM r Λ (Module.Finite.iff_fg.1 hΛ)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

end
