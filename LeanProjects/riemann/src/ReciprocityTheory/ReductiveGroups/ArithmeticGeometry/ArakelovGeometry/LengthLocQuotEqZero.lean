import Mathlib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {R : Type*} [CommRing R]

theorem length_loc_add {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂] (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂)
    (hg : Function.Injective g) (hh : Function.Surjective h) (ex : Function.Exact g h)
    (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₁) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₀) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₂) := by
  exact Module.length_eq_add_of_exact _ _ (LocalizedModule.map_injective _ g hg)
    (LocalizedModule.map_surjective _ h hh) (LocalizedModule.map_exact _ g h ex)

theorem length_loc_step (I q : Ideal R) (f : R) (hq : ∀ g, g ∈ q ↔ g * f ∈ I) (P : Ideal R)
    [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) +
        Module.length (Localization.AtPrime P)
          (LocalizedModule P.primeCompl (R ⧸ (I ⊔ Ideal.span {f}))) := by
  let g : (R ⧸ q) →ₗ[R] (R ⧸ I) :=
    Submodule.mapQ q I (LinearMap.mulRight R f) (by intro x hx; exact (hq x).mp hx)
  let π : (R ⧸ I) →ₗ[R] (R ⧸ (I ⊔ Ideal.span {f})) :=
    Submodule.mapQ I (I ⊔ Ideal.span {f}) LinearMap.id (by intro x hx; exact Ideal.mem_sup_left hx)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk (p := I) (x * f) = 0 at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    change Submodule.Quotient.mk (p := q) x = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hq x).mpr hz
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex : Function.Exact g π := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (p := I ⊔ Ideal.span {f}) y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      refine ⟨Submodule.Quotient.mk r, ?_⟩
      change Submodule.Quotient.mk (p := I) (r * f) = Submodule.Quotient.mk (a + r * f)
      rw [Submodule.Quotient.eq]
      simpa using I.neg_mem ha
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (p := I) (x * f) = Submodule.Quotient.mk y at hx
      rw [Submodule.Quotient.eq] at hx
      have e : y = x * f - (x * f - y) := by ring
      rw [e]
      exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩))
        (Ideal.mem_sup_left hx)
  exact length_loc_add g π hg hπ hex P

theorem length_loc_quot_eq_zero (q P : Ideal R) [P.IsPrime] (h : ¬ q ≤ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) = 0 := by
  obtain ⟨s, hsq, hsP⟩ := SetLike.not_le_iff_exists.mp h
  rw [Module.length_eq_zero_iff]
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  induction z using LocalizedModule.induction_on with
  | h m t =>
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
    refine ⟨⟨s, hsP⟩, ?_⟩
    rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def]
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact q.mul_mem_right _ hsq

theorem length_loc_quot_self (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ P)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  have hne : ∀ (r : R) (t : P.primeCompl),
      LocalizedModule.mk (Ideal.Quotient.mk P r) t = 0 → r ∈ P := by
    intro r t h0
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    rw [smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, smul_zero, Ideal.Quotient.eq_zero_iff_mem] at hu
    rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hu with h1 | h1
    · exact absurd h1 u.2
    · rcases Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h1 with h2 | h2
      · exact absurd h2 t.2
      · exact h2
  constructor
  · refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk P 1) 1, 0, fun h0 => ?_⟩⟩
    exact ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr (hne 1 1 h0))
  · intro x hx y
    induction x using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      have hr : r ∈ P.primeCompl := fun hrP => hx (by
        rw [(Ideal.Quotient.eq_zero_iff_mem.mpr hrP), LocalizedModule.zero_mk])
      induction y using LocalizedModule.induction_on with
      | h m' t' =>
        obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
        refine ⟨Localization.mk (r' * t) (t' * ⟨r, hr⟩), ?_⟩
        rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, ← map_mul]
        congr 1
        ring

theorem length_loc_top (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ (⊤ : Ideal R))) = 0 := by
  apply length_loc_quot_eq_zero
  intro h
  exact ‹P.IsPrime›.ne_top (top_le_iff.mp h)

theorem length_loc_chain (P : Ideal R) [P.IsPrime] : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal R)
    (f : Fin N → R) (q : Fin N → Ideal R), F (Fin.last N) = ⊤ →
    (∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j, q j ≤ P → q j = P) →
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ F 0)) =
      ((∑ j : Fin N, if q j = P then 1 else 0 : ℕ) : ℕ∞)
  | 0, F, f, q, hlast, _, _ => by
    rw [show F 0 = F (Fin.last 0) from rfl, hlast, length_loc_top]
    simp
  | N + 1, F, f, q, hlast, hj, hmin => by
    have ih := length_loc_chain P N (fun j => F j.succ) (fun j => f j.succ) (fun j => q j.succ)
      (by simpa [Fin.succ_last] using hlast)
      (fun j => by
        have h := hj j.succ
        first | rwa [← Fin.succ_castSucc] at h | rwa [Fin.succ_castSucc] at h)
      (fun j => hmin j.succ)
    obtain ⟨h1, _, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h1 h3
    rw [length_loc_step (F 0) (q 0) (f 0) h3 P, ← h1, ih, Fin.sum_univ_succ]
    by_cases hq : q 0 = P
    · rw [if_pos hq, hq, length_loc_quot_self]
      push_cast
      ring
    · rw [if_neg hq, length_loc_quot_eq_zero _ _ (fun h => hq (hmin 0 h))]
      simp

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
