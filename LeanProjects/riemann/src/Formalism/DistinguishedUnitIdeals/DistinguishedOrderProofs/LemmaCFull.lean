import Mathlib
import Formalism.DistinguishedUnitIdeals.LemmaCFull
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LinExtEqZeroOfMemExt
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfNoDown
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ArcLiftOfLocalizationData

noncomputable section

namespace Formalism.ExponentWindows.E.LC

open PowerSeries

section Alg

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem lift_of_forms (ϖ : O) (hϖ : Irreducible ϖ) {r₁ r₂ : ℕ} (C₁ : Submodule O (Fin r₁ → O))
    (C₂ : Submodule O (Fin r₂ → O)) (hsat : Saturated ϖ C₂)
    (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) (hmap : CMap C₁ C₂ prL) (t : O)
    (hcore : ∀ e ∈ C₂, ∀ lam : (Fin r₂ → O) →ₗ[O] O, lam e = 1 → ∀ a : O,
      (∀ v ∈ C₁, lam (prL v) ∈ Ideal.span {a}) → a ∣ t) :
    ∀ v ∈ C₂, ∃ v₁ ∈ C₁, prL v₁ = t • v := by
  classical
  have hle : C₁.map prL ≤ C₂ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hmap v hv
  obtain ⟨o, n, snf⟩ := Submodule.smithNormalFormOfLE (Pi.basisFun O (Fin r₂)) (C₁.map prL) C₂ hle
  obtain ⟨f, hf0, hf1⟩ := exists_proj_of_saturated ϖ hϖ C₂ hsat
  let P : (Fin r₂ → O) →ₗ[O] C₂ := (LinearMap.id - f).codRestrict C₂ (fun v => hf1 v)
  have hP : ∀ (v : Fin r₂ → O) (hv : v ∈ C₂), P v = ⟨v, hv⟩ := by
    intro v hv
    apply Subtype.ext
    simp [P, hf0 v hv]
  have hmem : ∀ (v : Fin r₁ → O) (hv : v ∈ C₁),
      (⟨prL v, hmap v hv⟩ : C₂) ∈ (C₁.map prL).comap C₂.subtype := fun v hv => ⟨v, hv, rfl⟩
  have hbasis : ∀ i : Fin o, t • snf.bM i ∈ (C₁.map prL).comap C₂.subtype := by
    intro i
    have h1 : (snf.bM.coord i ∘ₗ P) (snf.bM i : Fin r₂ → O) = 1 := by
      rw [LinearMap.comp_apply, hP _ (snf.bM i).2]
      simp
    by_cases hi : i ∈ Set.range snf.f
    · obtain ⟨j, rfl⟩ := hi
      obtain ⟨q, hq⟩ := hcore _ (snf.bM (snf.f j)).2 _ h1 (snf.a j) (by
        intro v hv
        rw [LinearMap.comp_apply, hP _ (hmap v hv)]
        have h2 := snf.repr_apply_embedding_eq_repr_smul ⟨_, hmem v hv⟩ (i := j)
        rw [Module.Basis.coord_apply, h2, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact Ideal.mem_span_singleton.2 ⟨_, rfl⟩)
      have h3 : t • snf.bM (snf.f j) = q • (snf.bN j : C₂) := by
        rw [snf.snf, smul_smul, hq, mul_comm]
      rw [h3]
      exact Submodule.smul_mem _ _ (snf.bN j).2
    · have h0 := hcore _ (snf.bM i).2 _ h1 0 (by
        intro v hv
        rw [LinearMap.comp_apply, hP _ (hmap v hv)]
        have h2 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem v hv⟩ hi
        rw [Module.Basis.coord_apply, h2]
        exact zero_mem _)
      rw [zero_dvd_iff] at h0
      rw [h0, zero_smul]
      exact zero_mem _
  intro v hv
  have hall : t • (⟨v, hv⟩ : C₂) ∈ (C₁.map prL).comap C₂.subtype := by
    rw [← snf.bM.sum_repr ⟨v, hv⟩, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (hbasis i)
  obtain ⟨v₁, hv₁, h⟩ := hall
  exact ⟨v₁, hv₁, by simpa using h⟩

theorem lam_dvd (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (K : ℕ → ℕ) (Y : PowerSeries O) (h : ∀ s < ell, p s ^ K s ∣ Y) :
    abelian₂ p K ell ∣ Y := by
  unfold abelian₂
  apply prod_dvd_of_coprimeRat ϖ (Finset.range ell) (fun s => p s ^ K s)
  · intro s hs
    exact isSat_pow_of_unitDist ϖ hϖ _ _ (hp.1 s (Finset.mem_range.1 hs)) _
  · intro s hs t ht hne
    exact coprimeRat₂_pow_pow ϖ _ _ (hp.2 s (Finset.mem_range.1 hs) t (Finset.mem_range.1 ht) hne) _ _
  · intro s hs
    exact h s (Finset.mem_range.1 hs)

theorem lam_isSat (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (K : ℕ → ℕ) : IsSat ϖ (abelian₂ p K ell) := by
  unfold abelian₂
  apply isSat_prod ϖ (Finset.range ell) (fun s => p s ^ K s)
  intro s hs
  exact isSat_pow_of_unitDist ϖ hϖ _ _ (hp.1 s (Finset.mem_range.1 hs)) _

theorem lam_ne_zero (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (K : ℕ → ℕ) : abelian₂ p K ell ≠ 0 := by
  unfold abelian₂
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  exact pow_ne_zero _ (ne_zero_of_unitDist ϖ hϖ _ _ (hp.1 s (Finset.mem_range.1 hs)))

theorem lamLess_eq (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s₁ b : ℕ) (hs : s₁ < ell) :
    LamLess p H ell s₁ b = abelian₂ p (Function.update H s₁ (H s₁ - b)) ell := by
  rw [lam_eq_pow_mul p _ ell s₁ hs, LamLess, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]

theorem lam_eq_lamLess (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s₁ b : ℕ) (hs : s₁ < ell)
    (hb : b ≤ H s₁) : abelian₂ p H ell = LamLess p H ell s₁ b * p s₁ ^ b := by
  rw [lam_eq_pow_mul p H ell s₁ hs, LamLess]
  have h1 : p s₁ ^ H s₁ = p s₁ ^ (H s₁ - b) * p s₁ ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hb]
  rw [h1]
  ring

variable {r : ℕ}

theorem levelCond_dvd_sub (ϖ : O) (hϖ : Irreducible ϖ) {d : ℕ} {p : PowerSeries O}
    (hp : UnitDist ϖ d p) (H b : ℕ) (k : Kind) (V : Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (h : LevelCond ϖ p H b k V y) (g : (Fin r → O) →ₗ[O] O) :
    p ^ (H - b) ∣ linExt g y := by
  have hd : p ^ (H - b) ∣ p ^ H := pow_dvd_pow p (Nat.sub_le H b)
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_mul_of_dvd_left hd _
  | up =>
    obtain ⟨N, c, z, _, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hd _)
  | down =>
    obtain ⟨N, c, z, _, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_add (dvd_mul_of_dvd_left hd _)
      (dvd_mul_of_dvd_left (hd.trans (pow_dvd_pow p (Nat.le_add_right H b))) _)

theorem levelCond_dvd (ϖ : O) (hϖ : Irreducible ϖ) {d : ℕ} {p : PowerSeries O}
    (hp : UnitDist ϖ d p) (H b : ℕ) (k : Kind) (V : Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (h : LevelCond ϖ p H b k V y) (g : (Fin r → O) →ₗ[O] O)
    (hg : k = Kind.up → ∀ v ∈ V, g v = 0) : p ^ H ∣ linExt g y := by
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_mul_right _ _
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      linExt_eq_zero_of_mem_ext g V (hg rfl) c hc, mul_zero, zero_add] at h1
    rw [h1]
    exact dvd_mul_right _ _
  | down =>
    obtain ⟨N, c, z, _, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (pow_dvd_pow p (Nat.le_add_right H b)) _)

theorem NN_dvd_lamLess (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (H b : ℕ → ℕ) (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (hy : NN ϖ p H b kind V ell y) (s₁ : ℕ) (hs₁ : s₁ < ell)
    (honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up) (g : (Fin r → O) →ₗ[O] O) :
    LamLess p H ell s₁ (b s₁) ∣ linExt g y := by
  rw [lamLess_eq p H ell s₁ (b s₁) hs₁]
  apply lam_dvd ϖ hϖ hp
  intro s hs
  by_cases h1 : s = s₁
  · subst h1
    rw [Function.update_self]
    exact levelCond_dvd_sub ϖ hϖ (hp.1 s hs) _ _ _ _ y (hy s hs) g
  · rw [Function.update_of_ne h1]
    exact levelCond_dvd ϖ hϖ (hp.1 s hs) _ _ _ _ y (hy s hs) g
      (fun hk => absurd hk (honly s hs h1))

theorem NN_dvd_lam (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (H b : ℕ → ℕ) (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (hy : NN ϖ p H b kind V ell y) (s₁ : ℕ)
    (honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up) (g : (Fin r → O) →ₗ[O] O)
    (hg : ∀ v ∈ V s₁, g v = 0) : abelian₂ p H ell ∣ linExt g y := by
  apply lam_dvd ϖ hϖ hp
  intro s hs
  refine levelCond_dvd ϖ hϖ (hp.1 s hs) _ _ _ _ y (hy s hs) g (fun hk => ?_)
  by_cases h1 : s = s₁
  · subst h1
    exact hg
  · exact absurd hk (honly s hs h1)

theorem NN_form (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (H b : ℕ → ℕ) (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (hy : NN ϖ p H b kind V ell y) (s₁ : ℕ) (hs₁ : s₁ < ell)
    (honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up) (hsat : Saturated ϖ (V s₁))
    (μ : (Fin r → O) →ₗ[O] O) (a : O) (ha : ∀ v ∈ V s₁, μ v ∈ Ideal.span {a}) :
    ∃ Y' Y'' : PowerSeries O,
      linExt μ y = LamLess p H ell s₁ (b s₁) * (C a * Y') + abelian₂ p H ell * Y'' := by
  obtain ⟨f, hf0, hf1⟩ := exists_proj_of_saturated ϖ hϖ (V s₁) hsat
  obtain ⟨Y'', hY''⟩ := NN_dvd_lam ϖ hϖ hp H b kind V y hy s₁ honly (μ ∘ₗ f)
    (fun v hv => by rw [LinearMap.comp_apply, hf0 v hv, map_zero])
  have hG := NN_dvd_lamLess ϖ hϖ hp H b kind V y hy s₁ hs₁ honly (μ - μ ∘ₗ f)
  have hCa : C a ∣ linExt (μ - μ ∘ₗ f) y := by
    rw [linExt_apply]
    refine Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right ?_ _
    have h1 : (μ - μ ∘ₗ f) (Pi.single i 1) = μ (Pi.single i 1 - f (Pi.single i 1)) := by
      rw [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    rw [h1]
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (ha _ (hf1 (Pi.single i 1)))
    rw [hq, map_mul]
    exact dvd_mul_right _ _
  obtain ⟨Y₀, hY₀⟩ := hCa
  have hsplit : linExt μ y = linExt (μ - μ ∘ₗ f) y + linExt (μ ∘ₗ f) y := by
    rw [linExt_sub]
    ring
  by_cases ha0 : a = 0
  · refine ⟨0, Y'', ?_⟩
    rw [hsplit, hY₀, hY'', ha0]
    simp
  · obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hdvd : LamLess p H ell s₁ (b s₁) ∣ Y₀ := by
      have hS : IsSat ϖ (LamLess p H ell s₁ (b s₁)) := by
        rw [lamLess_eq p H ell s₁ (b s₁) hs₁]
        exact lam_isSat ϖ hϖ hp _
      have h2 : LamLess p H ell s₁ (b s₁) ∣ C (ϖ ^ k) * (C (u : O) * Y₀) := by
        have h3 : C (ϖ ^ k) * (C (u : O) * Y₀) = C a * Y₀ := by
          rw [hu, map_mul]
          ring
        rw [h3, ← hY₀]
        exact hG
      have h4 := hS k _ h2
      have hunit : IsUnit (C (u : O) : PowerSeries O) := u.isUnit.map C
      exact (hunit.dvd_mul_left).1 h4
    obtain ⟨Y', hY'⟩ := hdvd
    refine ⟨Y', Y'', ?_⟩
    rw [hsplit, hY₀, hY'', hY']
    ring

theorem linExt_extL {r₁ r₂ : ℕ} (lam : (Fin r₂ → O) →ₗ[O] O)
    (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) (y : Fin r₁ → PowerSeries O) :
    linExt lam (extL prL y) = linExt (lam ∘ₗ prL) y := by
  classical
  have hy : y = ∑ i, y i • cst (Pi.single i (1 : O)) := by
    funext j
    simp [cst, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  rw [map_sum, map_sum, linExt_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, CL.extL_cst, linExt_cst]
  rfl

theorem lattice_condition_up_down_pair (ϖ : O) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (V : ℕ → Submodule O (Fin r → O)) (ell s₀ s₁ : ℕ) (hk1 : kind s₁ = Kind.up)
    (hk0 : kind s₀ = Kind.down) (hthin : ∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin)
    (e : Fin r → O) (he : e ∈ V s₁) :
    NN ϖ p H b kind V ell ((p s₀ ^ b s₀ * LamLess p H ell s₁ (b s₁)) • cst e) := by
  intro s hs
  by_cases h1 : s = s₁
  · subst h1
    rw [hk1]
    refine ⟨0, (p s₀ ^ b s₀ * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t) • cst e, 0,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, he, rfl⟩), ?_⟩
    simp only [pow_zero, map_one, smul_zero, add_zero, smul_smul, LamLess]
    congr 1
    ring
  · have hd : p s ^ H s ∣ LamLess p H ell s₁ (b s₁) :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t => p t ^ H t)
        (Finset.mem_erase.2 ⟨h1, Finset.mem_range.2 hs⟩)) _
    obtain ⟨q, hq⟩ := hd
    by_cases h0 : s = s₀
    · subst h0
      rw [hk0]
      refine ⟨0, 0, q • cst e, zero_mem _, ?_⟩
      rw [hq]
      simp only [pow_zero, map_one, smul_zero, zero_add, smul_smul]
      congr 1
      rw [pow_add]
      ring
    · rw [hthin s hs h0 h1]
      refine ⟨0, (p s₀ ^ b s₀ * q) • cst e, ?_⟩
      rw [hq]
      simp only [pow_zero, map_one, smul_smul]
      congr 1
      ring

end Alg

section Levels

variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂} {h : LatHom L₁ L₂} {c : ZMod n} {ell : ℕ}
  {Λ : PowerSeries O} {r₁ r₂ : ℕ} {S₁ : LevelData L₁ c ell Λ r₁} {S₂ : LevelData L₂ c ell Λ r₂}

theorem levels (m : LevelMap h S₁ S₂) (ϖ : O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O)) (g sig rr : ℕ)
    (hRD₁ : S₁.RD g) (hRD₂ : S₂.RD g) (hPa₁ : S₁.Partner sig) (hPa₂ : S₂.Partner sig)
    (hP3₁ : S₁.P3) (hP3₂ : S₂.P3) (hP4a₁ : S₁.DivisibleIff g) (hP4a₂ : S₂.DivisibleIff g)
    (hBr₁ : S₁.Bridge ϖ H b kind U₁) (hBr₂ : S₂.Bridge ϖ H b kind U₂) (hFl : S₂.FlReg ϖ H)
    (hMap : m.MapFl) (hP4d : h.LiftsDivisible c ell g rr)
    (y₂ : Fin r₂ → PowerSeries O) (hy₂ : NN ϖ B.p H b kind U₂ ell y₂) :
    ∃ y₁ : Fin r₁ → PowerSeries O, NN ϖ B.p H b kind U₁ ell (B.Th ell g ^ 2 • y₁) ∧
      ∀ s < ell, ∃ (N : ℕ) (z : Fin r₂ → PowerSeries O),
        C (ϖ ^ N) • (extL m.prL y₁ - C ((B.ℓ : O) ^ (2 * sig + rr)) • y₂) = B.p s ^ H s • z := by
  have hb₂ := (hBr₂.1 y₂).2 hy₂

  obtain ⟨w, hw⟩ := hPa₂.2 y₂
  have hw1 : ∀ s < ell, S₂.loc s w ∈ dv (B.p s ^ g) (S₂.Nl s) := by
    intro s hs
    have h1 : B.lc ^ sig • S₂.locL s y₂ ∈ dv (B.p s ^ g) (S₂.Nl s) :=
      Submodule.smul_mem _ _ ((hRD₂ s hs).1 (hb₂ s hs))
    have h2 : S₂.loc s w - B.lc ^ sig • S₂.locL s y₂ ∈ dv (B.p s ^ g) (S₂.Nl s) :=
      IteratedPhiHomomorphisms.le_dv _ _ ((hP3₂ s hs).1 (hw s hs))
    have h3 := Submodule.add_mem _ h2 h1
    rwa [sub_add_cancel] at h3
  have hwΘ : (w : V₂) ∈ dv (B.Th ell g) (L₂.N c) := (hP4a₂.2 w).2 hw1

  obtain ⟨x₁, hx₁, hfx⟩ := hP4d _ hwΘ
  have hx₁W : x₁ ∈ L₁.W c ell Λ := hP4a₁.1 hx₁
  have hx₁l := (hP4a₁.2 ⟨x₁, hx₁W⟩).1 hx₁

  obtain ⟨y₁, hy₁⟩ := hPa₁.1 ⟨x₁, hx₁W⟩
  refine ⟨y₁, ?_, ?_⟩
  · apply (hBr₁.1 _).1
    intro s hs
    have h1 : S₁.locL s y₁ ∈ dv (B.p s ^ g) (S₁.Nl s) := by
      have a1 := IteratedPhiHomomorphisms.le_dv (B.p s ^ g) _ ((hP3₁ s hs).1 (hy₁ s hs))
      have a2 := Submodule.smul_mem _ (B.lc ^ sig) (hx₁l s hs)
      have a3 := Submodule.add_mem _ a1 a2
      rwa [sub_add_cancel] at a3
    have h2 : B.p s ^ g • (B.p s ^ g • S₁.locL s y₁) ∈ S₁.Nb s :=
      IteratedPhiHomomorphisms.mem_dv.1 ((hRD₁ s hs).2 (IteratedPhiHomomorphisms.mem_dv.1 h1))
    have hΘ : B.Th ell g = B.p s ^ g * ∏ t ∈ (Finset.range ell).erase s, B.p t ^ g :=
      (Finset.mul_prod_erase _ (fun t => B.p t ^ g) (Finset.mem_range.2 hs)).symm
    have h3 : (B.p s ^ g * ∏ t ∈ (Finset.range ell).erase s, B.p t ^ g) ^ 2 • S₁.locL s y₁ =
        (∏ t ∈ (Finset.range ell).erase s, B.p t ^ g) ^ 2 •
          (B.p s ^ g • (B.p s ^ g • S₁.locL s y₁)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [map_smul, hΘ, h3]
    exact Submodule.smul_mem _ _ h2

  · intro s hs
    apply hFl s hs
    have hfW : h.f x₁ ∈ L₂.W c ell Λ := by
      rw [hfx]
      exact Submodule.smul_mem _ _ w.2
    have e1 := m.loc_comm s hs x₁ hx₁W hfW
    have e2 : S₂.loc s ⟨h.f x₁, hfW⟩ = B.lc ^ rr • S₂.loc s w := by
      rw [← map_smul]
      congr 1
      exact Subtype.ext hfx
    have a1 := hMap s hs _ (hy₁ s hs)
    rw [map_sub, map_smul, e1, e2, m.locL_comm s hs] at a1
    have a2 := Submodule.smul_mem _ (B.lc ^ (sig + rr)) (hw s hs)
    have a3 := Submodule.add_mem _ a1 a2
    rw [map_sub, map_smul]
    convert a3 using 1
    have hexp : 2 * sig + rr = sig + rr + sig := by ring
    rw [← IteratedPhiHomomorphisms.lc_pow, smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add, hexp]
    abel

end Levels

section Core

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
  [Module (PowerSeries O) V₂] {L₁ : Lat B n V₁} {L₂ : Lat B n V₂} {h : LatHom L₁ L₂} {c : ZMod n}
  {ell : ℕ} {Λ : PowerSeries O} {r₁ r₂ : ℕ} {S₁ : LevelData L₁ c ell Λ r₁}
  {S₂ : LevelData L₂ c ell Λ r₂}

theorem core (ϖ : O) (hϖ : Irreducible ϖ) (m : LevelMap h S₁ S₂) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O)) (g sig rr : ℕ)
    (hset : LevelModelSetting ϖ B.ℓ ell B.p H b kind U₁ U₂)
    (hRD₁ : S₁.RD g) (hRD₂ : S₂.RD g) (hPa₁ : S₁.Partner sig) (hPa₂ : S₂.Partner sig)
    (hP3₁ : S₁.P3) (hP3₂ : S₂.P3) (hP4a₁ : S₁.DivisibleIff g) (hP4a₂ : S₂.DivisibleIff g)
    (hBr₁ : S₁.Bridge ϖ H b kind U₁) (hBr₂ : S₂.Bridge ϖ H b kind U₂) (hFl : S₂.FlReg ϖ H)
    (hMap : m.MapFl) (hP4d : h.LiftsDivisible c ell g rr)
    (s₀ s₁ : ℕ) (hs₁ : s₁ < ell) (hk1 : kind s₁ = Kind.up)
    (hk0 : kind s₀ = Kind.down) (hthin : ∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin)
    (e : Fin r₂ → O) (he : e ∈ U₂ s₁) (lam : (Fin r₂ → O) →ₗ[O] O) (a : O)
    (ha : ∀ v ∈ U₁ s₁, lam (m.prL v) ∈ Ideal.span {a}) :
    C (lam e) * (C ((B.ℓ : O) ^ (2 * sig + rr)) * B.Th ell g ^ 2 * B.p s₀ ^ b s₀) ∈
      Ideal.span {C a, B.p s₁ ^ b s₁} := by
  obtain ⟨_, hp, hsat₁, _, hbH⟩ := hset
  have honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up := by
    intro s hs h1 hk
    by_cases h0 : s = s₀
    · rw [h0, hk0] at hk
      exact Kind.noConfusion hk
    · rw [hthin s hs h0 h1] at hk
      exact Kind.noConfusion hk
  obtain ⟨y₁, hNN₁, hδ⟩ := levels m ϖ H b kind U₁ U₂ g sig rr hRD₁ hRD₂ hPa₁ hPa₂ hP3₁ hP3₂ hP4a₁
    hP4a₂ hBr₁ hBr₂ hFl hMap hP4d _ (lattice_condition_up_down_pair ϖ B.p H b kind U₂ ell s₀ s₁ hk1 hk0 hthin e he)
  have hd : abelian₂ B.p H ell ∣ linExt lam (extL m.prL y₁ - C ((B.ℓ : O) ^ (2 * sig + rr)) •
      ((B.p s₀ ^ b s₀ * LamLess B.p H ell s₁ (b s₁)) • cst e)) := by
    apply lam_dvd ϖ hϖ hp
    intro s hs
    obtain ⟨N, z, hz⟩ := hδ s hs
    apply isSat_pow_of_unitDist ϖ hϖ _ _ (hp.1 s hs) _ N
    have h1 := congrArg (linExt lam) hz
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_mul_right _ _
  obtain ⟨d', hd'⟩ := hd
  obtain ⟨Y', Y'', hY⟩ := NN_form ϖ hϖ hp H b kind U₁ _ hNN₁ s₁ hs₁ honly (hsat₁ s₁ hs₁)
    (lam ∘ₗ m.prL) a ha
  rw [map_smul, ← linExt_extL, smul_eq_mul] at hY
  rw [map_sub, map_smul, map_smul, linExt_cst, smul_eq_mul, smul_eq_mul] at hd'
  have hΛ := lam_eq_lamLess B.p H ell s₁ (b s₁) hs₁ (hbH s₁ hs₁ hk1)
  have hG : LamLess B.p H ell s₁ (b s₁) ≠ 0 := by
    rw [lamLess_eq B.p H ell s₁ (b s₁) hs₁]
    exact lam_ne_zero ϖ hϖ hp _
  rw [hΛ] at hY hd'
  have key : LamLess B.p H ell s₁ (b s₁) *
      (C (lam e) * (C ((B.ℓ : O) ^ (2 * sig + rr)) * B.Th ell g ^ 2 * B.p s₀ ^ b s₀)) =
      LamLess B.p H ell s₁ (b s₁) *
        (Y' * C a + (Y'' - B.Th ell g ^ 2 * d') * B.p s₁ ^ b s₁) := by
    linear_combination hY - B.Th ell g ^ 2 * hd'
  rw [Ideal.mem_span_pair]
  exact ⟨Y', Y'' - B.Th ell g ^ 2 * d', (mul_left_cancel₀ hG key).symm⟩

end Core

theorem shape_ext {O : Type} [CommRing O] [Nontrivial O] (B : Base O) (ell : ℕ) (hℓ : 2 ≤ B.ℓ)
    (hsh : B.PShape ell) :
    ∃ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O), (∀ s, (E s).Monic) ∧
      (∀ s, (E s).natDegree = B.ℓ ^ s) ∧ (∀ s, ∀ i < B.ℓ ^ s, (B.ℓ : O) ∣ (E s).coeff i) ∧
      (∀ s, Associated ((E s).coeff 0) (B.ℓ : O)) ∧ (∀ s, IsUnit (u s)) ∧
      ∀ s < ell, B.p s = u s * (E s : PowerSeries O) := by
  have hall : ∀ s, ∃ (E : Polynomial O) (u : PowerSeries O), E.Monic ∧ E.natDegree = B.ℓ ^ s ∧
      (∀ i < B.ℓ ^ s, (B.ℓ : O) ∣ E.coeff i) ∧ Associated (E.coeff 0) (B.ℓ : O) ∧ IsUnit u ∧
      (s < ell → B.p s = u * (E : PowerSeries O)) := by
    intro s
    by_cases hs : s < ell
    · obtain ⟨E, u, h1, h2, h3, h4, h5, h6⟩ := hsh s hs
      exact ⟨E, u, h1, h2, h3, h4, h5, fun _ => h6⟩
    · have hpos : B.ℓ ^ s ≠ 0 := pow_ne_zero _ (by omega)
      refine ⟨Polynomial.X ^ (B.ℓ ^ s) + Polynomial.C (B.ℓ : O), 1,
        Polynomial.monic_X_pow_add_C _ hpos, Polynomial.natDegree_X_pow_add_C, ?_, ?_, isUnit_one,
        fun h => absurd h hs⟩
      · intro i hi
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add,
          Polynomial.coeff_C]
        split_ifs
        · exact dvd_rfl
        · exact dvd_zero _
      · rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (fun h => hpos h.symm), zero_add,
          Polynomial.coeff_C_zero]
  choose E u h1 h2 h3 h4 h5 h6 using hall
  exact ⟨E, u, h1, h2, h3, h4, h5, h6⟩

end Formalism.ExponentWindows.E.LC

namespace Formalism.ExponentWindows.E

open PowerSeries

theorem lemma_C_full_holds : LemmaCFull := by
  intro hVal O _ _ _ ϖ hϖ B e he hℓe n V₁ V₂ _ _ _ _ L₁ L₂ h c ell Λ r₁ r₂ S₁ S₂ m H b kind U₁ U₂
    g sig rr a₀ _ hsh hset hRD₁ hRD₂ hPa₁ hPa₂ hP3₁ hP3₂ hP4a₁ hP4a₂ hBr₁ hBr₂ hFl hMap hP4d
    s₀ s₁ h01 hs₁ hk1 hk0 hthin hC hA hB1 hB0
  have hs₀ : s₀ < ell := h01.trans hs₁
  obtain ⟨E, u, hE1, hE2, hE3, hE4, hu, hpE⟩ := LC.shape_ext B ell hset.1 hsh
  refine LC.lift_of_forms ϖ hϖ (U₁ s₁) (U₂ s₁) (hset.2.2.2.1 s₁ hs₁) m.prL hC _ ?_
  intro v hv lam hlam a ha
  have hc := LC.core ϖ hϖ m H b kind U₁ U₂ g sig rr hset hRD₁ hRD₂ hPa₁ hPa₂ hP3₁ hP3₂ hP4a₁ hP4a₂
    hBr₁ hBr₂ hFl hMap hP4d s₀ s₁ hs₁ hk1 hk0 hthin v hv lam a ha
  rw [hlam, map_one, one_mul] at hc
  have hTh : B.Th ell g = ∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g := by
    unfold Base.Th
    apply Finset.prod_congr rfl
    intro s hs
    rw [hpE s (Finset.mem_range.1 hs)]
  rw [hTh, hpE s₀ hs₀, hpE s₁ hs₁] at hc
  have hA' : (((2 * sig + rr : ℕ) : ℝ) + 2 * g * ell) ≤ a₀ := by exact_mod_cast hA
  have hB1' : 2 * (a₀ : ℝ) < b s₁ := by exact_mod_cast hB1
  have hbound : ∀ k : ℕ, C ((B.ℓ : O) ^ (2 * sig + rr)) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b s₀ ∈
      Ideal.span {C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b s₁} → k ≤ e * (2 * a₀) := by
    intro k hk
    have h2 := (hVal O ϖ hϖ B.ℓ e hset.1 he hℓe E u hE1 hE2 hE3 hE4 hu ell g (2 * sig + rr) (b s₀)
      (b s₁) s₀ s₁ k h01 (by linarith) hB0 hk).2
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have h3 : (k : ℝ) ≤ ((e * (2 * a₀) : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h3
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hc
  by_cases ha0 : a = 0
  · exfalso
    have h1 := hbound (e * (2 * a₀) + 1) (Ideal.mem_span_pair.2 ⟨0, y, by
      rw [← hxy, ha0]
      simp⟩)
    omega
  · obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have h1 := hbound k (Ideal.mem_span_pair.2 ⟨x * C (w : O), y, by
      rw [← hxy, hw, map_mul]
      ring⟩)
    have h2 : ϖ ^ k ∣ (ϖ ^ e) ^ (2 * a₀) := by
      rw [← pow_mul]
      exact pow_dvd_pow _ h1
    rw [hw]
    exact Units.mul_left_dvd.2 (h2.trans (hℓe.pow_pow (n := 2 * a₀)).symm.dvd)

end Formalism.ExponentWindows.E
