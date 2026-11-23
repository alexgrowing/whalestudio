import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.IsUnimodularCliffordLatticeStabilizer

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}
  {c t s : K} {ε : Oˣ} {β : Etau K τ}

theorem finrank_V : Module.finrank K (K × Etau K τ) = 3 := by
  rw [Module.finrank_prod, Module.finrank_self]
  exact congrArg (1 + ·) (QuadraticAlgebra.finrank_eq_two (-1 : K) τ)

theorem Uni.frame (L : IsLoc O Δ) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ h ∈ S, ∃ η : Oˣ, Bf τ c t e e = 0 ∧ Bf τ c t f f = 0 ∧ Bf τ c t e f = 1 ∧ Bf τ c t e h = 0 ∧ Bf τ c t f h = 0 ∧
      Bf τ c t h h = algebraMap O K η ∧ ∀ v ∈ S, ∃ a b d : O, v = a • e + b • f + d • h := by
  obtain ⟨s, hs⟩ := hS.fg
  have hd : ∀ y : K × Etau K τ, y ∈ Submodule.span O (s : Set (K × Etau K τ)) ↔
      ∀ x ∈ Submodule.span O (s : Set (K × Etau K τ)), Bf τ c t x y ∈ (algebraMap O K).range := by
    intro y
    have := hS.dual y
    rw [hs] at this
    exact this
  obtain ⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_frame L finrank_V (Bf_symm c t) (Submodule.fg_span (Finset.finite_toSet s)) hd
  rw [hs]
  exact ⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩

theorem exists_lat (L : IsLoc O Δ) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2)
    (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    ∃ Λ, IsLat O τ Λ ∧ S = S0 s β Λ := by
  classical
  obtain ⟨e, heS, f, hfS, h, hhS, η, hee, hff, hef, heh, hfh, hhh, hspan⟩ := Uni.frame L hS
  haveI := L.frac
  have h2O : IsUnit (2 : O) := L.two
  have h2 : (2 : K) ≠ 0 := by
    have := (h2O.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  set E : K := algebraMap O K ε with hE
  have hE0 : E ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hinvE : algebraMap O K ↑ε⁻¹ * E = 1 := by
    rw [hE, ← map_mul, Units.inv_mul, map_one]
  have anti : ∀ v w y, E • (psi s β v (psi s β w y) + psi s β w (psi s β v y))
      = (2 * Bf τ c t v w) • y := fun v w y => psi_anti hc hβ v w y
  have sq0 : ∀ v, Bf τ c t v v = 0 → ∀ y, psi s β v (psi s β v y) = 0 := by
    intro v hv y
    have := anti v v y
    rw [hv, mul_zero, zero_smul, ← two_smul K, smul_smul, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 (mul_ne_zero hE0 h2)
    · exact h0
  have orth : ∀ v w, Bf τ c t v w = 0 → ∀ y, psi s β v (psi s β w y) = -psi s β w (psi s β v y) := by
    intro v w hvw y
    have := anti v w y
    rw [hvw, mul_zero, zero_smul, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 hE0
    · exact eq_neg_of_add_eq_zero_left h0
  set κ : K := algebraMap O K (↑ε⁻¹ * 2) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ, map_mul, map_ofNat]
    exact mul_ne_zero (ε⁻¹.isUnit.map (algebraMap O K)).ne_zero h2
  have ef : ∀ y, psi s β e (psi s β f y) + psi s β f (psi s β e y) = κ • y := by
    intro y
    have := anti e f y
    rw [hef, mul_one] at this
    calc _ = (algebraMap O K ↑ε⁻¹ * E) • (psi s β e (psi s β f y) + psi s β f (psi s β e y)) := by
          rw [hinvE, one_smul]
      _ = κ • y := by rw [mul_smul, this, smul_smul, hκ, map_mul, map_ofNat]
  obtain ⟨w0, hw0⟩ : ∃ w0, psi s β e w0 ≠ 0 := by
    by_contra H
    push_neg at H
    have := ef 1
    rw [H (psi s β f 1), H 1, map_zero, add_zero, eq_comm, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact hκ0 h0
    · exact one_ne_zero h0
  obtain ⟨y1, hy1d⟩ : ∃ y1, y1 = psi s β e w0 := ⟨_, rfl⟩
  obtain ⟨y2, hy2d⟩ : ∃ y2, y2 = psi s β f y1 := ⟨_, rfl⟩
  have hy1 : y1 ≠ 0 := hy1d ▸ hw0
  have pe1 : psi s β e y1 = 0 := by
    rw [hy1d]
    exact sq0 e hee w0
  have pf2 : psi s β f y2 = 0 := by
    rw [hy2d]
    exact sq0 f hff y1
  have pf1 : psi s β f y1 = y2 := hy2d.symm
  have pe2 : psi s β e y2 = κ • y1 := by
    have := ef y1
    rw [pe1, map_zero, add_zero, ← hy2d] at this
    exact this
  have hind : (y2 * star y1).im ≠ 0 := by
    intro H0
    have H1 : y2.im * y1.re = y2.re * y1.im := by
      simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] at H0
      linear_combination H0
    obtain ⟨l, hl⟩ : ∃ l : K, y2 = l • y1 := by
      by_cases hr : y1.re = 0
      · have hi : y1.im ≠ 0 := fun hi => hy1 (QuadraticAlgebra.ext hr hi)
        refine ⟨y2.im / y1.im, ?_⟩
        rw [hr, mul_zero] at H1
        ext
        · simp only [QuadraticAlgebra.re_smul, smul_eq_mul, hr, mul_zero]
          rcases mul_eq_zero.mp H1.symm with h0 | h0
          · exact h0
          · exact absurd h0 hi
        · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
          field_simp
      · refine ⟨y2.re / y1.re, ?_⟩
        ext
        · simp only [QuadraticAlgebra.re_smul, smul_eq_mul]
          field_simp
        · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
          field_simp
          linear_combination H1
    have := pe2
    rw [hl, map_smul, pe1, smul_zero, eq_comm, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact hκ0 h0
    · exact hy1 h0
  have hhe : Bf τ c t h e = 0 := by rw [Bf_symm, heh]
  have hhf : Bf τ c t h f = 0 := by rw [Bf_symm, hfh]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, psi s β h y1 = μ • y1 := by
    obtain ⟨α, γ, hz⟩ : ∃ α γ : K, psi s β h y1 = α • y1 + γ • y2 := ⟨_, _, coord hind _⟩
    have hpz : psi s β e (psi s β h y1) = 0 := by
      rw [orth e h heh, pe1, map_zero, neg_zero]
    rw [hz, map_add, map_smul, map_smul, pe1, pe2, smul_zero, zero_add, smul_smul, smul_eq_zero] at hpz
    rcases hpz with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact ⟨α, by rw [hz, h1, zero_smul, add_zero]⟩
      · exact absurd h1 hκ0
    · exact absurd h0 hy1
  have ph2 : psi s β h y2 = -(μ • y2) := by
    rw [hy2d, orth h f hhf, hμ, map_smul]
  have hμ2 : E * (μ * μ) = algebraMap O K η := by
    have := anti h h y1
    rw [hhh, hμ, map_smul, hμ, smul_smul, ← two_smul K, smul_smul, smul_smul, ← sub_eq_zero, ← sub_smul,
      smul_eq_zero] at this
    rcases this with h0 | h0
    · have h0' : 2 * (E * (μ * μ) - algebraMap O K η) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp h0' with h1 | h1
      · exact absurd h1 h2
      · exact sub_eq_zero.mp h1
    · exact absurd h0 hy1
  obtain ⟨mμ, hmμ⟩ : ∃ mμ : O, algebraMap O K mμ = μ := by
    have hint : IsIntegral O μ := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C (((ε⁻¹ : Oˣ) : O) * (η : O)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [map_mul, ← hμ2, ← mul_assoc, hinvE, one_mul, sq, sub_self]
    exact IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Set (Etau K τ), ∀ b, b ∈ Λ ↔
      ∃ p q : O, b = algebraMap O K p • y1 + algebraMap O K q • y2 := ⟨_, fun _ => Iff.rfl⟩
  have hy1Λ : y1 ∈ Λ := (hΛ _).mpr ⟨1, 0, by simp⟩
  have hy2Λ : y2 ∈ Λ := (hΛ _).mpr ⟨0, 1, by simp⟩
  have hLat : IsLat O τ Λ := by
    refine ⟨⟨{y1, y2}, ?_⟩, ?_⟩
    · ext b
      rw [hΛ, Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_pair]
      constructor
      · rintro ⟨p, q, rfl⟩
        exact ⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩
      · rintro ⟨p, q, rfl⟩
        exact ⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩
    · rw [eq_top_iff]
      intro b _
      rw [coord hind b]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span hy1Λ))
        (Submodule.smul_mem _ _ (Submodule.subset_span hy2Λ))
  have hsub : S ⊆ S0 s β Λ := by
    intro v hv
    obtain ⟨a, b, d, rfl⟩ := hspan v hv
    rw [mem_S0_of_sum_eq hΛ, ← algebraMap_smul K a e, ← algebraMap_smul K b f, ← algebraMap_smul K d h]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, pe1, pe2, pf1, pf2, hμ, ph2]
    constructor
    · refine (hΛ _).mpr ⟨d * mμ, b, ?_⟩
      rw [map_mul, hmμ]
      module
    · refine (hΛ _).mpr ⟨a * (↑ε⁻¹ * 2), -(d * mμ), ?_⟩
      rw [map_mul, ← hκ, map_neg, map_mul, hmμ]
      module
  have hsup : S0 s β Λ ⊆ S := by
    intro y hy
    rw [hS.dual]
    intro x hx
    exact Bf_int h2O hc hβ hind hΛ (hsub hx) hy
  exact ⟨Λ, hLat, Set.Subset.antisymm hsub hsup⟩

theorem lattice_homothety_of_eq_unimodular (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hu : IsUnit β) {Λ Λ' : Set (Etau K τ)} (hΛ : IsLat O τ Λ) (hΛ' : IsLat O τ Λ')
    (hS : S0 s β Λ = S0 s β Λ') : ∃ k : Kˣ, Λ' = ((k : K) • ·) '' Λ := by
  obtain ⟨y₁, y₂, hy, hb⟩ := lat_basis L hD hΛ
  have h2 : (2 : K) ≠ 0 := by
    have := (L.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨e, f, h, he1, he2, hf1, hf2, -, -⟩ := exists_efh hD h2 hs hu hy
  have hy1 : y₁ ≠ 0 := by
    rintro rfl
    simp at hy
  have h0 : (0 : Etau K τ) ∈ Λ := (hb 0).mpr ⟨0, 0, by simp⟩
  have hy1m : y₁ ∈ Λ := (hb _).mpr ⟨1, 0, by simp⟩
  have hy2m : y₂ ∈ Λ := (hb _).mpr ⟨0, 1, by simp⟩
  have heS : e ∈ S0 s β Λ := (mem_S0_of_sum_eq hb).mpr ⟨by rw [he1]; exact h0, by rw [he2]; exact hy1m⟩
  have hfS : f ∈ S0 s β Λ := (mem_S0_of_sum_eq hb).mpr ⟨by rw [hf1]; exact hy2m, by rw [hf2]; exact h0⟩
  rw [hS] at heS hfS
  obtain ⟨u, hu'⟩ := hΛ'.fg
  have hspan := hΛ'.span
  subst hu'
  set M' : Submodule O (Etau K τ) := Submodule.span O (u : Set (Etau K τ)) with hM'
  set g : K →ₗ[O] Etau K τ := (LinearMap.toSpanSingleton K (Etau K τ) y₁).restrictScalars O with hg
  have hgp : ∀ p, g p = p • y₁ := fun p => rfl
  set J : Submodule O K := M'.comap g with hJ
  have hmemJ : ∀ p, p ∈ J ↔ p • y₁ ∈ M' := fun p => by rw [hJ, Submodule.mem_comap, hgp]
  have hginj : Function.Injective g := by
    intro p q hpq
    rw [hgp, hgp] at hpq
    exact smul_left_injective K hy1 hpq
  have hJfg : J.FG := Submodule.fg_of_fg_map_injective g hginj
    (Submodule.FG.of_le (Submodule.fg_span (Finset.finite_toSet u)) (Submodule.map_comap_le g M'))
  haveI := L.frac
  obtain ⟨k, hk⟩ := (FractionalIdeal.isPrincipal
    (⟨J, FractionalIdeal.isFractional_of_fg hJfg⟩ : FractionalIdeal (nonZeroDivisors O) K)).principal
  change J = Submodule.span O {k} at hk
  have hcoef : ∀ b ∈ M', ∀ p q : K, b = p • y₁ + q • y₂ → p ∈ J ∧ q ∈ J := by
    intro b hbM p q hbpq
    have hE : ∀ y ∈ M', psi s β e y ∈ M' := heS
    have hF : ∀ y ∈ M', psi s β f y ∈ M' := hfS
    have h1 := hE _ (hF _ hbM)
    have h2' := hE _ hbM
    rw [hbpq] at h1 h2'
    simp only [map_add, map_smul, he1, he2, hf1, hf2, smul_zero, add_zero, zero_add] at h1 h2'
    exact ⟨(hmemJ p).mpr h1, (hmemJ q).mpr h2'⟩
  have hback : ∀ p q : K, p ∈ J → q ∈ J → p • y₁ + q • y₂ ∈ M' := by
    intro p q hp hq
    have hF : ∀ y ∈ M', psi s β f y ∈ M' := hfS
    have := hF _ ((hmemJ q).mp hq)
    simp only [map_smul, hf1] at this
    exact M'.add_mem ((hmemJ p).mp hp) this
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hsub : (M' : Set (Etau K τ)) ⊆ {0} := by
      intro b hbM
      have hc := coord hy b
      obtain ⟨hp, hq⟩ := hcoef b hbM _ _ hc
      rw [hk, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hp hq
      rw [hc, hp, hq]
      simp
    have : Submodule.span K (M' : Set (Etau K τ)) ≤ ⊥ := by
      rw [Submodule.span_le]
      simpa using hsub
    rw [hspan, le_bot_iff] at this
    exact hy1 (by simpa [this] using (Submodule.mem_top : y₁ ∈ (⊤ : Submodule K (Etau K τ))))
  refine ⟨Units.mk0 k hk0, ?_⟩
  ext b
  simp only [Units.val_mk0, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hbM
    have hc := coord hy b
    obtain ⟨hp, hq⟩ := hcoef b hbM _ _ hc
    rw [hk, Submodule.mem_span_singleton] at hp hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨a', ha'⟩ := hq
    refine ⟨algebraMap O K a • y₁ + algebraMap O K a' • y₂, (hb _).mpr ⟨a, a', rfl⟩, ?_⟩
    rw [hc, ← ha, ← ha', smul_add, smul_smul, smul_smul, Algebra.smul_def a k, Algebra.smul_def a' k,
      mul_comm k, mul_comm k]
  · rintro ⟨y, hyΛ, rfl⟩
    obtain ⟨p, q, rfl⟩ := (hb y).mp hyΛ
    rw [smul_add, smul_smul, smul_smul]
    apply hback
    · rw [hk, Submodule.mem_span_singleton]
      exact ⟨p, by rw [Algebra.smul_def, mul_comm]⟩
    · rw [hk, Submodule.mem_span_singleton]
      exact ⟨q, by rw [Algebra.smul_def, mul_comm]⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem unimodular_image_mul_unit (z : (Etau K τ)ˣ) (Λ : Set (Etau K τ)) :
    S0 s β (((z : Etau K τ) * ·) '' Λ) = (fun v => (v.1, quo z * v.2)) '' S0 s β Λ := by
  have hq : quo z * quo z⁻¹ = 1 := by
    simp only [quo, inv_inv]
    calc (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ))
        = ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))
          * star ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [star_mul']
          ring
      _ = 1 := by simp
  have hw2 : ∀ w : K × Etau K τ, w = ((w.1, quo z⁻¹ * w.2).1, quo z * (w.1, quo z⁻¹ * w.2).2) := by
    intro w
    refine Prod.ext rfl ?_
    show w.2 = quo z * (quo z⁻¹ * w.2)
    rw [← mul_assoc, hq, one_mul]
  ext w
  constructor
  · intro hw
    refine ⟨(w.1, quo z⁻¹ * w.2), ?_, (hw2 w).symm⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hw ((z : Etau K τ) * y) ⟨y, hy, rfl⟩
    rw [hw2 w, psi_quo] at hxy
    have := (Units.mul_right_inj z).mp hxy
    rw [← this]
    exact hx
  · rintro ⟨v, hv, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [psi_quo]
    exact ⟨_, hv y hy, rfl⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem unimodular_image_smul_eq (k : Kˣ) (Λ : Set (Etau K τ)) : S0 s β (((k : K) • ·) '' Λ) = S0 s β Λ := by
  ext v
  simp only [S0, Set.mem_setOf_eq]
  constructor
  · intro h y hy
    have := h ((k : K) • y) ⟨y, hy, rfl⟩
    rw [map_smul] at this
    obtain ⟨x, hx, hxy⟩ := this
    have : x = psi s β v y := smul_right_injective _ (Units.ne_zero k) hxy
    exact this ▸ hx
  · rintro h _ ⟨y, hy, rfl⟩
    rw [map_smul]
    exact ⟨_, h y hy, rfl⟩

theorem Uni.iso (L : IsLoc O Δ) (ht : t ≠ 0) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    IsSquare (τ ^ 2 - 4) ∨ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = -2 * c * t := by
  obtain ⟨e, -, f, -, h, -, η, hee, -, hef, -⟩ := Uni.frame L hS
  have h2 : (2 : K) ≠ 0 := by
    have := L.two.map (algebraMap O K)
    rw [map_ofNat] at this
    exact this.ne_zero
  obtain ⟨x, ⟨p, q⟩⟩ := e
  rw [Bf_apply] at hee
  simp only [trace_def, re_mul, im_mul, re_star, im_star] at hee
  have hN : (2 * t) * (x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2)) = 0 := by
    field_simp
    linear_combination hee
  have hN' : x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2) = 0 :=
    (mul_eq_zero.mp hN).resolve_left (mul_ne_zero h2 ht)
  by_cases hx : x = 0
  · subst hx
    left
    by_cases hq : q = 0
    · exfalso
      subst hq
      have hp : p = 0 := by
        have : p ^ 2 = 0 := by linear_combination hN'
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      subst hp
      have : ((0 : K × Etau K τ)) = ((0 : K), (⟨0, 0⟩ : Etau K τ)) := rfl
      rw [← this, map_zero, LinearMap.zero_apply] at hef
      exact zero_ne_one hef
    · refine ⟨(2 * p + τ * q) / q, ?_⟩
      field_simp
      linear_combination (-4) * hN'
  · right
    refine ⟨t * (2 * p + τ * q) / x, t * q / x, ?_⟩
    field_simp
    linear_combination 2 * hee

end UpperTheory.V.Z.Sym.Loc.CP
