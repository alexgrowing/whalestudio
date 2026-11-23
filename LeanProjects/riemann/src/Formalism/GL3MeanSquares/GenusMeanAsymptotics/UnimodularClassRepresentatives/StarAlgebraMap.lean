import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulSubOneMemPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MeanB

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ θ : K, star θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 K)
  obtain ⟨θ, t, e, h⟩ := hK.2.2 P hP
  refine ⟨algebraMap (𝓞 K) K θ, fun h' => h ?_⟩
  rw [h'] at e
  have : t = θ := RingOfIntegers.coe_injective e
  rw [this, sub_self]; exact P.zero_mem

theorem star_algebraMap (hF : IsFixF K F) (a : F) : star (algebraMap F K a) = algebraMap F K a :=
  (hF _).2 ⟨a, rfl⟩

theorem finrank_eq_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) : finrank F K = 2 := by
  obtain ⟨θ, hθ⟩ := exists_star_ne hK
  set δ : K := θ - star θ with hδ
  have hδ0 : δ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
  have hsδ : star δ = -δ := by rw [hδ, star_sub, star_star]; ring
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hli : LinearIndependent F ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t e
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
    have e' := congrArg star e
    rw [star_add, star_mul', star_algebraMap hF, star_algebraMap hF, hsδ, star_zero] at e'
    have hs : algebraMap F K s = 0 := by
      have : 2 * algebraMap F K s = 0 := by linear_combination e + e'
      exact (mul_eq_zero.1 this).resolve_left h2
    have ht : algebraMap F K t = 0 := by
      rw [hs, zero_add] at e
      exact (mul_eq_zero.1 e).resolve_right hδ0
    exact ⟨(map_eq_zero _).1 hs, (map_eq_zero _).1 ht⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), δ]) := by
    intro a _
    obtain ⟨f1, hf1⟩ := (hF ((a + star a) / 2)).1 (by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
    obtain ⟨f2, hf2⟩ := (hF ((a - star a) / (2 * δ))).1 (by
      rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hsδ]
      field_simp
      ring)
    have : Set.range ![(1 : K), δ] = {1, δ} := by
      simp [Matrix.range_cons, Set.pair_comm]
    rw [this, Submodule.mem_span_pair]
    refine ⟨f1, f2, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, hf1, hf2]
    field_simp
    ring
  have := finrank_eq_card_basis (Basis.mk hli hsp)
  simpa using this

theorem algebraMap_comp (a : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) := rfl

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by
  let _ : Module F V := Module.compHom V (algebraMap F K)
  have t1 : IsScalarTower F K V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap F K a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let _ : Module (𝓞 F) V := Module.compHom V (algebraMap (𝓞 F) (𝓞 K))
  have t2 : IsScalarTower (𝓞 F) (𝓞 K) V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap (𝓞 F) (𝓞 K) a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have t3 : IsScalarTower (𝓞 F) F V := ⟨fun a b v => by
    change (algebraMap F K (a • b)) • v = (algebraMap (𝓞 F) (𝓞 K) a) • ((algebraMap F K b) • v)
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) a), algebraMap_comp, Algebra.smul_def, map_mul,
      mul_smul]⟩
  have : FiniteDimensional F V := FiniteDimensional.trans F K V
  have hrank : finrank F V = 2 * finrank K V := by
    rw [← finrank_mul_finrank F K V, finrank_eq_two hK hF]
  let M : Submodule (𝓞 F) V := L.restrictScalars (𝓞 F)
  let e : ↥M ≃ₗ[𝓞 F] ↥L := (Submodule.restrictScalarsEquiv (𝓞 F) (𝓞 K) V L).restrictScalars (𝓞 F)
  have hfg : M.FG := by
    have : Module.Finite (𝓞 K) ↥L := Module.Finite.iff_fg.2 hL.fg
    have : Module.Finite (𝓞 F) ↥L := Module.Finite.trans (𝓞 K) ↥L
    exact Module.Finite.iff_fg.1 (Module.Finite.equiv e.symm)
  have hspan : Submodule.span F (M : Set V) = ⊤ := by
    have key : ∀ (a : K), ∀ w ∈ Submodule.span F (M : Set V), a • w ∈ Submodule.span F (M : Set V) := by
      intro a w hw
      induction hw using Submodule.span_induction with
      | mem l hl =>
        obtain ⟨d, hd, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2
          (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)).exists_integral_multiple
        let z : 𝓞 K := ⟨d • a, hint⟩
        have hz : algebraMap (𝓞 K) K z = d • a := rfl
        have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
        have : a • l = ((d : F)⁻¹) • (z • l) := by
          rw [← algebraMap_smul K z l, hz, ← algebraMap_smul K ((d : F)⁻¹), smul_smul, map_inv₀,
            map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Int.cast_ne_zero.2 hd), one_mul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem z hl))
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul f x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro v hv0
    clear hv0
    have hv : v ∈ Submodule.span K (L : Set V) := hL.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem l hl => exact Submodule.subset_span hl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact key a x hx
  have main := MeanA.card_quot_pow_smul_top (F := F) M hfg hspan h𝔭 k
  have hQ : Nat.card (𝓞 F ⧸ 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ k := by
    rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hmap : (𝔭 ^ k • ⊤ : Submodule (𝓞 F) ↥M).map (e : ↥M →ₗ[𝓞 F] ↥L) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L).restrictScalars (𝓞 F) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, extP, ← Ideal.map_pow,
      Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  have e1 := Submodule.Quotient.equiv _ _ e hmap
  have e2 := Submodule.Quotient.restrictScalarsEquiv (𝓞 F)
    ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)
  rw [← Nat.card_congr e2.toEquiv, ← Nat.card_congr e1.toEquiv, main, hQ, hrank, ← pow_mul]
  congr 1; ring

theorem exists_star_int (a : 𝓞 K) : ∃ a' : 𝓞 K, algebraMap (𝓞 K) K a' = star (algebraMap (𝓞 K) K a) :=
  ⟨⟨star (algebraMap (𝓞 K) K a), map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)⟩, rfl⟩

theorem star_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    ∃ z' ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z' = star (algebraMap (𝓞 K) K z) := by
  rw [extP, ← Ideal.map_pow, Ideal.map] at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨_, Ideal.subset_span ⟨t, ht, rfl⟩, by rw [algebraMap_comp, star_algebraMap hF]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, map_add, star_add, ex, ey]⟩
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := exists_star_int a
    exact ⟨a' * x', Ideal.mul_mem_left _ _ hx', by
      rw [smul_eq_mul, map_mul, map_mul, star_mul', ex, ea]⟩

theorem comap_extP_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (extP K 𝔭 ^ k).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]

theorem congrP_algebraMap_iff_sub_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a b : 𝓞 F) :
    CongrP (K := K) 𝔭 k (algebraMap F K (a : F)) (algebraMap F K (b : F)) ↔ a - b ∈ 𝔭 ^ k := by
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have : z = algebraMap (𝓞 F) (𝓞 K) (t * (a - b)) := by
      apply RingOfIntegers.coe_injective
      rw [e, algebraMap_comp]
      simp
    rw [this, ← Ideal.mem_comap, comap_extP_pow] at hz
    exact MeanA.mem_pow_of_mul_mem h𝔭 ht hz
  · intro h
    refine ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), algebraMap (𝓞 F) (𝓞 K) (a - b), ?_, ?_⟩
    · rw [← Ideal.mem_comap, comap_extP_pow]; exact h
    · rw [algebraMap_comp]; simp

section form

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}

theorem exists_val (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (y : ↥L) :
    ∃ n : 𝓞 F, h (y : V) (y : V) = algebraMap F K (n : F) := by
  obtain ⟨a, ha⟩ := (hF (h y y)).1 (hs.eq y y)
  obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hLi y y.2 y y.2)
  have hint : IsIntegral ℤ a := by
    rw [← isIntegral_algebraMap_iff (algebraMap F K).injective, ha, ← hz]
    exact RingOfIntegers.isIntegral_coe z
  exact ⟨⟨a, hint⟩, ha.symm⟩

theorem form_mem_right (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (u : ↥L) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V) := by
  induction hw using Submodule.smul_induction_on' with
  | smul a ha v _ =>
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hLi u u.2 v v.2)
    refine ⟨a * c, Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [map_mul, hc, Submodule.coe_smul, ← algebraMap_smul K a (v : V), map_smul, smul_eq_mul]
  | add a _ b _ ha hb =>
    obtain ⟨x', hx', ex⟩ := ha
    obtain ⟨y', hy', ey⟩ := hb
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, ex, ey, Submodule.coe_add, map_add]⟩

theorem val_congr (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) {y y' : ↥L} {n n' : 𝓞 F}
    (hy : y - y' ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (e : h (y : V) (y : V) = algebraMap F K (n : F))
    (e' : h (y' : V) (y' : V) = algebraMap F K (n' : F)) : n - n' ∈ 𝔭 ^ k := by
  obtain ⟨z1, hz1, e1⟩ := form_mem_right hLi 𝔭 k y' hy
  obtain ⟨z2, hz2, e2⟩ := form_mem_right hLi 𝔭 k (y - y') hy
  obtain ⟨z3, hz3, e3⟩ := star_mem_extP hF 𝔭 k hz1
  rw [← comap_extP_pow (K := K), Ideal.mem_comap]
  have : algebraMap (𝓞 F) (𝓞 K) (n - n') = z1 + z2 + z3 := by
    apply RingOfIntegers.coe_injective
    have h3 : star (h (y' : V) ((y - y' : ↥L) : V)) = h ((y - y' : ↥L) : V) (y' : V) := hs.eq _ _
    rw [algebraMap_comp, map_add, map_add, e1, e2, e3, e1, h3]
    have : algebraMap F K ((n - n' : 𝓞 F) : F) = algebraMap F K (n : F) - algebraMap F K (n' : F) := by
      simp
    rw [this, ← e, ← e']
    simp only [Submodule.coe_sub, map_sub, LinearMap.sub_apply]
    ring
  rw [this]
  exact add_mem (add_mem hz1 hz2) hz3

end form

end Formalism.HermitianLattices.Ext.L3.MeanB
