import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm

namespace UpperTheory.V.Z.Sym.Loc.CP

open IsLocalRing

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {B : V →ₗ[K] V →ₗ[K] K} {S : Submodule O V}

theorem exists_smul_mem (L : IsLoc O Δ) (hf : S.FG) (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range) (y : V) :
    ∃ k : K, k ≠ 0 ∧ k • y ∈ S := by
  haveI := L.frac
  classical
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) (s.image fun x => B x y)
  refine ⟨algebraMap O K b, (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero b.2), (hd _).2 fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hb _ (Finset.mem_image_of_mem _ hx)
    exact ⟨a, by rw [ha, map_smul, Algebra.smul_def, smul_eq_mul]⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, LinearMap.map_smul₂, smul_eq_mul]
    exact mul_mem ⟨a, rfl⟩ hx

theorem exists_unit (L : IsLoc O Δ) (hB : ∀ x y, B x y = B y x) (hf : S.FG) (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range)
    (P : V →ₗ[K] V) (hP : ∀ x ∈ S, P x ∈ S) (hPP : ∀ x, P (P x) = P x) (hadj : ∀ x y, B x (P y) = B (P x) (P y)) (h0 : P ≠ 0) :
    ∃ v ∈ S, P v = v ∧ ∃ u : Oˣ, B v v = algebraMap O K u := by
  haveI := L.frac
  by_contra hn
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp' : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  have h1 : ∀ v ∈ S, ∃ a : O, B (P v) (P v) = algebraMap O K (p * a) := fun v hv => by
    obtain ⟨a, ha⟩ := (hd _).1 (hP v hv) _ (hP v hv)
    have : a ∈ maximalIdeal O := fun hu => hn ⟨P v, hP v hv, hPP v, hu.unit, ha.symm⟩
    rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨b, rfl⟩ := this
    exact ⟨b, ha.symm⟩
  obtain ⟨i, hi⟩ := L.two.exists_right_inv
  have hi' : (2 : K) * algebraMap O K i = 1 := by rw [← map_ofNat (algebraMap O K) 2, ← map_mul, hi, map_one]
  have h2 : ∀ v ∈ S, (algebraMap O K p)⁻¹ • P v ∈ S := fun v hv => (hd _).2 fun w hw => by
    obtain ⟨a, ha⟩ := h1 v hv
    obtain ⟨b, hb⟩ := h1 w hw
    obtain ⟨c, hc⟩ := h1 (v + w) (add_mem hv hw)
    simp only [map_add, LinearMap.add_apply, map_mul] at ha hb hc
    refine ⟨i * (c - a - b), ?_⟩
    rw [map_smul, hadj, smul_eq_mul, map_mul, map_sub, map_sub]
    rw [hB (P v) (P w)] at hc
    field_simp
    linear_combination (-algebraMap O K i) * hc + algebraMap O K i * ha + algebraMap O K i * hb + B (P w) (P v) * hi'
  have h3 : S.map (P.restrictScalars O) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (hf.map _) ?_ (maximalIdeal_le_jacobson _)
    rintro _ ⟨v, hv, rfl⟩
    have : (P.restrictScalars O) v = p • (P.restrictScalars O) ((algebraMap O K p)⁻¹ • P v) := by
      simp only [LinearMap.restrictScalars_apply, map_smul, hPP]
      rw [← algebraMap_smul K p, smul_smul, mul_inv_cancel₀ hp', one_smul]
    rw [this]
    exact Submodule.smul_mem_smul hp.not_isUnit ⟨_, h2 v hv, rfl⟩
  refine h0 (LinearMap.ext fun y => ?_)
  obtain ⟨k, hk, hy⟩ := exists_smul_mem L hf hd y
  have : P (k • y) = 0 := (Submodule.eq_bot_iff _).1 h3 _ ⟨_, hy, rfl⟩
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hk

theorem not_span_two (h3 : Module.finrank K V = 3) (a b : V) (h : ∀ x, ∃ s t : K, x = s • a + t • b) : False := by
  have := finrank_le_of_span_eq_top (R := K) (v := ![a, b]) (by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨s, t, rfl⟩ := h x
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
  simp [h3] at this

theorem exists_frame (L : IsLoc O Δ) (h3 : Module.finrank K V = 3) (hB : ∀ x y, B x y = B y x) (hf : S.FG)
    (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ h ∈ S, ∃ η : Oˣ, B e e = 0 ∧ B f f = 0 ∧ B e f = 1 ∧ B e h = 0 ∧ B f h = 0 ∧ B h h = algebraMap O K η ∧
      ∀ v ∈ S, ∃ a b c : O, v = a • e + b • f + c • h := by
  haveI := L.frac
  have sm : ∀ (a : O) (x : V), algebraMap O K a • x = a • x := fun a x => algebraMap_smul K a x
  have un : ∀ u : Oˣ, algebraMap O K u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have iv : ∀ u : Oˣ, (algebraMap O K u)⁻¹ = algebraMap O K (u⁻¹ : Oˣ) := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
  have pm : ∀ (e : V) (u : Oˣ), e ∈ S → ∀ x ∈ S, ∀ g ∈ S, ((algebraMap O K u)⁻¹ * B e x) • g ∈ S := fun e u he x hx g hg => by
    obtain ⟨a, ha⟩ := (hd x).1 hx e he
    rw [iv, ← ha, ← map_mul, sm]; exact S.smul_mem _ hg
  obtain ⟨e₁, m₁, -, u₁, q₁⟩ := exists_unit L hB hf hd LinearMap.id (fun _ h => h) (fun _ => rfl) (fun _ _ => rfl) fun h =>
    not_span_two h3 0 0 fun x => ⟨0, 0, by simpa using LinearMap.congr_fun h x⟩
  let P₂ : V →ₗ[K] V := LinearMap.id - ((algebraMap O K u₁)⁻¹ • B e₁).smulRight e₁
  have a₂ : ∀ x, P₂ x = x - ((algebraMap O K u₁)⁻¹ * B e₁ x) • e₁ := fun x => rfl
  have o₂ : ∀ x, B e₁ (P₂ x) = 0 := fun x => by rw [a₂, map_sub, map_smul, q₁, smul_eq_mul]; field_simp [un u₁]; ring
  obtain ⟨e₂, m₂, p₂, u₂, q₂⟩ := exists_unit L hB hf hd P₂ (fun x hx => sub_mem hx (pm e₁ u₁ m₁ x hx _ m₁))
    (fun x => by rw [a₂ (P₂ x), o₂]; simp) (fun x y => by rw [a₂ x, LinearMap.map_sub₂, LinearMap.map_smul₂, o₂]; simp) fun h =>
    not_span_two h3 e₁ 0 fun x => ⟨_, 0, by simpa [a₂, sub_eq_zero] using LinearMap.congr_fun h x⟩
  have b12 : B e₁ e₂ = 0 := p₂ ▸ o₂ e₂
  have b21 : B e₂ e₁ = 0 := hB _ _ ▸ b12
  let P₃ : V →ₗ[K] V := P₂ - ((algebraMap O K u₂)⁻¹ • B e₂).smulRight e₂
  have a₃ : ∀ x, P₃ x = x - ((algebraMap O K u₁)⁻¹ * B e₁ x) • e₁ - ((algebraMap O K u₂)⁻¹ * B e₂ x) • e₂ := fun x => rfl
  have o₃ : ∀ x, B e₁ (P₃ x) = 0 := fun x => by simp only [a₃, map_sub, map_smul, q₁, b12, smul_eq_mul]; field_simp [un u₁]; ring
  have o₃' : ∀ x, B e₂ (P₃ x) = 0 := fun x => by simp only [a₃, map_sub, map_smul, q₂, b21, smul_eq_mul]; field_simp [un u₂]; ring
  obtain ⟨e₃, m₃, p₃, u₃, q₃⟩ := exists_unit L hB hf hd P₃ (fun x hx => sub_mem (sub_mem hx (pm e₁ u₁ m₁ x hx _ m₁)) (pm e₂ u₂ m₂ x hx _ m₂))
    (fun x => by rw [a₃ (P₃ x), o₃, o₃']; simp)
    (fun x y => by rw [a₃ x, LinearMap.map_sub₂, LinearMap.map_sub₂, LinearMap.map_smul₂, LinearMap.map_smul₂, o₃, o₃']; simp) fun h =>
    not_span_two h3 e₁ e₂ fun x => ⟨_, _, by
      have := LinearMap.congr_fun h x
      rw [a₃, sub_sub, LinearMap.zero_apply, sub_eq_zero] at this
      exact this⟩
  have b13 : B e₁ e₃ = 0 := p₃ ▸ o₃ e₃
  have b23 : B e₂ e₃ = 0 := p₃ ▸ o₃' e₃
  have b31 : B e₃ e₁ = 0 := hB _ _ ▸ b13
  have b32 : B e₃ e₂ = 0 := hB _ _ ▸ b23
  obtain ⟨a, b, hab⟩ := L.nm_unit (-(u₂ * u₁⁻¹)) (-(u₃ * u₁⁻¹))
  have hab' : algebraMap O K u₁ * algebraMap O K a ^ 2 + algebraMap O K u₂ * algebraMap O K b ^ 2 + algebraMap O K u₃ = 0 := by
    have := congrArg (algebraMap O K) hab
    simp only [Units.val_neg, Units.val_mul, map_sub, map_mul, map_neg, map_pow, ← iv] at this
    have h1 := un u₁
    field_simp at this
    linear_combination this
  let t : Oˣ := L.two.unit * u₃
  have ht : algebraMap O K t = 2 * algebraMap O K u₃ := by simp [t, map_ofNat]
  have h2 : (2 : K) ≠ 0 := fun h => un t (by rw [ht, h, zero_mul])
  set A := algebraMap O K a with hA
  set C := algebraMap O K b with hC
  let e := A • e₁ + C • e₂ + e₃
  let f := (algebraMap O K t)⁻¹ • (e₃ - A • e₁ - C • e₂)
  let h := (algebraMap O K u₂ * C) • e₁ - (algebraMap O K u₁ * A) • e₂
  have me : e ∈ S := add_mem (add_mem (by rw [hA, sm]; exact S.smul_mem _ m₁) (by rw [hC, sm]; exact S.smul_mem _ m₂)) m₃
  have mf : f ∈ S := by
    simp only [f]
    rw [iv, sm]
    exact S.smul_mem _ (sub_mem (sub_mem m₃ (by rw [hA, sm]; exact S.smul_mem _ m₁)) (by rw [hC, sm]; exact S.smul_mem _ m₂))
  have mh : h ∈ S := sub_mem (by rw [hC, ← map_mul, sm]; exact S.smul_mem _ m₁) (by rw [hA, ← map_mul, sm]; exact S.smul_mem _ m₂)
  have n₃ := un u₃
  have g1 : B e e = 0 := by simp [e, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32]; linear_combination hab'
  have g2 : B f f = 0 := by
    simp [f, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32, ht]
    field_simp
    first | linear_combination hab' | (right; right; linear_combination hab') | (simp [h2, n₃]; linear_combination hab')
  have g3 : B e f = 1 := by simp [e, f, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32, ht]; field_simp; linear_combination -hab'
  have g4 : B e h = 0 := by simp [e, h, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32]; ring
  have g5 : B f h = 0 := by
    simp only [f, h, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, q₁, q₂, b12, b21, b31, b32]; ring
  have g6 : B h h = algebraMap O K (-(u₁ * u₂ * u₃) : Oˣ) := by
    simp [h, q₁, q₂, q₃, b12, b21]; linear_combination (algebraMap O K u₁ * algebraMap O K u₂) * hab'
  refine ⟨e, me, f, mf, h, mh, _, g1, g2, g3, g4, g5, g6, fun v hv => ?_⟩
  set η : Oˣ := -(u₁ * u₂ * u₃)
  have g3' : B f e = 1 := hB _ _ ▸ g3
  have g4' : B h e = 0 := hB _ _ ▸ g4
  have g5' : B h f = 0 := hB _ _ ▸ g5
  have li : LinearIndependent K ![e, f, h] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have k1 := congrArg (B f) hg
    have k2 := congrArg (B e) hg
    have k3 := congrArg (B h) hg
    simp [g1, g2, g3, g4, g5, g6, g3', g4', g5', un η] at k1 k2 k3
    intro i; fin_cases i <;> assumption
  have sp := li.span_eq_top_of_card_eq_finrank (by simp [h3])
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (sp ▸ Submodule.mem_top : v ∈ Submodule.span K (Set.range ![e, f, h]))
  rw [Fin.sum_univ_three] at hg
  obtain ⟨x, hx⟩ := (hd v).1 hv f mf
  obtain ⟨y, hy⟩ := (hd v).1 hv e me
  obtain ⟨z, hz⟩ := (hd v).1 hv h mh
  rw [← hg] at hx hy hz
  simp [g1, g2, g3, g4, g5, g6, g3', g4', g5'] at hx hy hz
  refine ⟨x, y, z * (η⁻¹ : Oˣ), ?_⟩
  rw [← sm, ← sm, ← sm, map_mul, hx, hy, hz, ← iv, mul_inv_cancel_right₀ (un η)]
  exact hg.symm

end UpperTheory.V.Z.Sym.Loc.CP
