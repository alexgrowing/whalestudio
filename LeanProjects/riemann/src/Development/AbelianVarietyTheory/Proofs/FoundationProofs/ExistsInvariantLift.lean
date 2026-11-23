import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThLift

theorem hilbert_ninety : ∀ (Ω K Γ : Type) [Field Ω] [Field K] [Algebra Ω K] [Group Γ] (ρ : Γ →* (K ≃ₐ[Ω] K)) (Δ : Subgroup Γ) [Δ.FiniteIndex] (c : Γ → K), (∀ γ, c γ ≠ 0) → (∀ γ γ', c (γ * γ') = ρ γ (c γ') * c γ) → (∀ γ, (∀ x : K, (∀ δ ∈ Δ, ρ δ x = x) → ρ γ x = x) → c γ = 1) → ∃ y : K, y ≠ 0 ∧ ∀ γ, c γ * ρ γ y = y := by
  intro Ω K Γ _ _ _ _ ρ Δ _ c c0 cm c1
  classical
  let L : Submonoid K :=
    { carrier := {x | ∀ δ ∈ Δ, ρ δ x = x}
      mul_mem' := fun {a b} ha hb δ hδ => by rw [map_mul, ha δ hδ, hb δ hδ]
      one_mem' := fun δ _ => map_one _ }
  let D : Subgroup Γ :=
    { carrier := {γ | ∀ x ∈ L, ρ γ x = x}
      mul_mem' := fun {a b} ha hb x hx => by rw [map_mul, AlgEquiv.mul_apply, hb x hx, ha x hx]
      one_mem' := fun x _ => by rw [map_one, AlgEquiv.one_apply]
      inv_mem' := fun {a} ha x hx => by
        conv_lhs => rw [← ha x hx]
        rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply] }
  have hΔD : Δ ≤ D := fun δ hδ x hx => hx δ hδ
  haveI : D.FiniteIndex := Subgroup.finiteIndex_of_le hΔD
  haveI : Fintype (Γ ⧸ D) := Fintype.ofFinite _
  let χ : Γ → (L →* K) := fun γ => ((ρ γ : K ≃ₐ[Ω] K) : K →* K).comp L.subtype
  have hinj : Function.Injective (fun q : Γ ⧸ D => χ q.out) := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    intro x hx
    have e : ρ q.out x = ρ q'.out x := DFunLike.congr_fun h ⟨x, hx⟩
    rw [map_mul, AlgEquiv.mul_apply, ← e, ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
  have hli := (linearIndependent_monoidHom L K).comp _ hinj
  obtain ⟨x, hx⟩ : ∃ x : L, ∑ q : Γ ⧸ D, c q.out * ρ q.out x ≠ 0 := by
    by_contra hx
    push_neg at hx
    have := Fintype.linearIndependent_iff.1 hli (fun q => c q.out)
      (by funext x; simpa [Finset.sum_apply, χ] using hx x) ((1 : Γ) : Γ ⧸ D)
    exact c0 _ this
  refine ⟨_, hx, fun γ => ?_⟩
  have F : ∀ g g' : Γ, (g : Γ ⧸ D) = g' → c g' * ρ g' x = c g * ρ g x := by
    intro g g' h
    rw [QuotientGroup.eq] at h
    have e : g' = g * (g⁻¹ * g') := by group
    rw [e, cm, c1 _ h, map_one, one_mul, map_mul, AlgEquiv.mul_apply, h _ x.2]
  rw [map_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (MulAction.toPerm γ) _ _ fun q => ?_
  rw [MulAction.toPerm_apply, F (γ * q.out) (γ • q).out
    (by rw [QuotientGroup.out_eq']; exact MulAction.Quotient.coe_smul_out D γ q), cm, map_mul, map_mul,
    AlgEquiv.mul_apply]
  ring

theorem fix_of_pow_eq_one {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K] {m : ℕ} (hm : m ≠ 0) {x : K}
    (hx : x ^ m = 1) (τ : K ≃ₐ[Ω] K) : τ x = x := by
  have hi : IsIntegral Ω x := IsIntegral.of_pow (Nat.pos_of_ne_zero hm) (by rw [hx]; exact isIntegral_one)
  obtain ⟨a, rfl⟩ := minpoly.mem_range_of_degree_eq_one Ω x
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact τ.commutes a

theorem exists_cocycle {Ω K Γ : Type} [Field Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K] [Group Γ]
    (ρ : Γ →* (K ≃ₐ[Ω] K)) (σ : K ≃ₐ[Ω] K) {m : ℕ} (hm : Odd m) {f k : K} (hf : f ≠ 0)
    (hh : ∀ γ : Γ, ∃ h : K, (∀ γ' : Γ, σ (ρ γ' h) = ρ γ' (σ h)) ∧ ρ γ f = f * h ^ m)
    (hc : ∀ γ : Γ, σ (ρ γ f) = ρ γ (σ f)) (hk : σ f * f = k ^ m) :
    ∃ c : Γ → K, (∀ γ, c γ ≠ 0) ∧ (∀ γ γ', c (γ * γ') = ρ γ (c γ') * c γ) ∧ (∀ γ, ρ γ f = f * c γ ^ m) ∧
      ∀ γ, ρ γ f = f → ρ γ k = k → c γ = 1 := by
  choose h hσh hfh using hh
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hσf : σ f ≠ 0 := (map_ne_zero _).2 hf
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hk
    exact mul_ne_zero hσf hf hk
  have hρk : ∀ γ, ρ γ k ≠ 0 := fun γ => (map_ne_zero _).2 hk0
  have h0 : ∀ γ, h γ ≠ 0 := by
    intro γ e
    have := hfh γ
    rw [e, zero_pow hm0, mul_zero] at this
    exact (map_ne_zero _).2 hf this
  have hσ0 : ∀ γ, σ (h γ) ≠ 0 := fun γ => (map_ne_zero _).2 (h0 γ)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Γ → K, ∀ γ, ζ γ = σ (h γ) * h γ * k / ρ γ k := ⟨_, fun _ => rfl⟩
  have hζ0 : ∀ γ, ζ γ ≠ 0 := fun γ => by
    rw [hζ]; exact div_ne_zero (mul_ne_zero (mul_ne_zero (hσ0 γ) (h0 γ)) hk0) (hρk γ)
  have hζm : ∀ γ, ζ γ ^ m = 1 := by
    intro γ
    have e1 : ρ γ k ^ m = σ f * σ (h γ) ^ m * (f * h γ ^ m) := by
      rw [← map_pow, ← hk, map_mul, ← hc, hfh, map_mul, map_pow]
    rw [hζ, div_pow, e1, mul_pow, mul_pow, ← hk, div_eq_one_iff_eq]
    · ring
    · exact mul_ne_zero (mul_ne_zero hσf (pow_ne_zero _ (hσ0 γ))) (mul_ne_zero hf (pow_ne_zero _ (h0 γ)))
  obtain ⟨e, he⟩ := hm
  refine ⟨fun γ => h γ / ζ γ ^ (e + 1), fun γ => div_ne_zero (h0 γ) (pow_ne_zero _ (hζ0 γ)), fun γ γ' => ?_,
    fun γ => ?_, fun γ hγf hγk => ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a : K, h (γ * γ') = a * (ρ γ (h γ') * h γ) :=
      ⟨h (γ * γ') / (ρ γ (h γ') * h γ), (div_mul_cancel₀ _ (mul_ne_zero ((map_ne_zero _).2 (h0 γ')) (h0 γ))).symm⟩
    have hρh : ρ γ (h γ') ≠ 0 := (map_ne_zero _).2 (h0 γ')
    have ham : a ^ m = 1 := by
      have e1 := hfh (γ * γ')
      rw [map_mul, AlgEquiv.mul_apply, hfh γ', map_mul, hfh γ, map_pow, ha, mul_pow, mul_pow] at e1
      have e2 : f * (ρ γ (h γ') ^ m * h γ ^ m) * a ^ m = f * (ρ γ (h γ') ^ m * h γ ^ m) * 1 := by
        linear_combination -e1
      exact mul_left_cancel₀ (mul_ne_zero hf (mul_ne_zero (pow_ne_zero _ hρh) (pow_ne_zero _ (h0 γ)))) e2
    have hρζ : ρ γ (ζ γ') = ζ γ' := fix_of_pow_eq_one hm0 (hζm γ') _
    have hσa : σ a = a := fix_of_pow_eq_one hm0 ham _
    have e3 : ζ (γ * γ') = a ^ 2 * (ζ γ' * ζ γ) := by
      rw [← hρζ, hζ, hζ, hζ, ha]
      simp only [map_mul, map_div₀, AlgEquiv.mul_apply, hσa, hσh]
      have := hρk γ
      have : ρ γ (ρ γ' k) ≠ 0 := (map_ne_zero _).2 (hρk γ')
      field_simp
    have e4 : (a ^ 2) ^ (e + 1) = a := by
      rw [← pow_mul, show 2 * (e + 1) = m + 1 by omega, pow_succ, ham, one_mul]
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0] at ham
      exact zero_ne_one ham
    simp only [map_div₀, map_pow, hρζ]
    rw [e3, mul_pow, e4, ha, mul_pow]
    have := hζ0 γ
    have := hζ0 γ'
    field_simp
  · rw [div_pow, ← pow_mul, mul_comm (e + 1), pow_mul, hζm, one_pow, div_one, hfh]
  · have e1 : h γ ^ m = 1 := by
      have := hfh γ
      rw [hγf] at this
      exact (mul_left_cancel₀ hf (this.symm.trans (mul_one f).symm))
    have e2 : ζ γ = h γ ^ 2 := by
      rw [hζ, hγk, fix_of_pow_eq_one hm0 e1, mul_div_assoc, div_self hk0, mul_one, sq]
    show h γ / ζ γ ^ (e + 1) = 1
    rw [e2, ← pow_mul, show 2 * (e + 1) = m + 1 by omega, pow_succ, e1, one_mul, div_self (h0 γ)]

theorem exists_invariant_rep (Ω K Γ : Type) [Field Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K] [Group Γ]
    (ρ : Γ →* (K ≃ₐ[Ω] K)) (Δ : Subgroup Γ) [Δ.FiniteIndex] (σ : K ≃ₐ[Ω] K) (m : ℕ) (hm : Odd m)
    (f : K) (hf : f ≠ 0) (hfΔ : ∀ δ ∈ Δ, ρ δ f = f)
    (hh : ∀ γ : Γ, ∃ h : K, (∀ δ ∈ Δ, ρ δ h = h) ∧ ρ γ f = f * h ^ m)
    (hc : ∀ x : K, (∀ δ ∈ Δ, ρ δ x = x) → ∀ γ : Γ, σ (ρ γ x) = ρ γ (σ x))
    (k : K) (hk : σ f * f = k ^ m) (Δ₂ : Subgroup Γ) [Δ₂.FiniteIndex] (hkΔ : ∀ δ ∈ Δ₂, ρ δ k = k) :
    ∃ u : K, u ≠ 0 ∧ ∀ γ : Γ, ρ γ (f * u ^ m) = f * u ^ m := by
  obtain ⟨c, c0, cm, cf, c1⟩ := exists_cocycle ρ σ hm hf
    (fun γ => by obtain ⟨h, h1, h2⟩ := hh γ; exact ⟨h, hc h h1, h2⟩) (hc f hfΔ) hk
  obtain ⟨y, y0, hy⟩ := hilbert_ninety Ω K Γ ρ (Δ ⊓ Δ₂) c c0 cm (fun γ hγ =>
    c1 γ (hγ f fun δ hδ => hfΔ δ hδ.1) (hγ k fun δ hδ => hkΔ δ hδ.2))
  refine ⟨y, y0, fun γ => ?_⟩
  rw [map_mul, map_pow, cf, mul_assoc, ← mul_pow, hy]

theorem gamma1_inf_le : ∀ (N L : ℕ), Nat.Coprime N L →
    CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma1 (N * L) := by
  intro N L hNL γ hγ
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hγ
  rw [CongruenceSubgroup.Gamma1_mem] at h1 ⊢
  rw [CongruenceSubgroup.Gamma_mem] at h2
  have key : ∀ a b : ℤ, (a : ZMod N) = b → (a : ZMod L) = b → (a : ZMod (N * L)) = b := by
    intro a b ha hb
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at ha hb ⊢
    push_cast
    exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hNL) ha hb
  exact ⟨by simpa using key _ 1 (by simpa using h1.1) (by simpa using h2.1),
    by simpa using key _ 1 (by simpa using h1.2.1) (by simpa using h2.2.2.2),
    by simpa using key _ 0 (by simpa using h1.2.2) (by simpa using h2.2.2.1)⟩

theorem cast_of_dvd {D M : ℕ} (h : D ∣ M) (a b : ℤ) (ha : (a : ZMod M) = b) : (a : ZMod D) = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at ha ⊢
  exact (Int.natCast_dvd_natCast.2 h).trans ha

theorem gamma_le_gamma1 : ∀ (D M : ℕ), D ∣ M → CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma1 D := by
  intro D M h γ h2
  rw [CongruenceSubgroup.Gamma1_mem]
  rw [CongruenceSubgroup.Gamma_mem] at h2
  exact ⟨by simpa using cast_of_dvd h _ 1 (by simpa using h2.1),
    by simpa using cast_of_dvd h _ 1 (by simpa using h2.2.2.2),
    by simpa using cast_of_dvd h _ 0 (by simpa using h2.2.2.1)⟩

theorem mem_Gam_of_mem_gamma1 : ∀ (N l n : ℕ), 1 ≤ n → ∀ γ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n),
    γ ∈ Gam N l ∧ ((en γ 0 0 : ℤ) : ZMod (l ^ n)) = 1 ∧ ((en γ 1 0 : ℤ) : ZMod (l ^ n)) = 0 := by
  intro N l n hn γ h
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have d1 : N ∣ N * l ^ n := dvd_mul_right _ _
  have d2 : l ^ n ∣ N * l ^ n := dvd_mul_left _ _
  have d3 : l ∣ N * l ^ n := (dvd_pow_self l (by omega)).trans d2
  refine ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨by simpa using cast_of_dvd d1 _ 1 (by simpa using h.1),
      by simpa using cast_of_dvd d1 _ 1 (by simpa using h.2.1),
      by simpa using cast_of_dvd d1 _ 0 (by simpa using h.2.2)⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    simpa using cast_of_dvd d3 _ 0 (by simpa using h.2.2)
  · simpa [en] using cast_of_dvd d2 _ 1 (by simpa using h.1)
  · simpa [en] using cast_of_dvd d2 _ 0 (by simpa using h.2.2)

theorem gamma_le_of_dvd {D M : ℕ} (h : D ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma D := by
  intro γ h2
  rw [CongruenceSubgroup.Gamma_mem] at h2 ⊢
  exact ⟨by simpa using cast_of_dvd h _ 1 (by simpa using h2.1),
    by simpa using cast_of_dvd h _ 0 (by simpa using h2.2.1),
    by simpa using cast_of_dvd h _ 0 (by simpa using h2.2.2.1),
    by simpa using cast_of_dvd h _ 1 (by simpa using h2.2.2.2)⟩

theorem exists_uniform_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (m D : ℕ), 0 < D →
    ∀ f : X.K, (∀ γ ∈ H, ∃ h : X.K, X.sl (ofSL γ) f = f * h ^ m) →
    ∃ M : ℕ, 0 < M ∧ D ∣ M ∧ (∀ ρ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL ρ) f = f) ∧
      ∀ γ ∈ H, ∃ h : X.K, (∀ ρ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL ρ) h = h) ∧ X.sl (ofSL γ) f = f * h ^ m := by
  intro Ω _ _ ε X H m D hD f hH
  classical
  obtain ⟨M₀, hM₀, hf⟩ := X.level f
  haveI : NeZero M₀ := ⟨hM₀.ne'⟩
  have hfin : (Set.range fun γ : SL(2, ℤ) => X.sl (ofSL γ) f).Finite := by
    refine (Set.finite_range fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M₀ => X.sl (ofSL q.out⁻¹) f).subset ?_
    rintro _ ⟨γ, rfl⟩
    refine ⟨(γ⁻¹ : SL(2, ℤ)), ?_⟩
    obtain ⟨d, hd⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma M₀) γ⁻¹
    simp only [hd, mul_inv_rev, inv_inv, map_mul, X.sl_mul, hf _ (inv_mem d.2)]
  have hex : ∀ t : X.K, ∃ (h : X.K) (L : ℕ), 0 < L ∧ (∀ ρ ∈ CongruenceSubgroup.Gamma L, X.sl (ofSL ρ) h = h) ∧
      ((∃ h', t = f * h' ^ m) → t = f * h ^ m) := by
    intro t
    by_cases ht : ∃ h', t = f * h' ^ m
    · obtain ⟨h, hh⟩ := ht
      obtain ⟨L, hL0, hL⟩ := X.level h
      exact ⟨h, L, hL0, hL, fun _ => hh⟩
    · exact ⟨1, 1, one_pos, fun _ _ => map_one _, fun h => absurd h ht⟩
  choose hh L hL0 hL ht using hex
  refine ⟨D * M₀ * ∏ t ∈ hfin.toFinset, L t, Nat.mul_pos (Nat.mul_pos hD hM₀) (Finset.prod_pos fun t _ => hL0 t),
    (dvd_mul_right _ _).mul_right _, fun ρ hρ => hf ρ (gamma_le_of_dvd ((dvd_mul_left _ _).mul_right _) hρ),
    fun γ hγ => ⟨hh (X.sl (ofSL γ) f), fun ρ hρ => hL _ ρ (gamma_le_of_dvd ?_ hρ), ht _ (hH γ hγ)⟩⟩
  exact (Finset.dvd_prod_of_mem L (hfin.mem_toFinset.2 ⟨γ, rfl⟩)).mul_left _

theorem toGQ_coe_eq (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  ext i j
  simp [toGQ, h, ofSL]

theorem cls_eq_of_mem_Gam : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w n : ℕ) [Fact l.Prime]
    (b : X.Fn l), b ∈ X.B N l w → ∀ (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f →
    ∀ γ ∈ Gam N l, ∀ s : ℤ, ((en γ 0 0 : ℤ) : ZMod (l ^ n)) = s → ((en γ 1 0 : ℤ) : ZMod (l ^ n)) = 0 →
    ∀ g : X.Kˣ, X.cls l n g = s ^ w • X.cls l n f →
    X.cls l n f = X.cls l n (Units.map (X.sl (ofSL γ)).toRingEquiv.toMonoidHom g) := by
  intro Ω _ _ ε X N l w n _ b hb f hf γ hγ s h0 h1 g hg
  have hsm : ∀ (r r' : ℤ_[l]) (y : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))),
      PadicInt.toZModPow n r = PadicInt.toZModPow n r' → r • y = r' • y := by
    intro r r' y h
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← sub_smul]
    exact GlobalTheory.KZ.ClsMod.smul_mem_of_toZModPow (by rw [map_sub, h, sub_self]) v
  set u : Fin 2 → ℤ_[l] := Matrix.mulVec (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ)) ![1, 0] with hu
  have u0 : PadicInt.toZModPow n (u 0) = s := by
    rw [← h0, hu]; simp [mZl, Matrix.mulVec, dotProduct, en]
  have u1 : PadicInt.toZModPow n (u 1) = 0 := by
    rw [← h1, hu]; simp [mZl, Matrix.mulVec, dotProduct, en]
  have key : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b ∧
      AdicCompletion.eval (idl l) (X.Kl l) n (b u) =
        ((s : ℤ_[l]) ^ w) • AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) := by
    clear hf
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine ⟨hb.2 γ hγ, ?_⟩
      obtain ⟨c, -, hc⟩ := hb.1
      rw [hc, hc, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, smul_smul]
      apply hsm
      simp only [map_mul, map_pow, u0, u1, map_intCast, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero,
        one_pow, one_mul]
      rcases Nat.eq_zero_or_pos (w - (i : ℕ)) with h | h
      · have : (i : ℕ) = w := by have := i.2; omega
        rw [this]
      · rw [zero_pow h.ne', mul_zero, mul_zero]
    | zero => simp
    | add x y _ _ hx hy => exact ⟨by rw [map_add, hx.1, hy.1], by simp only [Pi.add_apply, map_add, hx.2, hy.2, smul_add]⟩
    | smul a x _ hx => exact ⟨by rw [map_smul, hx.1], by simp only [Pi.smul_apply, map_smul, hx.2, smul_comm a]⟩
  have e1 : X.kmap l (X.sl (ofSL γ)).toRingEquiv (b u) = b ![1, 0] := by
    have := congrFun key.1 ![1, 0]
    rw [← toGQ_coe_eq]
    exact this
  rw [← hf, ← e1]
  refine (GlobalTheory.KZ.H3.cls_props Ω ε X l n).2.2.2.2.2.1 _ _ _ ?_
  rw [key.2, hg, hf, ← Int.cast_pow, Int.cast_smul_eq_zsmul]

theorem exists_central : ∀ (N l n M : ℕ), l.Prime → ¬ l ∣ N → 1 ≤ n → 0 < M → N * l ^ n ∣ M →
    ∃ z : SL(2, ℤ), z ∈ CongruenceSubgroup.Gamma1 N ∧ z ∈ CongruenceSubgroup.Gamma0 l ∧
      -z ∈ CongruenceSubgroup.Gamma (l ^ n) ∧ ((en z 0 0 : ℤ) : ZMod (l ^ n)) = -1 ∧ ((en z 1 0 : ℤ) : ZMod (l ^ n)) = 0 ∧
      ∀ γ : SL(2, ℤ), z * γ * z⁻¹ * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  intro N l n M hl hlN hn hM hd
  obtain ⟨v, A, hA, hMe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.ne_one
  have cA : Nat.Coprime l A := (Nat.Prime.coprime_iff_not_dvd hl).2 hA
  have cN : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
  have dN : N ∣ M := (dvd_mul_right _ _).trans hd
  have dL : l ^ n ∣ M := (dvd_mul_left _ _).trans hd
  have dl : l ∣ M := (dvd_pow_self l (by omega)).trans dL
  have dNA : N ∣ A := (cN.symm.pow_right v).dvd_of_dvd_mul_left (hMe ▸ dN)
  have dLv : l ^ n ∣ l ^ v := (cA.pow_left n).dvd_of_dvd_mul_right (hMe ▸ dL)
  obtain ⟨a, b, hab⟩ : IsCoprime ((l ^ v : ℕ) : ℤ) (A : ℤ) := Nat.isCoprime_iff_coprime.2 (cA.pow_left v)
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = 1 - 2 * b * A := ⟨_, rfl⟩
  have hx' : x = -1 + 2 * a * ((l ^ v : ℕ) : ℤ) := by rw [hx]; linear_combination (-2) * hab
  have hMz : (M : ℤ) = ((l ^ v : ℕ) : ℤ) * A := by exact_mod_cast hMe
  obtain ⟨t, ht⟩ : ∃ t : ℤ, x * x = 1 + t * M :=
    ⟨-4 * a * b, by rw [hMz]; linear_combination (x + 1) * hx + (-2 * b * A) * hx'⟩
  have zM : ∀ {D : ℕ}, D ∣ M → (M : ZMod D) = 0 := fun h => (ZMod.natCast_eq_zero_iff _ _).2 h
  have xN : (x : ZMod N) = 1 := by
    rw [hx]; simp [(ZMod.natCast_eq_zero_iff _ _).2 dNA]
  have xL : (x : ZMod (l ^ n)) = -1 := by
    rw [hx', Int.cast_add, Int.cast_mul, Int.cast_natCast, (ZMod.natCast_eq_zero_iff _ _).2 dLv]; simp
  let z : SL(2, ℤ) := ⟨!![x, -t ^ 2 * M; M, x * (1 - t * M)], by
    rw [Matrix.det_fin_two_of]; linear_combination (1 - t * M) * ht⟩
  have z00 : z 0 0 = x := rfl
  have z01 : z 0 1 = -t ^ 2 * M := rfl
  have z10 : z 1 0 = M := rfl
  have z11 : z 1 1 = x * (1 - t * M) := rfl
  refine ⟨z, ?_, ?_, ?_, ?_, ?_, fun γ => ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem, z00, z11, z10]
    simp [xN, zM dN]
  · rw [CongruenceSubgroup.Gamma0_mem, z10]
    simp [zM dl]
  · rw [CongruenceSubgroup.Gamma_mem]
    simp [z00, z01, z10, z11, xL, zM dL]
  · exact xL
  · exact (Int.cast_natCast M).trans (zM dL)
  · rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, z00, z01, z10, z11, mul_comm]

def rhoH {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) :
    H →* (X.K ≃ₐ[Ω] X.K) where
  toFun γ := X.sl (ofSL ((γ : SL(2, ℤ))⁻¹))
  map_one' := by ext x; simp [X.sl_one]
  map_mul' γ γ' := by
    ext x
    simp only [Subgroup.coe_mul, mul_inv_rev, map_mul, X.sl_mul, AlgEquiv.mul_apply]

theorem rhoH_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (γ : H)
    (x : X.K) : rhoH X H γ x = X.sl (ofSL ((γ : SL(2, ℤ))⁻¹)) x := rfl

theorem exists_invariant_lift : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ f : X.Kˣ, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧ AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧ (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n)) := by
  intro Ω _ _ _ ε X N l _ hl2 hlN hN n w hw b hb
  have P := fun n => GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨f₀, hf₀⟩ := (P n).1 (AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩⟩
    rw [← hf₀, (P 0).2.1]
    exact ⟨f₀, by simp⟩
  have hlp : l.Prime := Fact.out
  set m := l ^ n with hm
  have hmodd : Odd m := (hlp.odd_of_ne_two hl2).pow
  set Γ' := CongruenceSubgroup.Gamma1 (N * l ^ n) with hΓ'
  have hσ1 : ∀ γ ∈ Γ', ∃ h : X.K, X.sl (ofSL γ) (f₀ : X.K) = f₀ * h ^ m := by
    intro γ hγ
    obtain ⟨hg, h0, h1⟩ := mem_Gam_of_mem_gamma1 N l n hn γ hγ
    have e := cls_eq_of_mem_Gam Ω ε X N l w n b hb f₀ hf₀.symm γ hg 1 (by rw [h0]; simp) h1 f₀ (by rw [one_pow, one_smul])
    obtain ⟨g, hg⟩ := ((P n).2.1 _ _).1 e.symm
    exact ⟨g, by simpa using congrArg Units.val hg⟩
  obtain ⟨M, hM0, hDM, hfM, hhM⟩ :=
    exists_uniform_level Ω ε X Γ' m (N * l ^ n) (Nat.mul_pos hN (pow_pos hlp.pos n)) f₀ hσ1
  obtain ⟨z, hz1, hz0, hzl, hz00, hz10, hzc⟩ := exists_central N l n M hlp hlN hn hM0 hDM
  have hkz : ∀ f : X.Kˣ, AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f →
      ∃ k : X.K, X.sl (ofSL z) (f : X.K) * f = k ^ m := by
    intro f hf
    have e := cls_eq_of_mem_Gam Ω ε X N l w n b hb f hf z ⟨hz1, hz0⟩ (-1) (by rw [hz00]; simp) hz10 f⁻¹ (by
      rw [hw.neg_one_pow, neg_one_smul, eq_neg_iff_add_eq_zero, ← (P n).2.2.1, inv_mul_cancel, (P n).2.2.2.1])
    obtain ⟨g, hg⟩ := ((P n).2.1 _ _).1 e
    rw [map_inv, eq_inv_mul_iff_mul_eq] at hg
    exact ⟨g, by simpa using congrArg Units.val hg⟩
  have hΓM : CongruenceSubgroup.Gamma M ≤ Γ' := gamma_le_gamma1 _ _ hDM
  have hzn : ∀ γ ∈ Γ', z * γ * z⁻¹ ∈ Γ' := by
    intro γ hγ
    have e : z * γ * z⁻¹ = (z * γ * z⁻¹ * γ⁻¹) * γ := by group
    rw [e]; exact Γ'.mul_mem (hΓM (hzc γ)) hγ
  haveI : NeZero M := ⟨hM0.ne'⟩

  have hfix : ∀ x : X.K, (∀ δ ∈ (CongruenceSubgroup.Gamma M).subgroupOf Γ', rhoH X Γ' δ x = x) →
      ∀ ρ' ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL ρ') x = x := by
    intro x hx ρ' hρ'
    have := hx ⟨ρ'⁻¹, hΓM (inv_mem hρ')⟩ (by simpa [Subgroup.mem_subgroupOf] using inv_mem hρ')
    simpa [rhoH_apply] using this
  obtain ⟨k₀, hk₀⟩ := hkz f₀ hf₀.symm
  obtain ⟨M₂, hM₂, hk₂⟩ := X.level k₀
  haveI : NeZero M₂ := ⟨hM₂.ne'⟩
  obtain ⟨u, hu0, hu⟩ := exists_invariant_rep Ω X.K Γ' (rhoH X Γ') ((CongruenceSubgroup.Gamma M).subgroupOf Γ') (X.sl (ofSL z)) m hmodd
    (f₀ : X.K) f₀.ne_zero
    (fun δ hδ => by rw [rhoH_apply]; exact hfM _ (inv_mem (Subgroup.mem_subgroupOf.1 hδ)))
    (fun γ => by
      obtain ⟨h, hh1, hh2⟩ := hhM _ (inv_mem γ.2)
      exact ⟨h, fun δ hδ => by rw [rhoH_apply]; exact hh1 _ (inv_mem (Subgroup.mem_subgroupOf.1 hδ)),
        by rw [rhoH_apply]; exact hh2⟩)
    (fun x hx γ => by
      have hx' := hfix x hx
      rw [rhoH_apply, rhoH_apply, ← X.sl_mul (ofSL _) (ofSL z), ← X.sl_mul (ofSL z) (ofSL _), ← map_mul, ← map_mul]
      have e : z * (γ : SL(2, ℤ))⁻¹ = (z * (γ : SL(2, ℤ))⁻¹ * z⁻¹ * (γ : SL(2, ℤ))⁻¹⁻¹) * ((γ : SL(2, ℤ))⁻¹ * z) := by
        group
      rw [e, map_mul ofSL (z * (γ : SL(2, ℤ))⁻¹ * z⁻¹ * (γ : SL(2, ℤ))⁻¹⁻¹), X.sl_mul, hx' _ (hzc _)])
    k₀ hk₀ ((CongruenceSubgroup.Gamma M₂).subgroupOf Γ')
    (fun δ hδ => by rw [rhoH_apply]; exact hk₂ _ (inv_mem (Subgroup.mem_subgroupOf.1 hδ)))

  set U : X.Kˣ := Units.mk0 u hu0 with hU
  set F : X.Kˣ := f₀ * U ^ m with hF
  have hFinv : ∀ γ ∈ Γ', X.sl (ofSL γ) (F : X.K) = F := by
    intro γ hγ
    have := hu ⟨γ⁻¹, inv_mem hγ⟩
    rw [rhoH_apply] at this
    simpa [hF, hU] using this
  have hFcls : X.cls l n F = X.cls l n f₀ := ((P n).2.1 _ _).2 ⟨U, rfl⟩
  have hF' : AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n F := by rw [hFcls]; exact hf₀.symm
  obtain ⟨k, hk⟩ := hkz F hF'
  set sF := X.sl (ofSL z) (F : X.K) with hsF
  have hF0 : (F : X.K) ≠ 0 := F.ne_zero
  have hsF0 : sF ≠ 0 := by rw [hsF]; exact (map_ne_zero _).2 hF0
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hlp.ne_zero)] at hk
    exact mul_ne_zero hsF0 hF0 hk
  obtain ⟨e, he⟩ := hmodd
  set Kk : X.Kˣ := Units.mk0 k hk0 with hKk
  set F2 : X.Kˣ := F * (F * Kk⁻¹ ^ (e + 1)) ^ m with hF2
  have hF2eq : (F2 : X.K) = ((F : X.K) / sF) ^ (e + 1) := by
    have hs : sF = k ^ m / F := eq_div_of_mul_eq hF0 hk
    rw [hs, hF2]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hKk, Units.val_mk0]
    rw [he]
    field_simp
    ring
  have hsFinv : ∀ γ ∈ Γ', X.sl (ofSL γ) sF = sF := by
    intro γ hγ
    rw [hsF, ← X.sl_mul, ← map_mul]
    have e1 : z * γ = (z * γ * z⁻¹) * z := by group
    rw [e1, map_mul ofSL (z * γ * z⁻¹), X.sl_mul, hFinv _ (hzn γ hγ)]
  refine ⟨F2, fun γ hγ => ?_, by rw [hF'] ; exact ((P n).2.1 _ _).2 ⟨_, rfl⟩ |>.symm, ?_⟩
  · rw [hF2eq, map_pow, map_div₀, hFinv γ hγ, hsFinv γ hγ]
  · intro δ hδ hδl
    have hcop : Nat.Coprime N (l ^ n) := (((Nat.Prime.coprime_iff_not_dvd hlp).2 hlN).symm).pow_right n
    have m1 : z⁻¹ * δ ∈ Γ' := gamma1_inf_le N (l ^ n) hcop (Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hz1) hδ, by
      have e1 : z⁻¹ * δ = (-z)⁻¹ * (-δ) := by
        rw [eq_inv_mul_iff_mul_eq, neg_mul, mul_inv_cancel_left]
      rw [e1]; exact mul_mem (inv_mem hzl) hδl⟩)
    have m2 : z * δ ∈ Γ' := gamma1_inf_le N (l ^ n) hcop (Subgroup.mem_inf.2 ⟨mul_mem hz1 hδ, by
      rw [← neg_mul_neg]; exact mul_mem hzl hδl⟩)
    have a1 : X.sl (ofSL δ) (F : X.K) = sF := by
      rw [← hsFinv _ m1, hsF, ← X.sl_mul, ← map_mul, mul_inv_cancel_left]
    have a2 : X.sl (ofSL δ) sF = F := by
      rw [hsF, ← X.sl_mul, ← map_mul, hFinv _ m2]
    refine ⟨1, fun γ _ => map_one _, ?_⟩
    rw [hF2eq, map_pow, map_div₀, a1, a2, ← mul_pow, div_mul_div_cancel₀ hsF0, div_self hF0, one_pow, one_pow]

end GlobalTheory.ThLift
