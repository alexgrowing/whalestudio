import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RankOneClasses

open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [StarRing E] in
theorem ne_bot_of_isLattice {L : Submodule (𝓞 E) E} (h : Submodule.IsLattice E L) : L ≠ ⊥ := by
  intro hb
  have := h.span_eq_top
  rw [hb] at this
  simp at this

noncomputable def latUnit (L : Submodule (𝓞 E) E) (h : Submodule.IsLattice E L) :
    (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  Units.mk0 (⟨L, FractionalIdeal.isFractional_of_fg h.fg⟩ : FractionalIdeal (𝓞 E)⁰ E) (by
    intro h0
    exact ne_bot_of_isLattice h (FractionalIdeal.coeToSubmodule_eq_bot.mpr h0))

omit [StarRing E] in
theorem exists_scale {L M : Submodule (𝓞 E) E} (hL : Submodule.IsLattice E L)
    (hM : Submodule.IsLattice E M)
    (h : (QuotientGroup.mk (latUnit L hL) :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range) =
      QuotientGroup.mk (latUnit M hM)) :
    ∃ a : E, a ≠ 0 ∧ ∀ y, a * y ∈ M ↔ y ∈ L := by
  obtain ⟨a, ha⟩ := QuotientGroup.eq.mp h
  have h1 : latUnit M hM = toPrincipalIdeal (𝓞 E) E a * latUnit L hL := by
    rw [ha, mul_comm, mul_inv_cancel_left]
  have h2 : ((latUnit M hM : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (a : E) * (latUnit L hL : (FractionalIdeal (𝓞 E)⁰ E)ˣ) := by
    rw [h1, Units.val_mul, coe_toPrincipalIdeal]
  refine ⟨a, a.ne_zero, fun y => ?_⟩
  have h3 : (a : E) * y ∈ M ↔ (a : E) * y ∈
      ((latUnit M hM : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) := Iff.rfl
  rw [h3, h2, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, he⟩
    rw [mul_left_cancel₀ a.ne_zero he]
    exact hz
  · intro hy
    exact ⟨y, hy, rfl⟩

def idealOf (β : E) (L : Submodule (𝓞 E) E) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {t | ∃ x ∈ L, ∃ y ∈ L, t = star x * β * y}

theorem idealOf_fg (β : E) {L : Submodule (𝓞 E) E} (h : Submodule.IsLattice E L) :
    (idealOf β L).FG := by
  obtain ⟨d, hd, hdL⟩ : IsFractional (𝓞 E)⁰ L := FractionalIdeal.isFractional_of_fg h.fg
  have hd0 : (d : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hd
  have hs0 : star (d : E) ≠ 0 := by simpa using hd0
  have hle : idealOf β L ≤ Submodule.span (𝓞 E) {(star (d : E))⁻¹ * β * (d : E)⁻¹} := by
    refine Submodule.span_le.mpr ?_
    rintro t ⟨x, hx, y, hy, rfl⟩
    obtain ⟨p, hp⟩ := hdL x hx
    obtain ⟨q, hq⟩ := hdL y hy
    have hi : IsIntegral ℤ (star (p : E)) :=
      p.isIntegral_coe.map (starRingEnd E).toIntAlgHom
    let p' : 𝓞 E := ⟨star (p : E), hi⟩
    refine Submodule.mem_span_singleton.mpr ⟨p' * q, ?_⟩
    have hp' : (p : E) = d * x := hp
    have hq' : (q : E) = d * y := hq
    change (star (p : E) * (q : E)) * _ = _
    rw [hp', hq', star_mul']
    field_simp
  exact Submodule.FG.of_le (Submodule.fg_span_singleton _) hle

theorem idealOf_ne_bot {β : E} (hβ : β ≠ 0) {L : Submodule (𝓞 E) E}
    (h : Submodule.IsLattice E L) : idealOf β L ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff L).mp (ne_bot_of_isLattice h)
  refine (Submodule.ne_bot_iff _).mpr ⟨star x * β * x, Submodule.subset_span ⟨x, hx, x, hx, rfl⟩, ?_⟩
  simp [hx0, hβ]

theorem mul_mem_idealOf {β γ t a : E} {L M : Submodule (𝓞 E) E}
    (h : ∀ y ∈ L, a * y ∈ M) (ht : star a * γ * a = t * β) :
    ∀ z ∈ idealOf β L, t • z ∈ idealOf γ M := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * x, h x hx, a * y, h y hy, ?_⟩
    rw [smul_eq_mul, star_mul']
    linear_combination (-(star x * y)) * ht
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem exists_unit {β γ a : E} (hβ : β ≠ 0) (hγ : γ ≠ 0) {L M : Submodule (𝓞 E) E}
    (hL : Submodule.IsLattice E L) (ha : a ≠ 0) (h : ∀ y, a * y ∈ M ↔ y ∈ L)
    (hN : idealOf β L = idealOf γ M) :
    ∃ u : (𝓞 E)ˣ, star a * γ * a * ((u : 𝓞 E) : E) = β := by
  have hs : star a ≠ 0 := by simpa using ha
  have h1 : ∀ z ∈ idealOf β L, (star a * γ * a / β) • z ∈ idealOf β L := by
    intro z hz
    have := mul_mem_idealOf (γ := γ) (t := star a * γ * a / β) (fun y hy => (h y).mpr hy)
      (by field_simp) z hz
    rwa [← hN] at this
  have h2 : ∀ z ∈ idealOf β L, (β / (star a * γ * a)) • z ∈ idealOf β L := by
    intro z hz
    rw [hN] at hz
    exact mul_mem_idealOf (a := a⁻¹) (fun y hy => (h _).mp (by rwa [mul_inv_cancel_left₀ ha]))
      (by rw [star_inv₀]; field_simp) z hz
  have i1 := isIntegral_trans (R := ℤ) _ (isIntegral_of_smul_mem_submodule _ (idealOf_ne_bot hβ hL)
    (idealOf_fg β hL) _ h1)
  have i2 := isIntegral_trans (R := ℤ) _ (isIntegral_of_smul_mem_submodule _ (idealOf_ne_bot hβ hL)
    (idealOf_fg β hL) _ h2)
  refine ⟨⟨⟨_, i2⟩, ⟨_, i1⟩, ?_, ?_⟩, ?_⟩
  · apply RingOfIntegers.ext
    change β / (star a * γ * a) * (star a * γ * a / β) = 1
    field_simp
  · apply RingOfIntegers.ext
    change (star a * γ * a / β) * (β / (star a * γ * a)) = 1
    field_simp
  · change star a * γ * a * (β / (star a * γ * a)) = β
    field_simp

noncomputable def even_im_hermitian_sub (u : (𝓞 E)ˣ) : Fin (Units.rank E) → ZMod 2 :=
  fun i => (((Units.basisModTorsion E).repr (Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E)) i : ℤ) : ZMod 2)

omit [StarRing E] in
theorem exists_sq_of_parity {u w : (𝓞 E)ˣ} (h : even_im_hermitian_sub u = even_im_hermitian_sub w) :
    ∃ (ζ : (𝓞 E)ˣ) (v : (𝓞 E)ˣ), ζ ∈ Units.torsion E ∧ u = w * ζ * v ^ 2 := by
  have hd : ∀ i, ∃ k : ℤ,
      (Units.basisModTorsion E).repr (Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E)) i -
      (Units.basisModTorsion E).repr (Additive.ofMul (w : (𝓞 E)ˣ ⧸ Units.torsion E)) i = 2 * k := by
    intro i
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).mp (congrFun h i).symm
  choose k hk using hd
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective
    (Additive.toMul ((Units.basisModTorsion E).equivFun.symm k))
  have hv' : Additive.ofMul (v : (𝓞 E)ˣ ⧸ Units.torsion E) =
      (Units.basisModTorsion E).equivFun.symm k := by rw [hv]; rfl
  have he : Additive.ofMul (u : (𝓞 E)ˣ ⧸ Units.torsion E) =
      Additive.ofMul (w : (𝓞 E)ˣ ⧸ Units.torsion E) +
        (2 : ℤ) • Additive.ofMul (v : (𝓞 E)ˣ ⧸ Units.torsion E) := by
    apply (Units.basisModTorsion E).equivFun.injective
    rw [map_add, map_smul, hv', LinearEquiv.apply_symm_apply]
    funext i
    simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hk i
  have he' : ((w * v ^ 2 : (𝓞 E)ˣ) : (𝓞 E)ˣ ⧸ Units.torsion E) = u := by
    apply Additive.ofMul.injective
    rw [he, QuotientGroup.mk_mul, QuotientGroup.mk_pow, ofMul_mul, ofMul_pow, two_nsmul, two_zsmul]
  refine ⟨(w * v ^ 2)⁻¹ * u, v, QuotientGroup.eq.mp he', ?_⟩
  rw [mul_right_comm, mul_inv_cancel_left]

theorem eq_of_norm_eq (φ : E →+* ℂ) (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) {A B : E}
    (hA : star A = A) (hB : star B = B) (pA : 0 < (φ A).re) (pB : 0 < (φ B).re)
    (h : ‖φ A‖ = ‖φ B‖) : A = B := by
  apply φ.injective
  have a1 : ((φ A).re : ℂ) = φ A := Complex.conj_eq_iff_re.mp (by rw [← hφ, hA])
  have b1 : ((φ B).re : ℂ) = φ B := Complex.conj_eq_iff_re.mp (by rw [← hφ, hB])
  rw [← a1, ← b1, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg pA.le,
    Real.norm_of_nonneg pB.le] at h
  rw [← a1, ← b1, h]

theorem card_classes_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ N : Submodule (𝓞 E) E, ENat.card (Quot (fun X Y : {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2)) ≤ ((classNumber E * 2 ^ Formalism.HermitianLatticesTheory.fDeg E : ℕ) : ENat) := by
  intro E _ _ _ hE N
  classical
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hφ := hE.2.1 φ
  set S := {X : E × Submodule (𝓞 E) E // star X.1 = X.1 ∧ (∀ φ : E →+* ℂ, 0 < (φ X.1).re) ∧ Submodule.IsLattice E X.2 ∧ Submodule.span (𝓞 E) {t | ∃ x ∈ X.2, ∃ y ∈ X.2, t = star x * X.1 * y} = N} with hS
  have hne : ∀ X : S, X.1.1 ≠ 0 := by
    intro X h0
    have := X.2.2.1 φ
    rw [h0] at this
    simp at this
  let cls : S → (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range :=
    fun X => QuotientGroup.mk (latUnit X.1.2 X.2.2.2.1)
  let base : S → S := fun X => Classical.choose (⟨X, rfl⟩ : ∃ B, cls B = cls X)
  have hbase : ∀ X, cls (base X) = cls X := fun X =>
    Classical.choose_spec (⟨X, rfl⟩ : ∃ B, cls B = cls X)
  have hbase' : ∀ X Y, cls X = cls Y → base X = base Y := by
    intro X Y h
    simp only [base, h]
  have hex : ∀ X : S, ∃ (a : E) (u : (𝓞 E)ˣ), a ≠ 0 ∧ (∀ y, a * y ∈ (base X).1.2 ↔ y ∈ X.1.2) ∧
      star a * (base X).1.1 * a * ((u : 𝓞 E) : E) = X.1.1 := by
    intro X
    obtain ⟨a, ha, h⟩ := exists_scale X.2.2.2.1 (base X).2.2.2.1 (hbase X).symm
    obtain ⟨u, hu⟩ := exists_unit (hne X) (hne (base X)) X.2.2.2.1 ha h
      (X.2.2.2.2.trans (base X).2.2.2.2.symm)
    exact ⟨a, u, ha, h, hu⟩
  choose a u ha hm hu using hex
  have key : ∀ X Y : S, cls X = cls Y → even_im_hermitian_sub (u X) = even_im_hermitian_sub (u Y) →
      ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧ ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2 := by
    intro X Y hc hp
    obtain ⟨ζ, v, hζ, hv⟩ := exists_sq_of_parity hp
    have hb := hbase' X Y hc
    have hv0 : ((v : 𝓞 E) : E) ≠ 0 := by simp
    have haY := ha Y
    have hsY : star (a Y) ≠ 0 := by simpa using haY
    have hc0 : a X * ((v : 𝓞 E) : E) / a Y ≠ 0 := div_ne_zero (mul_ne_zero (ha X) hv0) haY
    refine ⟨a X * ((v : 𝓞 E) : E) / a Y, hc0, ?_, fun y => ?_⟩
    · apply eq_of_norm_eq φ hφ _ X.2.1 _ (X.2.2.1 φ)
      · have e1 : star (a X * ((v : 𝓞 E) : E) / a Y) * Y.1.1 * (a X * ((v : 𝓞 E) : E) / a Y) =
            star (a X) * (base X).1.1 * a X * ((u Y : 𝓞 E) : E) *
              (star ((v : 𝓞 E) : E) * ((v : 𝓞 E) : E)) := by
          rw [← hu Y, hb, star_div₀, star_mul']
          field_simp
        have e2 : X.1.1 = star (a X) * (base X).1.1 * a X * ((u Y : 𝓞 E) : E) *
              (((ζ : 𝓞 E) : E) * (((v : 𝓞 E) : E) * ((v : 𝓞 E) : E))) := by
          rw [← hu X, hv]
          push_cast
          ring
        have e3 : ‖φ ((ζ : 𝓞 E) : E)‖ = 1 := by
          have := (Units.mem_torsion E).mp hζ (InfinitePlace.mk φ)
          rwa [InfinitePlace.apply] at this
        rw [e1, e2]
        simp only [map_mul, norm_mul, hφ, e3, Complex.norm_conj, one_mul]
      · rw [star_mul', star_mul', star_star, Y.2.1]; ring
      · have : φ (star (a X * ((v : 𝓞 E) : E) / a Y) * Y.1.1 * (a X * ((v : 𝓞 E) : E) / a Y)) =
            (Complex.normSq (φ (a X * ((v : 𝓞 E) : E) / a Y)) : ℂ) * φ Y.1.1 := by
          rw [map_mul, map_mul, hφ, Complex.normSq_eq_conj_mul_self]; ring
        rw [this, Complex.re_ofReal_mul]
        exact mul_pos (Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hc0)) (Y.2.2.1 φ)
    · rw [← hm Y, ← hm X, hb]
      have : a Y * (a X * ((v : 𝓞 E) : E) / a Y * y) = v • (a X * y) := by
        change _ = ((v : 𝓞 E) : E) * _
        field_simp
      rw [this]
      exact Submodule.smul_mem_iff_of_isUnit _ v.isUnit
  let g : Quot (fun X Y : S => ∃ c : E, c ≠ 0 ∧ star c * Y.1.1 * c = X.1.1 ∧
      ∀ y, c * y ∈ Y.1.2 ↔ y ∈ X.1.2) → ClassGroup (𝓞 E) × (Fin (Units.rank E) → ZMod 2) :=
    fun q => ((ClassGroup.equiv E).symm (cls q.out), even_im_hermitian_sub (u q.out))
  have hg : Function.Injective g := by
    intro q r h
    rw [← q.out_eq, ← r.out_eq]
    exact Quot.sound (key _ _ ((ClassGroup.equiv E).symm.injective (congrArg Prod.fst h))
      (congrArg Prod.snd h))
  refine (ENat.card_le_card_of_injective hg).trans ?_
  rw [ENat.card_eq_coe_fintype_card, Nat.cast_le, Fintype.card_prod, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))

end GlobalTheory.RankOneClasses
