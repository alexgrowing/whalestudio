import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import GroundTheory.GlobalFields.Adele.Approximation

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Loc Polynomial
open scoped nonZeroDivisors

section Gen

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {a b : K}

private theorem int_star {x : QuadraticAlgebra K a b} (h : IsIntegral O x) : IsIntegral O (star x) :=
  h.map_of_comp_eq (RingHom.id O) (starRingEnd (QuadraticAlgebra K a b)) (by
    ext r <;> simp [IsScalarTower.algebraMap_apply O K (QuadraticAlgebra K a b), starRingEnd_apply])

private theorem int_alg {r : K} : IsIntegral O (algebraMap K (QuadraticAlgebra K a b) r) ↔ IsIntegral O r :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (QuadraticAlgebra K a b)) (algebraMap K (QuadraticAlgebra K a b)).injective

private theorem int_trace {x : QuadraticAlgebra K a b} (h : IsIntegral O x) : IsIntegral O (QuadraticAlgebra.trace x) := by
  rw [← int_alg (a := a) (b := b), QuadraticAlgebra.algebraMap_trace_eq_add_star]
  exact h.add (int_star h)

private theorem int_norm {x : QuadraticAlgebra K a b} (h : IsIntegral O x) : IsIntegral O (QuadraticAlgebra.norm x) := by
  rw [← int_alg (a := a) (b := b), QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  exact h.mul (int_star h)

private theorem int_of {x : QuadraticAlgebra K a b} (ht : IsIntegral O (QuadraticAlgebra.trace x))
    (hn : IsIntegral O (QuadraticAlgebra.norm x)) : IsIntegral O x := by
  let t : integralClosure O (QuadraticAlgebra K a b) := ⟨_, int_alg.2 ht⟩
  let n : integralClosure O (QuadraticAlgebra K a b) := ⟨_, int_alg.2 hn⟩
  have h : IsIntegral (integralClosure O (QuadraticAlgebra K a b)) x := by
    refine ⟨X ^ 2 - C t * X + C n, by monicity!, ?_⟩
    have := QuadraticAlgebra.sq_sub_trace_smul_add_norm_eq_zero x
    rw [Algebra.smul_def] at this
    simpa [t, n] using this
  exact isIntegral_trans x h

private theorem ex_mult [IsDomain O] [IsFractionRing O K] (x : QuadraticAlgebra K a b) :
    ∃ c : K, c ≠ 0 ∧ IsIntegral O (c • x) := by
  have h : IsAlgebraic O x := (IsFractionRing.isAlgebraic_iff O K _).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  refine ⟨algebraMap O K y, by simpa using hy, ?_⟩
  rwa [algebraMap_smul]

private theorem int_map {A B : Type} [CommRing A] [CommRing B] [Algebra O B] (f : A →+* B) {x : A} (h : IsIntegral ℤ x) :
    IsIntegral O (f x) :=
  (map_isIntegral_int f h).tower_top

private theorem id1 (x : QuadraticAlgebra K a b) (d n p q : K) : x * ⟨d * n * p, d * n * q⟩ =
    d • x * (algebraMap _ _ (n * p) + algebraMap _ _ q * (⟨0, n⟩ : QuadraticAlgebra K a b)) := by
  ext <;> simp <;> ring

private theorem id2 (x : QuadraticAlgebra K a b) {d n : K} (k l : K) (hd : d ≠ 0) (hn : n ≠ 0) :
    x - ⟨d * n * k, d * n * l⟩ = ⟨d * (n * (x.re / (d * n) - k)), d * (n * (x.im / (d * n) - l))⟩ := by
  ext <;> simp <;> field_simp

private theorem cint_of {τ : K} {u : (Etau K τ)ˣ} (h : IsIntegral O (u : Etau K τ))
    (h' : IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) : u ∈ Cint O τ :=
  ⟨h.mul (int_star h'), h'.mul (by rw [inv_inv]; exact int_star h)⟩

private def quoH (τ : K) : (Etau K τ)ˣ →* Etau K τ where
  toFun := quo
  map_one' := by simp [quo]
  map_mul' a b := by simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring

private theorem norm_quo {τ : K} (z : (Etau K τ)ˣ) : QuadraticAlgebra.norm (quo z) = 1 := by
  rw [quo, map_mul, QuadraticAlgebra.norm_star, ← map_mul, Units.mul_inv, map_one]

private theorem scal_of [CharZero K] {τ : K} {z : (Etau K τ)ˣ} (h : quo z = 1) : z ∈ scalE τ := by
  have h1 : (z : Etau K τ) = star (z : Etau K τ) := by
    have := congrArg (· * star (z : Etau K τ)) h
    simpa only [quo, mul_assoc, ← star_mul, Units.mul_inv, star_one, mul_one, one_mul] using this
  have h2 : (z : Etau K τ).im = 0 := by
    have := congrArg QuadraticAlgebra.im h1
    rw [QuadraticAlgebra.im_star] at this
    linear_combination this / 2
  have h3 : (z : Etau K τ).re ≠ 0 := fun h0 => z.ne_zero (by ext <;> simp [h0, h2])
  exact ⟨Units.mk0 _ h3, Units.ext (by ext <;> simp [h2])⟩

private theorem map_quo {K' : Type} [Field K'] (f : K →+* K') {τ : K} (z : (Etau K τ)ˣ) (z' : (Etau K' (f τ))ˣ)
    (h : (z' : Etau K' (f τ)) = emap f τ z) : quo z' = emap f τ (quo z) := by
  have h1 : z' = Units.map (emap f τ : Etau K τ →* Etau K' (f τ)) z := Units.ext h
  have h2 : ∀ x, emap f τ (star x) = star (emap f τ x) := fun x => by ext <;> simp [emap]
  rw [quo, quo, map_mul, h2, h1, ← map_inv]
  rfl

private theorem relIndex_of_fin {G M : Type} [Group G] [Monoid M] (f : G →* M) (A B : Subgroup G) (S : Set M) (hS : S.Finite)
    (hB : ∀ z ∈ B, f z ∈ S) (hA : ∀ z, f z = 1 → z ∈ A) : A.relIndex B ≠ 0 := by
  haveI := hS.to_subtype
  let c : B ⧸ A.subgroupOf B → S := fun q => ⟨f q.out, hB _ q.out.2⟩
  have hc : Function.Injective c := fun p q h => by
    have h' : f p.out = f q.out := congrArg Subtype.val h
    rw [← p.out_eq', ← q.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    apply hA
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, ← h', ← map_mul, inv_mul_cancel, map_one]
  haveI := Finite.of_injective c hc
  exact Subgroup.index_ne_zero_of_finite

end Gen

private theorem index_of_classes (E : Type) [Field E] [NumberField E] {G : Type} [Group G] (H : Subgroup G) (P : G → E → Prop)
    (h0 : ∀ x, P x 0) (hadd : ∀ x a b, P x a → P x b → P x (a + b))
    (hmul : ∀ x r a, IsIntegral ℤ r → P x a → P x (r * a))
    (hfr : ∀ x, ∃ d : E, d ≠ 0 ∧ IsIntegral ℤ d ∧ ∀ a, P x a → IsIntegral ℤ (d * a))
    (hne : ∀ x, ∃ a, a ≠ 0 ∧ P x a)
    (hinj : ∀ x y (e : Eˣ), (∀ a, P y (a * e) ↔ P x a) → x⁻¹ * y ∈ H) : H.index ≠ 0 := by
  let L : G → Submodule (𝓞 E) E := fun x =>
    { carrier := {a | P x a}
      zero_mem' := h0 x
      add_mem' := fun {a b} ha hb => hadd x a b ha hb
      smul_mem' := fun r a ha => hmul x r a r.isIntegral_coe ha }
  have hL : ∀ x, IsFractional (𝓞 E)⁰ (L x) := fun x => by
    obtain ⟨d, hd, hi, h⟩ := hfr x
    refine ⟨⟨d, hi⟩, mem_nonZeroDivisors_of_ne_zero fun h' => hd (congrArg Subtype.val h'), fun a ha => ⟨⟨_, h a ha⟩, rfl⟩⟩
  let J : G → FractionalIdeal (𝓞 E)⁰ E := fun x => ⟨L x, hL x⟩
  have hL0 : ∀ x, J x ≠ 0 := fun x h => by
    obtain ⟨a, ha, hp⟩ := hne x
    have : a ∈ J x := hp
    rw [h] at this
    exact ha ((FractionalIdeal.mem_zero_iff _).1 this)
  haveI : Finite ((FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range) :=
    Finite.of_equiv _ (ClassGroup.equiv (R := 𝓞 E) E).toEquiv
  let c : G ⧸ H → (FractionalIdeal (𝓞 E)⁰ E)ˣ ⧸ (toPrincipalIdeal (𝓞 E) E).range := fun q =>
    QuotientGroup.mk (Units.mk0 _ (hL0 q.out))
  have hc : Function.Injective c := fun p q h => by
    obtain ⟨e, he⟩ := QuotientGroup.eq.1 h
    rw [eq_inv_mul_iff_mul_eq] at he
    have he' := congrArg Units.val he
    simp only [Units.val_mul, Units.val_mk0, coe_toPrincipalIdeal] at he'
    rw [← p.out_eq', ← q.out_eq', QuotientGroup.eq]
    refine hinj _ _ e fun a => ?_
    change a * e ∈ J q.out ↔ a ∈ J p.out
    rw [← he', mul_comm (J p.out), FractionalIdeal.mem_singleton_mul]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [mul_comm] at h
      rwa [mul_left_cancel₀ e.ne_zero h]
    · exact fun h => ⟨a, h, mul_comm _ _⟩
  haveI : Finite (G ⧸ H) := Finite.of_injective c hc
  exact Subgroup.index_ne_zero_of_finite

section Glo

variable {F : Type} [Field F] [NumberField F]

private theorem mem_of_int {v : Pl F} {k : Kv v} (h : IsIntegral (Ov v) k) : k ∈ v.adicCompletionIntegers F := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

private theorem int_of_mem {v : Pl F} {k : Kv v} (h : k ∈ v.adicCompletionIntegers F) : IsIntegral (Ov v) k :=
  isIntegral_algebraMap (x := (⟨k, h⟩ : Ov v))

private theorem glob_int {t : F} (h : ∀ v : Pl F, IsIntegral (Ov v) (cv v t)) : IsIntegral ℤ t := by
  obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t fun v => by
    rw [← GroundTheory.Global.coe_mem_adicCompletionIntegers_iff]
    have := mem_of_int (h v)
    simpa [HeightOneSpectrum.algebraMap_adicCompletion] using this
  exact y.isIntegral_coe

private theorem loc_int {t : F} (h : IsIntegral ℤ t) (v : Pl F) : IsIntegral (Ov v) (cv v t) :=
  int_map (cv v) h

private theorem approx (a : ∀ v : Pl F, Kv v) (h : ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers F) :
    ∃ k : F, ∀ v, IsIntegral (Ov v) (a v - cv v k) := by
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) (K := F) ⟨a, h⟩
  exact ⟨k, fun v => int_of_mem (hk v)⟩

private theorem den (k : F) : ∃ d : F, d ≠ 0 ∧ IsIntegral ℤ d ∧ IsIntegral ℤ (d * k) := by
  have h : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic k)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  refine ⟨y, by simpa using hy, isIntegral_algebraMap (x := y), by simpa using hi⟩

variable {τ : F}

private theorem loc_intE {e : Etau F τ} (h : IsIntegral ℤ e) (v : Pl F) : IsIntegral (Ov v) (emap (cv v) τ e) :=
  int_map (emap (cv v) τ) h

private theorem glob_intE {e : Etau F τ} (h : ∀ v : Pl F, IsIntegral (Ov v) (emap (cv v) τ e)) : IsIntegral ℤ e := by
  refine int_of (glob_int fun v => ?_) (glob_int fun v => ?_)
  · convert int_trace (h v) using 1
    simp [QuadraticAlgebra.trace_def, emap, map_ofNat]
  · convert int_norm (h v) using 1
    simp [QuadraticAlgebra.norm_def, emap]

private theorem denE (x : ∀ v : Pl F, Etau (Kv v) (cv v τ)) (h : ∀ᶠ v in Filter.cofinite, IsIntegral (Ov v) (x v)) :
    ∃ d : F, d ≠ 0 ∧ IsIntegral ℤ d ∧ ∀ v, IsIntegral (Ov v) (cv v d • x v) := by
  have h1 : ∀ v : Pl F, ∃ c : Kv v, c ≠ 0 ∧ IsIntegral (Ov v) (c • x v) ∧ (IsIntegral (Ov v) (x v) → c = 1) := fun v => by
    by_cases hv : IsIntegral (Ov v) (x v)
    · exact ⟨1, one_ne_zero, by rwa [one_smul], fun _ => rfl⟩
    · obtain ⟨c, hc, hi⟩ := ex_mult (O := Ov v) (x v)
      exact ⟨c, hc, hi, fun h => absurd h hv⟩
  choose c hc0 hci hc1 using h1
  obtain ⟨k, hk⟩ := approx (fun v => (c v)⁻¹) (h.mono fun v hv => by rw [hc1 v hv, inv_one]; exact one_mem _)
  obtain ⟨d, hd, hdi, hdk⟩ := den k
  refine ⟨d, hd, hdi, fun v => ?_⟩
  have h2 : IsIntegral (Ov v) (cv v d * (c v)⁻¹) := by
    have := ((loc_int hdi v).mul (hk v)).add (loc_int hdk v)
    rwa [map_mul, ← mul_add, sub_add_cancel] at this
  have := (int_alg.2 h2).mul (hci v)
  rwa [← Algebra.smul_def, smul_smul, mul_assoc, inv_mul_cancel₀ (hc0 v), mul_one] at this

private theorem den2 (x : ∀ v : Pl F, Etau (Kv v) (cv v τ)) (h : ∀ᶠ v in Filter.cofinite, IsIntegral (Ov v) (x v)) :
    ∃ d : F, d ≠ 0 ∧ IsIntegral ℤ d ∧ ∀ v (p q : Kv v), IsIntegral (Ov v) p → IsIntegral (Ov v) q →
      IsIntegral (Ov v) (x v * ⟨cv v d * p, cv v d * q⟩) := by
  obtain ⟨d, hd, hdi, hx⟩ := denE x h
  obtain ⟨n, hn, hni, hnt⟩ := den τ
  refine ⟨d * n, mul_ne_zero hd hn, hdi.mul hni, fun v p q hp hq => ?_⟩
  have hw : IsIntegral (Ov v) (⟨0, cv v n⟩ : Etau (Kv v) (cv v τ)) := by
    refine int_of ?_ ?_
    · have := loc_int hnt v
      rw [map_mul, mul_comm] at this
      simpa [QuadraticAlgebra.trace_def] using this
    · simpa [QuadraticAlgebra.norm_def] using (loc_int hni v).mul (loc_int hni v)
  have := (hx v).mul ((int_alg.2 ((loc_int hni v).mul hp)).add ((int_alg.2 hq).mul hw))
  rwa [map_mul, id1]

private theorem recover (x xi yi : ∀ v : Pl F, Etau (Kv v) (cv v τ)) (hx : ∀ v, xi v * x v = 1)
    (hxi : ∀ᶠ v in Filter.cofinite, IsIntegral (Ov v) (xi v)) (hyi : ∀ᶠ v in Filter.cofinite, IsIntegral (Ov v) (yi v))
    (h : ∀ e : Etau F τ, (∀ v, IsIntegral (Ov v) (xi v * emap (cv v) τ e)) → ∀ v, IsIntegral (Ov v) (yi v * emap (cv v) τ e))
    (v : Pl F) : IsIntegral (Ov v) (yi v * x v) := by
  classical
  obtain ⟨d, hd, hdi, hd'⟩ := den2 xi hxi
  obtain ⟨n, hn, hni, hn'⟩ := den2 yi hyi
  let b : ∀ w : Pl F, Etau (Kv w) (cv w τ) := Pi.single v (x v)
  have hb : ∀ᶠ w in Filter.cofinite, b w = 0 :=
    (Filter.eventually_cofinite_ne v).mono fun w hw => Pi.single_eq_of_ne hw _
  obtain ⟨k, hk⟩ := approx (fun w => (b w).re / cv w (d * n)) (hb.mono fun w hw => by simp [hw])
  obtain ⟨l, hl⟩ := approx (fun w => (b w).im / cv w (d * n)) (hb.mono fun w hw => by simp [hw])
  let e : Etau F τ := ⟨d * n * k, d * n * l⟩
  have hd0 : ∀ w : Pl F, cv w d ≠ 0 := fun w => (_root_.map_ne_zero _).2 hd
  have hn0 : ∀ w : Pl F, cv w n ≠ 0 := fun w => (_root_.map_ne_zero _).2 hn
  have e1 : ∀ w, b w - emap (cv w) τ e = ⟨cv w d * (cv w n * ((b w).re / cv w (d * n) - cv w k)),
      cv w d * (cv w n * ((b w).im / cv w (d * n) - cv w l))⟩ := fun w => by
    rw [map_mul, ← id2 _ _ _ (hd0 w) (hn0 w), ← map_mul, ← map_mul, ← map_mul]
    rfl
  have e2 : ∀ w, b w - emap (cv w) τ e = ⟨cv w n * (cv w d * ((b w).re / cv w (d * n) - cv w k)),
      cv w n * (cv w d * ((b w).im / cv w (d * n) - cv w l))⟩ := fun w => by
    rw [e1, mul_left_comm (cv w d), mul_left_comm (cv w d)]
  have h1 : ∀ w, IsIntegral (Ov w) (xi w * emap (cv w) τ e) := fun w => by
    have h2 := hd' w _ _ ((loc_int hni w).mul (hk w)) ((loc_int hni w).mul (hl w))
    rw [← e1] at h2
    have h3 : IsIntegral (Ov w) (xi w * b w) := by
      by_cases hw : w = v
      · subst hw
        rw [show b w = x w from Pi.single_eq_same _ _, hx]
        exact isIntegral_one
      · rw [show b w = 0 from Pi.single_eq_of_ne hw _, mul_zero]
        exact isIntegral_zero
    have := h3.sub h2
    rwa [← mul_sub, sub_sub_cancel] at this
  have h2 := hn' v _ _ ((loc_int hdi v).mul (hk v)) ((loc_int hdi v).mul (hl v))
  rw [← e2] at h2
  have := h2.add (h e h1 v)
  rwa [← mul_add, sub_add_cancel, show b v = x v from Pi.single_eq_same _ _] at this

private theorem ta_int (x : TA τ) : ∀ᶠ v in Filter.cofinite, IsIntegral (Ov v) (x.1 v : Etau (Kv v) (cv v τ)) :=
  Filter.Eventually.mono x.2 fun v hv => by
    obtain ⟨u, hu⟩ := hv
    rw [← hu]
    exact (u : integralClosure (Ov v) (Etau (Kv v) (cv v τ))).2

private theorem fin_quo [IsTotallyReal F] (hτ : IsCM τ) :
    {u : Etau F τ | IsIntegral ℤ u ∧ QuadraticAlgebra.norm u = 1}.Finite := by
  have hD : τ ^ 2 - 4 ≠ 0 := fun h => by
    obtain ⟨σ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have := hτ (IsTotallyReal.complexEmbedding_isReal σ).embedding
    simp [h] at this
  have key : ∀ u : Etau F τ, QuadraticAlgebra.norm u = 1 → QuadraticAlgebra.trace u ^ 2 - 4 = (τ ^ 2 - 4) * u.im ^ 2 := fun u hu => by
    rw [QuadraticAlgebra.norm_def] at hu
    rw [QuadraticAlgebra.trace_def]
    linear_combination 4 * hu
  have h1 := Embeddings.finite_of_norm_le F ℂ 2
  refine Set.Finite.of_finite_fibers (fun u : Etau F τ => QuadraticAlgebra.trace u) (h1.subset ?_) ?_
  · rintro _ ⟨u, ⟨hi, hu⟩, rfl⟩
    refine ⟨int_trace hi, fun σ => ?_⟩
    let ρ := (IsTotallyReal.complexEmbedding_isReal σ).embedding
    have h2 := congrArg ρ (key u hu)
    have h3 := hτ ρ
    rw [map_mul, map_pow, map_sub, map_pow, map_ofNat] at h2
    rw [← (IsTotallyReal.complexEmbedding_isReal σ).coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs]
    refine abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (ρ u.im)]) (by norm_num) |> abs_le.2
  · rintro _ ⟨u, ⟨-, hu⟩, rfl⟩
    refine (Set.toFinite {u, star u}).subset ?_
    rintro w ⟨⟨-, hw⟩, ht⟩
    have ht : QuadraticAlgebra.trace w = QuadraticAlgebra.trace u := ht
    have h2 : w.im ^ 2 = u.im ^ 2 := mul_left_cancel₀ hD (by rw [← key w hw, ← key u hu, ht])
    rw [QuadraticAlgebra.trace_def, QuadraticAlgebra.trace_def] at ht
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · left
      ext
      · rw [h] at ht; linear_combination ht / 2
      · exact h
    · right
      change w = star u
      ext
      · rw [h] at ht; rw [QuadraticAlgebra.re_star]; linear_combination ht / 2
      · exact h

private theorem mem_box {x : TA τ} :
    x ∈ ((rpg _ _).box fun v => Cint (Ov v) (cv v τ) : Subgroup (TA τ)) ↔ ∀ v, x.1 v ∈ Cint (Ov v) (cv v τ) := by
  rw [RPG.box, Subgroup.mem_iInf]
  rfl

private theorem part2 [IsTotallyReal F] (hτ : IsCM τ) (φ : (Etau F τ)ˣ →* TA τ) (hφ : IsDiagT τ φ) :
    (scalE τ).relIndex (((rpg _ _).box fun v => Cint (Ov v) (cv v τ)).comap φ) ≠ 0 := by
  refine relIndex_of_fin (quoH τ) _ _ _ (fin_quo hτ) (fun z hz => ⟨glob_intE fun v => ?_, norm_quo z⟩) fun z => scal_of
  have := (mem_box.1 (Subgroup.mem_comap.1 hz) v).1
  rwa [map_quo (cv v) z _ (hφ z v)] at this

private theorem part1 [IsTotallyReal F] (hτ : IsCM τ) (φ : (Etau F τ)ˣ →* TA τ) (hφ : IsDiagT τ φ) :
    (φ.range ⊔ (rpg _ _).box fun v => Cint (Ov v) (cv v τ)).index ≠ 0 := by
  haveI : Fact (∀ r : F, r ^ 2 ≠ -1 + τ * r) := ⟨fun r h => by
    obtain ⟨σ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h1 := hτ (IsTotallyReal.complexEmbedding_isReal σ).embedding
    rw [show τ ^ 2 - 4 = (2 * r - τ) ^ 2 by linear_combination (-4) * h, map_pow] at h1
    exact absurd h1 (not_lt.2 (sq_nonneg _))⟩
  haveI : NumberField (Etau F τ) := NumberField.of_module_finite F _
  have hsm : ∀ (v : Pl F) (d : F) (y : Etau (Kv v) (cv v τ)), emap (cv v) τ (algebraMap F _ d) * y = cv v d • y := fun v d y => by
    rw [Algebra.smul_def]
    rfl
  have hI : ∀ d : F, IsIntegral ℤ d → IsIntegral ℤ (algebraMap F (Etau F τ) d) := fun d => map_isIntegral_int _
  refine index_of_classes (Etau F τ) _
    (fun (x : TA τ) a => ∀ v, IsIntegral (Ov v) (((x⁻¹).1 v : Etau (Kv v) (cv v τ)) * emap (cv v) τ a)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x v
    rw [map_zero, mul_zero]
    exact isIntegral_zero
  · intro x a b ha hb v
    rw [map_add, mul_add]
    exact (ha v).add (hb v)
  · intro x r a hr ha v
    rw [map_mul, mul_left_comm]
    exact (loc_intE hr v).mul (ha v)
  · intro x
    obtain ⟨d, hd, hdi, h⟩ := denE _ (ta_int x)
    refine ⟨algebraMap F _ d, (_root_.map_ne_zero _).2 hd, hI d hdi, fun a ha => glob_intE fun v => ?_⟩
    have := (h v).mul (ha v)
    rwa [smul_mul_assoc, show (x⁻¹).1 v = (x.1 v)⁻¹ from rfl, Units.mul_inv_cancel_left, ← hsm, ← map_mul] at this
  · intro x
    obtain ⟨d, hd, hdi, h⟩ := denE _ (ta_int x⁻¹)
    refine ⟨algebraMap F _ d, (_root_.map_ne_zero _).2 hd, fun v => ?_⟩
    rw [mul_comm, hsm]
    exact h v
  · intro x y e h
    have h1 := recover (fun v => (x.1 v : Etau (Kv v) (cv v τ))) (fun v => (x⁻¹).1 v) (fun v => (y⁻¹ * φ e).1 v)
      (fun v => Units.inv_mul _) (ta_int _) (ta_int _) fun a ha v => by
        have := (h a).2 ha v
        rwa [map_mul, ← hφ, mul_comm (emap _ _ a), ← mul_assoc] at this
    have h2 := recover (fun v => ((y⁻¹ * φ e)⁻¹.1 v : Etau (Kv v) (cv v τ))) (fun v => (y⁻¹ * φ e).1 v) (fun v => (x⁻¹).1 v)
      (fun v => Units.mul_inv _) (ta_int _) (ta_int _) fun a ha => (h a).1 fun v => by
        rw [map_mul, ← hφ, mul_comm (emap _ _ a), ← mul_assoc]
        exact ha v
    have h3 : x⁻¹ * (y⁻¹ * φ e)⁻¹ ∈ ((rpg _ _).box fun v => Cint (Ov v) (cv v τ) : Subgroup (TA τ)) :=
      mem_box.2 fun v => cint_of (h2 v) (by
        have := h1 v
        rw [show (x⁻¹ * (y⁻¹ * φ e)⁻¹).1 v = (x.1 v)⁻¹ * ((y⁻¹ * φ e).1 v)⁻¹ from rfl, _root_.mul_inv_rev, inv_inv, inv_inv]
        exact this)
    have h4 : x⁻¹ * y = φ e * (x⁻¹ * (y⁻¹ * φ e)⁻¹) := Subtype.ext (funext fun v => by
      change (x.1 v)⁻¹ * y.1 v = (φ e).1 v * ((x.1 v)⁻¹ * ((y.1 v)⁻¹ * (φ e).1 v)⁻¹)
      rw [_root_.mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel_left])
    rw [h4]
    exact Subgroup.mul_mem_sup ⟨e, rfl⟩ h3

end Glo

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.massFin :
    UpperTheory.V.Z.Sym.Glob.MassFin :=
  fun _ _ _ _ _ hτ φ hφ => ⟨part1 hτ φ hφ, part2 hτ φ hφ⟩
