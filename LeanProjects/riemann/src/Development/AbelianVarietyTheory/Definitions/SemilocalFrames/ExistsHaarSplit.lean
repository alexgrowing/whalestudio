import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdeles

noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc MeasureTheory

namespace GlobalTheory.SgGlob.LocModel

section Alg
variable {K B : Type} [Field K] [ValuativeRel K] [CommRing B] [Algebra K B]

structure IsUnitGen (cj : B ≃ₐ[K] B) (θ : B) (t n : K) : Prop where
  inj : Function.Injective (algebraMap K B)
  gen : ∀ x : B, ∃ a b : K, x = algebraMap K B a + algebraMap K B b * θ
  tr : θ + cj θ = algebraMap K B t
  nm : θ * cj θ = algebraMap K B n
  t_int : t ∈ 𝒪[K]
  n_int : n ∈ 𝒪[K]
  disc_ne : t ^ 2 - 4 * n ≠ 0
  disc_inv : (t ^ 2 - 4 * n)⁻¹ ∈ 𝒪[K]

theorem int_algebraMap {a : K} (ha : a ∈ 𝒪[K]) : IsIntegral 𝒪[K] (algebraMap K B a) :=
  (isIntegral_algebraMap (R := 𝒪[K]) (A := K) (x := ⟨a, ha⟩)).algebraMap

theorem mem_of_int {a : K} (ha : IsIntegral 𝒪[K] a) : a ∈ 𝒪[K] := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪[K]) (K := K)).1 ha
  rw [← hy]; exact y.2

theorem int_cj (cj : B ≃ₐ[K] B) {x : B} (hx : IsIntegral 𝒪[K] x) : IsIntegral 𝒪[K] (cj x) :=
  hx.map (cj.restrictScalars 𝒪[K]).toAlgHom

namespace IsUnitGen
variable {cj : B ≃ₐ[K] B} {θ : B} {t n : K} (h : IsUnitGen cj θ t n)
include h

theorem mem_of_int' {a : K} (ha : IsIntegral 𝒪[K] (algebraMap K B a)) : a ∈ 𝒪[K] :=
  mem_of_int ((isIntegral_algebraMap_iff h.inj).1 ha)

theorem cj_gen : cj θ = algebraMap K B t - θ := by rw [← h.tr]; ring

theorem delta_sq : (θ - cj θ) ^ 2 = algebraMap K B (t ^ 2 - 4 * n) := by
  simp only [map_sub, map_pow, map_mul, map_ofNat, ← h.tr, ← h.nm]; ring

theorem cj_cj (x : B) : cj (cj x) = x := by
  obtain ⟨a, b, rfl⟩ := h.gen x
  simp only [map_add, map_mul, AlgEquiv.commutes]
  rw [h.cj_gen, map_sub, AlgEquiv.commutes, h.cj_gen]; ring

theorem sub_cj (a b : K) : (algebraMap K B a + algebraMap K B b * θ - cj (algebraMap K B a + algebraMap K B b * θ))
    * (θ - cj θ) = algebraMap K B (b * (t ^ 2 - 4 * n)) := by
  rw [map_mul (algebraMap K B) b, ← h.delta_sq]
  simp only [map_add, map_mul, AlgEquiv.commutes]; ring

theorem cj_fix (x : B) : cj x = x ↔ ∃ a : K, algebraMap K B a = x := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := h.gen x
    have e := h.sub_cj a b
    rw [hx, sub_self, zero_mul, ← map_zero (algebraMap K B)] at e
    have hb : b = 0 := (mul_eq_zero.1 (h.inj e).symm).resolve_right h.disc_ne
    exact ⟨a, by simp [hb]⟩
  · rintro ⟨a, rfl⟩; exact cj.commutes a

theorem int_gen : IsIntegral 𝒪[K] θ := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨t, h.t_int⟩ * Polynomial.X + Polynomial.C ⟨n, h.n_int⟩, by monicity!, ?_⟩
  have e1 : algebraMap 𝒪[K] B ⟨t, h.t_int⟩ = algebraMap K B t := rfl
  have e2 : algebraMap 𝒪[K] B ⟨n, h.n_int⟩ = algebraMap K B n := rfl
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, e1, e2, ← h.tr, ← h.nm]
  ring

theorem int_delta : IsIntegral 𝒪[K] (θ - cj θ) := h.int_gen.sub (int_cj cj h.int_gen)

theorem mem_of_mul_disc {b : K} (hb : b * (t ^ 2 - 4 * n) ∈ 𝒪[K]) : b ∈ 𝒪[K] := by
  have := mul_mem hb h.disc_inv
  rwa [mul_inv_cancel_right₀ h.disc_ne] at this

theorem int_iff (a b : K) : IsIntegral 𝒪[K] (algebraMap K B a + algebraMap K B b * θ) ↔ a ∈ 𝒪[K] ∧ b ∈ 𝒪[K] := by
  constructor
  · intro hx
    have hb : b ∈ 𝒪[K] := by
      apply h.mem_of_mul_disc
      apply h.mem_of_int'
      rw [← h.sub_cj a b]
      exact (hx.sub (int_cj cj hx)).mul h.int_delta
    refine ⟨h.mem_of_int' ?_, hb⟩
    have := hx.sub ((int_algebraMap hb).mul h.int_gen)
    simpa using this
  · rintro ⟨ha, hb⟩
    exact (int_algebraMap ha).add ((int_algebraMap hb).mul h.int_gen)

theorem reduced : IsReduced B := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨a, b, rfl⟩ := h.gen x
  have h1 : IsNilpotent (algebraMap K B (b * (t ^ 2 - 4 * n))) := by
    rw [← h.sub_cj a b]
    exact (Commute.all _ _).isNilpotent_mul_right ((Commute.all _ _).isNilpotent_sub hx (hx.map cj))
  have hb : b = 0 := (mul_eq_zero.1 ((IsNilpotent.map_iff h.inj).1 h1).eq_zero).resolve_right h.disc_ne
  subst hb
  simp only [map_zero, zero_mul, add_zero] at hx ⊢
  rw [((IsNilpotent.map_iff h.inj).1 hx).eq_zero, map_zero]

theorem trace_eq [CharZero K] (hr : Module.finrank K B = 2) (x : B) :
    algebraMap K B (Algebra.trace K B x) = x + cj x := by
  have h1 : ∀ a : K, Algebra.trace K B (algebraMap K B a) = 2 * a := fun a => by
    rw [Algebra.trace_algebraMap, hr]; simp
  have h2 : Algebra.trace K B θ = t := by
    have e := congrArg (Algebra.trace K B) h.tr
    rw [map_add, Algebra.trace_eq_of_algEquiv cj, h1] at e
    linear_combination e / 2
  obtain ⟨a, b, rfl⟩ := h.gen x
  rw [map_add, h1, ← Algebra.smul_def, map_smul, h2, Algebra.smul_def, Algebra.smul_def]
  simp only [map_add, map_mul, AlgEquiv.commutes, map_ofNat, Algebra.algebraMap_self, RingHom.id_apply, ← h.tr]
  ring

theorem trace_dual [CharZero K] (hr : Module.finrank K B = 2) (x : B) :
    (∀ y : B, IsIntegral 𝒪[K] y → Algebra.trace K B (x * y) ∈ 𝒪[K]) ↔ IsIntegral 𝒪[K] x := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := h.gen x
    rw [h.int_iff]
    have e1 := h.trace_eq hr ((algebraMap K B a + algebraMap K B b * θ) * (θ - cj θ))
    have e2 := h.trace_eq hr ((algebraMap K B a + algebraMap K B b * θ) * (cj θ * (θ - cj θ)))
    have f1 : Algebra.trace K B ((algebraMap K B a + algebraMap K B b * θ) * (θ - cj θ)) = b * (t ^ 2 - 4 * n) := by
      apply h.inj
      rw [e1, map_mul (algebraMap K B) b, ← h.delta_sq]
      simp only [map_add, map_mul, map_sub, AlgEquiv.commutes, h.cj_cj]; ring
    have f2 : Algebra.trace K B ((algebraMap K B a + algebraMap K B b * θ) * (cj θ * (θ - cj θ)))
        = (-a) * (t ^ 2 - 4 * n) := by
      apply h.inj
      rw [e2, map_mul (algebraMap K B) (-a), ← h.delta_sq]
      simp only [map_add, map_mul, map_sub, map_neg, AlgEquiv.commutes, h.cj_cj]; ring
    have g1 := hx _ h.int_delta
    have g2 := hx _ ((int_cj cj h.int_gen).mul h.int_delta)
    rw [f1] at g1; rw [f2] at g2
    exact ⟨by simpa using neg_mem (h.mem_of_mul_disc g2), h.mem_of_mul_disc g1⟩
  · intro hx y hy
    apply h.mem_of_int'
    rw [h.trace_eq hr]
    exact (hx.mul hy).add (int_cj cj (hx.mul hy))

theorem unram (O : Subring B) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[K] x) (ϖ : 𝒪[K]) (hϖ : Prime ϖ) (x : B) (hx : x ∈ O)
    (hxx : x * x ∈ Submodule.span O {algebraMap K B ϖ}) : x ∈ Submodule.span O {algebraMap K B ϖ} := by
  have hϖ0 : (ϖ : K) ≠ 0 := fun e => hϖ.ne_zero (Subtype.ext e)
  have key : ∀ (c : K) (hc : c ∈ 𝒪[K]) (z : B), IsIntegral 𝒪[K] z → algebraMap K B c = z * algebraMap K B ϖ →
      ϖ ∣ ⟨c, hc⟩ := by
    intro c hc z hz e
    have : z = algebraMap K B (c / ϖ) := by
      rw [div_eq_mul_inv, map_mul, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, mul_one]
    rw [this] at hz
    refine ⟨⟨c / ϖ, h.mem_of_int' hz⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul]; field_simp
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 hxx
  have hz' : (z : B) * algebraMap K B ϖ = x * x := hz
  have hzi := (hO z).1 z.2
  have hxi := (hO x).1 hx
  obtain ⟨a, b, hab⟩ := h.gen x
  obtain ⟨ha, hb⟩ := (h.int_iff a b).1 (hab ▸ hxi)
  have hcz : cj z * algebraMap K B ϖ = cj x * cj x := by
    have := congrArg cj hz'
    simpa only [map_mul, AlgEquiv.commutes] using this
  have hd : t ^ 2 - 4 * n ∈ 𝒪[K] := sub_mem (pow_mem h.t_int 2) (mul_mem (by exact_mod_cast natCast_mem 𝒪[K] 4) h.n_int)
  have h3 : IsIntegral 𝒪[K] (3 : B) := by exact_mod_cast (isIntegral_natCast (R := 𝒪[K]) (B := B) 3)
  have h2 : IsIntegral 𝒪[K] (2 : B) := by exact_mod_cast (isIntegral_natCast (R := 𝒪[K]) (B := B) 2)
  have hbd : ϖ ∣ (⟨b * (t ^ 2 - 4 * n), mul_mem hb hd⟩ : 𝒪[K]) := by
    apply hϖ.dvd_of_dvd_pow (n := 3)
    refine key _ (pow_mem (mul_mem hb hd) 3)
      ((z * (x - 3 * cj x) + cj z * (3 * x - cj x)) * (θ - cj θ) ^ 3) ?_ ?_
    · exact ((hzi.mul (hxi.sub (h3.mul (int_cj cj hxi)))).add
        ((int_cj cj hzi).mul ((h3.mul hxi).sub (int_cj cj hxi)))).mul (h.int_delta.pow 3)
    · rw [map_pow, ← h.sub_cj a b, ← hab]
      linear_combination (-(x - 3 * cj x) * (θ - cj θ) ^ 3) * hz' - ((3 * x - cj x) * (θ - cj θ) ^ 3) * hcz
  obtain ⟨b', hb'⟩ : ϖ ∣ (⟨b, hb⟩ : 𝒪[K]) := by
    have := hbd.mul_right ⟨_, h.disc_inv⟩
    convert this using 1
    apply Subtype.ext
    simp only [MulMemClass.mk_mul_mk]
    rw [mul_inv_cancel_right₀ h.disc_ne]
  have eb : algebraMap K B b = algebraMap K B ϖ * algebraMap K B b' := by
    rw [← map_mul]; congr 1; exact congrArg Subtype.val hb'
  obtain ⟨a', ha'⟩ : ϖ ∣ (⟨a, ha⟩ : 𝒪[K]) := by
    apply hϖ.dvd_of_dvd_pow (n := 2)
    refine key _ (pow_mem ha 2) (z - algebraMap K B b' * θ * (2 * x - algebraMap K B b * θ)) ?_ ?_
    · exact hzi.sub (((int_algebraMap b'.2).mul h.int_gen).mul
        ((h2.mul hxi).sub ((int_algebraMap hb).mul h.int_gen)))
    · have ea : algebraMap K B a = x - algebraMap K B b * θ := by rw [hab]; ring
      rw [map_pow, ea]
      linear_combination (-1 : B) * hz' - θ * (2 * x - algebraMap K B b * θ) * eb
  have ea : algebraMap K B a = algebraMap K B ϖ * algebraMap K B a' := by
    rw [← map_mul]; congr 1; exact congrArg Subtype.val ha'
  refine Submodule.mem_span_singleton.2 ⟨⟨algebraMap K B a' + algebraMap K B b' * θ,
    (hO _).2 ((h.int_iff _ _).2 ⟨a'.2, b'.2⟩)⟩, ?_⟩
  change (algebraMap K B a' + algebraMap K B b' * θ) * algebraMap K B ϖ = x
  rw [hab, ea, eb]; ring

end IsUnitGen
end Alg

section Top
variable {K B : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CommRing B] [Algebra K B] [TopologicalSpace B] [IsModuleTopology K B]

theorem isOpen_int : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer

theorem isCompact_int : IsCompact (𝒪[K] : Set K) := IsNonarchimedeanLocalField.isCompact_closedBall K 1

theorem secondCountable : SecondCountableTopology K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  infer_instance

theorem isOpen_coord (f : B ≃ₗ[K] K × K) (S : Set B) (hS : ∀ x, x ∈ S ↔ (f x).1 ∈ 𝒪[K] ∧ (f x).2 ∈ 𝒪[K]) :
    IsOpen S := by
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearMap
  have : S = f ⁻¹' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) := by ext x; exact hS x
  rw [this]
  exact (isOpen_int.prod isOpen_int).preimage hf

theorem exists_haar [MeasurableSpace B] [BorelSpace B] (f : B ≃ₗ[K] K × K) (S : Set B)
    (hS : ∀ x, x ∈ S ↔ (f x).1 ∈ 𝒪[K] ∧ (f x).2 ∈ 𝒪[K]) :
    ∃ μ : Measure B, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ S = 1 := by
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup K B
  haveI : ContinuousSMul K B := IsModuleTopology.toContinuousSMul K B
  haveI := secondCountable (K := K)
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearMap
  have hg : Continuous f.symm := IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap
  let φ : B ≃ₜ K × K := ⟨f.toEquiv, hf, hg⟩
  haveI : SecondCountableTopology B := φ.secondCountableTopology
  haveI : LocallyCompactSpace B := φ.isOpenEmbedding.locallyCompactSpace
  have hc : IsCompact S := by
    have : S = φ ⁻¹' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) := by ext x; exact hS x
    rw [this]
    exact φ.isCompact_preimage.2 (isCompact_int.prod isCompact_int)
  have ho := isOpen_coord f S hS
  let P : TopologicalSpace.PositiveCompacts B := ⟨⟨S, hc⟩, by
    change (interior S).Nonempty
    rw [ho.interior_eq]
    exact ⟨0, (hS 0).2 (by simp)⟩⟩
  exact ⟨Measure.addHaarMeasure P, inferInstance, inferInstance, Measure.addHaarMeasure_self⟩

theorem continuous_char {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalAddGroup B] (ψ : AddChar B ℂ) (S : Set B) (hS : IsOpen S) (h0 : (0 : B) ∈ S) (hψ : ∀ x ∈ S, ψ x = 1) :
    Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => y - x) ⁻¹' S, hS.preimage (by fun_prop), by simpa using h0, fun y hy => ?_⟩
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ _ hy, mul_one]

theorem exists_de (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    [FiniteDimensional ℚ_[l] K] : ∃ de : K, de ≠ 0 ∧
      ∀ x : K, (∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * y)‖ ≤ 1) ↔ de * x ∈ 𝒪[K] := by
  haveI : ContinuousSMul ℚ_[l] K := continuousSMul_of_algebraMap _ _ hc
  haveI : T2Space K := by
    letI := IsTopologicalAddGroup.rightUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have htr : Continuous (Algebra.trace ℚ_[l] K) := LinearMap.continuous_of_finiteDimensional _
  have hsm : ∀ (c : ℚ_[l]) (y : K), Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K c * y) = c * Algebra.trace ℚ_[l] K y :=
    fun c y => by rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  obtain ⟨C, hC⟩ := (isCompact_int.image htr).isBounded.exists_norm_le
  obtain ⟨x₁, hx₁, hD₁⟩ : ∃ x : K, x ≠ 0 ∧ ∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * y)‖ ≤ 1 := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    have hc0 : 0 < ‖c‖ := lt_of_le_of_lt (le_max_right _ _) hc
    have hc1 : c ≠ 0 := norm_pos_iff.1 hc0
    refine ⟨algebraMap ℚ_[l] K c⁻¹, by simpa using hc1, fun y hy => ?_⟩
    rw [hsm, norm_mul, norm_inv, inv_mul_le_one₀ hc0]
    exact (hC _ ⟨y, hy, rfl⟩).trans ((le_max_left _ _).trans hc.le)
  obtain ⟨x₀, hx₀⟩ : ∃ x : K, ¬ ‖Algebra.trace ℚ_[l] K x‖ ≤ 1 := by
    have h1 : Algebra.trace ℚ_[l] K 1 ≠ 0 := by
      rw [← map_one (algebraMap ℚ_[l] K), Algebra.trace_algebraMap]
      simpa using (Module.finrank_pos (R := ℚ_[l]) (M := K)).ne'
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] 1
    refine ⟨algebraMap ℚ_[l] K (c / Algebra.trace ℚ_[l] K 1) * 1, ?_⟩
    rw [hsm, div_mul_cancel₀ _ h1]; exact not_le.2 hc
  have hx0 : x₀ ≠ 0 := by rintro rfl; simp at hx₀
  have hmem : ∀ x : K, (∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * y)‖ ≤ 1) → x / x₀ ∈ 𝒪[K] := by
    intro x hx
    by_cases hx' : x = 0
    · simp [hx']
    rcases ValuationRing.isInteger_or_isInteger 𝒪[K] (x / x₀) with ⟨y, hy⟩ | ⟨y, hy⟩
    · rw [← hy]; exact y.2
    · exfalso
      apply hx₀
      have := hx y y.2
      have e : (y : K) = (x / x₀)⁻¹ := hy
      rwa [e, inv_div, mul_div_cancel₀ _ hx'] at this
  let I : Ideal 𝒪[K] :=
    { carrier := {a | ∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x₀ * a * y)‖ ≤ 1}
      zero_mem' := fun y _ => by simp
      add_mem' := fun {a b} ha hb y hy => by
        have : x₀ * ((a + b : 𝒪[K]) : K) * y = x₀ * a * y + x₀ * b * y := by push_cast; ring
        rw [this, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha y hy) (hb y hy))
      smul_mem' := fun c a ha y hy => by
        have : x₀ * ((c • a : 𝒪[K]) : K) * y = x₀ * a * (c * y) := by
          simp only [smul_eq_mul]; push_cast; ring
        rw [this]
        exact ha _ (mul_mem c.2 hy) }
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  have hI : ∀ b : 𝒪[K], (∀ y ∈ 𝒪[K], ‖Algebra.trace ℚ_[l] K (x₀ * b * y)‖ ≤ 1) ↔ a ∣ b := fun b => by
    rw [← Ideal.mem_span_singleton]
    change b ∈ I ↔ _
    rw [ha]
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := (hI ⟨x₁ / x₀, hmem _ hD₁⟩).1 (by simpa only [mul_div_cancel₀ _ hx0] using hD₁)
    have := congrArg Subtype.val hc
    simp only [MulMemClass.coe_mul, h0, zero_mul] at this
    exact div_ne_zero hx₁ hx0 this
  refine ⟨(x₀ * a)⁻¹, inv_ne_zero (mul_ne_zero hx0 ha0), fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (hI ⟨x / x₀, hmem _ hx⟩).1 (by simpa only [mul_div_cancel₀ _ hx0] using hx)
    have e : x / x₀ = a * c := congrArg Subtype.val hc
    have : (x₀ * a)⁻¹ * x = c := by
      rw [div_eq_iff hx0] at e
      rw [e]; field_simp
    rw [this]; exact c.2
  · have := (hI a).2 dvd_rfl _ (mul_mem hx hy)
    convert this using 3
    field_simp

end Top

theorem char_eq_one_iff (l : ℕ) [hl : Fact l.Prime] (x : ℚ_[l]) (z : ℂ)
    (h : ∃ a : ℚ, (∃ n : ℕ, a.den = l ^ n) ∧ ‖x - (a : ℚ_[l])‖ ≤ 1 ∧
      z = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ))) : z = 1 ↔ ‖x‖ ≤ 1 := by
  obtain ⟨a, ⟨n, hn⟩, hx, rfl⟩ := h
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have : (a : ℂ) = (m : ℂ) := mul_left_cancel₀ h2 (by rw [hm]; ring)
    have ha : a = m := by exact_mod_cast this
    have e : x = (x - (a : ℚ_[l])) + (m : ℚ_[l]) := by rw [ha]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (Padic.norm_int_le_one m))
  · intro h1
    have ha : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have e : (a : ℚ_[l]) = x + -(x - (a : ℚ_[l])) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
    have hd : ¬ l ∣ a.den := GlobalTheory.LocalData.not_dvd_den l ha
    have hn0 : n = 0 := by
      by_contra h0
      exact hd (hn ▸ dvd_pow_self l h0)
    rw [hn0, pow_zero] at hn
    refine ⟨a.num, ?_⟩
    have : (a : ℂ) = (a.num : ℂ) := by exact_mod_cast congrArg (fun r : ℚ => (r : ℂ)) ((Rat.den_eq_one_iff a).1 hn).symm
    rw [this]; ring

section Build
variable {K B : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CommRing B] [Algebra K B] [TopologicalSpace B] [IsModuleTopology K B]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace B] [IsModuleTopology K B] in

theorem IsUnitGen.exists_coord {cj : B ≃ₐ[K] B} {θ : B} {t n : K} (h : IsUnitGen cj θ t n) :
    ∃ f : B ≃ₗ[K] K × K, ∀ x, IsIntegral 𝒪[K] x ↔ (f x).1 ∈ 𝒪[K] ∧ (f x).2 ∈ 𝒪[K] := by
  let g : K × K →ₗ[K] B := (LinearMap.toSpanSingleton K B 1).coprod (LinearMap.toSpanSingleton K B θ)
  have hg : ∀ z, g z = algebraMap K B z.1 + algebraMap K B z.2 * θ := fun z => by
    simp [g, Algebra.smul_def]
  have hb : Function.Bijective g := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ e
      rw [hg] at e
      have e2 := h.sub_cj a b
      simp only at e
      rw [e, map_zero, sub_zero, zero_mul, ← map_zero (algebraMap K B)] at e2
      have hb : b = 0 := (mul_eq_zero.1 (h.inj e2).symm).resolve_right h.disc_ne
      subst hb
      simp only [map_zero, zero_mul, add_zero] at e
      rw [← map_zero (algebraMap K B)] at e
      rw [h.inj e]; rfl
    · intro x
      obtain ⟨a, b, e⟩ := h.gen x
      exact ⟨(a, b), by rw [hg, e]⟩
  refine ⟨(LinearEquiv.ofBijective g hb).symm, fun x => ?_⟩
  rw [← h.int_iff, ← hg]
  have : g ((LinearEquiv.ofBijective g hb).symm x) = x := (LinearEquiv.ofBijective g hb).apply_symm_apply x
  rw [this]

theorem exists_splitG (L : LocE K B) {l : ℕ} (S : SplitAt K B L.cj l) :
    ∃ G : SplitG L, G.e = S.e ∧ G.q = S.q := by
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup K B
  haveI : ContinuousSMul K B := IsModuleTopology.toContinuousSMul K B
  have hs : Continuous S.e.symm := IsModuleTopology.continuous_of_linearMap S.e.symm.toLinearMap
  have hin : ∀ y ∈ 𝒪[K], S.e.symm (y, 0) ∈ L.O := by
    intro y hy
    rw [L.O_def]
    have e : S.e.symm (y, 0) = algebraMap K B y * S.e.symm (1, 0) := by
      apply S.e.injective; simp
    rw [e]
    refine (int_algebraMap hy).mul ?_
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    apply S.e.injective; simp
  have hout : ∀ w ∈ L.O, (S.e w).1 ∈ 𝒪[K] := by
    intro w hw
    rw [L.O_def] at hw
    exact mem_of_int (hw.map (((AlgHom.fst K K K).comp S.e.toAlgHom).restrictScalars 𝒪[K]))
  let j : K →+ B := S.e.symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl K K)
  have hj : ∀ y, j y = S.e.symm (y, 0) := fun _ => rfl
  have hq0 : (S.q : K) ≠ 0 := fun e => S.q_irr.ne_zero (Subtype.ext e)
  refine ⟨⟨S.e, S.e_cj, S.q, S.q_irr, L.psi0.compAddMonoidHom j, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · change Continuous fun y => L.psi0 (S.e.symm (y, 0))
    exact L.local_additive_char_continuous.comp (hs.comp (by fun_prop))
  · intro y hy
    change L.psi0 (S.e.symm (y, 0)) = 1
    simpa using (L.additive_character_dual_ring _).2 (hin y hy) 1 L.O.one_mem
  · by_contra hne
    push Not at hne
    have h1 : S.e.symm ((S.q : K)⁻¹, 0) ∈ L.O := by
      refine (L.additive_character_dual_ring _).1 fun w hw => ?_
      have := hne ⟨_, hout w hw⟩
      change L.psi0 (S.e.symm (_, 0)) = 1 at this
      rw [← this]
      congr 1
      apply S.e.injective
      ext <;> simp [div_eq_inv_mul]
    have h2 := hout _ h1
    simp only [AlgEquiv.apply_symm_apply] at h2
    exact S.q_irr.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h2⟩ (Subtype.ext (mul_inv_cancel₀ hq0)))
  · intro x
    rw [AddChar.map_add_eq_mul]
    change _ = L.psi0 (S.e.symm (_, 0)) * L.psi0 (S.e.symm (_, 0))
    rw [← L.local_additive_char_conj (S.e.symm ((S.e x).2, 0)), ← AddChar.map_add_eq_mul]
    congr 1
    apply S.e.injective
    ext <;> simp [S.e_cj]

omit [IsNonarchimedeanLocalField K] [IsModuleTopology K B] in

theorem mem_R_split [MeasurableSpace B] (L : LocE K B) (G : SplitG L) (μ : Measure B) (x : B) :
    x ∈ (Model.mk L (some G) μ).R ↔ (G.e x).1 ∈ 𝒪[K] ∧ ((G.e x).1 - (G.e x).2) / (G.q : K) ∈ 𝒪[K] := by
  have hq0 : (G.q : K) ≠ 0 := fun e => G.q_irr.ne_zero (Subtype.ext e)
  simp only [Model.R, Subring.mem_comap, Subring.mem_map, RingHom.mem_eqLocus, RingHom.comp_apply,
    Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, hc⟩, e⟩
    have e1 : (a : K) = (G.e x).1 := congrArg Prod.fst e
    have e2 : (b : K) = (G.e x).2 := congrArg Prod.snd e
    have e3 : (a : K) - b = G.q * c := congrArg Subtype.val hc
    rw [← e1, ← e2, e3, mul_div_cancel_left₀ _ hq0]
    exact ⟨a.2, c.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(⟨_, h1⟩, ⟨_, h1⟩ - G.q * ⟨_, h2⟩), ⟨⟨_, h2⟩, by simp⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change (G.e x).1 - G.q * (((G.e x).1 - (G.e x).2) / G.q) = (G.e x).2
      field_simp; ring

theorem exists_haar_split [MeasurableSpace B] [BorelSpace B] (L : LocE K B) (G : SplitG L) :
    ∃ μ : Measure B, (Model.mk L (some G) μ).HaarOK := by
  have hq0 : (G.q : K) ≠ 0 := fun e => G.q_irr.ne_zero (Subtype.ext e)
  let c : (K × K) ≃ₗ[K] K × K :=
    { toFun := fun z => (z.1, (z.1 - z.2) / G.q)
      invFun := fun z => (z.1, z.1 - G.q * z.2)
      map_add' := fun z w => by ext <;> simp; ring
      map_smul' := fun a z => by ext <;> simp; ring
      left_inv := fun z => by ext <;> simp; field_simp; ring
      right_inv := fun z => by ext <;> simp; field_simp }
  obtain ⟨μ, h1, h2, h3⟩ := exists_haar (G.e.toLinearEquiv.trans c) ((Model.mk L (some G) 0).R : Set B)
    (fun x => mem_R_split L G 0 x)
  exact ⟨μ, h1, h2, h3⟩

end Build

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem psiE_eq_one_iff (y : A.Ep) : A.psiE y = 1 ↔ (haveI := A.ellPrime;
    ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep y)‖ ≤ 1) := by
  haveI := A.ellPrime
  letI : Algebra ℚ_[resChar p] A.Ep := ((algebraMap A.Fp A.Ep).comp (algebraMap ℚ_[resChar p] A.Fp)).toAlgebra
  haveI : IsScalarTower ℚ_[resChar p] A.Fp A.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := A.qlFin
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  rw [Algebra.trace_trace]
  exact char_eq_one_iff _ _ _ (A.psiE_def y)

theorem exists_model {θ : A.Ep} {t n : A.Fp} (h : IsUnitGen A.cj θ t n) :
    ∃ (M : Model A.Fp A.Ep) (de : A.Fp), M.OK ∧ de ≠ 0 ∧
      (∀ x : A.Fp, (haveI := A.ellPrime;
        ∀ y ∈ 𝒪[A.Fp], ‖Algebra.trace ℚ_[resChar p] A.Fp (x * y)‖ ≤ 1) ↔ de * x ∈ 𝒪[A.Fp]) ∧
      M.L.cj = A.cj ∧ (∀ y, M.L.psi0 y = A.psiE (-(algebraMap A.Fp A.Ep de⁻¹ * y))) ∧
      (M.split.isSome ↔ A.split.isSome) ∧
      ∀ G : SplitG M.L, M.split = some G →
        (G.q : A.Fp) = (resChar p : A.Fp) ∧ ∃ S, A.split = some S ∧ S.e = G.e := by
  haveI := A.ellPrime
  haveI := A.lf
  haveI := A.char0
  haveI := A.top
  haveI := A.borel
  haveI := A.qlFin
  haveI : IsTopologicalAddGroup A.Ep := IsModuleTopology.topologicalAddGroup A.Fp A.Ep
  obtain ⟨de, hde, hgen⟩ := exists_de (K := A.Fp) (resChar p) A.qlCont
  let ψ : AddChar A.Ep ℂ :=
    A.psiE.compAddMonoidHom (-(AddMonoidHom.mulLeft (algebraMap A.Fp A.Ep de⁻¹)))
  have hψ : ∀ y, ψ y = A.psiE (-(algebraMap A.Fp A.Ep de⁻¹ * y)) := fun _ => rfl
  have hψ1 : ∀ y, ψ y = 1 ↔ ‖Algebra.trace ℚ_[resChar p] A.Fp (de⁻¹ * Algebra.trace A.Fp A.Ep y)‖ ≤ 1 := by
    intro y
    rw [hψ, psiE_eq_one_iff, map_neg, map_neg, norm_neg, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have hdual : ∀ x : A.Ep, (∀ y ∈ A.O, ψ (x * y) = 1) ↔ x ∈ A.O := by
    intro x
    rw [A.O_def, ← h.trace_dual A.rank]
    constructor
    · intro hx y hy
      have := (hgen (de⁻¹ * Algebra.trace A.Fp A.Ep (x * y))).1 fun c hc => by
        have h2 := (hψ1 _).1 (hx (algebraMap A.Fp A.Ep c * y) ((A.O_def _).2 ((int_algebraMap hc).mul hy)))
        rw [mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul] at h2
        convert h2 using 3
        ring
      rwa [mul_inv_cancel_left₀ hde] at this
    · intro hx y hy
      rw [hψ1]
      have := (hgen (de⁻¹ * Algebra.trace A.Fp A.Ep (x * y))).2 (by
        rw [mul_inv_cancel_left₀ hde]; exact hx y ((A.O_def y).1 hy)) 1 (one_mem _)
      rwa [mul_one] at this
  obtain ⟨f, hf⟩ := h.exists_coord
  have hfO : ∀ x, x ∈ (A.O : Set A.Ep) ↔ (f x).1 ∈ 𝒪[A.Fp] ∧ (f x).2 ∈ 𝒪[A.Fp] := fun x =>
    (A.O_def x).trans (hf x)
  let L : LocE A.Fp A.Ep :=
    { cj := A.cj
      cj_cj := h.cj_cj
      cj_fix := h.cj_fix
      free := A.free
      rank := A.rank
      reduced := h.reduced
      top := A.top
      O := A.O
      O_def := A.O_def
      unram := fun ϖ hϖ x hx => h.unram A.O A.O_def ϖ hϖ.prime x hx
      psi0 := ψ
      local_additive_char_continuous := continuous_char ψ A.O (isOpen_coord f _ hfO) A.O.zero_mem fun x hx => by
        simpa using (hdual x).2 hx 1 A.O.one_mem
      local_additive_char_conj := fun y => by
        have e : A.cj y = y + (A.cj y - y) := by ring
        have : ψ (A.cj y - y) = 1 := by
          rw [hψ1, map_sub, Algebra.trace_eq_of_algEquiv A.cj]; simp
        rw [e, AddChar.map_add_eq_mul, this, mul_one]
      additive_character_dual_ring := hdual }
  cases hS : A.split with
  | none =>
    obtain ⟨μ, h1, h2, h3⟩ := exists_haar f _ hfO
    exact ⟨⟨L, none, μ⟩, de, ⟨A.lf, A.char0, A.borel, h1, h2, h3⟩, hde, hgen, rfl, hψ, by simp,
      fun G hG => by cases hG⟩
  | some S =>
    obtain ⟨G, hG1, hG2⟩ := exists_splitG L S
    obtain ⟨μ, hμ⟩ := exists_haar_split L G
    refine ⟨⟨L, some G, μ⟩, de, ⟨A.lf, A.char0, A.borel, hμ⟩, hde, hgen, rfl, hψ, by simp, fun G' hG' => ?_⟩
    obtain rfl : G = G' := Option.some.inj hG'
    exact ⟨by rw [hG2]; exact S.q_eq, S, rfl, hG1.symm⟩

omit A in

theorem exists_isUnitGen [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (A : LocAt F E hc.sig p) :
    ∃ θ t n, IsUnitGen A.cj θ t n := by
  obtain ⟨θ, t, n, ht, hn, hd⟩ := GlobalTheory.cm_exists_unit_disc hc p.asIdeal p.isMaximal
  have hv : ∀ x : F, p.valuation F x ≤ 1 → A.ιF x ∈ 𝒪[A.Fp] := fun x hx => by
    have := (A.val x 1).2 (by simpa using hx)
    rw [Valuation.Compatible.vle_iff_le (v := valuation A.Fp), map_one, map_one] at this
    exact this
  have hi : ∀ x : 𝓞 F, A.ιF x ∈ 𝒪[A.Fp] := fun x => hv _ (p.valuation_le_one x)
  have hd1 : p.valuation F ((t : F) ^ 2 - 4 * n) = 1 := by
    have := (p.valuation_eq_one_iff_notMem (K := F)).2 hd
    simpa only [map_sub, map_pow, map_mul, map_ofNat] using this
  have hd0 : (t : F) ^ 2 - 4 * n ≠ 0 := fun e => by simp [e] at hd1
  have hθ : (θ : E) - star (θ : E) ≠ 0 := by
    intro e
    apply hd0
    apply (algebraMap F E).injective
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_zero, ← ht, ← hn]
    linear_combination ((θ : E) - star (θ : E)) * e
  have hcj : ∀ x : E, A.cj (A.ιE x) = A.ιE (star x) := A.cj_ιE
  have ed : A.ιF t ^ 2 - 4 * A.ιF n = A.ιF ((t : F) ^ 2 - 4 * n) := by
    simp only [map_sub, map_pow, map_mul, map_ofNat]
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  refine ⟨A.ιE θ, A.ιF t, A.ιF n, (algebraMap A.Fp A.Ep).injective, fun x => ?_, ?_, ?_, hi t, hi n, ?_, ?_⟩
  · have hx : x ∈ Submodule.span A.Fp (Set.range A.ιE) := A.span ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      obtain ⟨a, b, rfl⟩ := GlobalTheory.cm_exists_coords hc θ hθ y
      exact ⟨A.ιF a, A.ιF b, by rw [map_add, map_mul, A.compat, A.compat]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, by simp only [map_add]; ring⟩
    | smul c x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨c * a, c * b, by simp only [map_mul, Algebra.smul_def]; ring⟩
  · rw [hcj, ← map_add, ht, A.compat]
  · rw [hcj, ← map_mul, hn, A.compat]
  · rw [ed]; exact (map_ne_zero _).2 hd0
  · rw [ed, ← map_inv₀]; exact hv _ (by rw [map_inv₀, hd1, inv_one])

end GlobalTheory.SgGlob.LocModel
