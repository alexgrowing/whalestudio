import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallHeightOneLocalizationIntegrallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalKaehlerDBasisSmoothSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.ComplementaryForms

theorem height_under_eq_one {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (hne : Q.comap (algebraMap A B) ≠ ⊥) : (Q.comap (algebraMap A B)).height = 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro r hr hrp
    by_contra hcon
    have hr0 : r ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hr
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
      (bot_lt_iff_ne_bot.mpr hr0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

open KaehlerDifferential in
open scoped IntermediateField.algebraAdjoinAdjoin in

theorem exists_basis_D (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] [Algebra.IsSeparable F K] (d : ℕ) (v : Fin d → F)
    (hv : AlgebraicIndependent k v) (hgen : IntermediateField.adjoin k (Set.range v) = ⊤) :
    ∃ b : Module.Basis (Fin d) K Ω[K⁄k], ∀ j, b j = D k K (algebraMap F K (v j)) := by
  let P := MvPolynomial (Fin d) k
  let A := Algebra.adjoin k (Set.range v)
  let L := IntermediateField.adjoin k (Set.range v)
  letI : Algebra P A := hv.aevalEquiv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower k P A := .of_algebraMap_eq fun r => (hv.aevalEquiv.commutes r).symm
  haveI : Algebra.FormallyEtale P A :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.IsSeparable L F := ⟨fun a => by
    have ha : a ∈ L := by rw [show L = ⊤ from hgen]; trivial
    exact (show algebraMap L F ⟨a, ha⟩ = a from rfl) ▸ isSeparable_algebraMap _⟩
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_isSeparable _ F
  haveI : Algebra.FormallyEtale A F := .comp A L F
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let b₁ : Module.Basis (Fin d) A Ω[A⁄k] :=
    ((mvPolynomialBasis k (Fin d)).baseChange A).map (tensorKaehlerEquivOfFormallyEtale k P A)
  let b₂ : Module.Basis (Fin d) F Ω[F⁄k] := (b₁.baseChange F).map (tensorKaehlerEquivOfFormallyEtale k A F)
  have h₂ : ∀ j, b₂ j = D k F (v j) := by
    intro j
    simp only [b₂, b₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have e : algebraMap A F (algebraMap P A (MvPolynomial.X j)) = v j := by
      change algebraMap A F (hv.aevalEquiv (MvPolynomial.X j)) = v j
      rw [hv.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
    rw [← e, ← map_D k k A F, ← map_D k k P A]
    exact congrArg _ ((mapBaseChange_tmul k P A 1 _).trans (one_smul _ _))
  refine ⟨(b₂.baseChange K).map (tensorKaehlerEquivOfFormallyEtale k F K), fun j => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, h₂, map_D]

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem local_frame (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (d : ℕ)
    (τ : DR k K →ₗ[K] K) (w : Fin d → Ω[K⁄k]) (hw : τ (ExteriorAlgebra.ιMulti K d w) = 1)
    (f : B) (u' : Fin d → B) (b : Module.Basis (Fin d) K Ω[K⁄k]) (hb : ∀ j, b j = D k K (u' j : K))
    (hc : ∀ (v : B) (j : Fin d), ∃ c : B, (f : K) * b.repr (D k K (v : K)) j = c) :
    τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) ≠ 0 ∧
    ∀ y ∈ omB k K B d, ∃ c : B,
      (f : K) ^ d * τ y = τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) * c := by
  classical
  let φ : Ω[K⁄k] [⋀^Fin d]→ₗ[K] K := τ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)
  have hφ : ∀ v, τ (ExteriorAlgebra.ιMulti K d v) = φ v := fun v => rfl
  have hb' : (⇑b) = fun j => D k K (u' j : K) := funext hb
  have key : ∀ v, φ v = τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) * b.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det b φ]
    rw [AlternatingMap.smul_apply, smul_eq_mul, hφ, hb']
  set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg
  refine ⟨fun h0 => ?_, fun y hy => ?_⟩
  · have := key w
    rw [← hφ, hw, h0, zero_mul] at this
    exact one_ne_zero this
  have hdet : ∀ v : Fin d → K, (∀ j, v j ∈ B) →
      ∃ c : B, (f : K) ^ d * b.det (fun j => D k K (v j)) = c := by
    intro v hv
    choose M hM using fun i j => hc ⟨v j, hv j⟩ i
    refine ⟨(Matrix.of M).det, ?_⟩
    have hs := Matrix.det_smul (b.toMatrix fun j => D k K (v j)) (f : K)
    rw [Fintype.card_fin] at hs
    rw [Module.Basis.det_apply, ← hs]
    have : (f : K) • b.toMatrix (fun j => D k K (v j)) = (algebraMap B K).mapMatrix (Matrix.of M) := by
      ext i j
      simp only [Matrix.smul_apply, Module.Basis.toMatrix_apply, smul_eq_mul, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.of_apply]
      exact hM i j
    rw [this, ← RingHom.map_det]
    rfl
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, v, hv, rfl⟩ := hx
    obtain ⟨c, hc'⟩ := hdet v hv
    refine ⟨⟨c₀, hc₀⟩ * c, ?_⟩
    rw [map_smul, smul_eq_mul, hφ, key]
    push_cast
    rw [← hc']
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, h₁⟩ := hx
    obtain ⟨c₂, h₂⟩ := hy
    exact ⟨c₁ + c₂, by rw [map_add, mul_add, h₁, h₂]; push_cast; ring⟩
  | smul a x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨algebraMap k B a * c, ?_⟩
    rw [LinearMap.map_smul_of_tower, Algebra.smul_def, mul_left_comm, h]
    push_cast
    rw [IsScalarTower.algebraMap_apply k B K]
    ring

end GlobalTheory.ComplementaryForms

namespace GlobalTheory.ComplementaryForms

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem complementary_eq_topForms : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ z : K, (∀ b : B, Algebra.trace F K (z * b) ∈ A) ↔ ∃ y ∈ omB k K B d, τ y = z := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ z
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI : Algebra.IsSeparable F K := inferInstance

  haveI : IsNoetherianRing A := by
    subst hA; exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  haveI : UniqueFactorizationMonoid A := by
    subst hA; exact hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  haveI : IsIntegrallyClosed A := inferInstance
  have hgen : IntermediateField.adjoin k (Set.range u) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    have hle : ∀ t : A, (t : F) ∈ IntermediateField.adjoin k (Set.range u) := by
      intro t
      have ht : (t : F) ∈ Algebra.adjoin k (Set.range u) := hA ▸ t.2
      exact IntermediateField.algebra_adjoin_le_adjoin k _ ht
    exact div_mem (hle a) (hle s)
  have hrank : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := exists_basis_D k F K d u hu hgen
    simpa using Module.finrank_eq_card_basis b

  let C := integralClosure A K
  haveI : IsFractionRing C K := integralClosure.isFractionRing_of_finite_extension F K
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsNoetherianRing C := IsIntegralClosure.isNoetherianRing A F K C
  have hmem : ∀ x : K, x ∈ B ↔ x ∈ C := by subst hB; exact fun x => Iff.rfl
  let e : C ≃+* B :=
    { toFun := fun x => ⟨x.1, (hmem _).2 x.2⟩
      invFun := fun x => ⟨x.1, (hmem _).1 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsNoetherianRing B := isNoetherianRing_of_ringEquiv C e
  haveI : IsFractionRing B K := by subst hB; exact inferInstanceAs (IsFractionRing C K)
  haveI : IsIntegrallyClosed B := by subst hB; exact inferInstanceAs (IsIntegrallyClosed C)
  haveI : Algebra.Smooth k B := hsm
  haveI : FaithfulSMul A C := by
    refine (faithfulSMul_iff_algebraMap_injective A C).mpr fun a a' h => ?_
    have h' : algebraMap F K (a : F) = algebraMap F K (a' : F) := congrArg (fun x : C => (x : K)) h
    exact Subtype.val_injective ((algebraMap F K).injective h')
  haveI : Algebra.HasGoingDown A C := inferInstance

  have hunder : ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 →
      ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧
        ∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p) := by
    intro Q hQ hQ1
    set Q' : Ideal C := Q.comap (e : C →+* B)
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ Q
    have hQ'1 : Q'.height = 1 := (RingEquiv.height_comap e Q).trans hQ1
    have hne : Q'.comap (algebraMap A C) ≠ ⊥ := by
      have hQ'0 : Q' ≠ ⊥ := by
        rintro h
        rw [h, Ideal.height_bot] at hQ'1
        exact zero_ne_one hQ'1
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ'0
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (integralClosure.isIntegral x)
    refine ⟨Q'.comap (algebraMap A C), Ideal.comap_isPrime _ _, height_under_eq_one Q' hQ'1 hne, ?_⟩
    intro a b hab
    have : b = e (algebraMap A C a) := by
      apply Subtype.ext
      rw [hab]
      rfl
    rw [this]
    rfl
  constructor
  · intro hz
    let J : Ideal B :=
      { carrier := {c | ∃ y ∈ omB k K B d, τ y = (c : K) * z}
        add_mem' := by
          rintro c₁ c₂ ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add, h₁, h₂]; push_cast; ring⟩
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        smul_mem' := by
          rintro c c' ⟨y, hy, h⟩
          refine ⟨(c : K) • y, ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B d d).2.1 y hy).2.2.2 _ c.2, ?_⟩
          rw [map_smul, h, smul_eq_mul, smul_eq_mul]
          push_cast
          ring }
    suffices h1J : (1 : B) ∈ J by
      obtain ⟨y, hy, h⟩ := h1J
      exact ⟨y, hy, by simpa using h⟩
    by_contra hJ
    obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J (fun h => hJ (h ▸ Submodule.mem_top))
    haveI := hPmax.isPrime
    obtain ⟨f, u', bP, hfP, hb, hc⟩ := GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B d hrank P
    obtain ⟨hg0, hloc⟩ := local_frame k K B d τ _ hτ f u' bP hb hc
    set g := τ (ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K))) with hg
    obtain ⟨c, hcw⟩ := GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed B K ((f : K) ^ d * z / g) (by
      intro Q hQ hQ1
      obtain ⟨p, hp, hp1, hover⟩ := hunder Q hQ hQ1
      have hcod := (GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 z).1 (fun b =>
        ⟨1, ⟨_, hz b⟩, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩)
      obtain ⟨r, hr, y, hy, hyz⟩ := hcod Q hQ hover
      obtain ⟨c, hc'⟩ := hloc y hy
      refine ⟨r, c, hr, ?_⟩
      change (r : K) * ((f : K) ^ d * z / g) = c
      rw [mul_div_assoc', mul_left_comm, ← hyz, hc', mul_div_assoc]
      field_simp)
    have hfd : f ^ d ∈ J := by
      refine ⟨(c : K) • ExteriorAlgebra.ιMulti K d (fun j => D k K (u' j : K)),
        Submodule.subset_span ⟨c, c.2, _, fun j => (u' j).2, rfl⟩, ?_⟩
      rw [map_smul, smul_eq_mul, ← hg]
      have hcw' : (f : K) ^ d * z / g = c := hcw
      rw [← hcw']
      push_cast
      field_simp
    exact hfP (hPmax.isPrime.mem_of_pow_mem d (hJP hfd))
  · rintro ⟨y, hy, rfl⟩ b
    obtain ⟨c, hc⟩ := GlobalTheory.T.mem_of_forall_heightOne_localization_integrallyClosed A F (Algebra.trace F K (τ y * b)) (by
      intro p hp hp1
      exact (GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt k F K d u hu A hA B hB hsm τ hτ p hp hp1 (τ y)).2
        (fun Q hQ _ => ⟨1, (Ideal.ne_top_iff_one Q).1 hQ.ne_top, y, hy, by simp⟩) b)
    rw [hc]
    exact c.2

end GlobalTheory.ComplementaryForms
