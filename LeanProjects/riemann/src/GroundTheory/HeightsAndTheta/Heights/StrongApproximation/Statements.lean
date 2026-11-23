import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SAOpenStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.LocGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.DenseRangeFiniteAdele
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.EichAlongSub
import GroundTheory.HeightsAndTheta.Theta.GaussianExample
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

section Objects

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]

abbrev Kv (v : HeightOneSpectrum (𝓞 F)) : Type := v.adicCompletion F ⊗[F] E

variable {E}

def sigV (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : Kv E v →ₐ[v.adicCompletion F] Kv E v :=
  Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) (v.adicCompletion F)) c.toAlgHom

variable (E)

def inclV (v : HeightOneSpectrum (𝓞 F)) : E →+* Kv E v :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] Kv E v).toRingHom

variable (F) in

def evalAt (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def compAt (v : HeightOneSpectrum (𝓞 F)) : AE F E →+* Kv E v :=
  (Algebra.TensorProduct.map (evalAt F v) (AlgHom.id F E)).toRingHom

variable (F) in
open Classical in

def singleF (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] FiniteAdeleRing (𝓞 F) F where
  toFun x := ⟨Pi.single v x, by
    filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) ∈ Filter.cofinite by simp] with w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    simp [hw]⟩
  map_add' x y := by
    apply FiniteAdeleRing.ext; intro w
    change Pi.single v (x + y) w = Pi.single v x w + Pi.single v y w
    rw [Pi.single_add, Pi.add_apply]
  map_smul' a x := by
    apply FiniteAdeleRing.ext; intro w
    change Pi.single v (a • x) w = (a : w.adicCompletion F) * Pi.single v x w
    by_cases h : w = v
    · subst h; simp only [Pi.single_eq_same, Algebra.smul_def]; rfl
    · simp [h]

def singleV (v : HeightOneSpectrum (𝓞 F)) : Kv E v →+ AE F E :=
  (LinearMap.rTensor E (singleF F v)).toAddMonoidHom

def embed (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (g : Matrix (Fin N) (Fin N) (Kv E v)) :
    Matrix (Fin N) (Fin N) (AE F E) :=
  1 + (g - 1).map (singleV E v)

def restrictTo (S : Finset (HeightOneSpectrum (𝓞 F))) (a : AE F E) : AE F E :=
  ∑ v ∈ S, singleV E v (compAt E v a)

def trunc (S : Finset (HeightOneSpectrum (𝓞 F))) {N : ℕ} (x : Matrix (Fin N) (Fin N) (AE F E)) :
    Matrix (Fin N) (Fin N) (AE F E) :=
  1 + (x - 1).map (restrictTo E S)

def intAt (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (Kv E v) :=
  AddSubgroup.closure
    {x | ∃ a ∈ v.adicCompletionIntegers F, ∃ b : 𝓞 E, x = a ⊗ₜ[F] (algebraMap (𝓞 E) E b)}

variable {E}

def Cl [TopologicalSpace (AE F E)] (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) :
    Set (Matrix (Fin N) (Fin N) (AE F E)) :=
  closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) '' SU c.toRingHom J)

end Objects

def perpProj {R : Type*} [CommRing R] (σ : R →+* R) {N : ℕ} (J : Matrix (Fin N) (Fin N) R)
    (e f : Fin N → R) (u : Fin N → R) : Fin N → R :=
  u - hf σ J u f • e - hf σ J u e • f

def HypPairExists.Statement : Prop :=
  ∀ (E : Type) [Field E] (σ : E →+* E), (∀ x, σ (σ x) = x) → (2 : E) ≠ 0 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), Jᵀ = J.map σ → IsUnit J.det →
    ∀ e : Fin N → E, e ≠ 0 → hf σ J e e = 0 →
      ∃ f : Fin N → E, hf σ J f f = 0 ∧ hf σ J e f = 1

def AETopologicalRing.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
      IsTopologicalRing (AE F E) ∧ Continuous (sigA c) ∧
      (∃ δ : E, c δ = -δ ∧ ∀ a : AE F E, ∃! p : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F,
        a = p.1 • (1 : AE F E) + p.2 • inclA F E δ) ∧
      ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) (AE F E)),
        Continuous (fun p : Matrix (Fin N) (Fin N) (AE F E) × Matrix (Fin N) (Fin N) (AE F E) =>
          p.1 * p.2) ∧
        Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => gᵀ * J * g.map (sigA c)) ∧
        Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => g.det) ∧
        IsClosed (SU (sigA c) J)

def EDenseInAE.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
      DenseRange (inclA F E)

def OrthProjection.Statement : Prop :=
  (∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) R), Jᵀ = J.map σ →
    ∀ e f : Fin N → R, hf σ J e e = 0 → hf σ J f f = 0 → hf σ J e f = 1 →
      IsLinearMap R (perpProj σ J e f) ∧
      (∀ u, perpProj σ J e f (perpProj σ J e f u) = perpProj σ J e f u) ∧
      (∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0) ∧
      (∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u)) ∧
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E) (e f : Fin N → E),
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
      Continuous (perpProj (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f)) ∧
      ∀ u : Fin N → E, inclA F E ∘ perpProj c.toRingHom J e f u =
        perpProj (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) (inclA F E ∘ u))

def EichlerDense.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), Jᵀ = J.map c →
    ∀ e f : Fin N → E, hf c.toRingHom J e e = 0 → hf c.toRingHom J f f = 0 →
      hf c.toRingHom J e f = 1 →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
      eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) ⊆
          closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) ''
            eichAlong c.toRingHom J e f) ∧
        eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ f) (inclA F E ∘ e) ⊆
          closure ((fun γ : Matrix (Fin N) (Fin N) E => γ.map (inclA F E)) ''
            eichAlong c.toRingHom J f e)

def ClosureIsSubmonoid.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), Jᵀ = J.map c → IsUnit J.det →
    ∀ e f : Fin N → E, hf c.toRingHom J e e = 0 → hf c.toRingHom J f f = 0 →
      hf c.toRingHom J e f = 1 →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
      Cl c J ⊆ SU (sigA c) (J.map (inclA F E)) ∧ (1 : Matrix (Fin N) (Fin N) (AE F E)) ∈ Cl c J ∧
      (∀ a ∈ Cl c J, ∀ b ∈ Cl c J, a * b ∈ Cl c J) ∧
      eichSet (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f) ⊆ Cl c J

def LocalRingHypotheses.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ x, sigV c v (sigV c v x) = x) ∧
      (∀ x, sigV c v x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion F) (Kv E v))) ∧
      Module.finrank (v.adicCompletion F) (Kv E v) = 2 ∧ IsReduced (Kv E v) ∧
      (2 : v.adicCompletion F) ≠ 0 ∧
      (∀ x : E, sigV c v (inclV E v x) = inclV E v (c x)) ∧
      ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E) (x y : Fin N → E),
        inclV E v (hf c.toRingHom J x y) =
          hf (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ x) (inclV E v ∘ y)

def PlaceMaps.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    (∀ a b : AE F E, (∀ v, compAt E v a = compAt E v b) → a = b) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ x, compAt E v (singleV E v x) = x) ∧
      (∀ w, w ≠ v → ∀ x, compAt E w (singleV E v x) = 0) ∧
      (∀ x y, singleV E v (x * y) = singleV E v x * singleV E v y) ∧
      (∀ w, w ≠ v → ∀ x y, singleV E v x * singleV E w y = 0) ∧
      (∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y) ∧
      (∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x)) ∧
      (∀ a, compAt E v (sigA c a) = sigV c v (compAt E v a)) ∧
      (∀ x : E, compAt E v (inclA F E x) = inclV E v x) ∧
      ∀ N : ℕ,
        embed E v (1 : Matrix (Fin N) (Fin N) (Kv E v)) = 1 ∧
        (∀ g h : Matrix (Fin N) (Fin N) (Kv E v), embed E v (g * h) = embed E v g * embed E v h) ∧
        ∀ J : Matrix (Fin N) (Fin N) E,
          (∀ g ∈ SU (sigV c v).toRingHom (J.map (inclV E v)),
            embed E v g ∈ SU (sigA c) (J.map (inclA F E))) ∧
          ∀ x ∈ SU (sigA c) (J.map (inclA F E)),
            x.map (compAt E v) ∈ SU (sigV c v).toRingHom (J.map (inclV E v))

def EichlerAtPlace.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (J : Matrix (Fin N) (Fin N) E),
      (∀ (e : Fin N → E) (u : Fin N → Kv E v) (c' : Kv E v),
        embed E v (eich (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) u c') =
          eich (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (singleV E v ∘ u) (singleV E v c')) ∧
      (Jᵀ = J.map c → ∀ e f : Fin N → E, hf c.toRingHom J e e = 0 → hf c.toRingHom J f f = 0 →
        hf c.toRingHom J e f = 1 →
        ∀ g ∈ eichSet (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) (inclV E v ∘ f),
          embed E v g ∈ eichSet (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (inclA F E ∘ f))

def LocalInClosure.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), Jᵀ = J.map c → IsUnit J.det →
    (∃ e : Fin N → E, e ≠ 0 ∧ hf c.toRingHom J e e = 0) →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
    ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ g ∈ SU (sigV c v).toRingHom (J.map (inclV E v)),
      embed E v g ∈ Cl c J

def AENeighbourhoods.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
      (∀ (N : ℕ), ∀ U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E)),
        ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ M : Matrix (Fin N) (Fin N) (AE F E),
          (∀ i j, (∀ v ∈ S, compAt E v (M i j) = 0) ∧ ∀ v ∉ S, compAt E v (M i j) ∈ intAt E v) →
          M ∈ U) ∧
      ∀ a : AE F E, ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, compAt E v a ∈ intAt E v

def Truncation.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 →
    ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), Jᵀ = J.map c → IsUnit J.det →
    (∃ e : Fin N → E, e ≠ 0 ∧ hf c.toRingHom J e e = 0) →
    ∀ [TopologicalSpace (AE F E)] [IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (AE F E)],
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Matrix (Fin N) (Fin N) (AE F E)),
      (∀ v ∈ S, (trunc E S x).map (compAt E v) = x.map (compAt E v)) ∧
      (∀ v ∉ S, (trunc E S x).map (compAt E v) = 1) ∧
      (∀ l : List (HeightOneSpectrum (𝓞 F)), l.Nodup → (∀ v, v ∈ l ↔ v ∈ S) →
        trunc E S x = (l.map fun v => embed E v (x.map (compAt E v))).prod) ∧
      (x ∈ SU (sigA c) (J.map (inclA F E)) → trunc E S x ∈ Cl c J)

def SAHolds.Statement : Prop := SAStatement

def SAOpenHolds.Statement : Prop := SAOpenStatement

section Inhabitants

open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic

def placeOf (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)})
  isPrime := by
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hmem : Rat.ringOfIntegersEquiv.symm (p : ℤ) ∈
        Ideal.comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      exact Ideal.mem_span_singleton_self (p : ℤ)
    rw [h, Ideal.mem_bot] at hmem
    have := congrArg Rat.ringOfIntegersEquiv hmem
    rw [RingEquiv.apply_symm_apply, map_zero, Nat.cast_eq_zero] at this
    exact hp.ne_zero this

def v5 : HeightOneSpectrum (𝓞 ℚ) := placeOf 5 (by norm_num)

def v3 : HeightOneSpectrum (𝓞 ℚ) := placeOf 3 (by norm_num)

theorem place_three_ne_place_five : v3 ≠ v5 := by
  intro h
  have h1 : Rat.ringOfIntegersEquiv.symm ((3 : ℕ) : ℤ) ∈ v3.asIdeal := by
    change _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact Ideal.mem_span_singleton_self ((3 : ℕ) : ℤ)
  rw [h] at h1
  change _ ∈ Ideal.comap _ _ at h1
  rw [Ideal.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, Ideal.mem_span_singleton] at h1
  norm_num at h1

def gI : GaussQ := ⟨0, 1⟩

theorem conj_gI : conj ℚ GaussQ gI = -gI := by
  rw [conj_gaussQ]; ext <;> simp [gI]

theorem gauss_finrank : Module.finrank ℚ GaussQ = 2 := QuadraticAlgebra.finrank_eq_two _ _

theorem gauss_conj_ne_one : conj ℚ GaussQ ≠ 1 := by
  intro h
  have := congrArg (fun φ : GaussQ ≃ₐ[ℚ] GaussQ => (φ gI).im) h
  rw [conj_gI, AlgEquiv.one_apply] at this
  simp only [QuadraticAlgebra.im_neg, gI] at this
  norm_num at this

theorem gauss_invol (x : GaussQ) : (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x :=
  conj_conj x

theorem gauss_two_ne_zero : (2 : GaussQ) ≠ 0 := two_ne_zero

def hypPlane : Matrix (Fin 2) (Fin 2) GaussQ := !![0, 1; 1, 0]

def e0 : Fin 2 → GaussQ := ![1, 0]

def f0 : Fin 2 → GaussQ := ![0, 1]

theorem hypPlane_herm : hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) := by
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [hypPlane]

theorem hypPlane_herm' : hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom := hypPlane_herm

theorem hypPlane_unit : IsUnit hypPlane.det := by
  simp [hypPlane, det_fin_two]

theorem isotropic_vector_ne_zero : e0 ≠ 0 := by
  intro h; have := congrFun h 0; simp [e0] at this

theorem hf_e0e0 : hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 := by
  simp [hf, hypPlane, e0, Fin.sum_univ_two]

theorem hf_f0f0 : hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 := by
  simp [hf, hypPlane, f0, Fin.sum_univ_two]

theorem hf_e0f0 : hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 := by
  simp [hf, hypPlane, e0, f0, Fin.sum_univ_two]

theorem gauss_isotropic : ∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0 :=
  ⟨e0, isotropic_vector_ne_zero, hf_e0e0⟩

@[instance_reducible] def topAE : TopologicalSpace (AE ℚ GaussQ) := moduleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ)

attribute [local instance] topAE

theorem isModuleTopology_AE : IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) := ⟨rfl⟩

attribute [local instance] isModuleTopology_AE

theorem sigV_invol (v : HeightOneSpectrum (𝓞 ℚ)) (x : Kv GaussQ v) :
    sigV (conj ℚ GaussQ) v (sigV (conj ℚ GaussQ) v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigV, Algebra.TensorProduct.map_tmul, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigA_invol (x : AE ℚ GaussQ) : sigA (conj ℚ GaussQ) (sigA (conj ℚ GaussQ) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigA, Algebra.TensorProduct.map_tmul, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigV_inclV (v : HeightOneSpectrum (𝓞 ℚ)) (x : GaussQ) :
    sigV (conj ℚ GaussQ) v (inclV GaussQ v x) = inclV GaussQ v (conj ℚ GaussQ x) := by
  simp [sigV, inclV, Algebra.TensorProduct.map_tmul]

theorem sigA_inclA (x : GaussQ) :
    sigA (conj ℚ GaussQ) (inclA ℚ GaussQ x) = inclA ℚ GaussQ (conj ℚ GaussQ x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

theorem localConjugation_ne_id_at_five : sigV (conj ℚ GaussQ) v5 (inclV GaussQ v5 gI) = inclV GaussQ v5 (-gI) := by
  rw [sigV_inclV, conj_gI]

theorem compAt_tmul (a : FiniteAdeleRing (𝓞 ℚ) ℚ) (y : GaussQ) :
    compAt GaussQ v5 (a ⊗ₜ[ℚ] y) = a v5 ⊗ₜ[ℚ] y := rfl

theorem singleV_tmul (x : v5.adicCompletion ℚ) (y : GaussQ) :
    singleV GaussQ v5 (x ⊗ₜ[ℚ] y) = singleF ℚ v5 x ⊗ₜ[ℚ] y := rfl

open Classical in
theorem singleAdele_at_same_place (x : v5.adicCompletion ℚ) : singleF ℚ v5 x v5 = x := by
  change Pi.single v5 x v5 = x
  simp

open Classical in
theorem singleAdele_at_other_place (x : v5.adicCompletion ℚ) : singleF ℚ v5 x v3 = 0 := by
  change Pi.single v5 x v3 = 0
  simp [place_three_ne_place_five]

theorem one_mem_intAt : (1 : Kv GaussQ v5) ∈ intAt GaussQ v5 :=
  AddSubgroup.subset_closure ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩

theorem trunc_empty (x : Matrix (Fin 2) (Fin 2) (AE ℚ GaussQ)) : trunc GaussQ ∅ x = 1 := by
  ext i j; simp [trunc, restrictTo]

theorem embed_one_at_five : embed GaussQ v5 (1 : Matrix (Fin 2) (Fin 2) (Kv GaussQ v5)) = 1 := by
  ext i j; simp [embed]

theorem one_mem_Cl : (1 : Matrix (Fin 2) (Fin 2) (AE ℚ GaussQ)) ∈ Cl (conj ℚ GaussQ) hypPlane :=
  subset_closure ⟨1, one_mem_SU, by simp⟩

theorem perpProjection_isotropic_self : perpProj (conj ℚ GaussQ).toRingHom hypPlane e0 f0 e0 = 0 := by
  simp only [perpProj]
  rw [hf_e0f0, hf_e0e0]
  simp

def g5 : Matrix (Fin 2) (Fin 2) (Kv GaussQ v5) :=
  eich (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) (inclV GaussQ v5 ∘ e0) 0
    (inclV GaussQ v5 gI)

theorem unipotent_mem_eichlerAlong :
    g5 ∈ eichAlong (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5))
      (inclV GaussQ v5 ∘ e0) (inclV GaussQ v5 ∘ f0) := by
  refine ⟨0, inclV GaussQ v5 gI, hf_zero_left _ _ _, hf_zero_left _ _ _, ?_, rfl⟩
  rw [hf_zero_left]
  change inclV GaussQ v5 gI + sigV (conj ℚ GaussQ) v5 (inclV GaussQ v5 gI) + 0 = 0
  rw [localConjugation_ne_id_at_five, map_neg]; ring

theorem unipotent_mem_eichlerSet :
    g5 ∈ eichSet (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5))
      (inclV GaussQ v5 ∘ e0) (inclV GaussQ v5 ∘ f0) := Or.inl unipotent_mem_eichlerAlong

theorem hyperbolicPlane_hermitian_at_five : (hypPlane.map (inclV GaussQ v5))ᵀ =
    (hypPlane.map (inclV GaussQ v5)).map (sigV (conj ℚ GaussQ) v5).toRingHom := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hypPlane]

theorem unipotent_mem_specialUnitary : g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) :=
  eichAlong_sub (fun x => sigV_invol v5 x) hyperbolicPlane_hermitian_at_five
    (by simp [hf, hypPlane, e0, Fin.sum_univ_two]) unipotent_mem_eichlerAlong

def gA : Matrix (Fin 2) (Fin 2) (AE ℚ GaussQ) :=
  eich (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) (inclA ℚ GaussQ ∘ e0) 0
    (inclA ℚ GaussQ gI)

theorem hypPlane_herm_A : (hypPlane.map (inclA ℚ GaussQ))ᵀ =
    (hypPlane.map (inclA ℚ GaussQ)).map (sigA (conj ℚ GaussQ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hypPlane]

theorem gA_mem_SU : gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) := by
  refine eichAlong_sub (f := inclA ℚ GaussQ ∘ f0) (fun x => sigA_invol x) hypPlane_herm_A
    (by simp [hf, hypPlane, e0, Fin.sum_univ_two]) ⟨0, inclA ℚ GaussQ gI, hf_zero_left _ _ _,
      hf_zero_left _ _ _, ?_, rfl⟩
  rw [hf_zero_left, sigA_inclA, conj_gI, map_neg]; ring

theorem inv_mem_SU {R : Type*} [CommRing R] (σ : R →+* R) {N : ℕ} (J : Matrix (Fin N) (Fin N) R)
    {a : Matrix (Fin N) (Fin N) R} (ha : a ∈ SU σ J) : a⁻¹ ∈ SU σ J := by
  obtain ⟨hdet, hu⟩ := ha
  have hunit : IsUnit a.det := by rw [hdet]; exact isUnit_one
  have hmap : a.map σ * a⁻¹.map σ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.map_one _ (map_zero σ) (map_one σ)]
  refine ⟨by rw [Matrix.det_nonsing_inv, hdet, Ring.inverse_one], ?_⟩
  calc a⁻¹ᵀ * J * a⁻¹.map σ = a⁻¹ᵀ * (aᵀ * J * a.map σ) * a⁻¹.map σ := by rw [hu]
    _ = (a * a⁻¹)ᵀ * J * (a.map σ * a⁻¹.map σ) := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Matrix.mul_nonsing_inv _ hunit, hmap]; simp

theorem HypPairExists.hyps :
    (∀ x, (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x) ∧ (2 : GaussQ) ≠ 0 ∧
      hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom ∧ IsUnit hypPlane.det ∧ e0 ≠ 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 :=
  ⟨gauss_invol, gauss_two_ne_zero, hypPlane_herm', hypPlane_unit, isotropic_vector_ne_zero, hf_e0e0⟩

theorem AETopologicalRing.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) :=
  ⟨gauss_finrank, gauss_conj_ne_one, isModuleTopology_AE⟩

theorem EDenseInAE.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) :=
  ⟨gauss_finrank, gauss_conj_ne_one, isModuleTopology_AE⟩

theorem OrthProjection.hyps :
    (∀ x, (conj ℚ GaussQ).toRingHom ((conj ℚ GaussQ).toRingHom x) = x) ∧
      hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ).toRingHom ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) :=
  ⟨gauss_invol, hypPlane_herm', hf_e0e0, hf_f0f0, hf_e0f0, gauss_finrank, gauss_conj_ne_one,
    isModuleTopology_AE⟩

theorem EichlerDense.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hf_e0e0, hf_f0f0, hf_e0f0, isModuleTopology_AE⟩

theorem ClosureIsSubmonoid.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hypPlane_unit, hf_e0e0, hf_f0f0, hf_e0f0,
    isModuleTopology_AE⟩

theorem LocalRingHypotheses.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ Nonempty (HeightOneSpectrum (𝓞 ℚ)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, ⟨v5⟩⟩

theorem PlaceMaps.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ v3 ≠ v5 ∧
      g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, place_three_ne_place_five, unipotent_mem_specialUnitary, gA_mem_SU⟩

theorem EichlerAtPlace.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 e0 = 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane f0 f0 = 0 ∧
      hf (conj ℚ GaussQ).toRingHom hypPlane e0 f0 = 1 ∧
      g5 ∈ eichSet (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5))
        (inclV GaussQ v5 ∘ e0) (inclV GaussQ v5 ∘ f0) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hf_e0e0, hf_f0f0, hf_e0f0, unipotent_mem_eichlerSet⟩

theorem LocalInClosure.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      (∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0) ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      g5 ∈ SU (sigV (conj ℚ GaussQ) v5).toRingHom (hypPlane.map (inclV GaussQ v5)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hypPlane_unit, gauss_isotropic,
    isModuleTopology_AE, unipotent_mem_specialUnitary⟩

theorem AENeighbourhoods.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      (Set.univ : Set (Matrix (Fin 2) (Fin 2) (AE ℚ GaussQ))) ∈ 𝓝 0 :=
  ⟨gauss_finrank, gauss_conj_ne_one, isModuleTopology_AE, Filter.univ_mem⟩

theorem Truncation.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      (∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0) ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      [v5].Nodup ∧ (∀ v, v ∈ [v5] ↔ v ∈ ({v5} : Finset (HeightOneSpectrum (𝓞 ℚ)))) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hypPlane_unit, gauss_isotropic,
    isModuleTopology_AE, List.nodup_singleton _, fun v => by simp, gA_mem_SU⟩

theorem SAHolds.hyps :
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      (∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0) ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hypPlane_unit, gauss_isotropic,
    isModuleTopology_AE, gA_mem_SU⟩

theorem SAOpenHolds.hyps :
    let Kg := SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ))
    Module.finrank ℚ GaussQ = 2 ∧ conj ℚ GaussQ ≠ 1 ∧ hypPlaneᵀ = hypPlane.map (conj ℚ GaussQ) ∧
      IsUnit hypPlane.det ∧
      (∃ e : Fin 2 → GaussQ, e ≠ 0 ∧ hf (conj ℚ GaussQ).toRingHom hypPlane e e = 0) ∧
      IsModuleTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) (AE ℚ GaussQ) ∧
      Kg ⊆ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) ∧ 1 ∈ Kg ∧
      (∀ a ∈ Kg, ∀ b ∈ Kg, a * b ∈ Kg) ∧ (∀ a ∈ Kg, a⁻¹ ∈ Kg) ∧
      (∃ O, IsOpen O ∧ O ∩ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) = Kg) ∧
      gA ∈ SU (sigA (conj ℚ GaussQ)) (hypPlane.map (inclA ℚ GaussQ)) :=
  ⟨gauss_finrank, gauss_conj_ne_one, hypPlane_herm, hypPlane_unit, gauss_isotropic,
    isModuleTopology_AE, le_rfl, one_mem_SU, fun _ ha _ hb => mul_mem_SU ha hb,
    fun _ ha => inv_mem_SU _ _ ha, ⟨Set.univ, isOpen_univ, Set.univ_inter _⟩, gA_mem_SU⟩

end Inhabitants

end StrongApprox

end GroundTheory.Heights₂.Heights
