import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjectiveCokerOfIsLocallyConstantFinrankRange

open MvPolynomial Module
open Function (Injective)
open scoped TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.FormsFamily

variable {R σ Hh : Type} [CommRing R]

abbrev formsIn (I : Ideal (MvPolynomial σ R)) (e : ℕ) : Submodule R (homogeneousSubmodule σ R e) :=
  (I.restrictScalars R).comap (homogeneousSubmodule σ R e).subtype

def cmp (B : Type) [CommRing B] [Algebra R B] (e : ℕ) :
    B ⊗[R] homogeneousSubmodule σ R e →ₗ[B] MvPolynomial σ B :=
  (algebraTensorAlgEquiv R B).toLinearEquiv.toLinearMap ∘ₗ (homogeneousSubmodule σ R e).subtype.baseChange B

theorem cmp_tmul (B : Type) [CommRing B] [Algebra R B] (e : ℕ) (b : B) (F : homogeneousSubmodule σ R e) :
    cmp B e (b ⊗ₜ F) = b • map (algebraMap R B) (F : MvPolynomial σ R) := by
  simp [cmp, algebraTensorAlgEquiv_tmul]

theorem cmp_injective (B : Type) [CommRing B] [Algebra R B] (e : ℕ) :
    Injective (cmp (R := R) (σ := σ) B e) := by
  refine (algebraTensorAlgEquiv R B).injective.comp
    (lTensor_subtype_injective_of_retraction (homogeneousSubmodule σ R e)
      ((homogeneousComponent e).codRestrict _ fun F => homogeneousComponent_mem e F) ?_ B)
  ext1 F
  exact Subtype.ext (homogeneousComponent_eq_self F.2)

theorem map_homogeneousComponent {B : Type} [CommRing B] (φ : R →+* B) (n : ℕ) (p : MvPolynomial σ R) :
    map φ (homogeneousComponent n p) = homogeneousComponent n (map φ p) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem mem_span_of_mem_map {B : Type} [CommRing B] (φ : R →+* B) (I : Ideal (MvPolynomial σ R))
    {F : MvPolynomial σ B} (hF : F ∈ I.map (map φ)) : F ∈ Submodule.span B (map φ '' (I : Set (MvPolynomial σ R))) := by
  have hX : ∀ (i : σ), ∀ G ∈ Submodule.span B (map φ '' (I : Set (MvPolynomial σ R))),
      X i * G ∈ Submodule.span B (map φ '' (I : Set (MvPolynomial σ R))) := by
    intro i G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨X i * y, I.mul_mem_left _ hy, by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  have hm : ∀ (a : MvPolynomial σ B), ∀ G ∈ Submodule.span B (map φ '' (I : Set (MvPolynomial σ R))),
      a * G ∈ Submodule.span B (map φ '' (I : Set (MvPolynomial σ R))) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C b => intro G hG; rw [C_mul']; exact Submodule.smul_mem _ _ hG
    | add p q hp hq => intro G hG; rw [add_mul]; exact add_mem (hp G hG) (hq G hG)
    | mul_X p i hp => intro G hG; rw [mul_assoc]; exact hp _ (hX i G hG)
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => simp
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact hm a x hx

theorem map_cmp_formsIn (B : Type) [CommRing B] [Algebra R B] (I : Ideal (MvPolynomial σ R))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ) :
    ((formsIn I e).baseChange B).map (cmp B e) =
      homogeneousSubmodule σ B e ⊓ (I.map (map (algebraMap R B))).restrictScalars B := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    rw [TensorProduct.mk_apply, cmp_tmul, one_smul]
    exact ⟨IsHomogeneous.map F.2 _, Ideal.mem_map_of_mem _ hF⟩
  · rintro F ⟨hF, hFI⟩
    have h1 := mem_span_of_mem_map _ I hFI
    rw [← homogeneousComponent_eq_self hF]
    clear hF hFI
    induction h1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨1 ⊗ₜ ⟨homogeneousComponent e y, homogeneousComponent_mem e y⟩,
        Submodule.tmul_mem_baseChange_of_mem _ (hI y hy e), ?_⟩
      rw [cmp_tmul, one_smul, map_homogeneousComponent]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem range_cmp (B : Type) [CommRing B] [Algebra R B] (e : ℕ) :
    LinearMap.range (cmp (R := R) (σ := σ) B e) = homogeneousSubmodule σ B e := by
  have h := map_cmp_formsIn B (⊤ : Ideal (MvPolynomial σ R)) (fun _ _ _ => trivial) e
  rw [Ideal.map_top] at h
  simpa [formsIn] using h

def formsBasis (R σ : Type) [CommRing R] (e : ℕ) :
    Basis {m : σ →₀ ℕ | m.degree = e} R (homogeneousSubmodule σ R e) :=
  (basisRestrictSupport R {m : σ →₀ ℕ | m.degree = e}).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported σ R e).symm)

theorem forms_free (e : ℕ) : Module.Free R (homogeneousSubmodule σ R e) := .of_basis (formsBasis R σ e)

theorem forms_finite [Finite σ] (e : ℕ) : Module.Finite R (homogeneousSubmodule σ R e) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)

theorem finrank_tensor_forms (K : Type) [Field K] [Algebra R K] (e : ℕ) :
    finrank K (K ⊗[R] homogeneousSubmodule σ R e) = Nat.card {m : σ →₀ ℕ | m.degree = e} :=
  Module.finrank_eq_nat_card_basis ((formsBasis R σ e).baseChange K)

theorem finrank_quot_add_dimDeg [Finite σ] (K : Type) [Field K] [Algebra R K] (I : Ideal (MvPolynomial σ R))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ) :
    finrank K (K ⊗[R] (homogeneousSubmodule σ R e ⧸ formsIn I e)) + dimDeg (I.map (map (algebraMap R K))) e =
      Nat.card {m : σ →₀ ℕ | m.degree = e} := by
  haveI := forms_finite (R := R) (σ := σ) e
  rw [(baseChangeQuotEquiv K _).finrank_eq, dimDeg, ← map_cmp_formsIn K I hI e,
    ← (Submodule.equivMapOfInjective _ (cmp_injective K e) _).finrank_eq, Submodule.finrank_quotient_add_finrank,
    finrank_tensor_forms]

def ev (d : ℕ) (p : Hh → σ → R) : homogeneousSubmodule σ R d →ₗ[R] (Hh → R) :=
  LinearMap.pi fun h => (aeval (p h)).toLinearMap ∘ₗ (homogeneousSubmodule σ R d).subtype

theorem ev_apply (d : ℕ) (p : Hh → σ → R) (F : homogeneousSubmodule σ R d) (h : Hh) :
    ev d p F h = eval (p h) (F : MvPolynomial σ R) := by
  simp [ev, coe_aeval_eq_eval]

theorem eval_eq_zero_of_mem_vanIdeal {d : ℕ} {p : Hh → σ → R} {F : MvPolynomial σ R} (hF : F ∈ vanIdeal d p)
    (h : Hh) : eval (p h) F = 0 := by
  have : vanIdeal d p ≤ RingHom.ker (eval (p h)) := Ideal.span_le.2 fun G hG => hG.2 h
  exact this hF

theorem component_mem_vanIdeal (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI := (MvPolynomial.gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R))
  have h : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨d, hx.1⟩
  have := h e hF
  rwa [show ((DirectSum.decompose (homogeneousSubmodule σ R) F e : homogeneousSubmodule σ R e) : MvPolynomial σ R)
    = homogeneousComponent e F from MvPolynomial.decomposition.decompose'_apply F e] at this

theorem ker_ev (d : ℕ) (p : Hh → σ → R) : LinearMap.ker (ev d p) = formsIn (vanIdeal d p) d := by
  ext F
  rw [LinearMap.mem_ker, funext_iff]
  simp only [ev_apply]
  exact ⟨fun h => Ideal.subset_span ⟨F.2, h⟩, fun h => eval_eq_zero_of_mem_vanIdeal h⟩

theorem map_cmp_ker_ev [Finite Hh] (B : Type) [CommRing B] [Algebra R B] (d : ℕ) (p : Hh → σ → R) :
    (LinearMap.ker ((ev d p).baseChange B)).map (cmp B d) =
      homogeneousSubmodule σ B d ⊓ (vanIdeal d fun h i => algebraMap R B (p h i)).restrictScalars B := by
  classical
  letI := Fintype.ofFinite Hh
  have key : ∀ z h, TensorProduct.piScalarRight R B B Hh ((ev d p).baseChange B z) h =
      eval (fun i => algebraMap R B (p h i)) (cmp B d z) := by
    intro z h
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | tmul b F =>
      rw [cmp_tmul, smul_eval, LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul]
      beta_reduce
      rw [ev_apply, Algebra.smul_def, mul_comm, eval_map]
      congr 1
      rw [← eval₂_id, eval₂_comp_left, RingHom.comp_id]
      rfl
  ext F
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h1 : cmp B d z ∈ homogeneousSubmodule σ B d := range_cmp (R := R) B d ▸ LinearMap.mem_range_self _ z
    refine ⟨h1, Ideal.subset_span ⟨h1, fun h => ?_⟩⟩
    rw [← key, LinearMap.mem_ker.1 hz]
    simp
  · rintro ⟨h1, h2⟩
    rw [← range_cmp (R := R) B d] at h1
    obtain ⟨z, rfl⟩ := h1
    refine ⟨z, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← (TensorProduct.piScalarRight R B B Hh).map_eq_zero_iff]
    ext h
    rw [key]
    exact eval_eq_zero_of_mem_vanIdeal h2 h

theorem map_vanIdeal_of_ker [Finite Hh] (B : Type) [CommRing B] [Algebra R B] (d : ℕ) (p : Hh → σ → R)
    (h : (LinearMap.ker (ev d p)).baseChange B = LinearMap.ker ((ev d p).baseChange B)) :
    (vanIdeal d p).map (map (algebraMap R B)) = vanIdeal d fun h i => algebraMap R B (p h i) := by
  have h1 := map_cmp_ker_ev B d p
  rw [← h, ker_ev, map_cmp_formsIn B _ (component_mem_vanIdeal d p)] at h1
  apply le_antisymm
  · rw [vanIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact (h1.le ⟨IsHomogeneous.map hF.1 _, Ideal.mem_map_of_mem _ (Ideal.subset_span hF)⟩).2
  · rw [vanIdeal, Ideal.span_le]
    intro F hF
    exact (h1.ge ⟨hF.1, Ideal.subset_span hF⟩).2

theorem finrank_range_ev_add_dimDeg [Finite σ] [Finite Hh] (K : Type) [Field K] [Algebra R K] (d : ℕ)
    (p : Hh → σ → R) :
    finrank K (LinearMap.range ((ev d p).baseChange K)) + dimDeg (vanIdeal d fun h i => algebraMap R K (p h i)) d =
      Nat.card {m : σ →₀ ℕ | m.degree = d} := by
  haveI := forms_finite (R := R) (σ := σ) d
  rw [dimDeg, ← map_cmp_ker_ev K d p,
    ← (Submodule.equivMapOfInjective _ (cmp_injective K d) _).finrank_eq,
    LinearMap.finrank_range_add_finrank_ker, finrank_tensor_forms]

theorem exists_finrank_le (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (K : Type) [Field K] [Algebra R K] :
    ∃ f : R, algebraMap R K f ≠ 0 ∧ ∀ (L : Type) [Field L] [Algebra R L], algebraMap R L f ≠ 0 →
      finrank L (L ⊗[R] M) ≤ finrank K (K ⊗[R] M) := by
  let q : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩
  obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1
    (Semicont.eventually_finrank_fiber_le (M := M) q)
  refine ⟨f, hpf, fun L _ _ hL => ?_⟩
  let q' : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R L), RingHom.ker_isPrime _⟩
  rw [finrank_tensorProduct_eq_finrank_fiber L q' rfl, finrank_tensorProduct_eq_finrank_fiber K q rfl]
  exact hf (show q' ∈ _ from hL)

theorem exists_dimDeg_map_le [Finite σ] (I : Ideal (MvPolynomial σ R))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ) (K : Type) [Field K] (x : R →+* K) :
    ∃ f : R, x f ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 →
      dimDeg (I.map (map x)) e ≤ dimDeg (I.map (map y)) e := by
  haveI := forms_finite (R := R) (σ := σ) e
  letI := x.toAlgebra
  obtain ⟨f, hf, h⟩ := exists_finrank_le (R := R) (homogeneousSubmodule σ R e ⧸ formsIn I e) K
  refine ⟨f, hf, fun L _ y hy => ?_⟩
  letI := y.toAlgebra
  have h1 := h L hy
  have h2 := finrank_quot_add_dimDeg K I hI e
  have h3 := finrank_quot_add_dimDeg L I hI e
  change _ + dimDeg (I.map (map x)) e = _ at h2
  change _ + dimDeg (I.map (map y)) e = _ at h3
  omega

theorem exists_dimDeg_vanIdeal_le [Finite σ] [Finite Hh] (d : ℕ) (p : Hh → σ → R)
    (K : Type) [Field K] (x : R →+* K) :
    ∃ f : R, x f ≠ 0 ∧ ∀ (L : Type) [Field L] (y : R →+* L), y f ≠ 0 →
      dimDeg (vanIdeal d fun h i => y (p h i)) d ≤ dimDeg (vanIdeal d fun h i => x (p h i)) d := by
  letI := Fintype.ofFinite Hh
  letI := x.toAlgebra
  obtain ⟨f, hf, h⟩ := exists_finrank_le (R := R) ((Hh → R) ⧸ LinearMap.range (ev d p)) K
  refine ⟨f, hf, fun L _ y hy => ?_⟩
  letI := y.toAlgebra
  have h1 := h L hy
  have h2 := finrank_range_ev_add_dimDeg K d p
  have h3 := finrank_range_ev_add_dimDeg L d p
  have h4 := finrank_baseChange_coker_add_finrank_range K (ev d p)
  have h5 := finrank_baseChange_coker_add_finrank_range L (ev d p)
  rw [Module.finrank_eq_nat_card_basis ((Pi.basisFun R Hh).baseChange K)] at h4
  rw [Module.finrank_eq_nat_card_basis ((Pi.basisFun R Hh).baseChange L)] at h5
  change _ + dimDeg (vanIdeal d fun h i => x (p h i)) d = _ at h2
  change _ + dimDeg (vanIdeal d fun h i => y (p h i)) d = _ at h3
  omega

theorem map_vanIdeal_of_const [IsReduced R] [Finite σ] [Finite Hh] (d : ℕ) (p : Hh → σ → R) (ρ : ℚ)
    (h : ∀ (K : Type) [Field K] (x : R →+* K), (dimDeg (vanIdeal d fun h i => x (p h i)) d : ℚ) = ρ)
    (B : Type) [CommRing B] (x : R →+* B) :
    (vanIdeal d p).map (map x) = vanIdeal d fun h i => x (p h i) := by
  haveI := forms_finite (R := R) (σ := σ) d
  letI := x.toAlgebra
  obtain ⟨s, hs⟩ := exists_comp_comp_eq_of_isLocallyConstant_finrank_range (ev d p)
    (IsLocallyConstant.of_constant _ fun q q' => by
      have h1 := finrank_range_ev_add_dimDeg q.asIdeal.ResidueField d p
      have h2 := finrank_range_ev_add_dimDeg q'.asIdeal.ResidueField d p
      have h3 := Nat.cast_injective (R := ℚ) ((h _ (algebraMap R q.asIdeal.ResidueField)).trans
        (h _ (algebraMap R q'.asIdeal.ResidueField)).symm)
      omega)
  exact map_vanIdeal_of_ker B d p (baseChange_ker_of_comp_comp_eq _ s hs B)

theorem map_vanIdeal_of_flat [Finite Hh] (d : ℕ) (p : Hh → σ → R) (B : Type) [CommRing B] [Algebra R B]
    [Module.Flat R B] :
    (vanIdeal d p).map (map (algebraMap R B)) = vanIdeal d fun h i => algebraMap R B (p h i) :=
  map_vanIdeal_of_ker B d p (baseChange_ker B _)

theorem projective_of_const [IsReduced R] [Finite σ] (I : Ideal (MvPolynomial σ R))
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) (e : ℕ) (ρ : ℚ)
    (h : ∀ (K : Type) [Field K] (x : R →+* K), (dimDeg (I.map (map x)) e : ℚ) = ρ) :
    Module.Projective R (homogeneousSubmodule σ R e ⧸ formsIn I e) := by
  haveI := forms_finite (R := R) (σ := σ) e
  refine projective_of_finite_of_isLocallyConstant_finrank_fiber
    (IsLocallyConstant.of_constant _ fun q q' => ?_)
  have h1 := finrank_quot_add_dimDeg q.asIdeal.ResidueField I hI e
  have h2 := finrank_quot_add_dimDeg q'.asIdeal.ResidueField I hI e
  have h3 := Nat.cast_injective (R := ℚ) ((h _ (algebraMap R q.asIdeal.ResidueField)).trans
    (h _ (algebraMap R q'.asIdeal.ResidueField)).symm)
  omega

theorem map_vanIdeal_of_const_away [IsReduced R] [Finite σ] [Finite Hh] (d : ℕ) (p : Hh → σ → R) (ρ : ℚ) (f : R)
    (h : ∀ (K : Type) [Field K] (x : R →+* K), x f ≠ 0 → (dimDeg (vanIdeal d fun h i => x (p h i)) d : ℚ) = ρ)
    (K : Type) [Field K] (x : R →+* K) (hx : x f ≠ 0) :
    (vanIdeal d p).map (map x) = vanIdeal d fun h i => x (p h i) := by
  let A := Localization.Away f
  haveI : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
  haveI : IsReduced A := isReduced_localizationPreserves (Submonoid.powers f) A inferInstance
  let x' : A →+* K := IsLocalization.Away.lift f (IsUnit.mk0 _ hx)
  have hx' : x'.comp (algebraMap R A) = x := IsLocalization.Away.lift_comp f _
  have h1 := map_vanIdeal_of_const d (fun h i => algebraMap R A (p h i)) ρ (fun L _ y =>
    h L (y.comp (algebraMap R A)) ((IsLocalization.Away.algebraMap_isUnit (S := A) f).map y).ne_zero) K x'
  rw [← map_vanIdeal_of_flat, Ideal.map_map] at h1
  rw [← hx']
  convert h1 using 2
  · exact RingHom.ext fun F => (map_map _ _ F).symm
  · rfl

theorem dimDeg_eq_of_cutBy {K : Type} [Field K] {I : Ideal (MvPolynomial σ K)} {Q : Polynomial ℚ} {d : ℕ}
    {p : Hh → σ → K} (h : CutBy I Q d p) {e : ℕ} (he : e ≥ d) :
    (dimDeg (vanIdeal d p) e : ℚ) = Q.eval (e : ℚ) := by
  have : homogeneousSubmodule σ K e ⊓ (vanIdeal d p).restrictScalars K =
      homogeneousSubmodule σ K e ⊓ I.restrictScalars K := by
    ext F
    exact and_congr_right fun hF => ((h e he).2 F hF).symm
  rw [← (h e he).1, dimDeg, dimDeg, this]

end GlobalTheory.ZM.FormsFamily
