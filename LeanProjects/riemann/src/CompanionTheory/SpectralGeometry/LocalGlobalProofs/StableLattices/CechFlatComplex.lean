import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatQuotientWeaklyRegular
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocalizationOfIsStandardSmooth

open IsLocalRing TensorProduct RingTheory.Sequence
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.CIFlatPf

theorem isRegular_fibre (k E : Type) [Field k] [CommRing E] [Algebra k E] (g : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g k E] (f : Fin g → E)
    (hA : IsArtinianRing (E ⧸ Ideal.span (Set.range f))) (Q : Ideal E) [Q.IsPrime]
    (hQ : Ideal.span (Set.range f) ≤ Q) :
    IsRegular (Localization.AtPrime Q) (List.ofFn fun i => algebraMap E (Localization.AtPrime Q) (f i)) := by
  haveI : IsRegularRing k := GroundTheory.Arith.SchemeCoh.isRegularRing_of_smooth_field k k
  haveI : Algebra.IsStandardSmooth k E :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  haveI hreg : IsRegularLocalRing (Localization.AtPrime Q) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth k E Q
  set I : Ideal E := Ideal.span (Set.range f) with hI
  have hmaxOf : ∀ P : Ideal E, P.IsPrime → I ≤ P → P.IsMaximal := by
    intro P hP hIP
    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ P := by
      rw [Ideal.mk_ker]
      exact hIP
    haveI : (P.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    haveI : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
    have hc : (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker]
    rw [← hc]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  haveI hQmax : Q.IsMaximal := hmaxOf Q inferInstance hQ
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial g k E
  letI := φ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) k) E := hφ
  have hht := GlobalTheory.StabFlat.height_of_etale_mvPolynomial k E g Q
  set ys := List.ofFn fun i => algebraMap E (Localization.AtPrime Q) (f i) with hys
  have hofList : Ideal.ofList ys = I.map (algebraMap E (Localization.AtPrime Q)) := by
    rw [hI, Ideal.map_span, ← Set.range_comp]
    delta Ideal.ofList
    congr 1
    ext r
    simp [hys, List.mem_ofFn]
  have hIm : Ideal.ofList ys ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [hofList, Ideal.map_le_iff_le_comap]
    calc I ≤ Q := hQ
      _ = _ := (Localization.AtPrime.under_maximalIdeal (I := Q)).symm
  have hrad : (Ideal.ofList ys).radical = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hIm, inferInstance⟩
    · apply le_sInf
      rintro J ⟨hJ, hJp⟩
      have hP : (J.comap (algebraMap E (Localization.AtPrime Q))).IsPrime := Ideal.comap_isPrime _ _
      have hIP : I ≤ J.comap (algebraMap E (Localization.AtPrime Q)) := by
        rw [← Ideal.map_le_iff_le_comap, ← hofList]
        exact hJ
      have hPQ : J.comap (algebraMap E (Localization.AtPrime Q)) ≤ Q := by
        calc J.comap (algebraMap E (Localization.AtPrime Q))
            ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
                (algebraMap E (Localization.AtPrime Q)) :=
              Ideal.comap_mono (IsLocalRing.le_maximalIdeal hJp.ne_top)
          _ = Q := Localization.AtPrime.under_maximalIdeal
      have hPmax := hmaxOf _ hP hIP
      have hPeq : J.comap (algebraMap E (Localization.AtPrime Q)) = Q :=
        hPmax.eq_of_le hQmax.ne_top hPQ
      have hJm : J = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
        have hPeq' : Ideal.under E J = Q := hPeq
        rw [← IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) J, hPeq',
          Localization.AtPrime.map_eq_maximalIdeal]
      exact hJm.ge
  have hQg : Q.height = g := by exact_mod_cast hht
  have hlen : (ys.length : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime Q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q), hys,
      List.length_ofFn, hQg]
    rfl
  exact GlobalTheory.isRegular_of_radical_eq_maximalIdeal hrad hlen

theorem residueField_exists (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (x : p.ResidueField) :
    ∃ a : R, ∃ b : R, b ∉ p ∧ b • x = algebraMap R p.ResidueField a := by
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime p) p.ResidueField) :=
    IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  refine ⟨a, s, s.2, ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField (s : R),
    ← map_mul, IsLocalization.mk'_spec', ← IsScalarTower.algebraMap_apply]

theorem fibre_exists (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (p : Ideal R) [p.IsPrime]
    (e : p.Fiber C) : ∃ b : R, b ∉ p ∧ ∃ c : C, b • e = (1 : p.ResidueField) ⊗ₜ[R] c := by
  induction e using TensorProduct.induction_on with
  | zero => exact ⟨1, p.primeCompl.one_mem, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, b, hb, hx⟩ := residueField_exists R p x
    refine ⟨b, hb, a • c, ?_⟩
    rw [TensorProduct.smul_tmul', hx, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add e₁ e₂ h₁ h₂ =>
    obtain ⟨b₁, hb₁, c₁, hc₁⟩ := h₁
    obtain ⟨b₂, hb₂, c₂, hc₂⟩ := h₂
    refine ⟨b₁ * b₂, p.primeCompl.mul_mem hb₁ hb₂, b₂ • c₁ + b₁ • c₂, ?_⟩
    have k₁ : (b₁ * b₂) • e₁ = (1 : p.ResidueField) ⊗ₜ[R] (b₂ • c₁) := by
      rw [mul_comm b₁ b₂, mul_smul, hc₁, TensorProduct.tmul_smul]
    have k₂ : (b₁ * b₂) • e₂ = (1 : p.ResidueField) ⊗ₜ[R] (b₁ • c₂) := by
      rw [mul_smul, hc₂, TensorProduct.tmul_smul]
    rw [smul_add, k₁, k₂, TensorProduct.tmul_add]

theorem exists_localization_fibre (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (q : Ideal C) [q.IsPrime] :
    ∃ (Q : Ideal ((q.under R).Fiber C)) (_ : Q.IsPrime)
      (e : Localization.AtPrime Q ≃+* (Localization.AtPrime q ⧸
        (q.under R).map (algebraMap R (Localization.AtPrime q)))),
      (∀ c ∈ q, (1 : (q.under R).ResidueField) ⊗ₜ[R] c ∈ Q) ∧
      ∀ c : C, e (algebraMap _ _ ((1 : (q.under R).ResidueField) ⊗ₜ[R] c)) =
        Ideal.Quotient.mk _ (algebraMap C (Localization.AtPrime q) c) := by
  set p := q.under R with hp
  let B := Localization.AtPrime q
  let J : Ideal B := p.map (algebraMap R B)
  have hmem : ∀ c : C, c ∉ q → IsUnit (algebraMap C B c) := fun c hc =>
    IsLocalization.map_units (M := q.primeCompl) B ⟨c, hc⟩
  have hRB : ∀ r : R, algebraMap R B r = algebraMap C B (algebraMap R C r) := fun r =>
    IsScalarTower.algebraMap_apply R C B r
  have hJ : J ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, hRB]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff B q _).mpr hr
  haveI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (fun h => (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp (h ▸ hJ)))
  haveI : IsLocalRing (B ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let cA : C →ₐ[R] B ⧸ J := (Ideal.Quotient.mkₐ R J).comp (IsScalarTower.toAlgHom R C B)
  have hcA : ∀ c, cA c = Ideal.Quotient.mk J (algebraMap C B c) := fun c => rfl
  have h1 : p ≤ RingHom.ker (algebraMap R (B ⧸ J)) := fun r hr =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  have h2 : p.primeCompl ≤ (IsUnit.submonoid (B ⧸ J)).comap (algebraMap R (B ⧸ J)) := by
    intro r hr
    have : IsUnit (algebraMap C B (algebraMap R C r)) := hmem _ hr
    exact (this.map (Ideal.Quotient.mk J))
  let hA : p.ResidueField →ₐ[R] B ⧸ J :=
    { Ideal.ResidueField.lift p (algebraMap R (B ⧸ J)) h1 h2 with
      commutes' := fun r => Ideal.ResidueField.lift_algebraMap p _ h1 h2 r }
  let θ : p.Fiber C →ₐ[R] B ⧸ J := Algebra.TensorProduct.productMap hA cA
  have hθ : ∀ c, θ ((1 : p.ResidueField) ⊗ₜ[R] c) = cA c := fun c => by
    simp [θ]
  letI : Algebra (p.Fiber C) (B ⧸ J) := θ.toRingHom.toAlgebra
  have hal : ∀ x, algebraMap (p.Fiber C) (B ⧸ J) x = θ x := fun _ => rfl
  let Q : Ideal (p.Fiber C) := (maximalIdeal (B ⧸ J)).comap (algebraMap (p.Fiber C) (B ⧸ J))
  haveI hQ : Q.IsPrime := inferInstance
  have hunit : ∀ t : C, t ∉ q → ((1 : p.ResidueField) ⊗ₜ[R] t : p.Fiber C) ∈ Q.primeCompl := by
    intro t ht h
    have h4 : θ ((1 : p.ResidueField) ⊗ₜ[R] t) ∈ maximalIdeal (B ⧸ J) := h
    rw [hθ, hcA] at h4
    exact h4 ((hmem t ht).map (Ideal.Quotient.mk J))
  have hzero : ∀ w ∈ p.map (algebraMap R C), (1 : p.ResidueField) ⊗ₜ[R] w = (0 : p.Fiber C) := by
    have : p.map (algebraMap R C) ≤ RingHom.ker
        (Algebra.TensorProduct.includeRight : C →ₐ[R] p.Fiber C).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (1 : p.ResidueField) ⊗ₜ[R] (algebraMap R C r) = 0
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
        Ideal.algebraMap_residueField_eq_zero.mpr hr, TensorProduct.zero_tmul]
    exact fun w hw => this hw
  have hloc : IsLocalization Q.primeCompl (B ⧸ J) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨s, hs⟩
      by_contra h
      exact hs h
    · intro z
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.surj q.primeCompl b
      refine ⟨⟨(1 : p.ResidueField) ⊗ₜ[R] c, ⟨(1 : p.ResidueField) ⊗ₜ[R] (t : C), hunit t t.2⟩⟩, ?_⟩
      change Ideal.Quotient.mk J b * θ ((1 : p.ResidueField) ⊗ₜ[R] (t : C)) = θ ((1 : p.ResidueField) ⊗ₜ[R] c)
      rw [hθ, hθ, hcA, hcA, ← map_mul, hct]
    · intro x y hxy
      have he : θ (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hxy
      obtain ⟨b, hb, c, hc⟩ := fibre_exists R C p (x - y)
      have hc0 : cA c = 0 := by
        rw [← hθ, ← hc, map_smul, he, smul_zero]
      have hcJ : algebraMap C B c ∈ (p.map (algebraMap R C)).map (algebraMap C B) := by
        have : algebraMap C B c ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hc0
        rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      obtain ⟨m, hm, hmc⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl B _ c).mp hcJ
      have hz : (1 : p.ResidueField) ⊗ₜ[R] (m * c) = (0 : p.Fiber C) := hzero _ hmc
      have hs : ((1 : p.ResidueField) ⊗ₜ[R] m : p.Fiber C) * (x - y) = 0 := by
        have h3 : b • (((1 : p.ResidueField) ⊗ₜ[R] m : p.Fiber C) * (x - y)) = 0 := by
          rw [← mul_smul_comm, hc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hz]
        rw [← algebraMap_smul p.ResidueField b] at h3
        exact (smul_eq_zero.mp h3).resolve_left fun h => hb (Ideal.algebraMap_residueField_eq_zero.mp h)
      exact ⟨⟨_, hunit m hm⟩, by rw [← sub_eq_zero, ← mul_sub]; exact hs⟩
  refine ⟨Q, hQ, (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (B ⧸ J)).toRingEquiv, ?_, fun c => ?_⟩
  · intro c hc
    change θ ((1 : p.ResidueField) ⊗ₜ[R] c) ∈ maximalIdeal (B ⧸ J)
    rw [hθ, hcA]
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq] at hy
    have h6 : algebraMap C B c ∈ maximalIdeal B :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff B q _).mpr hc
    have h7 := (maximalIdeal B).sub_mem (Ideal.mul_mem_right b _ h6) (hJ hy)
    rw [sub_sub_cancel] at h7
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h7)
  have h5 := (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (B ⧸ J)).commutes ((1 : p.ResidueField) ⊗ₜ[R] c)
  exact h5.trans ((hθ c).trans (hcA c))

theorem isArtinianRing_fibre_quotient (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (p : Ideal R) [p.IsPrime]
    {g : ℕ} (f : Fin g → C) [Algebra.QuasiFinite R (C ⧸ Ideal.span (Set.range f))] :
    IsArtinianRing (p.Fiber C ⧸ Ideal.span (Set.range fun i => (1 : p.ResidueField) ⊗ₜ[R] f i)) := by
  set I : Ideal C := Ideal.span (Set.range f) with hI
  set J : Ideal (p.ResidueField ⊗[R] C) :=
    Ideal.span (Set.range fun i => (1 : p.ResidueField) ⊗ₜ[R] f i) with hJ
  have hmap : I.map (Algebra.TensorProduct.includeRight : C →ₐ[R] p.ResidueField ⊗[R] C) = J := by
    rw [hI, Ideal.map_span, ← Set.range_comp]
    rfl
  have hfin : Module.Finite p.ResidueField (p.ResidueField ⊗[R] (C ⧸ I)) :=
    Algebra.QuasiFinite.finite_fiber (R := R) (S := C ⧸ I) p
  have hart : IsArtinianRing (p.ResidueField ⊗[R] (C ⧸ I)) :=
    IsArtinianRing.of_finite p.ResidueField _
  let φ : p.ResidueField ⊗[R] (C ⧸ I) →ₐ[p.ResidueField] (p.ResidueField ⊗[R] C) ⧸ J :=
    Algebra.TensorProduct.lift
      ((Ideal.Quotient.mkₐ p.ResidueField J).comp Algebra.TensorProduct.includeLeft)
      (Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R J).comp Algebra.TensorProduct.includeRight)
        (fun a ha => by
          rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, ← hmap]
          exact Ideal.mem_map_of_mem _ ha))
      (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x c =>
      refine ⟨x ⊗ₜ[R] Ideal.Quotient.mk I c, ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      show Ideal.Quotient.mk J (x ⊗ₜ[R] (1 : C)) *
          Ideal.Quotient.mk J ((1 : p.ResidueField) ⊗ₜ[R] c) = _
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add a b ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      exact ⟨s + s', by rw [map_add, hs, hs', map_add]⟩
  exact hsurj.isArtinianRing

theorem flat_localization (R C : Type) [CommRing R] [IsNoetherianRing R] [CommRing C] [Algebra R C] (g : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g R C] (f : Fin g → C)
    [Algebra.QuasiFinite R (C ⧸ Ideal.span (Set.range f))] (q : Ideal C) [q.IsPrime] :
    Module.Flat R (Localization.AtPrime q ⧸ (Ideal.span (Set.range f)).map (algebraMap C (Localization.AtPrime q))) := by
  have : Algebra.IsStandardSmooth R C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  by_cases hq : Ideal.span (Set.range f) ≤ q
  swap
  · obtain ⟨x, hx, hxq⟩ := SetLike.not_le_iff_exists.mp hq
    have hu : IsUnit (algebraMap C (Localization.AtPrime q) x) :=
      IsLocalization.map_units (M := q.primeCompl) _ ⟨x, hxq⟩
    have htop := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (algebraMap C (Localization.AtPrime q)) hx) hu
    rw [htop]
    have : Subsingleton (Localization.AtPrime q ⧸ (⊤ : Ideal (Localization.AtPrime q))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    have : Module.Free R (Localization.AtPrime q ⧸ (⊤ : Ideal (Localization.AtPrime q))) :=
      Module.Free.of_subsingleton _ _
    exact Module.Flat.of_free
  let p := q.under R
  let B := Localization.AtPrime q
  let A := Localization.AtPrime p
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver p q
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing q.primeCompl B inferInstance
  have : Module.Flat R B := Module.Flat.trans R C B
  have : Module.Flat A B := (Module.flat_iff_of_isLocalization A p.primeCompl B).mpr inferInstance
  let rs : List B := List.ofFn fun i => algebraMap C B (f i)
  have hofl : Ideal.ofList rs = (Ideal.span (Set.range f)).map (algebraMap C B) := by
    rw [Ideal.map_span, Ideal.ofList]
    congr 1
    ext x
    simp [rs, List.mem_ofFn]
  have hrs : ∀ r ∈ rs, r ∈ maximalIdeal B := by
    intro r hr
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff B q _).mpr (hq (Ideal.subset_span ⟨i, rfl⟩))
  have hmA : (maximalIdeal A).map (algebraMap A B) = p.map (algebraMap R B) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hW : IsWeaklyRegular (B ⧸ (maximalIdeal A).map (algebraMap A B)) rs := by
    rw [hmA]
    obtain ⟨Q, hQ, e, hcQ, he⟩ := exists_localization_fibre R C q
    have hreg := isRegular_fibre p.ResidueField (p.Fiber C) g
      (fun i => (1 : p.ResidueField) ⊗ₜ[R] f i) (isArtinianRing_fibre_quotient R C p f) Q (by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hcQ _ (hq (Ideal.subset_span ⟨i, rfl⟩)))
    rw [← isWeaklyRegular_map_algebraMap_iff (B ⧸ p.map (algebraMap R B))]
    haveI i1 := RingHomInvPair.of_ringEquiv e
    haveI i2 := RingHomInvPair.symm (e : Localization.AtPrime Q →+* (B ⧸ p.map (algebraMap R B)))
      (e.symm : (B ⧸ p.map (algebraMap R B)) →+* Localization.AtPrime Q)
    have h2 := (LinearEquiv.isWeaklyRegular_congr' e.toSemilinearEquiv _).mp hreg.1
    convert h2 using 1
    simp only [rs, List.map_ofFn]
    congr 1
    ext i
    exact (he (f i)).symm
  have h := GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre A B rs hrs hW
  rw [hofl] at h
  exact Module.Flat.trans R A _

theorem ciFlat : CompanionTheory.ObstructionTrivialLocus.CIFlat := by
  intro R C _ _ _ _ g _ f _
  have : Algebra.IsStandardSmooth R C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Module.Flat R C := inferInstance
  refine Module.flat_of_isLocalized_maximal C (C ⧸ Ideal.span (Set.range f))
    (fun q _ => Localization.AtPrime q ⊗[C] (C ⧸ Ideal.span (Set.range f)))
    (fun q _ => TensorProduct.mk C _ _ 1) fun q _ => ?_
  have h := flat_localization R C g f q
  exact Module.Flat.of_linearEquiv
    (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime q)
      (Ideal.span (Set.range f))).restrictScalars R).toLinearEquiv.symm)

end GlobalTheory.CompanionTheory.CIFlatPf
