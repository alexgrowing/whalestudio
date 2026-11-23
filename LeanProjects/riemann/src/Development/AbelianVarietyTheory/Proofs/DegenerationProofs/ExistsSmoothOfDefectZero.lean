import Mathlib
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

open TensorProduct KaehlerDifferential

namespace GlobalTheory.SS.DefectZero

theorem isSmoothAt_iff_injective (R A B K : Type) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] [IsNoetherianRing A] [Algebra.FormallySmooth R A]
    [Module.Free A Ω[A⁄R]] [Module.Finite A Ω[A⁄R]] (hs : Function.Surjective (algebraMap A B))
    (q : Ideal B) [q.IsPrime] (hq : q = RingHom.ker (algebraMap B K)) :
    Algebra.IsSmoothAt R q ↔ Function.Injective (cotangentComplexBaseChange R B A K) := by
  let p : Ideal A := q.comap (algebraMap A B)
  let P := Localization.AtPrime p
  let S := Localization.AtPrime q
  let : Algebra P S := (Localization.localRingHom p q (algebraMap A B) rfl).toAlgebra
  have : IsScalarTower A P S := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A B S]
    exact (Localization.localRingHom_to_map p q (algebraMap A B) rfl x).symm
  have : IsScalarTower R P S := .to₁₃₄ R A P S
  have hu : ∀ y : q.primeCompl, IsUnit (algebraMap B K y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 (hq.ge h)
  let : Algebra S K := (IsLocalization.lift (S := S) hu).toAlgebra
  have : IsScalarTower B S K := .of_algebraMap_eq fun x => (IsLocalization.lift_eq hu x).symm
  let : Algebra P K := ((algebraMap S K).comp (algebraMap P S)).toAlgebra
  have : IsScalarTower P S K := .of_algebraMap_eq' rfl
  have : IsScalarTower A S K := .to₁₃₄ A B S K
  have : IsScalarTower A P K := .to₁₂₄ A P S K
  have : Algebra.FormallyEtale A P := .of_isLocalization p.primeCompl
  have : Algebra.FormallySmooth R P := .comp _ A _
  have : Module.Free P Ω[P⁄R] := .of_equiv (tensorKaehlerEquivOfFormallyEtale R A P)
  have : Module.Finite P Ω[P⁄R] := .equiv (tensorKaehlerEquivOfFormallyEtale R A P)
  have h₁ : Function.Surjective (algebraMap P S) :=
    (RingHom.surjectiveOnStalks_of_surjective hs).localRingHom_surjective _ _ rfl
  have h₃ : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact hq.le hx
  rw [Algebra.IsSmoothAt, Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange P K h₁
    (IsNoetherian.noetherian _) h₃]
  have hker : (RingHom.ker (algebraMap A B)).localized' P p.primeCompl (Algebra.linearMap A P) =
      RingHom.ker (algebraMap P S) := by
    ext x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    have e : algebraMap P S (IsLocalization.mk' P x s) = 0 ↔ algebraMap A S x = 0 := by
      rw [IsScalarTower.algebraMap_apply A P S, ← IsLocalization.mk'_spec P x s, map_mul]
      exact ((IsLocalization.map_units P s).map _).mul_left_eq_zero.symm
    rw [RingHom.mem_ker, e, Submodule.localized'_eq_span]
    change _ ∈ Ideal.map (algebraMap A P) _ ↔ _
    rw [IsLocalization.mk'_mem_map_algebraMap_iff, IsScalarTower.algebraMap_apply A B S,
      IsLocalization.map_eq_zero_iff q.primeCompl]
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨⟨algebraMap A B t, ht⟩, by simpa [RingHom.mem_ker] using h⟩
    · rintro ⟨⟨t, ht⟩, h⟩
      obtain ⟨t, rfl⟩ := hs t
      exact ⟨t, ht, by simpa [RingHom.mem_ker] using h⟩
  let e₁ : P ⊗[A] RingHom.ker (algebraMap A B) ≃ₗ[P] RingHom.ker (algebraMap P S) :=
    (IsLocalizedModule.isBaseChange p.primeCompl P ((RingHom.ker (algebraMap A B)).toLocalized' P
      p.primeCompl (Algebra.linearMap A P))).equiv ≪≫ₗ LinearEquiv.ofEq _ _ hker
  let eₗ : K ⊗[A] RingHom.ker (algebraMap A B) ≃ₗ[K] K ⊗[P] RingHom.ker (algebraMap P S) :=
    (AlgebraTensorModule.cancelBaseChange A P K K _).symm ≪≫ₗ
      AlgebraTensorModule.congr (.refl K K) e₁
  let eᵣ : K ⊗[A] Ω[A⁄R] ≃ₗ[K] K ⊗[P] Ω[P⁄R] :=
    (AlgebraTensorModule.cancelBaseChange A P K K _).symm ≪≫ₗ
      AlgebraTensorModule.congr (.refl K K) (tensorKaehlerEquivOfFormallyEtale R A P)
  have hc : cotangentComplexBaseChange R S P K ∘ₗ eₗ.toLinearMap =
      eᵣ.toLinearMap ∘ₗ cotangentComplexBaseChange R B A K := by
    ext x
    simp [eₗ, eᵣ, e₁, cotangentComplexBaseChange_tmul, IsBaseChange.equiv_tmul]
  rw [← eₗ.injective_comp, ← eᵣ.comp_injective]
  exact iff_of_eq (congrArg Function.Injective (congrArg DFunLike.coe hc))

theorem isSmoothAt_of_ker (R C B : Type) [CommRing R] [IsRegularRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra.FinitePresentation R C] [Algebra R B] (ψ : C →ₐ[R] B)
    (hs : Function.Surjective ψ) (x : Ideal B) [x.IsPrime] (x' : Ideal C) [x'.IsPrime]
    (hx : x' = x.comap ψ.toRingHom) [Algebra.IsSmoothAt R x'] (q : Ideal C) [q.IsPrime]
    (hq : q ≤ x') (h : ∀ c, ψ c = 0 → ∃ u ∉ q, u * c = 0) : Algebra.IsSmoothAt R x := by
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x'
  have hS : IsRegularRing (Localization.Away f) := GlobalTheory.isRegularRing_of_smooth R _
  have disj : Disjoint (Submonoid.powers f : Set C) (x' : Set C) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let qS := x'.map (algebraMap C (Localization.Away f))
  have : qS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime qS) x' := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f)
      (Localization.AtPrime qS) qS
    exact (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm
  have := isRegularRing_iff.mp hS qS
  have : IsRegularLocalRing (Localization.AtPrime x') :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv x'.primeCompl
      (Localization.AtPrime qS) (Localization.AtPrime x')).toRingEquiv
  have := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain (Localization.AtPrime x')
  let l := Localization.localAlgHom x' x ψ hx
  have hl : Function.Bijective l := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_,
      (RingHom.surjectiveOnStalks_of_surjective (f := ψ.toRingHom) hs).localRingHom_surjective _ _ hx⟩
    obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq x'.primeCompl y
    change Localization.localRingHom x' x ψ.toRingHom hx _ = 0 at hy
    rw [Localization.localRingHom_mk',
      IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨⟨t, ht⟩, hy⟩ := hy
    obtain ⟨t, rfl⟩ := hs t
    obtain ⟨u, hu, hut⟩ := h (t * y) (by rw [map_mul]; exact hy)
    have h1 := congrArg (algebraMap C (Localization.AtPrime x')) hut
    rw [map_mul, map_zero, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · obtain ⟨⟨v, hv⟩, hvu⟩ := (IsLocalization.map_eq_zero_iff x'.primeCompl _ _).mp h1
      rcases ‹q.IsPrime›.mem_or_mem_of_mul_eq_zero hvu with h2 | h2
      · exact (hv (hq h2)).elim
      · exact (hu h2).elim
    · obtain ⟨v, hvu⟩ := (IsLocalization.map_eq_zero_iff x'.primeCompl _ _).mp h1
      rw [IsLocalization.mk'_eq_zero_iff]
      exact ⟨v * ⟨t, fun h => ht (hx.le h)⟩, (mul_assoc _ _ _).trans hvu⟩
  exact .of_equiv (AlgEquiv.ofBijective l hl)

theorem exists_smul_eq_zero (A K Q : Type) [CommRing A] [Field K] [Algebra A K] [AddCommGroup Q]
    [Module A Q] [Module.Finite A Q] [Subsingleton (K ⊗[A] Q)] (m : Q) :
    ∃ u : A, algebraMap A K u ≠ 0 ∧ u • m = 0 := by
  let p := RingHom.ker (algebraMap A K)
  have : p.IsPrime := RingHom.ker_isPrime _
  have hp : (⟨p, this⟩ : PrimeSpectrum A) ∉ Module.support A Q := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro hn
    let g : p.ResidueField →ₐ[A] K := Ideal.ResidueField.liftₐ p (Algebra.ofId A K) le_rfl
      fun y hy => isUnit_iff_ne_zero.mpr hy
    let := g.toRingHom.toAlgebra
    have : IsScalarTower A p.ResidueField K := .of_algebraMap_eq fun y => (g.commutes y).symm
    have h1 : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[A] Q)) :=
      Module.FaithfullyFlat.lTensor_nontrivial _ _ _
    rw [(AlgebraTensorModule.cancelBaseChange A p.ResidueField K K Q).nontrivial_congr] at h1
    exact not_subsingleton _ ‹_›
  exact Module.notMem_support_iff'.mp hp m

theorem span_one_tmul {A K M I : Type} [CommRing A] [CommRing K] [Algebra A K] [AddCommGroup M]
    [Module A M] (g : I → M) (hg : Submodule.span A (Set.range g) = ⊤) :
    Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[A] g i) = ⊤ := by
  have h := Submodule.baseChange_span (R := A) (A := K) (Set.range g)
  rw [hg, Submodule.baseChange_top, ← Set.range_comp] at h
  exact h.symm

theorem mem_span_of_map_eq_zero (R A B D : Type) [CommRing R] [CommRing A] [CommRing B]
    [CommRing D] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra B D]
    [Algebra A D] [IsScalarTower A B D] (hs : Function.Surjective (algebraMap A B)) :
    ∃ ψ : D ⊗[A] Ω[A⁄R] →ₗ[D] D ⊗[B] Ω[B⁄R], LinearMap.ker ψ = Submodule.span D (Set.range
      fun h : RingHom.ker (algebraMap A B) => (1 : D) ⊗ₜ[A] KaehlerDifferential.D R A h.1) := by
  let c := AlgebraTensorModule.cancelBaseChange A B D D Ω[A⁄R]
  refine ⟨(mapBaseChange R A B).baseChange D ∘ₗ c.symm.toLinearMap, le_antisymm ?_ ?_⟩
  · intro v hv
    obtain ⟨v, rfl⟩ := c.surjective v
    have hv' : (mapBaseChange R A B).lTensor D v = 0 := by
      simpa [LinearMap.baseChange_eq_ltensor] using hv
    obtain ⟨w, rfl⟩ := (lTensor_exact D (mapBaseChange R A B).exact_subtype_ker_map
      (mapBaseChange_surjective R A B hs) v).mp hv'
    clear hv hv'
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | tmul d w =>
      obtain ⟨y, hy⟩ := (exact_kerCotangentToTensor_mapBaseChange R A B hs w.1).mp w.2
      obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ y
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← hy, kerCotangentToTensor_toCotangent]
      have : c (d ⊗ₜ[B] ((1 : B) ⊗ₜ[A] KaehlerDifferential.D R A y.1)) =
          d • (1 : D) ⊗ₜ[A] KaehlerDifferential.D R A y.1 := by
        simp [c, smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    simp [c, RingHom.mem_ker.mp y.2]

theorem mem_span_of_residue {A D k M I I' : Type} [CommRing A] [CommRing D] [IsLocalRing D]
    [IsNoetherianRing D] [CommRing k] [Algebra A D] [Algebra D k] [Algebra A k]
    [IsScalarTower A D k] [AddCommGroup M] [Module A M] [Module.Finite A M] (π : D)
    (hπ : π ∈ IsLocalRing.maximalIdeal D) (hs : Function.Surjective (algebraMap D k))
    (hk : ∀ d, algebraMap D k d = 0 → π ∣ d) (g : I → M) (a : I' → I)
    (hsat : ∀ v, π • v ∈ Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i) →
      v ∈ Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i))
    (hsp : ∀ i, (1 : k) ⊗ₜ[A] g i ∈
      Submodule.span k (Set.range fun j => (1 : k) ⊗ₜ[A] g (a j))) (i : I) :
    (1 : D) ⊗ₜ[A] g i ∈ Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g (a j)) := by
  set N := Submodule.span D (Set.range fun i => (1 : D) ⊗ₜ[A] g i)
  set N' := Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g (a j))
  have hN' : N' ≤ N := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨a j, rfl⟩)
  let ρ : D ⊗[A] M →ₗ[D] k ⊗[A] M := AlgebraTensorModule.rTensor A M (Algebra.linearMap D k)
  have hker : ∀ v, ρ v = 0 → ∃ w, v = π • w := by
    intro v hv
    obtain ⟨w, rfl⟩ := (rTensor_exact M
      ((Algebra.linearMap D k).restrictScalars A).exact_subtype_ker_map hs v).mp hv
    clear hv
    induction w with
    | zero => exact ⟨0, by rw [map_zero, smul_zero]⟩
    | add x y hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx, hy, smul_add]⟩
    | tmul d m =>
      obtain ⟨e, he⟩ := hk d.1 d.2
      exact ⟨e ⊗ₜ m, by
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, he, smul_tmul', smul_eq_mul]⟩
  have hle : N ≤ N' ⊔ IsLocalRing.maximalIdeal D • N := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : (1 : k) ⊗ₜ[A] g i ∈ N'.map ρ := by
      rw [Submodule.map_span, ← Set.range_comp]
      have h2 := hsp i
      rw [← Submodule.restrictScalars_mem D, Submodule.restrictScalars_span D k hs] at h2
      simpa [ρ, Function.comp_def] using h2
    obtain ⟨n, hn, hρ⟩ := h1
    obtain ⟨w, hw⟩ := hker ((1 : D) ⊗ₜ[A] g i - n) (by rw [map_sub, hρ]; simp [ρ])
    have hwN : w ∈ N := hsat w (hw ▸ sub_mem (Submodule.subset_span ⟨i, rfl⟩) (hN' hn))
    have : (1 : D) ⊗ₜ[A] g i = n + π • w := by rw [← hw]; abel
    change (1 : D) ⊗ₜ[A] g i ∈ _
    rw [this]
    exact Submodule.add_mem_sup hn (Submodule.smul_mem_smul hπ hwN)
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian N)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_span_of_tower {A D K M I : Type} [CommRing A] [CommRing D] [CommRing K] [Algebra A D]
    [Algebra D K] [Algebra A K] [IsScalarTower A D K] [AddCommGroup M] [Module A M] (g : I → M)
    (m : M) (h : (1 : D) ⊗ₜ[A] m ∈ Submodule.span D (Set.range fun j => (1 : D) ⊗ₜ[A] g j)) :
    (1 : K) ⊗ₜ[A] m ∈ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] g j) := by
  let ρ : D ⊗[A] M →ₗ[D] K ⊗[A] M := AlgebraTensorModule.rTensor A M (Algebra.linearMap D K)
  have h1 := Submodule.mem_map_of_mem (f := ρ) h
  rw [Submodule.map_span, ← Set.range_comp] at h1
  have h2 := Submodule.span_le_restrictScalars D K _ h1
  simpa [ρ, Function.comp_def] using h2

theorem exists_mul_mem_span (R A B K I : Type) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
    [IsNoetherianRing A] (hi : Function.Injective (cotangentComplexBaseChange R B A K))
    (f : I → RingHom.ker (algebraMap A B))
    (hf : ∀ h : RingHom.ker (algebraMap A B), (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A h.1 ∈
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A (f j).1))
    (h : RingHom.ker (algebraMap A B)) :
    ∃ u : A, algebraMap A K u ≠ 0 ∧ u * h.1 ∈ Ideal.span (Set.range fun j => (f j).1) := by
  let N := Submodule.span A (Set.range f)
  have h1 : ∀ h : RingHom.ker (algebraMap A B),
      (1 : K) ⊗ₜ[A] h ∈ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] f j) := by
    intro h
    rw [← Submodule.apply_mem_span_image_iff_mem_span hi, ← Set.range_comp]
    simpa [Function.comp_def, cotangentComplexBaseChange_tmul] using hf h
  have h2 : ∀ h, (1 : K) ⊗ₜ[A] N.mkQ h = 0 := by
    intro h
    have h3 : Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] f j) ≤
        LinearMap.ker (N.mkQ.baseChange K) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : N.mkQ (f j) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨j, rfl⟩)
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.baseChange_tmul, this, tmul_zero]
    exact h3 (h1 h)
  have : Subsingleton (K ⊗[A] (RingHom.ker (algebraMap A B) ⧸ N)) := by
    refine subsingleton_of_forall_eq 0 fun v => ?_
    induction v with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul d m =>
      obtain ⟨m, rfl⟩ := N.mkQ_surjective m
      rw [← mul_one d, ← smul_eq_mul, ← smul_tmul', h2, smul_zero]
  obtain ⟨u, hu, hm⟩ := exists_smul_eq_zero A K _ (N.mkQ h)
  refine ⟨u, hu, ?_⟩
  rw [← map_smul] at hm
  have h4 := Submodule.mem_map_of_mem (f := (RingHom.ker (algebraMap A B)).subtype)
    ((Submodule.Quotient.mk_eq_zero N).mp hm)
  rw [Submodule.map_span, ← Set.range_comp] at h4
  exact h4

theorem injective_of_linearIndependent (R A C k I : Type) [CommRing R] [CommRing A] [CommRing C]
    [Field k] [Algebra R A] [Algebra A C] [Algebra C k] [Algebra A k] [IsScalarTower A C k]
    (f : I → A) (hf : RingHom.ker (algebraMap A C) = Ideal.span (Set.range f))
    (hl : LinearIndependent k fun j => (1 : k) ⊗ₜ[A] KaehlerDifferential.D R A (f j)) :
    Function.Injective (cotangentComplexBaseChange R C A k) := by
  let g : I → RingHom.ker (algebraMap A C) := fun j => ⟨f j, hf.ge (Ideal.subset_span ⟨j, rfl⟩)⟩
  have hg : Submodule.span A (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective (RingHom.ker (algebraMap A C)).injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hf.symm
  refine LinearMap.injective_of_linearIndependent (span_one_tmul g hg) ?_
  simpa [Function.comp_def, cotangentComplexBaseChange_tmul, g] using hl

theorem isSmoothAt_of_torsion_free (R A B D : Type) [CommRing R] [IsRegularRing R] [CommRing A]
    [CommRing B] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [Algebra B D] [Algebra.FiniteType R A]
    [Algebra.FormallySmooth R A] [Module.Free A Ω[A⁄R]]
    (hs : Function.Surjective (algebraMap A B)) (q x : Ideal B) [q.IsPrime] [x.IsPrime]
    (hq : q = RingHom.ker (algebraMap B D))
    (hx : x = (IsLocalRing.maximalIdeal D).comap (algebraMap B D)) [Algebra.IsSmoothAt R q]
    (ht : ∀ w ∈ Submodule.torsion D (D ⊗[B] Ω[B⁄R]), w = 0) : Algebra.IsSmoothAt R x := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  let : Algebra A D := ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B D := .of_algebraMap_eq' rfl
  let k := IsLocalRing.ResidueField D
  let K := FractionRing D
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  let g : RingHom.ker (algebraMap A B) → Ω[A⁄R] := fun h => KaehlerDifferential.D R A h.1
  obtain ⟨I, a, -, hsp, hl⟩ := exists_linearIndependent' k fun h => (1 : k) ⊗ₜ[A] g h
  obtain ⟨ψ, hψ⟩ := mem_span_of_map_eq_zero R A B D hs
  have hD := mem_span_of_residue (k := k) π (hπ.maximalIdeal_eq.ge (Ideal.mem_span_singleton_self π))
    IsLocalRing.residue_surjective
    (fun d hd => Ideal.mem_span_singleton.mp
      (hπ.maximalIdeal_eq.le ((IsLocalRing.residue_eq_zero_iff d).mp hd))) g a
    (fun v hv => hψ.le (ht _ ⟨⟨π, mem_nonZeroDivisors_of_ne_zero hπ.ne_zero⟩,
      (ψ.map_smul π v).symm.trans (hψ.ge hv)⟩))
    (fun i => hsp.ge (Submodule.subset_span ⟨i, rfl⟩))
  have hqK : q = RingHom.ker (algebraMap B K) := by
    rw [hq, IsScalarTower.algebraMap_eq B D K, RingHom.ker_comp_of_injective _
      (IsFractionRing.injective D K)]
  have hi := (isSmoothAt_iff_injective R A B K hs q hqK).mp ‹_›
  have hu := exists_mul_mem_span R A B K I hi a fun h =>
    mem_span_of_tower (D := D) (fun j => g (a j)) (g h) (hD h)
  let J : Ideal A := Ideal.span (Set.range fun j => (a j).1)
  have hJ : ∀ y ∈ J, algebraMap A B y = 0 := fun y hy =>
    (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact (a j).2) :
      J ≤ RingHom.ker (algebraMap A B)) hy
  let φ : (A ⧸ J) →ₐ[R] B := Ideal.Quotient.liftₐ J (IsScalarTower.toAlgHom R A B) hJ
  have hφ : Function.Surjective φ := fun b => by
    obtain ⟨y, rfl⟩ := hs b
    exact ⟨Ideal.Quotient.mk J y, rfl⟩
  let : Algebra (A ⧸ J) k := ((algebraMap B k).comp φ.toRingHom).toAlgebra
  have : IsScalarTower A (A ⧸ J) k := .of_algebraMap_eq' rfl
  have hxk : x.comap φ.toRingHom = RingHom.ker (algebraMap (A ⧸ J) k) := by
    ext y
    rw [hx]
    exact (IsLocalRing.residue_eq_zero_iff _).symm
  have : Algebra.IsSmoothAt R (x.comap φ.toRingHom) :=
    (isSmoothAt_iff_injective R A (A ⧸ J) k Ideal.Quotient.mk_surjective _ hxk).mpr
      (injective_of_linearIndependent R A (A ⧸ J) k I (fun j => (a j).1) Ideal.mk_ker hl)
  have : Algebra.FinitePresentation R (A ⧸ J) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine isSmoothAt_of_ker R (A ⧸ J) B φ hφ x _ rfl (q.comap φ.toRingHom) (Ideal.comap_mono ?_) ?_
  · rw [hq, hx]
    exact Ideal.ker_le_comap _
  · intro c hc
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨u, hu0, hu⟩ := hu ⟨c, hc⟩
    refine ⟨Ideal.Quotient.mk J u, fun h => hu0 ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_apply A B K]
      exact hqK.le h
    · rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hu

end GlobalTheory.SS.DefectZero

namespace GlobalTheory.SS

theorem exists_smooth_of_defect_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → Defect a π 0 → ∃ f : B, IsUnit (a f) ∧ Algebra.Smooth R (Localization.Away f) := by
  intro R _ _ _ π hπ B _ _ _ _ hsm R' _ _ a hun hdef
  obtain ⟨_, _, hπ'⟩ := hun
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R B›
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) B :=
    .of_algebraMap_eq fun r => (φ.commutes r).symm
  let := a.toRingHom.toAlgebra
  let q := RingHom.ker (algebraMap B R')
  have : q.IsPrime := RingHom.ker_isPrime _
  have : Algebra.IsSmoothAt R q :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm
      (show (⟨q, this⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen (algebraMap R B π) from
        fun h => hπ'.ne_zero ((a.commutes π).symm.trans h))
  have := DefectZero.isSmoothAt_of_torsion_free R (MvPolynomial (Fin n) R) B R' hφ q _ rfl rfl
    fun w hw => by simpa using hdef w hw
  obtain ⟨f, hf, h⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R
    ((IsLocalRing.maximalIdeal R').comap (algebraMap B R'))
  exact ⟨f, IsLocalRing.notMem_maximalIdeal.mp hf, h⟩

end GlobalTheory.SS
