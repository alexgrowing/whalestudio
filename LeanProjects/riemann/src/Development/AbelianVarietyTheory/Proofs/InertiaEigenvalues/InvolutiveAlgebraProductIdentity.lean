import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DualLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightedCountStableLatticesProductDescentGLStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetEqOneOfSelfDualLatticeStatement

noncomputable section

namespace GlobalTheory.UnitLemma.Swap

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial

section Gen

variable {E : Type} [Field E] {C : Type} [CommRing C] [Algebra E C] [Module.Finite E C]

theorem chi_dvd (g : C) (hs : (LinearMap.mulLeft E g).charpoly.Separable) (f : E[X]) (hf : aeval g f = 0) :
    (LinearMap.mulLeft E g).charpoly ∣ f := by
  classical
  by_cases hf0 : f = 0
  · rw [hf0]
    exact dvd_zero _
  set T := LinearMap.mulLeft E g with hT
  have hlm : Algebra.lmul E C g = T := by
    ext x
    simp [hT]
  have hfT : aeval T f = 0 := by
    rw [← hlm, Polynomial.aeval_algHom_apply, hf, map_zero]

  let b := Module.finBasis E C
  let M := LinearMap.toMatrixAlgEquiv b T
  have hMχ : M.charpoly = T.charpoly := LinearMap.charpoly_toMatrix T b
  have hfM : aeval M f = 0 := by
    have hM : M = (LinearMap.toMatrixAlgEquiv b).toAlgHom T := rfl
    rw [hM, Polynomial.aeval_algHom_apply, hfT, map_zero]
  let L := AlgebraicClosure E
  let ML : Matrix (Fin (Module.finrank E C)) (Fin (Module.finrank E C)) L :=
    (AlgHom.mapMatrix (Algebra.ofId E L)) M
  have hmon : T.charpoly.Monic := LinearMap.charpoly_monic T
  have hcL : ML.charpoly = T.charpoly.map (algebraMap E L) := by
    rw [← hMχ]
    exact Matrix.charpoly_map M (algebraMap E L)
  have hfL : aeval ML (f.map (algebraMap E L)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, hfM, map_zero]
  have hroot : ∀ x ∈ (T.charpoly.map (algebraMap E L)).roots, (f.map (algebraMap E L)).IsRoot x := by
    intro x hx
    have hx' : IsRoot ML.charpoly x := by
      rw [hcL]
      exact (Polynomial.mem_roots (hmon.map _).ne_zero).mp hx
    have : Nonempty (Fin (Module.finrank E C)) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      rw [Matrix.charpoly_isEmpty] at hx'
      simp at hx'
    have hsp : x ∈ spectrum L ML := Matrix.mem_spectrum_of_isRoot_charpoly hx'
    have h2 := spectrum.subset_polynomial_aeval ML (f.map (algebraMap E L)) ⟨x, hsp, rfl⟩
    rw [hfL, spectrum.zero_eq] at h2
    exact h2
  have hsplit : (T.charpoly.map (algebraMap E L)).Splits := IsAlgClosed.splits _
  have hnd : (T.charpoly.map (algebraMap E L)).roots.Nodup := Polynomial.nodup_roots (hs.map)
  have hfL0 : f.map (algebraMap E L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap E L).injective).mpr hf0
  have hdvd : T.charpoly.map (algebraMap E L) ∣ f.map (algebraMap E L) := by
    rw [hsplit.eq_prod_roots_of_monic (hmon.map _),
      Multiset.prod_X_sub_C_dvd_iff_le_roots hfL0, Multiset.le_iff_subset hnd]
    intro x hx
    exact (Polynomial.mem_roots hfL0).mpr (hroot x hx)
  exact (Polynomial.map_dvd_map (algebraMap E L) (algebraMap E L).injective hmon).mp hdvd

theorem isReduced (g : C) (hs : (LinearMap.mulLeft E g).charpoly.Separable) : IsReduced C := by
  classical
  have hint : IsIntegral E g := IsIntegral.of_finite E g

  have hμ : (LinearMap.mulLeft E g).charpoly ∣ minpoly E g := chi_dvd g hs _ (minpoly.aeval E g)
  have hdeg : Module.finrank E C ≤ (minpoly E g).natDegree := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft E g)]
    exact Polynomial.natDegree_le_of_dvd hμ (minpoly.ne_zero hint)
  have htop : Algebra.adjoin E ({g} : Set C) = ⊤ := by
    have h1 : Module.finrank E (Algebra.adjoin E ({g} : Set C)) = (minpoly E g).natDegree :=
      (Algebra.adjoin.powerBasis hint).finrank
    have h2 : Module.finrank E (Subalgebra.toSubmodule (Algebra.adjoin E ({g} : Set C))) =
        (minpoly E g).natDegree := (Subalgebra.finrank_toSubmodule _).trans h1
    apply Algebra.toSubmodule_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le _) (hdeg.trans h2.ge)

  have hss : Module.End.IsSemisimple (LinearMap.mulLeft E g) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree (LinearMap.aeval_self_charpoly _)
  have hlm : Algebra.lmul E C g = LinearMap.mulLeft E g := by
    ext x
    simp
  refine ⟨fun x hx => ?_⟩
  have hxmem : x ∈ Algebra.adjoin E ({g} : Set C) := by
    rw [htop]
    exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hxmem
  have hsp : Module.End.IsSemisimple (Algebra.lmul E C (aeval g p)) := by
    rw [← Polynomial.aeval_algHom_apply, hlm]
    exact Module.End.IsSemisimple.aeval hss p
  have hnil : IsNilpotent (Algebra.lmul E C (aeval g p)) := hx.map (Algebra.lmul E C)
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hsp
  exact Algebra.lmul_injective (h0.trans (map_zero _).symm)

theorem eq_zero_of_trace [CharZero E] (g : C) (hs : (LinearMap.mulLeft E g).charpoly.Separable) (x : C)
    (hx : ∀ y, Algebra.trace E C (x * y) = 0) : x = 0 := by
  classical
  have : IsReduced C := isReduced g hs
  have : IsArtinianRing C := IsArtinianRing.of_finite E C
  have : IsSemisimpleRing C := IsArtinianRing.isSemisimpleRing_of_isReduced C

  let J : Ideal C :=
    { carrier := {x | ∀ y, Algebra.trace E C (x * y) = 0}
      add_mem' := fun {a b} ha hb y => by
        show Algebra.trace E C ((a + b) * y) = 0
        rw [add_mul, map_add, ha y, hb y, add_zero]
      zero_mem' := fun y => by
        show Algebra.trace E C (0 * y) = 0
        rw [zero_mul, map_zero]
      smul_mem' := fun c {a} ha y => by
        show Algebra.trace E C (c * a * y) = 0
        rw [mul_comm c a, mul_assoc]
        exact ha (c * y) }
  obtain ⟨e, he, hJ⟩ := IsSemisimpleRing.ideal_eq_span_idempotent J
  have heJ : e ∈ J := hJ ▸ Ideal.subset_span (Set.mem_singleton e)

  have hte : LinearMap.trace E C (Algebra.lmul E C e) = 0 := by
    have := heJ 1
    rwa [mul_one, Algebra.trace_apply] at this
  have h0 : Algebra.lmul E C e = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (he.map (Algebra.lmul E C)) hte
  have he0 : e = 0 := Algebra.lmul_injective (h0.trans (map_zero _).symm)
  have hxJ : x ∈ J := hx
  rw [hJ, he0, Ideal.mem_span_singleton, zero_dvd_iff] at hxJ
  exact hxJ

end Gen

section Orb

variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) : t ∈ stabLat O L ↔ L = mulLat O (t : A) L := by
  change (∀ y, y ∈ L ↔ (t : A) * y ∈ L) ↔ _
  constructor
  · intro h
    ext y
    constructor
    · intro hy
      refine Submodule.mem_map.2 ⟨((t⁻¹ : Aˣ) : A) * y, (h _).2 ?_, ?_⟩
      · simpa using hy
      · simp
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      exact (h z).1 hz
  · intro h y
    constructor
    · intro hy
      rw [h]
      exact Submodule.mem_map.2 ⟨y, hy, rfl⟩
    · intro hy
      rw [h] at hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy
      have hzy' : (t : A) * z = (t : A) * y := hzy
      have hz' : z = y := by
        have := congrArg (fun w => ((t⁻¹ : Aˣ) : A) * w) hzy'
        simpa using this
      exact hz' ▸ hz

private theorem mulLat_mulLat' (a b : A) (L : Submodule O A) :
    mulLat O a (mulLat O b L) = mulLat O (a * b) L := by
  ext y
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, mul_assoc a b w⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨b * w, ⟨w, hw, rfl⟩, (mul_assoc a b w).symm⟩

private theorem mulLat_one_inertia_eigenvalues (L : Submodule O A) : mulLat O (1 : A) L = L := by
  ext y
  simp [mulLat]

private theorem mem_stabLat_mulLat_iff (s u : Aˣ) (L : Submodule O A) :
    u ∈ stabLat O (mulLat O (s : A) L) ↔ u ∈ stabLat O L := by
  rw [mem_stabLat_iff, mem_stabLat_iff, mulLat_mulLat', mul_comm, ← mulLat_mulLat']
  constructor
  · intro h
    have := congrArg (mulLat O ((s⁻¹ : Aˣ) : A)) h
    simpa [mulLat_mulLat', mulLat_one_inertia_eigenvalues] using this
  · intro h
    rw [← h]

theorem orbSum_hom (G : Subgroup Aˣ) (θ : G →* A'ˣ) (hθ : Function.Surjective θ)
    (X : Set (Submodule O A)) (X' : Set (Submodule O A')) (e : X ≃ X')
    (hrel : ∀ (t : G) (L M : X), M.1 = mulLat O ((t : Aˣ) : A) L.1 ↔ (e M).1 = mulLat O ((θ t : A'ˣ) : A') (e L).1)
    (hint : ∀ t : G, (t : Aˣ) ∈ intUnits O A ↔ θ t ∈ intUnits O A') :
    orbSum O G X (fun _ => 1) = orbSum O ⊤ X' (fun _ => 1) := by

  have hr : ∀ L M : X, (∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)) ↔
      (∃ t ∈ (⊤ : Subgroup A'ˣ), ((e M) : Submodule O A') = mulLat O (t : A') ((e L) : Submodule O A')) := by
    intro L M
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨θ ⟨t, ht⟩, Subgroup.mem_top _, (hrel ⟨t, ht⟩ L M).1 h⟩
    · rintro ⟨s, -, h⟩
      obtain ⟨t, rfl⟩ := hθ s
      exact ⟨t, t.2, (hrel t L M).2 h⟩
  let Φ : Orb O G X ≃ Orb O ⊤ X' := Quot.congr e hr
  let W' : X' → ℕ := fun L' => (stabLat O (L' : Submodule O A') ⊓ ⊤).relIndex (intUnits O A' ⊓ ⊤)

  have hW' : ∀ L' M' : X', (∃ s ∈ (⊤ : Subgroup A'ˣ),
      (M' : Submodule O A') = mulLat O (s : A') (L' : Submodule O A')) → W' L' = W' M' := by
    rintro L' M' ⟨s, -, h⟩
    have hst : stabLat O (M' : Submodule O A') = stabLat O (L' : Submodule O A') := by
      ext u
      rw [h]
      exact mem_stabLat_mulLat_iff s u _
    show (stabLat O (L' : Submodule O A') ⊓ ⊤).relIndex _ = (stabLat O (M' : Submodule O A') ⊓ ⊤).relIndex _
    rw [hst]

  have key : ∀ L : X, (stabLat O (L : Submodule O A) ⊓ G).relIndex (intUnits O A ⊓ G) = W' (e L) := by
    intro L
    have h1 : (stabLat O (L : Submodule O A) ⊓ G).subgroupOf G =
        (stabLat O ((e L) : Submodule O A')).comap θ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap, mem_stabLat_iff, mem_stabLat_iff]
      exact ⟨fun h => (hrel t L L).1 h.1, fun h => ⟨(hrel t L L).2 h, t.2⟩⟩
    have h2 : (intUnits O A ⊓ G).subgroupOf G = (intUnits O A').comap θ := by
      ext t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap]
      exact ⟨fun h => (hint t).1 h.1, fun h => ⟨(hint t).2 h, t.2⟩⟩
    show _ = (stabLat O ((e L) : Submodule O A') ⊓ ⊤).relIndex (intUnits O A' ⊓ ⊤)
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : intUnits O A ⊓ G ≤ G), h1, h2,
      Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hθ, inf_top_eq, inf_top_eq]
  unfold orbSum
  rw [← finsum_comp_equiv Φ]
  refine finsum_congr fun o => ?_
  have e1 : Φ o = Quot.mk _ (e (Quot.out o)) := by
    rw [← Quot.congr_mk e hr]
    exact congrArg Φ (Quot.out_eq o).symm
  have h1 : W' (Quot.out (Φ o)) = W' (e (Quot.out o)) :=
    (congrArg (Quot.lift W' hW') (Quot.out_eq (Φ o))).trans (congrArg (Quot.lift W' hW') e1)
  simp only [one_mul]
  exact congrArg (fun n : ℕ => (n : ℚ)) ((key (Quot.out o)).trans h1.symm)

theorem stable_adjoin (φ : A →ₐ[O] A') (g : A) (M : Submodule O A') (hM : ∀ y ∈ M, φ g * y ∈ M) {a : A}
    (ha : a ∈ Algebra.adjoin O ({g} : Set A)) : ∀ y ∈ M, φ a * y ∈ M := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hM
  | algebraMap r =>
    intro y hy
    rw [AlgHom.commutes, ← Algebra.smul_def]
    exact M.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [map_add, add_mul]
    exact M.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [map_mul, mul_assoc]
    exact hx _ (hz y hy)

end Orb

variable {K : UQ}

theorem sigma_smul (B : InvAlg K) (a : K.O) : ∃ b : K.O, ∀ y, B.σ (a • y) = b • B.σ y := by
  obtain ⟨b, hb⟩ := K.c_int a
  refine ⟨b, fun y => ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply K.O K.E B.A a,
    IsScalarTower.algebraMap_apply K.O K.E B.A b, B.σ_alg, hb]

theorem sigma_integral (B : InvAlg K) {y : B.A} (hi : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E

  choose c' hc' using K.c_int
  let φ : K.O →+* K.O :=
    { toFun := c'
      map_one' := hinj (by simp [← hc'])
      map_mul' := fun x y => hinj (by simp [← hc'])
      map_zero' := hinj (by simp [← hc'])
      map_add' := fun x y => hinj (by simp [← hc']) }
  have hsq : (algebraMap K.O B.A).comp φ = B.σ.toRingHom.comp (algebraMap K.O B.A) := by
    refine RingHom.ext fun x => ?_
    show algebraMap K.O B.A (c' x) = B.σ (algebraMap K.O B.A x)
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A (c' x), IsScalarTower.algebraMap_apply K.O K.E B.A x,
      B.σ_alg, hc']
  exact IsIntegral.map_of_comp_eq φ B.σ.toRingHom hsq hi

theorem conj_mem (x : K.E) : K.c x ∈ (algebraMap K.O K.E).range ↔ x ∈ (1 : Submodule K.O K.E) := by
  rw [RingHom.mem_range, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := K.c_int y
    exact ⟨z, by rw [← hz, hy, K.c_c]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := K.c_int y
    exact ⟨z, hz.symm⟩

theorem mem_range_iff (x : K.E) : x ∈ (algebraMap K.O K.E).range ↔ x ∈ (1 : Submodule K.O K.E) := by
  rw [RingHom.mem_range, Submodule.mem_one]

theorem exists_norm (B : InvAlg K) {e : B.A} (hi : e * e = e) (hs : e + B.σ e = 1) (x : B.A) (hx : IsUnit x)
    (hf : B.σ x = x) : ∃ u : B.Aˣ, x = 1 * (u * B.σ (u : B.A)) := by
  obtain ⟨v, rfl⟩ := hx
  have hse : B.σ e = 1 - e := by rw [← hs]; ring
  have hvw : (v : B.A) * ((v⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv v

  have hu : (e * v + (1 - e)) * (e * ((v⁻¹ : B.Aˣ) : B.A) + (1 - e)) = 1 := by
    linear_combination ((v : B.A) * ((v⁻¹ : B.Aˣ) : B.A) - v - ((v⁻¹ : B.Aˣ) : B.A) + 1) * hi + e * hvw
  refine ⟨Units.mkOfMulEqOne _ _ hu, ?_⟩
  rw [Units.val_mkOfMulEqOne, map_add, map_mul, map_sub, map_one, hf, hse]
  linear_combination ((v : B.A) ^ 2 - 2 * v + 1) * hi

section Half

variable {C : Type} [CommRing C] [Algebra K.E C] [Algebra K.O C] [IsScalarTower K.O K.E C] [Module.Finite K.E C]

structure Half (B : InvAlg K) (e : B.A) (π : B.A →ₐ[K.E] C) : Prop where
  idem : e * e = e
  swap : e + B.σ e = 1
  surj : Function.Surjective π
  ker : ∀ y, π y = 0 ↔ e * y = 0
  tr : ∀ y, Algebra.trace K.E B.A (e * y) = Algebra.trace K.E C (π y)

namespace Half

variable {B : InvAlg K} {e : B.A} {π : B.A →ₐ[K.E] C}

theorem map_sigma (h : Half B e π) : π (B.σ e) = 0 := by
  have hs : B.σ e = 1 - e := by rw [← h.swap]; ring
  refine (h.ker _).2 ?_
  rw [hs, mul_sub, mul_one, h.idem, sub_self]

theorem map_e (h : Half B e π) : π e = 1 := by
  have h1 : π (e + B.σ e) = 1 := by rw [h.swap, map_one]
  rwa [map_add, h.map_sigma, add_zero] at h1

theorem ext (h : Half B e π) {y z : B.A} (h1 : π y = π z) (h2 : π (B.σ y) = π (B.σ z)) : y = z := by
  have a1 : e * (y - z) = 0 := (h.ker _).1 (by rw [map_sub, h1, sub_self])
  have a2 : e * B.σ (y - z) = 0 := (h.ker _).1 (by rw [map_sub, map_sub, h2, sub_self])
  have a3 : B.σ e * (y - z) = 0 := by
    have := congrArg B.σ a2
    rwa [map_mul, B.σ_σ, map_zero] at this
  have : y - z = 0 := by
    calc y - z = (e + B.σ e) * (y - z) := by rw [h.swap, one_mul]
    _ = 0 := by rw [add_mul, a1, a3, add_zero]
  exact sub_eq_zero.1 this

theorem exists_sec (h : Half B e π) : ∃ s : C →ₗ[K.E] B.A, (∀ a, π (s a) = a) ∧ ∀ a, π (B.σ (s a)) = 0 := by
  obtain ⟨s₀, hs₀⟩ := LinearMap.exists_rightInverse_of_surjective π.toLinearMap
    (LinearMap.range_eq_top.2 h.surj)
  refine ⟨(LinearMap.mulLeft K.E e).comp s₀, fun a => ?_, fun a => ?_⟩
  · have hs : π (s₀ a) = a := by simpa using LinearMap.congr_fun hs₀ a
    simp [map_mul, h.map_e, hs]
  · simp [map_mul, h.map_sigma]

theorem herm (h : Half B e π) (y z : B.A) : B.herm 1 y z =
    Algebra.traceForm K.E C (π (B.σ z)) (π y) + K.c (Algebra.traceForm K.E C (π (B.σ y)) (π z)) := by
  have key : ∀ w : B.A, Algebra.trace K.E B.A w =
      Algebra.trace K.E C (π w) + K.c (Algebra.trace K.E C (π (B.σ w))) := by
    intro w
    have h3 : Algebra.trace K.E B.A (B.σ e * w) = K.c (Algebra.trace K.E B.A (e * B.σ w)) := by
      have : B.σ e * w = B.σ (e * B.σ w) := by rw [map_mul, B.σ_σ]
      rw [this, GlobalTheory.UnitLemma.Basic.trace_sigma B]
    calc Algebra.trace K.E B.A w = Algebra.trace K.E B.A (e * w) + Algebra.trace K.E B.A (B.σ e * w) := by
          rw [← map_add, ← add_mul, h.swap, one_mul]
    _ = _ := by rw [h.tr, h3, h.tr]
  show Algebra.trace K.E B.A (1 * y * B.σ z) = _
  rw [one_mul, key, Algebra.traceForm_apply, Algebra.traceForm_apply]
  simp only [map_mul, B.σ_σ]
  rw [mul_comm (π y)]

private theorem idempotent_mul_aeval_mul_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e : S} (y : S)
    (he : e * e = e) (p : R[X]) : e * aeval (e * y) p = e * aeval y p := by
  have key : ∀ i : ℕ, e * e ^ i = e := by
    intro i
    induction i with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, he]
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, mul_smul_comm, mul_pow, ← mul_assoc, key]

private theorem isIntegral_idempotent_mul_of_monic {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {e y : S}
    (he : e * e = e) (p : R[X]) (hp : p.Monic) (h0 : e * aeval y p = 0) : IsIntegral R (e * y) := by
  refine ⟨X * p, monic_X.mul hp, ?_⟩
  rw [← aeval_def, map_mul, aeval_X]
  calc e * y * aeval (e * y) p = y * (e * aeval (e * y) p) := by ring
  _ = 0 := by rw [idempotent_mul_aeval_mul_eq y he, h0, mul_zero]
theorem integral (h : Half B e π) {y : B.A} (h1 : IsIntegral K.O (π y)) (h2 : IsIntegral K.O (π (B.σ y))) :
    IsIntegral K.O y := by
  have hey : IsIntegral K.O (e * y) := by
    obtain ⟨p, hp, hpy⟩ := h1
    refine isIntegral_idempotent_mul_of_monic h.idem p hp ((h.ker _).1 ?_)
    have e1 : π (aeval y p) = aeval (π y) p :=
      (Polynomial.aeval_algHom_apply (π.restrictScalars K.O) y p).symm
    rw [e1, aeval_def]
    exact hpy
  have hez : IsIntegral K.O (e * B.σ y) := by
    obtain ⟨p, hp, hpy⟩ := h2
    refine isIntegral_idempotent_mul_of_monic h.idem p hp ((h.ker _).1 ?_)
    have e1 : π (aeval (B.σ y) p) = aeval (π (B.σ y)) p :=
      (Polynomial.aeval_algHom_apply (π.restrictScalars K.O) (B.σ y) p).symm
    rw [e1, aeval_def]
    exact hpy
  have hy : y = e * y + B.σ (e * B.σ y) := by rw [map_mul, B.σ_σ, ← add_mul, h.swap, one_mul]
  rw [hy]
  exact hey.add (sigma_integral B hez)

theorem nondeg (h : Half B e π) (hs : B.P.Separable) : (Algebra.traceForm K.E C).Nondegenerate := by
  have key : ∀ x : C, (∀ w : C, Algebra.trace K.E C (x * w) = 0) → x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := h.surj x
    have h0 : e * y = 0 := by
      refine eq_zero_of_trace B.g hs (e * y) fun w => ?_
      rw [mul_assoc, h.tr, map_mul]
      exact hx (π w)
    exact (h.ker y).2 h0
  refine ⟨fun x hx => key x fun w => ?_, fun x hx => key x fun w => ?_⟩
  · have h1 := hx w
    rwa [Algebra.traceForm_apply] at h1
  · have h1 := hx w
    rwa [Algebra.traceForm_apply, mul_comm] at h1

end Half

def img {B : InvAlg K} (π : B.A →ₐ[K.E] C) (L : Submodule K.O B.A) : Submodule K.O C :=
  L.map (π.restrictScalars K.O).toLinearMap

def dual (M : Submodule K.O C) : Submodule K.O C := (Algebra.traceForm K.E C).dualSubmodule M

def lift {B : InvAlg K} (π : B.A →ₐ[K.E] C) (M : Submodule K.O C) : Submodule K.O B.A where
  carrier := {y | π y ∈ M ∧ π (B.σ y) ∈ dual M}
  add_mem' := fun ha hb => ⟨by rw [map_add]; exact M.add_mem ha.1 hb.1,
    by rw [map_add, map_add]; exact (dual M).add_mem ha.2 hb.2⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := fun a y hy => by
    obtain ⟨b, hb⟩ := sigma_smul B a
    exact ⟨by rw [π.map_smul_of_tower]; exact M.smul_mem _ hy.1,
      by rw [hb, π.map_smul_of_tower]; exact (dual M).smul_mem _ hy.2⟩

namespace Half

variable {B : InvAlg K} {e : B.A} {π : B.A →ₐ[K.E] C}

private theorem mem_lift_iff' {y : B.A} {M : Submodule K.O C} :
    y ∈ lift π M ↔ π y ∈ M ∧ π (B.σ y) ∈ dual M := Iff.rfl

private theorem mem_dual_iff_inertia_eigenvalues {x : C} {M : Submodule K.O C} :
    x ∈ dual M ↔ ∀ y ∈ M, Algebra.trace K.E C (x * y) ∈ (algebraMap K.O K.E).range := by
  simp only [dual, LinearMap.BilinForm.mem_dualSubmodule, Algebra.traceForm_apply, Submodule.mem_one,
    RingHom.mem_range]
theorem eq_lift (h : Half B e π) (he : e ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) {L : Submodule K.O B.A}
    (hL : L ∈ B.X 1) : L = lift π (img π L) := by
  obtain ⟨_, hg, hsd⟩ := hL
  have heL : ∀ y ∈ L, e * y ∈ L := stable_adjoin (AlgHom.id K.O B.A) B.g L hg he

  have fwd : ∀ y ∈ L, π (B.σ y) ∈ dual (img π L) := by
    intro y hy
    rw [mem_dual_iff_inertia_eigenvalues]
    rintro _ ⟨w, hw, rfl⟩
    have h1 := (hsd (e * w)).1 (heL w hw) y hy
    rw [h.herm] at h1
    have h0 : π (B.σ (e * w)) = 0 := by rw [map_mul, map_mul, h.map_sigma, zero_mul]
    have h2 : π (e * w) = π w := by rw [map_mul, h.map_e, one_mul]
    rw [h0, h2] at h1
    simpa [Algebra.traceForm_apply] using h1
  ext y
  constructor
  · intro hy
    exact mem_lift_iff'.2 ⟨⟨y, hy, rfl⟩, fwd y hy⟩
  · intro hy
    obtain ⟨hy1, hy2⟩ := mem_lift_iff'.1 hy
    rw [hsd y]
    intro z hz
    rw [h.herm]
    refine add_mem ?_ ?_
    · have h3 := mem_dual_iff_inertia_eigenvalues.1 (fwd z hz) (π y) hy1
      simpa [Algebra.traceForm_apply] using h3
    · rw [conj_mem, ← mem_range_iff]
      have h3 := mem_dual_iff_inertia_eigenvalues.1 hy2 (π z) ⟨z, hz, rfl⟩
      simpa [Algebra.traceForm_apply] using h3

theorem img_lift (h : Half B e π) (M : Submodule K.O C) : img π (lift π M) = M := by
  obtain ⟨s, hs1, hs2⟩ := h.exists_sec
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_lift_iff'.1 hy).1
  · intro ha
    refine ⟨s a, mem_lift_iff'.2 ⟨?_, ?_⟩, hs1 a⟩
    · rw [hs1]; exact ha
    · rw [hs2]; exact (dual M).zero_mem

theorem img_mem (h : Half B e π) {L : Submodule K.O B.A} (hL : L ∈ B.X 1) :
    IsLat K.O K.E (img π L) ∧ ∀ y ∈ img π L, π B.g * y ∈ img π L := by
  obtain ⟨⟨hfg, hspan⟩, hg, -⟩ := hL
  refine ⟨⟨hfg.map _, ?_⟩, ?_⟩
  · rw [show (img π L : Set C) = π.toLinearMap '' (L : Set B.A) from Submodule.map_coe _ _,
      ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top.2 h.surj]
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨B.g * w, hg w hw, map_mul π B.g w⟩

private theorem sigma_smul' (B : InvAlg K) (a : K.E) (y : B.A) : B.σ (a • y) = K.c a • B.σ y := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

private theorem dual_dual_eq_and_isLat_dual (hB : (Algebra.traceForm K.E C).Nondegenerate) (M : Submodule K.O C)
    (hM : IsLat K.O K.E M) : dual (dual M) = M ∧ IsLat K.O K.E (dual M) := by
  classical
  have : Submodule.IsLattice K.E M := ⟨hM.1, hM.2⟩
  obtain ⟨ι, _, b, hMb⟩ : ∃ (ι : Type) (_ : Finite ι) (b : Module.Basis ι K.E C),
      M = Submodule.span K.O (Set.range b) := by
    let bM := Module.Free.chooseBasis K.O M
    refine ⟨_, inferInstance, bM.extendOfIsLattice K.E, ?_⟩
    have h1 : Set.range (bM.extendOfIsLattice K.E) = M.subtype '' Set.range bM := by
      rw [← Set.range_comp]; ext x; simp
    rw [h1, Submodule.span_image, bM.span_eq, Submodule.map_top, Submodule.range_subtype]
  subst hMb
  refine ⟨LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hB (Algebra.traceForm_isSymm K.E) b, ?_⟩
  show IsLat K.O K.E ((Algebra.traceForm K.E C).dualSubmodule _)
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB b]
  exact ⟨Submodule.fg_span (Set.finite_range _), by rw [Submodule.span_span_of_tower, Module.Basis.span_eq]⟩

private theorem mem_adjoin_of_mul_eq_one_of_isIntegral {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {v w : S}
    (hvw : v * w = 1) (hv : IsIntegral R v) : v ∈ Algebra.adjoin R ({w} : Set S) := by
  obtain ⟨p, hpm, hp⟩ := hv
  let : Invertible v := ⟨w, (mul_comm _ _).trans hvw, hvw⟩
  have h1 := eval₂_reflect_mul_pow (algebraMap R S) v p.natDegree p le_rfl
  rw [hp] at h1
  have h2 : aeval w (reflect p.natDegree p) = 0 := by
    have hu : IsUnit (v ^ p.natDegree) := (isUnit_iff_exists_inv.2 ⟨w, hvw⟩).pow _
    rw [aeval_def]
    exact hu.mul_left_eq_zero.1 h1
  have h0 : (reflect p.natDegree p).coeff 0 = 1 := by
    rw [coeff_reflect, revAt_zero]; exact hpm
  have h3 := divX_mul_X_add (reflect p.natDegree p)
  rw [h0, map_one] at h3
  have h4 : aeval w (divX (reflect p.natDegree p)) * w + 1 = 0 := by
    rw [← h3, map_add, map_mul, aeval_X, map_one] at h2; exact h2
  have h5 : v = -aeval w (divX (reflect p.natDegree p)) := by
    calc v = v * 1 := (mul_one v).symm
      _ = v * (-(aeval w (divX (reflect p.natDegree p)) * w)) := by
        rw [← eq_neg_of_add_eq_zero_right h4]
      _ = -aeval w (divX (reflect p.natDegree p)) * (v * w) := by ring
      _ = -aeval w (divX (reflect p.natDegree p)) := by rw [hvw, mul_one]
  rw [h5]
  exact neg_mem (aeval_mem_adjoin_singleton R w)
theorem lift_mem (h : Half B e π) (hs : B.P.Separable) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    {M : Submodule K.O C} (hM : IsLat K.O K.E M) (hg : ∀ y ∈ M, π B.g * y ∈ M) : lift π M ∈ B.X 1 := by
  obtain ⟨s, hs1, hs2⟩ := h.exists_sec
  obtain ⟨hdd, hdl⟩ := dual_dual_eq_and_isLat_dual (h.nondeg hs) M hM
  have hsM : ∀ a ∈ M, s a ∈ lift π M := fun a ha =>
    mem_lift_iff'.2 ⟨by rw [hs1]; exact ha, by rw [hs2]; exact (dual M).zero_mem⟩
  have hσsD : ∀ b ∈ dual M, B.σ (s b) ∈ lift π M := fun b hb =>
    mem_lift_iff'.2 ⟨by rw [hs2]; exact M.zero_mem, by rw [B.σ_σ, hs1]; exact hb⟩

  have hdec : ∀ y, y = s (π y) + B.σ (s (π (B.σ y))) := fun y =>
    h.ext (by rw [map_add, hs1, hs2, add_zero]) (by rw [map_add, map_add, hs2, B.σ_σ, hs1, zero_add])
  show IsLat K.O K.E (lift π M) ∧ (∀ y ∈ lift π M, B.g * y ∈ lift π M) ∧
    ∀ y, y ∈ lift π M ↔ ∀ z ∈ lift π M, B.herm 1 y z ∈ (algebraMap K.O K.E).range
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hdl.1
    have hN₂ : ∀ x ∈ dual M, B.σ (s x) ∈ Submodule.span K.O ((fun x => B.σ (s x)) '' (S : Set C)) := by
      intro x hx
      rw [← hS] at hx
      refine Submodule.span_induction
        (p := fun x _ => B.σ (s x) ∈ Submodule.span K.O ((fun x => B.σ (s x)) '' (S : Set C))) ?_ ?_ ?_ ?_ hx
      · intro x hx'; exact Submodule.subset_span ⟨x, hx', rfl⟩
      · simp
      · intro x x' _ _ h1 h2; rw [map_add, map_add]; exact add_mem h1 h2
      · intro a x _ h1
        obtain ⟨b, hb⟩ := sigma_smul B a
        rw [LinearMap.map_smul_of_tower, hb]; exact Submodule.smul_mem _ _ h1
    refine Submodule.FG.of_le ((hM.1.map (s.restrictScalars K.O)).sup
      (Submodule.fg_span (S.finite_toSet.image (fun x => B.σ (s x))))) ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_lift_iff'.1 hy
    rw [hdec y]
    exact Submodule.add_mem_sup ⟨π y, hy1, rfl⟩ (hN₂ _ hy2)
  · rw [eq_top_iff]
    intro y _
    rw [hdec y]
    refine add_mem ?_ ?_
    · have hx : π y ∈ Submodule.span K.E (M : Set C) := by rw [hM.2]; trivial
      have h1 : s (π y) ∈ (Submodule.span K.E (M : Set C)).map s := ⟨π y, hx, rfl⟩
      rw [Submodule.map_span] at h1
      exact Submodule.span_mono (by rintro _ ⟨a, ha, rfl⟩; exact hsM a ha) h1
    · have hx : π (B.σ y) ∈ Submodule.span K.E (dual M : Set C) := by rw [hdl.2]; trivial
      refine Submodule.span_induction
        (p := fun x _ => B.σ (s x) ∈ Submodule.span K.E (lift π M : Set B.A)) ?_ ?_ ?_ ?_ hx
      · intro x hx'; exact Submodule.subset_span (hσsD x hx')
      · simp
      · intro x x' _ _ h1 h2; rw [map_add, map_add]; exact add_mem h1 h2
      · intro a x _ h1; rw [map_smul, sigma_smul']; exact Submodule.smul_mem _ _ h1
  ·
    have hσg : B.σ B.g * B.g = 1 := by rw [mul_comm]; exact hu
    have hvint : IsIntegral K.O (π (B.σ B.g)) := (sigma_integral B hi).map (π.restrictScalars K.O)
    have hvw : π (B.σ B.g) * π B.g = 1 := by rw [← map_mul, hσg, map_one]
    have hinvM : ∀ a ∈ M, π (B.σ B.g) * a ∈ M :=
      stable_adjoin (AlgHom.id K.O C) (π B.g) M hg (mem_adjoin_of_mul_eq_one_of_isIntegral hvw hvint)
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_lift_iff'.1 hy
    refine mem_lift_iff'.2 ⟨by rw [map_mul]; exact hg _ hy1, ?_⟩
    rw [mem_dual_iff_inertia_eigenvalues] at hy2 ⊢
    intro a ha
    have h1 := hy2 _ (hinvM a ha)
    rw [map_mul B.σ, map_mul π]
    rwa [mul_comm (π (B.σ B.g)) (π (B.σ y)), mul_assoc]
  · intro y
    constructor
    · intro hy z hz
      obtain ⟨hy1, hy2⟩ := mem_lift_iff'.1 hy
      obtain ⟨hz1, hz2⟩ := mem_lift_iff'.1 hz
      rw [h.herm]
      refine add_mem ?_ ?_
      · have h3 := mem_dual_iff_inertia_eigenvalues.1 hz2 (π y) hy1
        simpa [Algebra.traceForm_apply] using h3
      · rw [conj_mem, ← mem_range_iff]
        have h3 := mem_dual_iff_inertia_eigenvalues.1 hy2 (π z) hz1
        simpa [Algebra.traceForm_apply] using h3
    · intro H
      refine mem_lift_iff'.2 ⟨?_, ?_⟩
      · have h4 : π y ∈ dual (dual M) := by
          rw [mem_dual_iff_inertia_eigenvalues]
          intro b hb
          have h5 := H _ (hσsD b hb)
          rw [h.herm, B.σ_σ, hs1, hs2] at h5
          simp only [map_zero, add_zero, Algebra.traceForm_apply] at h5
          rw [mul_comm]; exact h5
        rwa [hdd] at h4
      · rw [mem_dual_iff_inertia_eigenvalues]
        intro a ha
        have h5 := H _ (hsM a ha)
        rw [h.herm, hs1, hs2] at h5
        simp only [map_zero, LinearMap.zero_apply, zero_add, Algebra.traceForm_apply] at h5
        rw [mem_range_iff, ← conj_mem]; exact h5

theorem mulLat_lift (t : B.T) (M : Submodule K.O C) :
    mulLat K.O ((t : B.Aˣ) : B.A) (lift π M) =
      lift π (mulLat K.O ((Units.map (π : B.A →* C) t : Cˣ) : C) M) := by
  set u : B.A := ((t : B.Aˣ) : B.A) with hu
  have ht : u * B.σ u = 1 := t.2
  have hU : ((Units.map (π : B.A →* C) t : Cˣ) : C) = π u := rfl
  have hπ : π (B.σ u) * π u = 1 := by rw [← map_mul, mul_comm, ht, map_one]
  rw [hU]
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw1, hw2⟩ := mem_lift_iff'.1 hw
    refine mem_lift_iff'.2 ⟨⟨π w, hw1, (map_mul π u w).symm⟩, ?_⟩
    rw [mem_dual_iff_inertia_eigenvalues]
    rintro _ ⟨m, hm, rfl⟩
    have h1 := mem_dual_iff_inertia_eigenvalues.1 hw2 m hm
    have : π (B.σ ((LinearMap.mulLeft K.O u) w)) * (LinearMap.mulLeft K.O (π u)) m = π (B.σ w) * m := by
      simp only [LinearMap.mulLeft_apply, map_mul]
      calc π (B.σ u) * π (B.σ w) * (π u * m) = (π (B.σ u) * π u) * (π (B.σ w) * m) := by ring
        _ = π (B.σ w) * m := by rw [hπ, one_mul]
    rw [this]; exact h1
  · intro hy
    obtain ⟨⟨m, hm, hmy⟩, hy2⟩ := mem_lift_iff'.1 hy
    refine ⟨B.σ u * y, mem_lift_iff'.2 ⟨?_, ?_⟩, ?_⟩
    · have : π (B.σ u * y) = m := by
        rw [map_mul, ← hmy, LinearMap.mulLeft_apply, ← mul_assoc, hπ, one_mul]
      rw [this]; exact hm
    · rw [mem_dual_iff_inertia_eigenvalues]
      intro m' hm'
      have h1 := mem_dual_iff_inertia_eigenvalues.1 hy2 (π u * m') ⟨m', hm', rfl⟩
      have : π (B.σ (B.σ u * y)) * m' = π (B.σ y) * (π u * m') := by
        rw [map_mul, B.σ_σ, map_mul]; ring
      rw [this]; exact h1
    · show u * (B.σ u * y) = y
      rw [← mul_assoc, ht, one_mul]

theorem N_one (h : Half B e π) (he : e ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hs : B.P.Separable)
    (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) : B.N 1 = countGL K.O K.E (π B.g) := by

  have hsurj : Function.Surjective ((Units.map (π : B.A →* C)).comp B.T.subtype) := by
    intro u
    obtain ⟨w, hw⟩ := h.surj (u : C)
    obtain ⟨w', hw'⟩ := h.surj ((u⁻¹ : Cˣ) : C)
    have he2 : e * e = e := h.idem
    have hsw : B.σ e = 1 - e := eq_sub_of_add_eq' h.swap
    have hes : e * B.σ e = 0 := by rw [hsw, mul_sub, mul_one, he2, sub_self]
    have hss : B.σ e * B.σ e = B.σ e := by rw [← map_mul, he2]
    have hww : e * (w * w') = e := by
      apply h.ext
      · rw [map_mul, map_mul, hw, hw', h.map_e, Units.mul_inv, mul_one]
      · rw [map_mul, map_mul, h.map_sigma, zero_mul]
    set t₀ : B.A := e * w + B.σ (e * w') with ht₀
    have hσt : B.σ t₀ = B.σ e * B.σ w + e * w' := by
      rw [ht₀, map_add, B.σ_σ, map_mul]
    have h1 : t₀ * B.σ t₀ = 1 := by
      have hww' : B.σ e * (B.σ w' * B.σ w) = B.σ e := by
        rw [← map_mul, ← map_mul, mul_comm w' w, hww]
      calc t₀ * B.σ t₀ = e * e * (w * w') + (e * B.σ e) * (w * B.σ w)
            + (B.σ e * B.σ e) * (B.σ w' * B.σ w) + (e * B.σ e) * (w' * B.σ w') := by
              rw [hσt, ht₀, map_mul]; ring
        _ = e + B.σ e := by rw [he2, hes, hss, hww, hww']; ring
        _ = 1 := h.swap
    refine ⟨⟨Units.mkOfMulEqOne t₀ (B.σ t₀) h1, h1⟩, ?_⟩
    apply Units.ext
    show π t₀ = (u : C)
    rw [ht₀, map_add, map_mul, map_mul, map_mul, h.map_e, hw, h.map_sigma, one_mul, zero_mul, add_zero]
  show orbSum K.O B.T (B.X 1) (fun _ => 1) =
    orbSum K.O ⊤ {L : Submodule K.O C | IsLat K.O K.E L ∧ ∀ y ∈ L, π B.g * y ∈ L} (fun _ => 1)
  refine orbSum_hom B.T ((Units.map (π : B.A →* C)).comp B.T.subtype) hsurj (B.X 1) _
    { toFun := fun L => ⟨img π L.1, h.img_mem L.2⟩
      invFun := fun M => ⟨lift π M.1, h.lift_mem hs hu hi M.2.1 M.2.2⟩
      left_inv := fun L => Subtype.ext (h.eq_lift he L.2).symm
      right_inv := fun M => Subtype.ext (h.img_lift M.1) } ?_ ?_
  ·
    intro t L M
    show M.1 = mulLat K.O ((t : B.Aˣ) : B.A) L.1 ↔
      img π M.1 = mulLat K.O ((Units.map (π : B.A →* C) (t : B.Aˣ) : Cˣ) : C) (img π L.1)
    constructor
    · intro hM
      calc img π M.1 = img π (mulLat K.O ((t : B.Aˣ) : B.A) (lift π (img π L.1))) := by
            rw [hM, ← h.eq_lift he L.2]
        _ = img π (lift π (mulLat K.O ((Units.map (π : B.A →* C) (t : B.Aˣ) : Cˣ) : C) (img π L.1))) := by
            rw [mulLat_lift]
        _ = _ := h.img_lift _
    · intro hM
      calc M.1 = lift π (img π M.1) := h.eq_lift he M.2
        _ = lift π (mulLat K.O ((Units.map (π : B.A →* C) (t : B.Aˣ) : Cˣ) : C) (img π L.1)) := by rw [hM]
        _ = mulLat K.O ((t : B.Aˣ) : B.A) (lift π (img π L.1)) := (mulLat_lift t _).symm
        _ = mulLat K.O ((t : B.Aˣ) : B.A) L.1 := by rw [← h.eq_lift he L.2]
  ·
    intro t
    have ht : ((t : B.Aˣ) : B.A) * B.σ ((t : B.Aˣ) : B.A) = 1 := t.2
    have hinv : (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) = B.σ ((t : B.Aˣ) : B.A) := Units.inv_eq_of_mul_eq_one_right ht
    have hcoe : ∀ s : B.Aˣ, ((Units.map (π : B.A →* C) s : Cˣ) : C) = π (s : B.A) := fun s => rfl
    show (IsIntegral K.O ((t : B.Aˣ) : B.A) ∧ IsIntegral K.O (((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A)) ↔
      (IsIntegral K.O ((Units.map (π : B.A →* C) (t : B.Aˣ) : Cˣ) : C) ∧
        IsIntegral K.O (((Units.map (π : B.A →* C) (t : B.Aˣ))⁻¹ : Cˣ) : C))
    rw [← map_inv, hcoe, hcoe, hinv]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.map (π.restrictScalars K.O), h2.map (π.restrictScalars K.O)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h.integral h1 ?_, h.integral h2 ?_⟩
      · exact h2
      · rw [B.σ_σ]; exact h1

end Half

end Half

theorem Half.prod {C₁ C₂ : Type} [CommRing C₁] [Algebra K.E C₁] [Module.Finite K.E C₁] [CommRing C₂]
    [Algebra K.E C₂] [Module.Finite K.E C₂] {B₁ B₂ : InvAlg K} {e₁ : B₁.A} {e₂ : B₂.A} {π₁ : B₁.A →ₐ[K.E] C₁}
    {π₂ : B₂.A →ₐ[K.E] C₂} (h₁ : Half B₁ e₁ π₁) (h₂ : Half B₂ e₂ π₂) :
    Half (B₁.prod B₂) ((e₁, e₂) : B₁.A × B₂.A) (π₁.prodMap π₂ : B₁.A × B₂.A →ₐ[K.E] C₁ × C₂) where
  idem := Prod.ext h₁.idem h₂.idem
  swap := Prod.ext h₁.swap h₂.swap
  surj := fun y => by
    obtain ⟨a, ha⟩ := h₁.surj y.1
    obtain ⟨b, hb⟩ := h₂.surj y.2
    exact ⟨(a, b), Prod.ext ha hb⟩
  ker := fun y => ⟨fun hy => Prod.ext ((h₁.ker y.1).1 (congrArg Prod.fst hy)) ((h₂.ker y.2).1 (congrArg Prod.snd hy)),
    fun hy => Prod.ext ((h₁.ker y.1).2 (congrArg Prod.fst hy)) ((h₂.ker y.2).2 (congrArg Prod.snd hy))⟩
  tr := fun y => by
    have h1 := Algebra.trace_prod_apply (R := K.E) (S := B₁.A) (T := B₂.A)
      (((e₁, e₂) : B₁.A × B₂.A) * (show B₁.A × B₂.A from y))
    have h2 := Algebra.trace_prod_apply (R := K.E) (S := C₁) (T := C₂) ((π₁ y.1, π₂ y.2))
    exact h1.trans ((congrArg₂ (· + ·) (h₁.tr y.1) (h₂.tr y.2)).trans h2.symm)

theorem half_quot (B : InvAlg K) {e f : B.A} (hi : e * e = e) (hef : e + f = 1) (hs : B.σ e = f) :
    Half B e (Ideal.Quotient.mkₐ K.E (Ideal.span {f})) ∧
      B.P = (LinearMap.mulLeft K.E (Ideal.Quotient.mk (Ideal.span {f}) B.g)).charpoly *
        (LinearMap.mulLeft K.E (Ideal.Quotient.mk (Ideal.span {e}) B.g)).charpoly := by
  have hf : f = 1 - e := by rw [← hef]; ring
  have hef0 : e * f = 0 := by rw [hf, mul_sub, mul_one, hi, sub_self]
  have hfe0 : f * e = 0 := by rw [mul_comm]; exact hef0
  have hff : f * f = f := by
    rw [hf]
    calc (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
      _ = 1 - e := by rw [hi]; ring
  set I : Ideal B.A := Ideal.span {f} with hI
  set J : Ideal B.A := Ideal.span {e} with hJ

  have hIe : Ideal.Quotient.mk I e = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    rw [show e - 1 = -f by rw [hf]; ring]
    exact I.neg_mem (Ideal.mem_span_singleton_self f)
  have hJe : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)
  have hIf : Ideal.Quotient.mk I f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)
  have hJf : Ideal.Quotient.mk J f = 1 := by
    rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    rw [show f - 1 = -e by rw [hf]; ring]
    exact J.neg_mem (Ideal.mem_span_singleton_self e)

  let Φ : B.A →ₐ[K.E] (B.A ⧸ I) × (B.A ⧸ J) := (Ideal.Quotient.mkₐ K.E I).prod (Ideal.Quotient.mkₐ K.E J)
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro y hy
      have h1 : Ideal.Quotient.mk I y = 0 := congrArg Prod.fst hy
      have h2 : Ideal.Quotient.mk J y = 0 := congrArg Prod.snd hy
      rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at h1
      rw [Ideal.Quotient.eq_zero_iff_mem, hJ, Ideal.mem_span_singleton] at h2
      obtain ⟨a, rfl⟩ := h1
      obtain ⟨b, hb⟩ := h2
      calc f * a = f * (f * a) := by rw [← mul_assoc, hff]
        _ = f * (e * b) := by rw [hb]
        _ = 0 := by rw [← mul_assoc, hfe0, zero_mul]
    · rintro ⟨u, v⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
      refine ⟨a * e + b * f, ?_⟩
      show (Ideal.Quotient.mk I (a * e + b * f), Ideal.Quotient.mk J (a * e + b * f)) = _
      simp only [map_add, map_mul, hIe, hIf, hJe, hJf, mul_one, mul_zero, add_zero, zero_add]
  let Ψ : B.A ≃ₐ[K.E] (B.A ⧸ I) × (B.A ⧸ J) := AlgEquiv.ofBijective Φ hΦ
  have hΨ : ∀ y, Ψ y = (Ideal.Quotient.mk I y, Ideal.Quotient.mk J y) := fun y => rfl
  refine ⟨⟨hi, by rw [hs]; exact hef, Ideal.Quotient.mkₐ_surjective K.E I, ?_, ?_⟩, ?_⟩
  · intro y
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      rw [← mul_assoc, hef0, zero_mul]
    · intro h
      refine ⟨y, ?_⟩
      calc y = (e + f) * y := by rw [hef, one_mul]
        _ = f * y := by rw [add_mul, h, zero_add]
  · intro y
    rw [← Algebra.trace_eq_of_algEquiv Ψ, hΨ, Algebra.trace_prod_apply]
    simp only [map_mul, hIe, hJe, one_mul, zero_mul, map_zero, add_zero, Ideal.Quotient.mkₐ_eq_mk]
  ·
    have hconj : Ψ.toLinearEquiv.conj (LinearMap.mulLeft K.E B.g) =
        (LinearMap.mulLeft K.E (Ideal.Quotient.mk I B.g)).prodMap
          (LinearMap.mulLeft K.E (Ideal.Quotient.mk J B.g)) := by
      refine LinearMap.ext fun x => ?_
      change Ψ (B.g * Ψ.symm x) = _
      rw [map_mul, AlgEquiv.apply_symm_apply, hΨ]
      rfl
    calc B.P = (LinearMap.mulLeft K.E B.g).charpoly := rfl
      _ = (Ψ.toLinearEquiv.conj (LinearMap.mulLeft K.E B.g)).charpoly :=
        (LinearEquiv.charpoly_conj _ _).symm
      _ = _ := by rw [hconj, LinearMap.charpoly_prodMap]

theorem stSum_eq (B : InvAlg K) {e : B.A} (hi : e * e = e) (hs : e + B.σ e = 1) (F : B.A → ℚ) (c : ℚ)
    (hF : ∀ x : B.A, IsUnit x → B.σ x = x → F x = c) : ∑ᶠ k : B.Cl, F k.rep = c := by
  have h1 : B.σ ((1 : B.Aˣ) : B.A) = ((1 : B.Aˣ) : B.A) := by rw [Units.val_one, map_one]
  let k₀ : B.Cl := Quot.mk _ ⟨1, h1⟩

  have hall : ∀ k : B.Cl, k = k₀ := by
    intro k
    induction k using Quot.ind with
    | mk x =>
      obtain ⟨u, hu⟩ := exists_norm B hi hs (x.1 : B.A) x.1.isUnit x.2
      exact (Quot.sound ⟨u, by simpa using hu⟩).symm
  have : Unique B.Cl := ⟨⟨k₀⟩, hall⟩
  rw [finsum_unique]
  exact hF _ (Quot.out (default : B.Cl)).1.isUnit (Quot.out (default : B.Cl)).2

theorem val_mul {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  have hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [map_mul, WithZero.log_mul hx' hy', neg_add]

theorem val_res (m f : K.O[X]) (hm : m.Monic) (p q : K.E[X]) (hp : p.Monic) (hq : q.Monic)
    (d1 : p ∣ m.map (algebraMap K.O K.E)) (d2 : q ∣ m.map (algebraMap K.O K.E))
    (h0 : p ∣ f.map (algebraMap K.O K.E)) (h1 : q ∣ (1 - f).map (algebraMap K.O K.E)) :
    val K.O (resultant p q) = 0 := by
  have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective K.O K.E

  have lift : ∀ r : K.E[X], r.Monic → r ∣ m.map (algebraMap K.O K.E) →
      ∃ r₀ : K.O[X], r₀.Monic ∧ r₀.map (algebraMap K.O K.E) = r := by
    intro r hr hd
    obtain ⟨r₀, h⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K.E hm hd
    rw [hr.leadingCoeff, C_1, mul_one] at h
    refine ⟨r₀, monic_of_injective hinj ?_, h⟩
    rw [h]; exact hr
  obtain ⟨p₀, hp₀, rfl⟩ := lift p hp d1
  obtain ⟨q₀, hq₀, rfl⟩ := lift q hq d2

  have dvdO : ∀ r₀ g : K.O[X], r₀.Monic →
      r₀.map (algebraMap K.O K.E) ∣ g.map (algebraMap K.O K.E) → r₀ ∣ g := by
    intro r₀ g hr h
    rw [← modByMonic_eq_zero_iff_dvd hr]
    apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_zero, map_modByMonic _ hr]
    exact (modByMonic_eq_zero_iff_dvd (hr.map _)).2 h
  obtain ⟨a, ha⟩ := dvdO p₀ f hp₀ h0
  obtain ⟨b, hb⟩ := dvdO q₀ (1 - f) hq₀ h1

  have hcop : IsCoprime p₀ q₀ := ⟨a, b, by rw [mul_comm a, mul_comm b, ← ha, ← hb]; ring⟩
  have hu : IsUnit (resultant p₀ q₀) := (isUnit_resultant_iff_isCoprime hp₀).2 hcop
  have hres : resultant (p₀.map (algebraMap K.O K.E)) (q₀.map (algebraMap K.O K.E)) =
      algebraMap K.O K.E (resultant p₀ q₀) := by
    rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]
    exact resultant_map_map p₀ q₀ _ _ _
  have hv : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E
      (algebraMap K.O K.E (resultant p₀ q₀)) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    show resultant p₀ q₀ ∉ IsLocalRing.maximalIdeal K.O
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hu
  rw [hres]
  simp only [val, hv, WithZero.log_one, neg_zero]

theorem val_res_mul (p₁ q₁ p₂ q₂ : K.E[X]) (hp₁ : p₁.Monic) (hq₁ : q₁.Monic) (hp₂ : p₂.Monic) (hq₂ : q₂.Monic)
    (hc : IsCoprime (p₁ * q₁) (p₂ * q₂)) : val K.O (resultant (p₁ * q₁) (p₂ * q₂)) =
      val K.O (resultant p₁ p₂) + val K.O (resultant p₁ q₂) +
        (val K.O (resultant q₁ p₂) + val K.O (resultant q₁ q₂)) := by
  have hd1 : (p₁ * q₁).natDegree = p₁.natDegree + q₁.natDegree := hp₁.natDegree_mul hq₁
  have hd2 : (p₂ * q₂).natDegree = p₂.natDegree + q₂.natDegree := hp₂.natDegree_mul hq₂

  have hR : ∀ f : K.E[X], resultant f (p₂ * q₂) = resultant f p₂ * resultant f q₂ := fun f => by
    have h := resultant_mul_right f p₂ q₂ f.natDegree le_rfl
    rw [← hd2] at h
    exact h

  have hL : resultant (p₁ * q₁) (p₂ * q₂) = resultant p₁ (p₂ * q₂) * resultant q₁ (p₂ * q₂) := by
    have h := resultant_mul_left p₁ q₁ (p₂ * q₂) (p₂ * q₂).natDegree le_rfl
    rw [← hd1] at h
    exact h
  have c11 : IsCoprime p₁ p₂ := (hc.of_mul_left_left).of_mul_right_left
  have c12 : IsCoprime p₁ q₂ := (hc.of_mul_left_left).of_mul_right_right
  have c21 : IsCoprime q₁ p₂ := (hc.of_mul_left_right).of_mul_right_left
  have c22 : IsCoprime q₁ q₂ := (hc.of_mul_left_right).of_mul_right_right
  have n11 := resultant_ne_zero p₁ p₂ c11
  have n12 := resultant_ne_zero p₁ q₂ c12
  have n21 := resultant_ne_zero q₁ p₂ c21
  have n22 := resultant_ne_zero q₁ q₂ c22
  rw [hL, hR, hR, val_mul (mul_ne_zero n11 n12) (mul_ne_zero n21 n22), val_mul n11 n12, val_mul n21 n22]

theorem chi_dvd_quot (B : InvAlg K) (I : Ideal B.A)
    (hs : (LinearMap.mulLeft K.E (Ideal.Quotient.mk I B.g)).charpoly.Separable) (f : K.O[X])
    (hf : aeval B.g f ∈ I) :
    (LinearMap.mulLeft K.E (Ideal.Quotient.mk I B.g)).charpoly ∣ f.map (algebraMap K.O K.E) := by
  refine chi_dvd (Ideal.Quotient.mk I B.g) hs (f.map (algebraMap K.O K.E)) ?_
  rw [Polynomial.aeval_map_algebraMap]
  have : Ideal.Quotient.mk I B.g = Ideal.Quotient.mkₐ K.O I B.g := rfl
  rw [this, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact hf

private theorem stSum_eq_N_one_of_swap_idempotent (B : InvAlg K) {e : B.A} (hi : e * e = e) (hs : e + B.σ e = 1) :
    B.stSum = B.N 1 :=
  stSum_eq B hi hs B.N (B.N 1) fun x hx hf => by
    obtain ⟨u, hu⟩ := exists_norm B hi hs x hx hf
    rw [hu]
    exact (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B 1 u).1

private theorem kapSum_eq_eta_gramDet_mul_N_one (B₁ B₂ : InvAlg K) {e : (B₁.prod B₂).A} (hi : e * e = e)
    (hs : e + (B₁.prod B₂).σ e = 1) :
    InvAlg.kapSum B₁ B₂ = K.eta (B₁.gramDet 1) * (B₁.prod B₂).N 1 :=
  stSum_eq (B₁.prod B₂) hi hs (fun x => K.eta (B₁.gramDet x.1) * (B₁.prod B₂).N x) _ fun x hx hf => by
    obtain ⟨u, hu⟩ := exists_norm (B₁.prod B₂) hi hs x hx hf
    let u₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) u
    have h1 : x.1 = 1 * ((u₁ : B₁.A) * B₁.σ (u₁ : B₁.A)) := congrArg Prod.fst hu
    show K.eta (B₁.gramDet x.1) * (B₁.prod B₂).N x = _
    rw [h1, (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B₁ 1 u₁).2, hu, (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (B₁.prod B₂) 1 u).1]

private theorem prod_P' (B₁ B₂ : InvAlg K) : (B₁.prod B₂).P = B₁.P * B₂.P := by
  show (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly = B₁.P * B₂.P
  have h : LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A) =
      (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := LinearMap.ext fun _ => rfl
  rw [h, LinearMap.charpoly_prodMap]
  rfl

private theorem X_one_nonempty_of_N_one_ne_zero (B : InvAlg K) (h : B.N 1 ≠ 0) : (B.X 1).Nonempty := by
  by_contra hne
  apply h
  have : IsEmpty (Orb K.O B.T (B.X 1)) :=
    ⟨fun o => Quot.inductionOn (motive := fun _ => False) o fun L => hne ⟨L.1, L.2⟩⟩
  show orbSum K.O B.T (B.X 1) (fun _ => 1) = 0
  unfold orbSum
  exact finsum_of_isEmpty _

theorem identity_of_swap : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    (∃ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A), e * e = e ∧ e + (B₁.prod B₂).σ e = 1) →
    InvAlg.Identity B₁ B₂ := by
  intro K B₁ B₂ hu₁ hu₂ hs hi₁ hi₂ ⟨e, he, hee, hes⟩

  obtain ⟨F, hF⟩ : ∃ F : K.O[X], aeval (B₁.prod B₂).g F = e := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at he
    exact (AlgHom.mem_range _).1 he
  have hF₁ : aeval B₁.g F = e.1 := by
    rw [← hF]
    show aeval B₁.g F = (AlgHom.fst K.O B₁.A B₂.A) (aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) F)
    rw [← Polynomial.aeval_algHom_apply]; rfl
  have hF₂ : aeval B₂.g F = e.2 := by
    rw [← hF]
    show aeval B₂.g F = (AlgHom.snd K.O B₁.A B₂.A) (aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) F)
    rw [← Polynomial.aeval_algHom_apply]; rfl
  have hi₁' : e.1 * e.1 = e.1 := congrArg Prod.fst hee
  have hi₂' : e.2 * e.2 = e.2 := congrArg Prod.snd hee
  have hs₁ : e.1 + B₁.σ e.1 = 1 := congrArg Prod.fst hes
  have hs₂ : e.2 + B₂.σ e.2 = 1 := congrArg Prod.snd hes
  have he₁ : e.1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) :=
    hF₁ ▸ Polynomial.aeval_mem_adjoin_singleton K.O B₁.g
  have he₂ : e.2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) :=
    hF₂ ▸ Polynomial.aeval_mem_adjoin_singleton K.O B₂.g
  have hσe₁ : B₁.σ e.1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    rw [eq_sub_of_add_eq' hs₁]; exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) he₁
  have hσe₂ : B₂.σ e.2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    rw [eq_sub_of_add_eq' hs₂]; exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) he₂
  have hP₁ : B₁.P.Separable := hs.of_mul_left
  have hP₂ : B₂.P.Separable := hs.of_mul_right

  obtain ⟨h₁, hd₁⟩ := half_quot B₁ hi₁' hs₁ rfl
  obtain ⟨h₂, hd₂⟩ := half_quot B₂ hi₂' hs₂ rfl
  obtain ⟨h₁', hd₁'⟩ := half_quot B₁ (e := B₁.σ e.1) (f := e.1) (by rw [← map_mul, hi₁'])
    (by rw [add_comm]; exact hs₁) (B₁.σ_σ _)
  obtain ⟨h₂', hd₂'⟩ := half_quot B₂ (e := B₂.σ e.2) (f := e.2) (by rw [← map_mul, hi₂'])
    (by rw [add_comm]; exact hs₂) (B₂.σ_σ _)
  set p₁ := (LinearMap.mulLeft K.E (Ideal.Quotient.mk (Ideal.span {B₁.σ e.1}) B₁.g)).charpoly with hp₁
  set q₁ := (LinearMap.mulLeft K.E (Ideal.Quotient.mk (Ideal.span {e.1}) B₁.g)).charpoly with hq₁
  set p₂ := (LinearMap.mulLeft K.E (Ideal.Quotient.mk (Ideal.span {B₂.σ e.2}) B₂.g)).charpoly with hp₂
  set q₂ := (LinearMap.mulLeft K.E (Ideal.Quotient.mk (Ideal.span {e.2}) B₂.g)).charpoly with hq₂
  have N₁p := h₁.N_one he₁ hP₁ hu₁ hi₁
  have N₂p := h₂.N_one he₂ hP₂ hu₂ hi₂
  have N₁q := h₁'.N_one hσe₁ hP₁ hu₁ hi₁
  have N₂q := h₂'.N_one hσe₂ hP₂ hu₂ hi₂

  have hP : (B₁.prod B₂).P.Separable := by rw [prod_P']; exact hs
  have hu : (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 := Prod.ext hu₁ hu₂
  have hi : IsIntegral K.O (B₁.prod B₂).g := IsIntegral.pair hi₁ hi₂
  have hσe : (B₁.prod B₂).σ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := by
    rw [eq_sub_of_add_eq' hes]; exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) he
  have NBp := (Half.prod h₁ h₂).N_one he hP hu hi
  have NBq := (Half.prod h₁' h₂').N_one hσe hP hu hi
  have hsp : (p₁ * p₂).Separable := hs.of_dvd ⟨q₁ * q₂, by rw [hd₁, hd₂]; ring⟩
  have hsq : (q₁ * q₂).Separable := hs.of_dvd ⟨p₁ * p₂, by rw [hd₁, hd₂]; ring⟩
  have Cp := GlobalTheory.T.weighted_count_stable_lattices_product_descent_GL K.O K.E (B₁.A ⧸ Ideal.span {B₁.σ e.1}) (B₂.A ⧸ Ideal.span {B₂.σ e.2})
    (Ideal.Quotient.mk _ B₁.g) (Ideal.Quotient.mk _ B₂.g) hsp
  have Cq := GlobalTheory.T.weighted_count_stable_lattices_product_descent_GL K.O K.E (B₁.A ⧸ Ideal.span {e.1}) (B₂.A ⧸ Ideal.span {e.2})
    (Ideal.Quotient.mk _ B₁.g) (Ideal.Quotient.mk _ B₂.g) hsq
  have hc : ((Nat.card (IsLocalRing.ResidueField K.O) : ℕ) : ℚ) = (K.q : ℚ) ^ 2 := by
    rw [K.card_res]; push_cast; ring
  have E1 : (B₁.prod B₂).N 1 = ((K.q : ℚ) ^ 2) ^ val K.O (resultant p₁ p₂) * (B₁.N 1 * B₂.N 1) := by
    rw [NBp, N₁p, N₂p, ← hc]
    exact Cp
  have E2 : (B₁.prod B₂).N 1 = ((K.q : ℚ) ^ 2) ^ val K.O (resultant q₁ q₂) * (B₁.N 1 * B₂.N 1) := by
    rw [NBq, N₁q, N₂q, ← hc]
    exact Cq

  obtain ⟨m₁, hm₁, hm₁'⟩ := hi₁
  obtain ⟨m₂, hm₂, hm₂'⟩ := hi₂
  have dP₁ : B₁.P ∣ m₁.map (algebraMap K.O K.E) :=
    chi_dvd B₁.g hP₁ _ (by rw [aeval_map_algebraMap, aeval_def]; exact hm₁')
  have dP₂ : B₂.P ∣ m₂.map (algebraMap K.O K.E) :=
    chi_dvd B₂.g hP₂ _ (by rw [aeval_map_algebraMap, aeval_def]; exact hm₂')
  have dm₁ : B₁.P ∣ (m₁ * m₂).map (algebraMap K.O K.E) := by
    rw [Polynomial.map_mul]; exact dP₁.mul_right _
  have dm₂ : B₂.P ∣ (m₁ * m₂).map (algebraMap K.O K.E) := by
    rw [Polynomial.map_mul]; exact dP₂.mul_left _
  have dp₁ : p₁ ∣ B₁.P := ⟨q₁, hd₁⟩
  have dq₁ : q₁ ∣ B₁.P := ⟨p₁, by rw [hd₁, mul_comm]⟩
  have dp₂ : p₂ ∣ B₂.P := ⟨q₂, hd₂⟩
  have dq₂ : q₂ ∣ B₂.P := ⟨p₂, by rw [hd₂, mul_comm]⟩
  have fp₁ : p₁ ∣ (1 - F).map (algebraMap K.O K.E) :=
    chi_dvd_quot B₁ _ (hP₁.of_dvd dp₁) (1 - F) (by
      rw [map_sub, map_one, hF₁, ← eq_sub_of_add_eq' hs₁]; exact Ideal.mem_span_singleton_self _)
  have fp₂ : p₂ ∣ (1 - F).map (algebraMap K.O K.E) :=
    chi_dvd_quot B₂ _ (hP₂.of_dvd dp₂) (1 - F) (by
      rw [map_sub, map_one, hF₂, ← eq_sub_of_add_eq' hs₂]; exact Ideal.mem_span_singleton_self _)
  have fq₁ : q₁ ∣ F.map (algebraMap K.O K.E) :=
    chi_dvd_quot B₁ _ (hP₁.of_dvd dq₁) F (by rw [hF₁]; exact Ideal.mem_span_singleton_self _)
  have fq₂ : q₂ ∣ F.map (algebraMap K.O K.E) :=
    chi_dvd_quot B₂ _ (hP₂.of_dvd dq₂) F (by rw [hF₂]; exact Ideal.mem_span_singleton_self _)
  have mp₁ : p₁.Monic := LinearMap.charpoly_monic _
  have mq₁ : q₁.Monic := LinearMap.charpoly_monic _
  have mp₂ : p₂.Monic := LinearMap.charpoly_monic _
  have mq₂ : q₂.Monic := LinearMap.charpoly_monic _
  have x₁ : val K.O (resultant p₁ q₂) = 0 :=
    val_res (m₁ * m₂) (1 - F) (hm₁.mul hm₂) p₁ q₂ mp₁ mq₂ (dp₁.trans dm₁) (dq₂.trans dm₂) fp₁
      (by rw [sub_sub_cancel]; exact fq₂)
  have x₂ : val K.O (resultant q₁ p₂) = 0 :=
    val_res (m₁ * m₂) F (hm₁.mul hm₂) q₁ p₂ mq₁ mp₂ (dq₁.trans dm₁) (dp₂.trans dm₂) fq₁ fp₂
  have hcop : IsCoprime (p₁ * q₁) (p₂ * q₂) := by rw [← hd₁, ← hd₂]; exact hs.isCoprime
  have hv : val K.O (resultant B₁.P B₂.P) = val K.O (resultant p₁ p₂) + val K.O (resultant q₁ q₂) := by
    rw [hd₁, hd₂, val_res_mul p₁ q₁ p₂ q₂ mp₁ mq₁ mp₂ mq₂ hcop, x₁, x₂]; ring

  show (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * InvAlg.kapSum B₁ B₂ = B₁.stSum * B₂.stSum
  rw [kapSum_eq_eta_gramDet_mul_N_one B₁ B₂ hee hes, stSum_eq_N_one_of_swap_idempotent B₁ hi₁' hs₁, stSum_eq_N_one_of_swap_idempotent B₂ hi₂' hs₂, hv]
  by_cases hz : B₁.N 1 * B₂.N 1 = 0
  · rw [E1, hz]; simp
  · have hcard : 1 < Nat.card (IsLocalRing.ResidueField K.O) := Finite.one_lt_card
    have hQ : (0 : ℚ) < (K.q : ℚ) ^ 2 := by
      rw [← hc]; exact_mod_cast (by omega : 0 < Nat.card (IsLocalRing.ResidueField K.O))
    have hQ1 : (K.q : ℚ) ^ 2 ≠ 1 := by
      rw [← hc]; exact_mod_cast hcard.ne'
    have hab : val K.O (resultant p₁ p₂) = val K.O (resultant q₁ q₂) :=
      zpow_right_injective₀ hQ hQ1 (mul_right_cancel₀ hz (E1.symm.trans E2))
    have hne := X_one_nonempty_of_N_one_ne_zero B₁ (left_ne_zero_of_mul hz)
    rw [GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice K B₁ 1 (map_one _) hne, E1, ← hab]
    have hQ0 : (K.q : ℚ) ^ 2 ≠ 0 := hQ.ne'
    rw [show -(val K.O (resultant p₁ p₂) + val K.O (resultant p₁ p₂)) =
        2 * (-val K.O (resultant p₁ p₂)) by ring, zpow_mul,
      show (-(K.q : ℚ)) ^ (2 : ℤ) = (K.q : ℚ) ^ 2 by rw [zpow_two, neg_mul_neg, sq],
      one_mul, ← mul_assoc, ← zpow_add₀ hQ0, neg_add_cancel, zpow_zero, one_mul]

end GlobalTheory.UnitLemma.Swap
