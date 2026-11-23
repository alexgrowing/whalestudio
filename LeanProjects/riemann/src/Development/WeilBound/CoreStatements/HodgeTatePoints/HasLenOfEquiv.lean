import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.UpSmith
import ReciprocityTheory.DualLattices.MemOfSumSingleEqZero

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

lemma hasLen_of_equiv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨f⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans f⟩, hx⟩

lemma fg_of_iff {V : Type} [AddCommGroup V] [Module R V] {A B : Submodule R V} (h : A.FG)
    (e : ∀ x, x ∈ B ↔ x ∈ A) : B.FG := by
  rwa [show B = A from SetLike.ext e]

lemma free_of_fg (hv : v.Integers R) {Y : Type} (A : Submodule R (Y → C)) (hA : A.FG) :
    Module.Free R A := by
  classical
  haveI := hv.hom_inj.isDomain
  haveI := ValuationRing.of_integers v hv
  haveI : Module.Finite R A := Module.Finite.iff_fg.mpr hA
  haveI : Module.Flat R A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro m hm
    obtain ⟨⟨r, hr⟩, h⟩ := (Submodule.mem_torsion_iff m).1 hm
    have hr0 : algebraMap R C r ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero hr (hv.hom_inj (by simpa using h0))
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext y
    have h1 : algebraMap R C r * (m : Y → C) y = 0 := by
      have h2 := congrArg (fun z : A => (z : Y → C) y) h
      simpa [Algebra.smul_def] using h2
    simpa using (mul_eq_zero.1 h1).resolve_left hr0
  exact Module.free_of_flat_of_isLocalRing

lemma fg_ker (hv : v.Integers R) {P Y : Type} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (φ : P →ₗ[R] (Y → C)) : (LinearMap.ker φ).FG := by
  classical
  have hfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  haveI : Module.Free R (LinearMap.range φ) := free_of_fg hv _ hfg
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict φ)
  have hker : LinearMap.ker φ = LinearMap.range (LinearMap.id - s.comp φ.rangeRestrict) := by
    rw [← LinearMap.ker_rangeRestrict]
    apply le_antisymm
    · intro x hx
      refine ⟨x, ?_⟩
      rw [LinearMap.mem_ker] at hx
      simp [hx]
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      have h1 := LinearMap.congr_fun hs (φ.rangeRestrict y)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
      rw [h1, sub_self]
  rw [hker, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

lemma fg_inf_comap (hv : v.Integers R) {V Y : Type} [AddCommGroup V] [Module R V]
    (A : Submodule R V) (hA : A.FG) (φ : V →ₗ[R] (Y → C)) (B : Submodule R (Y → C)) (hB : B.FG) :
    (A ⊓ B.comap φ).FG := by
  classical
  haveI : Module.Finite R A := Module.Finite.iff_fg.mpr hA
  haveI : Module.Finite R B := Module.Finite.iff_fg.mpr hB
  let ψ : (A × B) →ₗ[R] (Y → C) :=
    φ.comp (A.subtype.comp (LinearMap.fst R A B)) - B.subtype.comp (LinearMap.snd R A B)
  have hk := fg_ker hv ψ
  have heq : A ⊓ B.comap φ = (LinearMap.ker ψ).map (A.subtype.comp (LinearMap.fst R A B)) := by
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      refine ⟨(⟨x, hxA⟩, ⟨φ x, hxB⟩), ?_, rfl⟩
      simp [ψ]
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      have h' : φ a = b := by simpa [ψ, sub_eq_zero] using hab
      refine ⟨a.2, ?_⟩
      show φ a ∈ B
      rw [h']
      exact b.2
  rw [heq]
  exact hk.map _

lemma exists_hasLen (hv : v.Integers R) {Y : Type} (A B : Submodule R (Y → C)) (hA : A.FG)
    (hB : B.FG) : ∃ x, HasLen v R (A ⧸ B.comap A.subtype) x := by
  classical
  haveI := hv.hom_inj.isDomain
  haveI : Module.Finite R A := Module.Finite.iff_fg.mpr hA
  haveI : Module.Free R A := free_of_fg hv A hA
  set K : Submodule R A := B.comap A.subtype with hK
  have hKfg : K.FG := by
    apply Submodule.fg_of_fg_map_injective A.subtype A.injective_subtype
    rw [hK, Submodule.map_comap_subtype]
    have h5 := fg_inf_comap hv A hA LinearMap.id B hB
    simpa using h5
  let b := Module.finBasis R A
  let e := b.equivFun
  obtain ⟨s, hs⟩ := hKfg.map (e : A →ₗ[R] (Fin (Module.finrank R A) → R))
  obtain ⟨c, ⟨f⟩⟩ := Smith.smith_gen hv (Module.finrank R A)
    (fun i : s => (i : Fin (Module.finrank R A) → R))
  refine ⟨_, Module.finrank R A, c, ⟨?_⟩, rfl⟩
  have hr : Set.range (fun i : s => (i : Fin (Module.finrank R A) → R)) = ↑s := by
    first
    | (ext; simp)
    | ext
    | simp
  have hs' : Submodule.span R (Set.range (fun i : s => (i : Fin (Module.finrank R A) → R))) =
      K.map (e : A →ₗ[R] (Fin (Module.finrank R A) → R)) := by
    rw [hr, hs]
  exact (Submodule.Quotient.equiv K _ e (by rw [hs'] <;> rfl)).trans f

lemma len_ne_zero_iff (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) : x ≠ 0 ↔ ∃ r : R, r ≠ 0 ∧ ∀ m : M, r • m = 0 := by
  haveI := hv.hom_inj.isDomain
  obtain ⟨m, c, ⟨f⟩, rfl⟩ := h
  have hvc : ∀ i, v (algebraMap R C (c i)) = 0 ↔ c i = 0 := fun i => by
    rw [Valuation.zero_iff, map_eq_zero_iff _ hv.hom_inj]
  constructor
  · intro hx
    have hc : ∀ i, c i ≠ 0 := fun i hci =>
      hx (Finset.prod_eq_zero (Finset.mem_univ i) ((hvc i).2 hci))
    refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 (fun i _ => hc i), fun x => ?_⟩
    apply f.injective
    rw [map_smul, map_zero]
    funext i
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f x i)
    simp only [Pi.smul_apply, Pi.zero_apply]
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem c (Finset.mem_univ i)) y
  · rintro ⟨r, hr, hkill⟩ hx
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hx
    have hci := (hvc i).1 hi
    have h1 := congrArg f (hkill (f.symm (Pi.single i (Submodule.Quotient.mk 1))))
    rw [map_smul, LinearEquiv.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 i
    rw [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, hci, zero_dvd_iff, smul_eq_mul,
      mul_one] at h2
    exact hr h2

lemma colen_ne_zero (_hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {M : Submodule R (X → C)} (h : IsLat R M) : ∃ c, c ≠ 0 ∧ HasColen R v M c := by
  obtain ⟨B, hB, hM⟩ := h
  refine ⟨v B.det, ?_, B, hM, rfl⟩
  rw [Ne, Valuation.zero_iff]
  exact hB.ne_zero

lemma pi_span_fg (c : C) (Y : Type) [Finite Y] :
    (Submodule.pi Set.univ fun _ : Y => (Submodule.span R {c} : Submodule R C)).FG := by
  classical
  let L : (Y → R) →ₗ[R] (Y → C) :=
    LinearMap.pi (fun y => (LinearMap.toSpanSingleton R C c).comp (LinearMap.proj y))
  have heq : Submodule.pi Set.univ (fun _ : Y => (Submodule.span R {c} : Submodule R C)) =
      LinearMap.range L := by
    ext f
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_span_singleton,
      LinearMap.mem_range]
    constructor
    · intro hf
      choose a ha using hf
      exact ⟨a, funext fun y => by simp [L, ha y]⟩
    · rintro ⟨a, rfl⟩ y
      exact ⟨a y, by simp [L]⟩
  rw [heq, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map L

lemma intFun_fg (Y : Type) [Finite Y] : (intFun (C := C) R Y).FG := by
  have heq : intFun (C := C) R Y =
      Submodule.pi Set.univ (fun _ : Y => (Submodule.span R {(1 : C)} : Submodule R C)) := by
    ext f
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_span_singleton,
      Algebra.smul_def, mul_one]
    exact Iff.rfl
  rw [heq]
  exact pi_span_fg 1 Y

lemma inf_addFun_fg (hv : v.Integers R) (p : ℕ) {N : Type} [AddCommGroup N] [Finite N]
    (A : Submodule R (N → C)) (hA : A.FG) : (A ⊓ addFun R p N).FG := by
  classical
  let φ : (N → C) →ₗ[R] (N × N → C) :=
    LinearMap.funLeft R C (fun q : N × N => q.1 + q.2) - LinearMap.funLeft R C Prod.fst -
      LinearMap.funLeft R C Prod.snd
  refine fg_of_iff (fg_inf_comap hv A hA φ _ (pi_span_fg (R := R) ((p : ℕ) : C) (N × N)))
    (fun f => ?_)
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_pi]
  refine and_congr_right fun _ => ⟨fun h q _ => h q.1 q.2, fun h => ?_⟩
  show ∀ x y : N, f (x + y) - f x - f y ∈ pInt R p
  exact fun x y => h (x, y) (Set.mem_univ _)

lemma aug_fg (hv : v.Integers R) {N : Type} [AddCommGroup N]
    (A : Submodule R (N → C)) (hA : A.FG) : (augIdeal A).FG := by
  classical
  let φ : (N → C) →ₗ[R] (Unit → C) := LinearMap.pi (fun _ : Unit => LinearMap.proj (0 : N))
  refine fg_of_iff (fg_inf_comap hv A hA φ ⊥ Submodule.fg_bot) (fun f => ?_)
  unfold augIdeal
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_bot,
    LinearMap.mem_ker]
  exact and_congr_right fun _ => ⟨fun h => funext fun _ => h, fun h => congrFun h ()⟩

lemma sq_aug_fg (hv : v.Integers R) {N : Type} [AddCommGroup N]
    (A : Submodule R (N → C)) (hA : A.FG) : (sqIdeal (augIdeal A)).FG := by
  have hI := aug_fg hv A hA
  have heq : sqIdeal (augIdeal A) = augIdeal A * augIdeal A := by
    rw [Submodule.mul_eq_span_mul_set]
    unfold sqIdeal
    congr 1
    ext h
    simp [Set.mem_mul, eq_comm]
  rw [heq]
  exact hI.mul hI

end Gen

private theorem exists_smul_delta_mem_of_isLat {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {v : Valuation C NNReal} (hv : v.Integers R) {N : Type} [Fintype N] [DecidableEq N]
    (M : Submodule R (N → C)) (hM : IsLat R M) :
    ∃ d : R, d ≠ 0 ∧ ∀ x : N, (fun y => if y = x then algebraMap R C d else 0) ∈ M := by
  classical
  haveI := hv.hom_inj.isDomain
  haveI := hv.isFractionRing
  obtain ⟨B, hB, rfl⟩ := hM
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Finset.univ.image (fun q : N × N => B⁻¹ q.1 q.2))
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun x => ?_⟩
  have hx : ∀ j, ∃ a : R, algebraMap R C a = d • B⁻¹ j x := fun j =>
    (RingHom.mem_rangeS).1 (hint _ (Finset.mem_image.2 ⟨(j, x), Finset.mem_univ _, rfl⟩))
  choose a ha using hx
  have heq : (fun y => if y = x then algebraMap R C d else 0) = ∑ j, a j • (fun y => B y j) := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    simp only [Algebra.smul_def]
    have hmul : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
    have h1 := congrFun (congrFun hmul y) x
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    have key : ∑ j, algebraMap R C (a j) * B y j = algebraMap R C d * ∑ j, B y j * B⁻¹ j x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [ha, Algebra.smul_def]; ring)
    rw [key, h1]
    split_ifs <;> simp
  rw [heq]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

private theorem exists_smul_augIdeal_mem_sqIdeal_of_isLat {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {v : Valuation C NNReal} (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N]
    [DecidableEq N] (M : Submodule R (N → C)) (hM : IsLat R M) (hint : M ≤ intFun R N) :
    ∃ r : R, r ≠ 0 ∧ ∀ f ∈ augIdeal M, r • f ∈ sqIdeal (augIdeal M) := by
  classical
  haveI := hv.hom_inj.isDomain
  obtain ⟨d, hd, hδ⟩ := exists_smul_delta_mem_of_isLat hv M hM
  refine ⟨d * d, mul_ne_zero hd hd, fun f hf => ?_⟩
  set δ : N → (N → C) := fun x y => if y = x then algebraMap R C d else 0 with hδdef
  have hf' : f ∈ M ⊓ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : N => C) 0) := hf
  obtain ⟨hfM, hf0'⟩ := Submodule.mem_inf.1 hf'
  have hf0 : f 0 = 0 := LinearMap.mem_ker.1 hf0'
  have hfi : ∀ x, ∃ r : R, algebraMap R C r = f x := hint hfM
  choose c hc using hfi
  have hδaug : ∀ x, x ≠ 0 → δ x ∈ augIdeal M := fun x hx =>
    (show δ x ∈ M ⊓ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : N => C) 0) from
      Submodule.mem_inf.2 ⟨hδ x, LinearMap.mem_ker.2 (by simp [hδdef, Ne.symm hx])⟩)
  have heq : (d * d) • f = ∑ x ∈ Finset.univ.erase 0, c x • (δ x * δ x) := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.mul_apply, hδdef]
    by_cases hy : y = 0
    · subst hy
      rw [hf0, smul_zero]
      symm
      apply Finset.sum_eq_zero
      intro x hx
      simp [Ne.symm (Finset.ne_of_mem_erase hx)]
    · rw [Finset.sum_eq_single y]
      · rw [if_pos (rfl : y = y), Algebra.smul_def, Algebra.smul_def, ← hc y, map_mul]
        ring
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨hy, Finset.mem_univ y⟩) h
  rw [heq]
  exact Submodule.sum_mem _ (fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨δ x, hδaug x (Finset.ne_of_mem_erase hx), δ x, hδaug x (Finset.ne_of_mem_erase hx), rfl⟩))

theorem lens : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∃ cA cN cO : NNReal, cA ≠ 0 ∧ cN ≠ 0 ∧ cO ≠ 0 ∧ HasLen v R (AFQuot p AA.carrier) cA ∧ HasColen R v AA.carrier cN ∧ HasLen v R (OmAA AA.carrier) cO := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA
  classical
  haveI := hv.hom_inj.isDomain
  have hMfg : AA.carrier.FG := by
    obtain ⟨B, -, hB⟩ := AA.lat
    rw [hB]
    exact Submodule.fg_span (Set.finite_range _)
  have hp0 : (p : R) ≠ 0 := by
    intro h
    have h2 : ((p : ℕ) : C) = 0 := by rw [← map_natCast (algebraMap R C), h, map_zero]
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h2
  have hlinfg : (linFun R p N).FG := inf_addFun_fg hv p (intFun R N) (intFun_fg (C := C) (R := R) N)
  have hBfg : (afFun p AA.carrier ⊔ pFun R p N).FG :=
    (inf_addFun_fg hv p AA.carrier hMfg).sup (pi_span_fg (R := R) ((p : ℕ) : C) N)
  obtain ⟨cA, hA⟩ := exists_hasLen hv (linFun R p N) (afFun p AA.carrier ⊔ pFun R p N) hlinfg hBfg
  have hA0 : cA ≠ 0 := by
    rw [len_ne_zero_iff hv hA]
    refine ⟨p, hp0, fun m => ?_⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    apply Submodule.mem_sup_right
    have hfx : ∀ x, ∃ r : R, algebraMap R C r = (f : N → C) x := (Submodule.mem_inf.1 f.2).1
    unfold pFun
    rw [Submodule.mem_pi]
    intro x _
    obtain ⟨r, hr⟩ := hfx x
    unfold pInt
    rw [Submodule.mem_span_singleton]
    refine ⟨r, ?_⟩
    simp only [Submodule.subtype_apply, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, ← hr,
      map_natCast]
    ring
  obtain ⟨cN, hcN0, hcN⟩ := colen_ne_zero hv AA.lat
  have haug := aug_fg hv AA.carrier hMfg
  have hsq := sq_aug_fg hv AA.carrier hMfg
  obtain ⟨cO, hO⟩ := exists_hasLen hv (augIdeal AA.carrier) (sqIdeal (augIdeal AA.carrier)) haug hsq
  have hO0 : cO ≠ 0 := by
    rw [len_ne_zero_iff hv hO]
    obtain ⟨r, hr0, hr⟩ := exists_smul_augIdeal_mem_sqIdeal_of_isLat hv AA.carrier AA.lat AA.le_int
    refine ⟨r, hr0, fun m => ?_⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hr f f.2
  exact ⟨cA, cN, cO, hA0, hcN0, hO0, hA, hcN, hO⟩

end PositivityTheory.HtPt.Rc
