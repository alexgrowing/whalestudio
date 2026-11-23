import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Inter

section General

variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem exists_smul_mem {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (L : Submodule O V) (hL : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ a : nonZeroDivisors O, (a : O) • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := by rw [hL]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, by simpa using hy⟩
  | zero => exact ⟨1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    refine ⟨a * b, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [Submonoid.coe_mul, mul_comm, mul_smul]
      exact L.smul_mem _ ha
    · rw [Submonoid.coe_mul, mul_smul]
      exact L.smul_mem _ hb
  | smul c y _ hy =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
    refine ⟨s * a, ?_⟩
    have key : ((s * a : nonZeroDivisors O) : O) • (IsLocalization.mk' K r s • y) = r • ((a : O) • y) := by
      rw [← algebraMap_smul K ((s * a : nonZeroDivisors O) : O), ← algebraMap_smul K r,
        ← algebraMap_smul K (a : O) y, smul_smul, smul_smul]
      congr 1
      rw [← IsLocalization.mk'_spec K r s, Submonoid.coe_mul, map_mul]
      ring
    rw [key]
    exact L.smul_mem r ha

private theorem isUnit_end_lemma {M : Type} [AddCommGroup M] [Module K M] [Module O M] [IsScalarTower O K M]
    (x : nonZeroDivisors O) : IsUnit (algebraMap O (Module.End O M) x) := by
  have hx : algebraMap O K x ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
  rw [Module.End.isUnit_iff]
  refine ⟨fun m₁ m₂ h => ?_, fun m => ⟨(algebraMap O K x)⁻¹ • m, ?_⟩⟩
  · simp only [Module.algebraMap_end_apply] at h
    rw [← algebraMap_smul K (x : O) m₁, ← algebraMap_smul K (x : O) m₂] at h
    exact smul_right_injective M hx h
  · simp only [Module.algebraMap_end_apply]
    rw [← algebraMap_smul K (x : O), smul_smul, mul_inv_cancel₀ hx, one_smul]

private theorem isLocalizedModule_lemma_2 {V : Type} [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (L : Submodule O V) (hL : Submodule.span K (L : Set V) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) L.subtype where
  map_units x := isUnit_end_lemma (K := K) x
  surj y := by
    obtain ⟨a, ha⟩ := exists_smul_mem L hL y
    exact ⟨(⟨_, ha⟩, a), rfl⟩
  exists_of_eq {x₁ x₂} h := ⟨1, by rw [show x₁ = x₂ from Subtype.ext h]⟩

theorem exists_extend {V W : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]
    (L : Submodule O V) (hL : Submodule.span K (L : Set V) = ⊤) (t : L →ₗ[O] W) :
    ∃ T : V →ₗ[K] W, ∀ x : L, T x = t x := by
  have := isLocalizedModule_lemma_2 L hL
  refine ⟨(IsLocalizedModule.lift (nonZeroDivisors O) L.subtype t
      (fun x => isUnit_end_lemma (K := K) x)).extendScalarsOfIsLocalization (nonZeroDivisors O) K,
    fun x => ?_⟩
  rw [LinearMap.extendScalarsOfIsLocalization_apply']
  exact IsLocalizedModule.lift_apply (S := nonZeroDivisors O) (f := L.subtype) t _ x

private theorem retract_lemma_3 [IsDedekindDomain O] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
    (ψ : M →ₗ[O] K) : ∃ r : M →ₗ[O] M, (∀ x, ψ (r x) = 0) ∧ ∀ x, ψ x = 0 → r x = x := by
  by_cases h0 : ∀ x, ψ x = 0
  · exact ⟨LinearMap.id, fun x => h0 x, fun x _ => rfl⟩
  simp only [not_forall] at h0
  obtain ⟨x₀, hx₀⟩ := h0
  have hfg : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map ψ
  let J : FractionalIdeal (nonZeroDivisors O) K :=
    ⟨LinearMap.range ψ, FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors O) hfg⟩
  have hJc : ∀ y, y ∈ J ↔ y ∈ LinearMap.range ψ := fun y => Iff.rfl
  have hJ : J ≠ 0 := by
    intro hJ
    have h := (hJc (ψ x₀)).2 (LinearMap.mem_range_self ψ x₀)
    rw [hJ, FractionalIdeal.mem_zero_iff] at h
    exact hx₀ h
  have hint : ∀ b ∈ J⁻¹, ∀ x, ∃ o : O, algebraMap O K o = b * ψ x := fun b hb x =>
    (FractionalIdeal.mem_one_iff (S := nonZeroDivisors O)).1
      (((FractionalIdeal.mem_inv_iff hJ).1 hb) (ψ x) ((hJc _).2 (LinearMap.mem_range_self ψ x)))
  have h1 : (1 : K) ∈ (J : Submodule O K) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors O) K) : Submodule O K) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.mem_coe]
    exact FractionalIdeal.one_mem_one (S := nonZeroDivisors O)
  obtain ⟨g, hg1, hg2⟩ : ∃ g : M →ₗ[O] M, (∀ x, ψ (g x) = 1 * ψ x) ∧ ∀ x, ψ x = 0 → g x = 0 := by
    refine Submodule.mul_induction_on
      (C := fun y => ∃ g : M →ₗ[O] M, (∀ x, ψ (g x) = y * ψ x) ∧ ∀ x, ψ x = 0 → g x = 0) h1 ?_ ?_
    · intro a ha b hb
      obtain ⟨l, rfl⟩ := LinearMap.mem_range.1 ((hJc a).1 (FractionalIdeal.mem_coe.1 ha))
      have hb' := hint b (FractionalIdeal.mem_coe.1 hb)
      let c : M →ₗ[O] O :=
        { toFun := fun x => (hb' x).choose
          map_add' := fun x y => by
            apply IsFractionRing.injective O K
            rw [(hb' (x + y)).choose_spec, map_add (algebraMap O K), (hb' x).choose_spec,
              (hb' y).choose_spec, map_add ψ, mul_add]
          map_smul' := fun o x => by
            apply IsFractionRing.injective O K
            rw [(hb' (o • x)).choose_spec, RingHom.id_apply, smul_eq_mul, map_mul,
              (hb' x).choose_spec, map_smul ψ, Algebra.smul_def]
            ring }
      have hc : ∀ x, algebraMap O K (c x) = b * ψ x := fun x => (hb' x).choose_spec
      refine ⟨c.smulRight l, fun x => ?_, fun x hx => ?_⟩
      · rw [LinearMap.smulRight_apply, map_smul ψ, Algebra.smul_def, hc]
        ring
      · have hcx : c x = 0 := IsFractionRing.injective O K (by rw [hc, hx, mul_zero, map_zero])
        rw [LinearMap.smulRight_apply, hcx, zero_smul]
    · rintro y z ⟨g, hg1, hg2⟩ ⟨g', hg1', hg2'⟩
      refine ⟨g + g', fun x => ?_, fun x hx => ?_⟩
      · rw [LinearMap.add_apply, map_add, hg1, hg1', add_mul]
      · rw [LinearMap.add_apply, hg2 x hx, hg2' x hx, add_zero]
  refine ⟨LinearMap.id - g, fun x => ?_, fun x hx => ?_⟩
  · rw [LinearMap.sub_apply, map_sub, hg1, one_mul, LinearMap.id_apply, sub_self]
  · rw [LinearMap.sub_apply, hg2 x hx, LinearMap.id_apply, sub_zero]

end General

section Retr

variable {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem exists_retraction {U V : Type} [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (q : U →ₗ[K] V) (hq : Function.Injective q) (L : Submodule O V) [Module.Finite O L]
    (hL : Submodule.span K (L : Set V) = ⊤) :
    ∃ T : V →ₗ[K] U, (∀ u, T (q u) = u) ∧ ∀ x ∈ L, q (T x) ∈ L := by
  classical
  have : Module.Finite K V := by
    obtain ⟨S, hS⟩ := Module.Finite.iff_fg.1 ‹Module.Finite O L›
    refine ⟨⟨S, ?_⟩⟩
    rw [← Submodule.span_span_of_tower O K, hS, hL]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range q)
  let pC : V →ₗ[K] C := Submodule.projectionOnto C (LinearMap.range q) hC.symm
  let b := Module.finBasis K C
  let φ : Fin (Module.finrank K C) → V →ₗ[K] K := fun i => b.coord i ∘ₗ pC
  have hW : ∀ v : V, v ∈ LinearMap.range q ↔ ∀ i, φ i v = 0 := fun v => by
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hC.symm, ← b.forall_coord_eq_zero_iff]
    exact Iff.rfl
  have key : ∀ s : Finset (Fin (Module.finrank K C)), ∃ r : L →ₗ[O] L,
      (∀ x, ∀ i ∈ s, φ i (r x : V) = 0) ∧ ∀ x : L, (∀ i ∈ s, φ i (x : V) = 0) → r x = x := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨LinearMap.id, fun x i hi => by simp at hi, fun x _ => rfl⟩
    · intro j s _ ih
      obtain ⟨r, hr1, hr2⟩ := ih
      obtain ⟨r', hr'1, hr'2⟩ := retract_lemma_3 ((((φ j).restrictScalars O) ∘ₗ L.subtype) ∘ₗ r)
      refine ⟨r ∘ₗ r' ∘ₗ r, fun x i hi => ?_, fun x hx => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · simpa using hr'1 (r x)
        · simpa using hr1 (r' (r x)) i hi
      · have hrx : r x = x := hr2 x fun i hi => hx i (Finset.mem_insert_of_mem hi)
        have hr'x : r' x = x := hr'2 x (by simpa [hrx] using hx j (Finset.mem_insert_self j s))
        simp only [LinearMap.comp_apply, hrx, hr'x]
  obtain ⟨r, hr1, hr2⟩ := key Finset.univ
  have hrW : ∀ x, (r x : V) ∈ LinearMap.range q := fun x =>
    (hW _).2 fun i => hr1 x i (Finset.mem_univ i)
  have hrfix : ∀ x : L, (x : V) ∈ LinearMap.range q → r x = x := fun x hx =>
    hr2 x fun i _ => (hW _).1 hx i
  have hex : ∀ x : L, ∃ u, q u = (r x : V) := fun x => LinearMap.mem_range.1 (hrW x)
  let t : L →ₗ[O] U :=
    { toFun := fun x => (hex x).choose
      map_add' := fun x y => by
        apply hq
        rw [(hex (x + y)).choose_spec, map_add q, (hex x).choose_spec, (hex y).choose_spec,
          map_add r, Submodule.coe_add]
      map_smul' := fun o x => by
        apply hq
        rw [(hex (o • x)).choose_spec, RingHom.id_apply, LinearMap.map_smul_of_tower q,
          (hex x).choose_spec, map_smul r, Submodule.coe_smul] }
  have ht : ∀ x, q (t x) = (r x : V) := fun x => (hex x).choose_spec
  obtain ⟨T, hT⟩ := exists_extend L hL t
  refine ⟨T, fun u => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := exists_smul_mem L hL (q u)
    have hmem : ((⟨(a : O) • q u, ha⟩ : L) : V) ∈ LinearMap.range q :=
      LinearMap.mem_range.2 ⟨(a : O) • u, LinearMap.map_smul_of_tower q _ u⟩
    have h1 : t ⟨(a : O) • q u, ha⟩ = (a : O) • u := by
      apply hq
      rw [ht, hrfix _ hmem, LinearMap.map_smul_of_tower]
    have h2 : (a : O) • T (q u) = (a : O) • u := by
      rw [← LinearMap.map_smul_of_tower, ← h1]
      exact hT ⟨(a : O) • q u, ha⟩
    have hne : algebraMap O K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    rw [← algebraMap_smul K (a : O), ← algebraMap_smul K (a : O) u] at h2
    exact smul_right_injective U hne h2
  · rw [show T x = t ⟨x, hx⟩ from hT ⟨x, hx⟩, ht]
    exact (r ⟨x, hx⟩).2

end Retr

theorem mulVec_mem_latS {F E : Type} [Field F] [CommRing E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (S : Subring (E ⊗[F] R)) {O : Type} [CommRing O] [Algebra O E] {n k : ℕ}
    (P : Matrix (Fin k) (Fin n) E) (L : Submodule O (Fin n → E)) (M : Submodule O (Fin k → E))
    (h : ∀ x ∈ L, P *ᵥ x ∈ M) (x : Fin n → E ⊗[F] R) (hx : x ∈ latS (F := F) R S L) :
    (P.map (inclE (F := F) R)) *ᵥ x ∈ latS (F := F) R S M := by
  unfold latS at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    refine Submodule.subset_span ⟨P *ᵥ z, h z hz, ?_⟩
    funext i
    exact RingHom.map_mulVec _ _ _ i
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hy

theorem hat_comap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n k : ℕ) (Q : Matrix (Fin n) (Fin k) E), Function.Injective Q.mulVec → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat (L.comap (Q.mulVecLin.restrictScalars (𝓞 E))) ∧ ∀ x : Fin k → E ⊗[F] Ad F, x ∈ hat F (L.comap (Q.mulVecLin.restrictScalars (𝓞 E))) ↔ (Q.map (inclE (F := F) (Ad F))) *ᵥ x ∈ hat F L := by
  intro F E _ _ _ _ _ n k Q hQ L hL
  obtain ⟨hLf, hLs⟩ := hL
  have := hLf
  set L' := L.comap (Q.mulVecLin.restrictScalars (𝓞 E)) with hL'
  have hmem : ∀ y, y ∈ L' ↔ Q *ᵥ y ∈ L := fun y => Iff.rfl
  refine ⟨(show Module.Finite (𝓞 E) L' ∧ Submodule.span E (L' : Set (Fin k → E)) = ⊤ from ⟨?_, ?_⟩), ?_⟩
  · let f : L' →ₗ[𝓞 E] L :=
      ((Q.mulVecLin.restrictScalars (𝓞 E)).domRestrict L').codRestrict L (fun y => y.2)
    refine Module.Finite.of_injective f (fun y₁ y₂ h => ?_)
    apply Subtype.ext
    apply hQ
    exact congrArg Subtype.val h
  · refine eq_top_iff.2 (fun y _ => ?_)
    obtain ⟨a, ha⟩ := exists_smul_mem (K := E) L hLs (Q *ᵥ y)
    have hay : (a : 𝓞 E) • y ∈ L' := by
      rw [hmem, Matrix.mulVec_smul]
      exact ha
    have hne : algebraMap (𝓞 E) E a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have hy : y = (algebraMap (𝓞 E) E a)⁻¹ • ((a : 𝓞 E) • y) := by
      rw [← algebraMap_smul E (a : 𝓞 E) y, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hay)
  · intro x
    constructor
    · intro hx
      exact mulVec_mem_latS (F := F) (Ad F) (OAd F E) Q L' L (fun y hy => hy) x hx
    · intro hx
      obtain ⟨T, hT1, hT2⟩ := exists_retraction (O := 𝓞 E) (K := E) Q.mulVecLin hQ L hLs
      set R' := LinearMap.toMatrix' T with hR'
      have hRQ : R' * Q = 1 := by
        have h1 : T ∘ₗ Q.mulVecLin = LinearMap.id := LinearMap.ext hT1
        have h2 := congrArg LinearMap.toMatrix' h1
        rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
          LinearMap.toMatrix'_toLin'] at h2
      have hR : ∀ y ∈ L, R' *ᵥ y ∈ L' := fun y hy => by
        rw [hmem, hR', LinearMap.toMatrix'_mulVec]
        exact hT2 y hy
      have hx' := mulVec_mem_latS (F := F) (Ad F) (OAd F E) R' L L' hR _ hx
      rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, hRQ, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec] at hx'

end GlobalTheory.St.G.Inter
