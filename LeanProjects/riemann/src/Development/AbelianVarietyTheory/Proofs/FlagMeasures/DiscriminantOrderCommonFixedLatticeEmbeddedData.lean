import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.FixDisc

open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem lattice_of_idx {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (hle : B ≤ A)
    (h : idxN A B ≠ 0) : Submodule.IsLattice K B := by
  refine ⟨hA.fg.of_le hle, ?_⟩
  rw [eq_top_iff, ← hA.span_eq_top, Submodule.span_le]
  intro x hx
  have h1 : idxN A B • x ∈ B := AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup (K := A.toAddSubgroup) hx
  have h2 : ((idxN A B : ℕ) : K) ≠ 0 := by exact_mod_cast h
  have h3 : x = ((idxN A B : ℕ) : K)⁻¹ • (idxN A B • x) := by
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

omit [NumberField K] in

theorem lattice_map {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    {A : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    Submodule.IsLattice K (A.map (f.restrictScalars (𝓞 K))) := by
  refine ⟨hA.fg.map _, ?_⟩
  have : ((A.map (f.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) = f '' A := rfl
  rw [this, ← Submodule.map_span, hA.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hf]

theorem exists_rat_basis [Module ℚ V] [Module.Finite ℚ V] {A : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ V)) ℚ V, A.toAddSubgroup = AddSubgroup.closure (Set.range b) := by
  have hfin : Module.Finite (𝓞 K) A := Module.Finite.iff_fg.mpr hA.fg
  have hfinZ : Module.Finite ℤ A := Module.Finite.trans (𝓞 K) _
  have hL : Submodule.IsLattice ℚ (A.restrictScalars ℤ) := by
    refine ⟨Module.Finite.iff_fg.mp hfinZ, ?_⟩
    rw [eq_top_iff]
    intro x _
    have h := idxN_ne_zero hA (Submodule.fg_span_singleton (R := 𝓞 K) x)
    set n := idxN (Submodule.span (𝓞 K) {x}) A with hn
    have h1 : n • x ∈ A := AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup
      (K := (Submodule.span (𝓞 K) {x}).toAddSubgroup) (Submodule.mem_span_singleton_self x)
    have h2 : (n : ℚ) ≠ 0 := by exact_mod_cast h
    have h3 : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hr : Module.finrank ℤ (A.restrictScalars ℤ) = Module.finrank ℚ V := by
    unfold Module.finrank
    rw [Submodule.IsLattice.rank' ℚ]
  let b₀ := Module.finBasisOfFinrankEq ℤ (A.restrictScalars ℤ) hr
  refine ⟨b₀.extendOfIsLattice ℚ, ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  have e : Set.range (b₀.extendOfIsLattice ℚ) = (A.restrictScalars ℤ).subtype '' Set.range b₀ := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp
  rw [e, ← Submodule.map_span, b₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  rfl

theorem idx_gmap [FiniteDimensional K V] {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) (F : V ≃ₗ[K] V) (h1 : B ≤ A) (h2 : gmap F B ≤ A) :
    (idxN A (gmap F B) : ℚ) = |Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| * idxN A B := by
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  have : IsScalarTower ℚ K V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite ℚ V := Module.Finite.trans K V
  obtain ⟨a, ha⟩ := exists_rat_basis hA
  obtain ⟨b, hb⟩ := exists_rat_basis hB
  have hb' : (gmap F B).toAddSubgroup = AddSubgroup.closure (Set.range (b.map (F.restrictScalars ℚ))) := by
    have e : (gmap F B).toAddSubgroup = B.toAddSubgroup.map (F : V →ₗ[K] V).toAddMonoidHom := by
      ext x
      simp [gmap]
    rw [e, hb, AddMonoidHom.map_closure, ← Set.range_comp]
    rfl
  have e1 := AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr h1) b a hb ha
  have e2 := AddSubgroup.relIndex_eq_abs_det _ _ ((Submodule.toAddSubgroup_le _ _).mpr h2) _ a hb' ha
  unfold idxN
  rw [e1, e2, ← abs_mul, ← LinearMap.det_restrictScalars,
    ← a.det_comp ((F : V →ₗ[K] V).restrictScalars ℚ) b]
  rfl

theorem idx_gmap' [FiniteDimensional K V] {A B C D : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) (F : V ≃ₗ[K] V) (hBC : B ≤ C)
    (hDC : D ≤ C) (hi : idxN C B = idxN C D) (hDA : D ≤ A) (h2 : gmap F B ≤ A) :
    (idxN A (gmap F B) : ℚ) = |Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| * idxN A D := by
  have hE : Submodule.IsLattice K (A ⊔ C) := Submodule.IsLattice.sup K A C
  have e := idx_gmap hE hB F (hBC.trans le_sup_right) (h2.trans le_sup_left)
  rw [← idxN_mul h2 (le_sup_left : A ≤ A ⊔ C), ← idxN_mul hBC (le_sup_right : C ≤ A ⊔ C), hi,
    idxN_mul hDC (le_sup_right : C ≤ A ⊔ C), ← idxN_mul hDA (le_sup_left : A ≤ A ⊔ C)] at e
  have h0 : ((idxN (A ⊔ C) A : ℕ) : ℚ) ≠ 0 := by exact_mod_cast idxN_ne_zero hA hE.fg
  push_cast at e
  rw [← mul_assoc] at e
  exact mul_right_cancel₀ h0 e

end Index

theorem norm_le {K : Type} [Field K] [NumberField K] (a : K) (c : ℝ) (h : ∀ σ : K →+* ℂ, ‖σ a‖ ≤ c) :
    ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ c ^ Module.finrank ℚ K := by
  have e := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
  rw [norm_prod, eq_ratCast, Complex.norm_ratCast] at e
  rw [Rat.cast_abs, e, ← AlgHom.card ℚ K ℂ, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => h σ.toRingHom)

theorem det_one_sub_le {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U)
    (hσ : ∀ x : K, σ (star x) = star (σ x)) (herm : ∀ x y : U, star (h x y) = h y x)
    (hpos : ∀ w : U, w ≠ 0 → 0 < (σ (h w w)).re) (hη : ∀ x y : U, h (η x) (η y) = h x y) :
    ‖σ (LinearMap.det (LinearMap.id - η))‖ ≤ 2 ^ Module.finrank K U := by
  let u := Module.finBasis K U
  have hb := Formalism.HermitianLatticeCounting.P.det_form_bound_field K U σ h η hσ herm hpos hη _ u u
  set G : Matrix (Fin (Module.finrank K U)) (Fin (Module.finrank K U)) K :=
    Matrix.of fun a b => h (u a) (u b) with hG
  set A := LinearMap.toMatrix u u (LinearMap.id - η) with hA
  have e : (Matrix.of fun a b => bEta h η (u a) (u b)) = G * (A.conjTranspose).transpose := by
    ext a b
    have h1 : u b - η (u b) = ∑ c, A c b • u c := by
      simp only [hA, LinearMap.toMatrix_apply]
      exact (u.sum_repr _).symm
    simp only [bEta, Matrix.of_apply, h1, map_sum, map_smulₛₗ, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, hG, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]; rfl
  have hG0 : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvG⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have h1 : ∀ b, h (∑ a, v a • u a) (u b) = 0 := by
      intro b
      have := congrFun hvG b
      simpa [Matrix.vecMul, dotProduct, hG, map_sum] using this
    have h2 : h (∑ a, v a • u a) = 0 := u.ext fun b => h1 b
    have h3 : (∑ a, v a • u a) = 0 := by
      by_contra hne
      have := hpos _ hne
      rw [h2] at this
      simp at this
    exact hv (funext (Fintype.linearIndependent_iff.1 u.linearIndependent v h3))
  have hp : 0 < ‖σ G.det‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hG0)
  rw [e, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose, map_mul, norm_mul, hσ, norm_star,
    mul_assoc, Real.mul_self_sqrt hp.le, hA, LinearMap.det_toMatrix, mul_comm] at hb
  exact le_of_mul_le_mul_right hb hp

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem aniso {H : HermSpace K V} (hP : PD H.B.flip) (x : V) (hx : H.B x x = 0) : x = 0 := by
  by_contra h0
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := hP σ x h0
  rw [LinearMap.flip_apply, hx] at this
  simp at this

omit [NumberField K] [StarRing K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem mem_fixSp (η : V ≃ₗ[K] V) (x : V) : x ∈ fixSp η ↔ η x = x := by
  simp [fixSp, sub_eq_zero]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem exists_proj_aut {H : HermSpace K V} (hK : IsCMUnram K) (hP : PD H.B.flip) {η : V ≃ₗ[K] V}
    (hη : ∀ x y, H.B (η x) (η y) = H.B x y) {g : ℕ} (hg : 0 < g) :
    ∃ (p : V →ₗ[K] fixSp η) (F : V ≃ₗ[K] V), (∀ t : fixSp η, p t = t) ∧
      (∀ (x : V) (t : fixSp η), H.B t (p x) = H.B t x) ∧ (∀ x, p (x - η x) = 0) ∧
      (∀ x, F x = p x + (g : K)⁻¹ • (x - η x)) ∧
      ((|Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| : ℚ) : ℝ) ≤
        (2 / (g : ℝ)) ^ (2 * (Module.finrank K V - Module.finrank K (fixSp η)) * fDeg K) := by
  set S : Submodule K V := LinearMap.range ((η : V →ₗ[K] V) - LinearMap.id) with hS
  have hrk : Module.finrank K S + Module.finrank K (fixSp η) = Module.finrank K V :=
    LinearMap.finrank_range_add_finrank_ker _
  have horth : ∀ t ∈ fixSp η, ∀ s ∈ S, H.B t s = 0 := by
    rintro t ht _ ⟨y, rfl⟩
    have := hη t y
    rw [(mem_fixSp η t).1 ht] at this
    simp [this]
  have hdis : Disjoint (fixSp η) S := by
    rw [Submodule.disjoint_def]
    exact fun x h1 h2 => aniso hP x (horth x h1 x h2)
  have hc : IsCompl (fixSp η) S :=
    ⟨hdis, codisjoint_iff.2 (Submodule.eq_top_of_disjoint _ _ (by omega) hdis)⟩
  set p := Submodule.projectionOnto (fixSp η) S hc with hp
  have p1 : ∀ t : fixSp η, p t = t := Submodule.projectionOnto_apply_left hc
  have p2 : ∀ x, p x = 0 ↔ x ∈ S := fun x => Submodule.projectionOnto_apply_eq_zero_iff hc
  have p3 : ∀ x, x - p x ∈ S := fun x => by rw [← p2, map_sub, p1, sub_self]
  have p4 : ∀ x, x - η x ∈ S := fun x => ⟨-x, by simp; abel⟩
  have hg0 : (g : K) ≠ 0 := by exact_mod_cast hg.ne'
  set F₀ : V →ₗ[K] V := (fixSp η).subtype ∘ₗ p + (g : K)⁻¹ • (LinearMap.id - (η : V →ₗ[K] V)) with hF₀
  have f1 : ∀ x, F₀ x = p x + (g : K)⁻¹ • (x - η x) := fun x => rfl
  have hinj : Function.Injective F₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have a1 := congrArg p hx
    rw [f1, map_add, map_smul, (p2 _).2 (p4 x), p1, smul_zero, add_zero, map_zero] at a1
    rw [f1, a1, Submodule.coe_zero, zero_add, smul_eq_zero, sub_eq_zero] at hx
    have a2 : x ∈ fixSp η := (mem_fixSp η x).2 (hx.resolve_left (inv_ne_zero hg0)).symm
    have a3 := p1 ⟨x, a2⟩
    rw [a1] at a3
    exact (congrArg Subtype.val a3).symm
  refine ⟨p, LinearEquiv.ofInjectiveEndo F₀ hinj, p1, fun x t => ?_, fun x => (p2 _).2 (p4 x), f1, ?_⟩
  · have := horth t t.2 _ (p3 x)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have hFF : ((LinearEquiv.ofInjectiveEndo F₀ hinj : V ≃ₗ[K] V) : V →ₗ[K] V) = F₀ := rfl
  have hd : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hex : 2 * (Module.finrank K V - Module.finrank K (fixSp η)) * fDeg K =
      Module.finrank K S * Module.finrank ℚ K := by
    rw [hd, ← hrk, Nat.add_sub_cancel]; ring
  rw [hFF, hex, pow_mul]
  refine norm_le _ _ fun σ => ?_
  have hηS : ∀ x ∈ S, (η : V →ₗ[K] V) x ∈ S := fun x hx => by
    have := S.sub_mem hx (p4 x)
    simpa using this
  have hFS : S ≤ S.comap F₀ := fun x hx => by
    rw [Submodule.mem_comap, f1, (p2 x).2 hx, Submodule.coe_zero, zero_add]
    exact S.smul_mem _ (p4 x)
  have q1 : S.mapQ S F₀ hFS = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
    rw [Submodule.Quotient.eq, f1]
    have := S.sub_mem (S.smul_mem (g : K)⁻¹ (p4 x)) (p3 x)
    convert this using 1
    abel
  have q2 : F₀.restrict hFS = (g : K)⁻¹ • (LinearMap.id - (η : V →ₗ[K] V).restrict hηS) := by
    ext x
    change F₀ x = (g : K)⁻¹ • ((x : V) - η x)
    rw [f1, (p2 x).2 x.2, Submodule.coe_zero, zero_add]
  have hb := det_one_sub_le σ (H.B.domRestrict₁₂ S S) ((η : V →ₗ[K] V).restrict hηS) (hK.2.1 σ)
    (fun x y => H.herm x y) (fun w hw => hP σ w (fun h0 => hw (Subtype.ext h0))) (fun x y => hη x y)
  rw [LinearMap.det_eq_det_mul_det S F₀ hFS, q1, q2, LinearMap.det_id, mul_one, LinearMap.det_smul, map_mul,
    norm_mul, map_pow, norm_pow, map_inv₀, norm_inv, map_natCast, Complex.norm_natCast, div_eq_inv_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem flip_nondeg {H : HermSpace K V} (hP : PD H.B.flip) : H.B.flip.Nondegenerate :=
  ⟨fun x hx => aniso hP x (hx x), fun x hx => aniso hP x (hx x)⟩

theorem disc_latIn {H : HermSpace K V} (hP : PD H.B.flip) {U : Submodule K V} (p : V →ₗ[K] U)
    (p1 : ∀ t : U, p t = t) (p2 : ∀ (x : V) (t : U), H.B t (p x) = H.B t x) {A : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) :
    discN (hRes H.B.flip U) (latIn U A) =
      idxN (Formalism.HermitianLatticesTheory.dual H.B.flip A) ((latIn U A).comap (p.restrictScalars (𝓞 K))) := by
  have dl := dualLattice (𝓞 K) K V H.B.flip (flip_isSymm H) (flip_nondeg hP) star_algebraMap_ringOfIntegers_mem_range A hA
  have hs : (hRes H.B.flip U).IsSymm := ⟨fun x y => H.herm y x⟩
  have hn : (hRes H.B.flip U).Nondegenerate :=
    ⟨fun x hx => Subtype.ext (aniso hP x (hx x)), fun x hx => Subtype.ext (aniso hP x (hx x))⟩
  have hL := lattice_map dl.1 p (fun t => ⟨t, p1 t⟩)
  have dl' := dualLattice (𝓞 K) K U (hRes H.B.flip U) hs hn star_algebraMap_ringOfIntegers_mem_range _ hL
  have e : Formalism.HermitianLatticesTheory.dual (hRes H.B.flip U) ((Formalism.HermitianLatticesTheory.dual H.B.flip A).map (p.restrictScalars (𝓞 K))) =
      latIn U A := by
    ext t
    change _ ↔ (t : V) ∈ A
    have e0 : (t : V) ∈ A ↔ (t : V) ∈ Formalism.HermitianLatticesTheory.dual H.B.flip (Formalism.HermitianLatticesTheory.dual H.B.flip A) := by rw [dl.2.1]
    rw [e0, dualBasic_mem_dual, dualBasic_mem_dual H.B.flip _ (t : V)]
    constructor
    · intro h y hy
      have := h (p y) ⟨y, hy, rfl⟩
      change H.B t (p y) ∈ _ at this
      rw [p2] at this
      exact this
    · rintro h _ ⟨y, hy, rfl⟩
      change H.B t (p y) ∈ _
      rw [p2]
      exact h y hy
  rw [discN, ← e, dl'.2.1, e]
  exact (AddSubgroup.relIndex_comap (latIn U A).toAddSubgroup (p.restrictScalars (𝓞 K)).toAddMonoidHom
    (Formalism.HermitianLatticesTheory.dual H.B.flip A).toAddSubgroup).symm

omit [StarRing K] [FiniteDimensional K V] in

theorem exists_same_index {U : Submodule K V} (p : V →ₗ[K] U) (p1 : ∀ t : U, p t = t)
    {D : Submodule (𝓞 K) V} (hD : Submodule.IsLattice K D) :
    ∃ B C : Submodule (𝓞 K) V, Submodule.IsLattice K B ∧ Submodule.IsLattice K C ∧ B ≤ C ∧ D ≤ C ∧
      idxN C B = idxN C D ∧ ∀ b ∈ B, ∃ m : U, (m : V) ∈ D ∧ ∃ y ∈ D, b = m + (y - p y) := by
  set P : V →ₗ[𝓞 K] V := (U.subtype ∘ₗ p).restrictScalars (𝓞 K) with hP
  have hPx : ∀ x, P x = p x := fun _ => rfl
  set B : Submodule (𝓞 K) V := (D ⊓ U.restrictScalars (𝓞 K)) ⊔ D.map (LinearMap.id - P) with hB
  have hBm : ∀ b ∈ B, ∃ m : U, (m : V) ∈ D ∧ ∃ y ∈ D, b = m + (y - p y) := by
    intro b hb
    obtain ⟨m, ⟨hm1, hm2⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hb
    exact ⟨⟨m, hm2⟩, hm1, y, hy, rfl⟩
  have hC : Submodule.IsLattice K (D.map P ⊔ D) :=
    Submodule.IsLattice.of_le_of_isLattice_of_fg K le_sup_right ((hD.fg.map P).sup hD.fg)
  have e1 : D.map P ⊔ B = D.map P ⊔ D := by
    refine le_antisymm (sup_le le_sup_left (sup_le (inf_le_left.trans le_sup_right) ?_))
      (sup_le le_sup_left fun y hy => ?_)
    · rintro _ ⟨y, hy, rfl⟩
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hy) (Submodule.mem_sup_left ⟨y, hy, rfl⟩)
    · have : y = P y + (LinearMap.id - P : V →ₗ[𝓞 K] V) y := by simp
      rw [this]
      exact Submodule.add_mem_sup ⟨y, hy, rfl⟩ (Submodule.mem_sup_right ⟨y, hy, rfl⟩)
  have e2 : B ⊓ D.map P = D ⊓ D.map P := by
    refine le_antisymm ?_ ?_
    · rintro b ⟨hb, z, hz, rfl⟩
      refine ⟨?_, z, hz, rfl⟩
      obtain ⟨m, hm, y, hy, e⟩ := hBm _ hb
      have := congrArg p e
      rw [hPx, map_add, map_sub, p1, p1, p1, sub_self, add_zero] at this
      rw [SetLike.mem_coe, hPx, this]
      exact hm
    · rintro b ⟨hb, z, hz, rfl⟩
      exact ⟨Submodule.mem_sup_left ⟨hb, (p z).2⟩, z, hz, rfl⟩
  have k : ∀ X : Submodule (𝓞 K) V, idxN (D.map P ⊔ X) X = idxN (D.map P) (X ⊓ D.map P) := by
    intro X
    unfold idxN
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right]
    exact (AddSubgroup.inf_relIndex_right _ _).symm
  have e3 : idxN (D.map P ⊔ D) B = idxN (D.map P ⊔ D) D := by
    rw [k D, ← e1, k B, e2]
  have hBC : B ≤ D.map P ⊔ D := e1 ▸ le_sup_right
  exact ⟨B, _, lattice_of_idx hC hBC (e3 ▸ idxN_ne_zero hD hC.fg), hC, hBC, le_sup_right, e3, hBm⟩

theorem core {H : HermSpace K V} (hK : IsCMUnram K) (hP : PD H.B.flip) {η : V ≃ₗ[K] V}
    (hη : ∀ x y, H.B (η x) (η y) = H.B x y) {g : ℕ} (hg : 0 < g) {A D : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) (hD : Submodule.IsLattice K D) (hle : D ≤ Formalism.HermitianLatticesTheory.dual H.B.flip A)
    (hfix : ∀ t ∈ fixSp η, t ∈ D → t ∈ A)
    (hpair : ∀ y ∈ D, (g : K)⁻¹ • (y - η y) ∈ Formalism.HermitianLatticesTheory.dual H.B.flip A) :
    (discN (hRes H.B.flip (fixSp η)) (latIn (fixSp η) A) : ℝ) ≤
      (2 / (g : ℝ)) ^ (2 * (Module.finrank K V - Module.finrank K (fixSp η)) * fDeg K) *
        idxN (Formalism.HermitianLatticesTheory.dual H.B.flip A) D := by
  obtain ⟨p, F, p1, p2, p3, hF, hN⟩ := exists_proj_aut hK hP hη hg
  obtain ⟨B, C, hB, hC, hBC, hDC, hi, hBm⟩ := exists_same_index p p1 hD
  have dl := (dualLattice (𝓞 K) K V H.B.flip (flip_isSymm H) (flip_nondeg hP) star_algebraMap_ringOfIntegers_mem_range A hA).1
  have key : ∀ b ∈ gmap F B, ∃ m : fixSp η, (m : V) ∈ D ∧ ∃ y ∈ D, b = m + (g : K)⁻¹ • (y - η y) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨m, hm, y, hy, rfl⟩ := hBm b hb
    refine ⟨m, hm, y, hy, ?_⟩
    change F _ = _
    rw [hF, map_add, map_sub, p1, p1, sub_self, add_zero, map_add, map_sub, (mem_fixSp η m).1 m.2,
      (mem_fixSp η (p y)).1 (p y).2]
    congr 2
    abel
  have h1 : gmap F B ≤ Formalism.HermitianLatticesTheory.dual H.B.flip A := by
    intro b hb
    obtain ⟨m, hm, y, hy, rfl⟩ := key b hb
    exact Submodule.add_mem _ (hle hm) (hpair y hy)
  have h2 : gmap F B ≤ (latIn (fixSp η) A).comap (p.restrictScalars (𝓞 K)) := by
    intro b hb
    obtain ⟨m, hm, y, hy, rfl⟩ := key b hb
    change ((p _ : fixSp η) : V) ∈ A
    rw [map_add, map_smul, p3, smul_zero, add_zero, p1]
    exact hfix m m.2 hm
  have hFB : Submodule.IsLattice K (gmap F B) := lattice_map hB (F : V →ₗ[K] V) F.surjective
  have h3 : idxN (Formalism.HermitianLatticesTheory.dual H.B.flip A) ((latIn (fixSp η) A).comap (p.restrictScalars (𝓞 K))) ≤
      idxN (Formalism.HermitianLatticesTheory.dual H.B.flip A) (gmap F B) :=
    AddSubgroup.relIndex_le_of_le_left ((Submodule.toAddSubgroup_le _ _).mpr h2) (idxN_ne_zero hFB dl.fg)
  have h4 := congrArg (fun q : ℚ => (q : ℝ)) (idx_gmap' dl hB hC F hBC hDC hi hle h1)
  simp only [Rat.cast_mul, Rat.cast_natCast] at h4
  rw [disc_latIn hP p p1 p2 hA]
  refine (Nat.cast_le.2 h3).trans ?_
  rw [h4]
  exact mul_le_mul_of_nonneg_right hN (by positivity)

end GlobalTheory.DegCnt.FixDisc

namespace GlobalTheory.DegCnt.FixDisc

open GlobalTheory.Mass.DiscOrder

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ∀ p ∈ Trip H g L₀ j x x', (GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (fixSp p.2.2)) (GlobalTheory.Mass.latIn (fixSp p.2.2) (fixLat p.1.2)) : ℝ) ≤ (2 / (g : ℝ)) ^ (2 * ((Module.finrank K V) - Module.finrank K (fixSp p.2.2)) * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x' := by
  intro K V _ _ _ _ _ _ _ _ H hK hP L₀ g j D₀ hL hD₀ _ hg x x' hx hx' p hp
  obtain ⟨⟨-, -, m1, i1, -⟩, ⟨-, -, m2, i2, -⟩, hη, -, hΓ⟩ := hp
  have hη' := (mem_isomGrp H _).1 hη
  have l1 : fixLat p.1.2 ≤ L₀ := fun y hy => (m1.1 hy).2
  have l2 : fixLat p.2.1.2 ≤ L₀ := fun y hy => (m2.1 hy).2
  change GlobalTheory.Mass.idxN L₀ (fixLat p.1.2) = x at i1
  change GlobalTheory.Mass.idxN L₀ (fixLat p.2.1.2) = x' at i2
  have hA := lattice_of_idx hL.1 l1 (by omega)
  have hD := lattice_of_idx hL.1 l2 (by omega)
  obtain ⟨an, -, -, hint, -⟩ :=
    Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V H.B.flip (flip_isSymm H) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  have l3 := (hint L₀).1 hL.2
  have l4 := an _ _ l1
  have hg0 : (g : K) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hc := core hK hP hη' (by omega : 0 < g) hA hD (l2.trans (l3.trans l4))
    (fun t ht hD => by
      have h1 : (p.2.2 t, t) ∈ p.1.2 := (hΓ t t).1 hD
      rw [(mem_fixSp _ t).1 ht] at h1
      exact h1)
    (fun y hy => by
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro z hz
      have h1 : (p.2.2 y, y) ∈ p.1.2 := (hΓ y y).1 hy
      have h2 : (z, z) ∈ p.1.2 := hz
      obtain ⟨t, ht⟩ := m1.2.2.2.2.2.2 _ h1 _ h2
      refine Submodule.mem_one.2 ⟨-t, ?_⟩
      rw [LinearMap.flip_apply, map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, ← neg_sub, ht,
        map_mul, map_natCast, map_neg, smul_eq_mul]
      field_simp)
  rw [← idxN_mul (l2.trans l3) l4, ← idxN_mul l2 l3, i2,
    idxN_dual H.B.flip (flip_isSymm H) (flip_nondeg hP) hA x L₀ hL.1 l1 i1] at hc
  change GlobalTheory.Mass.idxN _ _ = D₀ at hD₀
  rw [hD₀] at hc
  refine hc.trans (le_of_eq ?_)
  push_cast
  ring

end GlobalTheory.DegCnt.FixDisc
