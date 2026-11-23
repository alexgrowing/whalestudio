import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

open NumberField Formalism.MainNotions.S PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel

theorem count_split_gen (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hl : IsNonarchimedeanLocalField F)
    (e : E ≃ₐ[F] F × F) (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F])
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
    (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]) (hπ : IsSplitCoord e H Λ π Ph)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E) (h1 : ∀ a b, G₀ a b ∈ M.L.O)
    (h2 : ∀ a b, G₀ b a = M.L.cj (G₀ a b)) :
    H.dens ϖ Λ G₀ * (Nat.card 𝓀[F] : ℝ) ^
        ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
      (Formalism.L2.SG.DensExact.countSplit 𝓀[F] (Module.finrank E V) (Fintype.card ι)
        (Ph.map (IsLocalRing.residue 𝒪[F]))
        (Matrix.of fun i j => resF F ((e (G₀ ((Fintype.equivFin ι).symm j)
          ((Fintype.equivFin ι).symm i))).1)) : ℝ) := by
  haveI := hl
  obtain ⟨hπa, hπL, hdet, hform⟩ := hπ
  have hlift : ∀ c : 𝓀[F], liftF F c ∈ 𝒪[F] := fun c =>
    ((IsLocalRing.residue_surjective c).choose).2
  obtain ⟨lamV, hlamV⟩ : ∃ f : (Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Module.finrank E V) → 𝓀[F]) → V,
      ∀ p, f p = π.symm (fun k => liftF F (p.1 k), fun l => liftF F (p.2 l)) := ⟨_, fun _ => rfl⟩
  have hlamπ : ∀ p, π (lamV p) = (fun k => liftF F (p.1 k), fun l => liftF F (p.2 l)) := fun p => by
    rw [hlamV, AddEquiv.apply_symm_apply]
  have hlamΛ : ∀ p, lamV p ∈ Λ := fun p =>
    (hπL _).2 ⟨fun k => by rw [hlamπ]; exact hlift _, fun k => by rw [hlamπ]; exact hlift _⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) ×
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) →
      ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ,
      ∀ XY a, Ψ XY a = Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ)
        (lamV (XY.1 ((Fintype.equivFin ι) a), XY.2 ((Fintype.equivFin ι) a))) := ⟨_, fun _ _ => rfl⟩
  have hΨinj : Function.Injective Ψ := by
    intro XY XY' h
    have key : ∀ a, (∀ k, XY.1 ((Fintype.equivFin ι) a) k = XY'.1 ((Fintype.equivFin ι) a) k) ∧
        ∀ k, XY.2 ((Fintype.equivFin ι) a) k = XY'.2 ((Fintype.equivFin ι) a) k := by
      intro a
      have h3 := congrFun h a
      rw [hΨ, hΨ, mk_eq_iff e H Λ π hπa hπL hϖ (hlamΛ _) (hlamΛ _)] at h3
      simpa only [hlamπ, resF_liftF] using h3
    refine Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)
    · simpa using (key ((Fintype.equivFin ι).symm i)).1 k
    · simpa using (key ((Fintype.equivFin ι).symm i)).2 k
  obtain ⟨g, hg⟩ : ∃ g : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} →
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) ×
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]),
      ∀ v, g v = (fun i k => resF F ((π (v.1 ((Fintype.equivFin ι).symm i))).1 k),
        fun j l => resF F ((π (v.1 ((Fintype.equivFin ι).symm j))).2 l)) := ⟨_, fun _ => rfl⟩
  have hfg : (fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) = Ψ ∘ g := by
    funext v a
    have hv : v.1 a ∈ Λ := v.2.1.1 a
    rw [Function.comp_apply, hΨ, mk_eq_iff e H Λ π hπa hπL hϖ hv (hlamΛ _), hlamπ, hg]
    simp [Equiv.symm_apply_apply, resF_liftF]
  have hrange : Set.range g = {XY : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) ×
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) |
      LinearIndependent 𝓀[F] XY.1 ∧ LinearIndependent 𝓀[F] XY.2 ∧
        ∀ i j, ∑ k, ∑ l, XY.1 i k * (Ph.map (IsLocalRing.residue 𝒪[F])) k l * XY.2 j l =
          (Matrix.of fun i j => resF F ((e (G₀ ((Fintype.equivFin ι).symm j)
            ((Fintype.equivFin ι).symm i))).1)) i j} := by
    ext ⟨X, Y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv⟩
      rw [hg] at hv
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hv
      have hvΛ : ∀ a, v.1 a ∈ Λ := v.2.1.1
      have hP := (prim_iff e hO H Λ π hπa hπL hϖ v.1 hvΛ).1 v.2.1
      have hG := (gram_iff e hes hO H Λ π Ph ⟨hπa, hπL, hdet, hform⟩ hϖ G₀ h1 h2 v.1 hvΛ).1 v.2.2
      refine ⟨hP.1.comp _ (Fintype.equivFin ι).symm.injective,
        hP.2.comp _ (Fintype.equivFin ι).symm.injective, fun i j => ?_⟩
      have h3 := hG ((Fintype.equivFin ι).symm j) ((Fintype.equivFin ι).symm i)
      rw [resF_bil _ _ (fun k => ((hπL _).1 (hvΛ _)).1 k) (fun l => ((hπL _).1 (hvΛ _)).2 l)] at h3
      simpa [Matrix.map_apply] using h3
    · rintro ⟨hX, hY, hXY⟩
      have hvΛ : ∀ a, lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)) ∈ Λ :=
        fun a => hlamΛ _
      have e1 : (PI.UnitaryGroupMassFormula.CntFormula.redM F fun a =>
          (π (lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)))).1) =
          X ∘ (Fintype.equivFin ι) := by
        funext a k
        simp [PI.UnitaryGroupMassFormula.CntFormula.redM, hlamπ, resF_liftF]
      have e2 : (PI.UnitaryGroupMassFormula.CntFormula.redM F fun a =>
          (π (lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)))).2) =
          Y ∘ (Fintype.equivFin ι) := by
        funext a k
        simp [PI.UnitaryGroupMassFormula.CntFormula.redM, hlamπ, resF_liftF]
      refine ⟨⟨fun a => lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)), ?_, ?_⟩, ?_⟩
      · rw [prim_iff e hO H Λ π hπa hπL hϖ _ hvΛ, e1, e2]
        exact ⟨hX.comp _ (Fintype.equivFin ι).injective, hY.comp _ (Fintype.equivFin ι).injective⟩
      · rw [gram_iff e hes hO H Λ π Ph ⟨hπa, hπL, hdet, hform⟩ hϖ G₀ h1 h2 _ hvΛ]
        intro a b
        rw [resF_bil _ _ (fun k => ((hπL _).1 (hvΛ _)).1 k) (fun l => ((hπL _).1 (hvΛ _)).2 l)]
        have h4 := hXY ((Fintype.equivFin ι) b) ((Fintype.equivFin ι) a)
        simpa [Matrix.map_apply, hlamπ, resF_liftF] using h4
      · rw [hg]
        refine Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)
        · simp [hlamπ, resF_liftF]
        · simp [hlamπ, resF_liftF]
  have hQ : (Nat.card 𝓀[F] : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  unfold Formalism.MainNotions.S.Loc.HermSp.dens
  rw [div_mul_cancel₀ _ (zpow_ne_zero _ hQ), hfg, Set.range_comp, Nat.card_image_of_injective hΨinj,
    hrange, Formalism.L2.SG.DensExact.countSplit, Nat.card_coe_set_eq]

theorem diag_red (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    (e : E ≃ₐ[F] F × F) (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]) :
    (Matrix.of fun i j => resF F ((e ((Matrix.diagonal fun i => algebraMap F E (a i : F))
        ((Fintype.equivFin ι).symm j) ((Fintype.equivFin ι).symm i))).1) :
      Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F]) =
      Matrix.diagonal fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i)) := by
  have hc : ∀ x : 𝒪[F], resF F (x : F) = IsLocalRing.residue 𝒪[F] x := fun x => by
    unfold resF
    rw [dif_pos x.2]
  have h0 : resF F 0 = 0 := by simpa using hc 0
  ext i j
  rw [Matrix.of_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, AlgEquiv.commutes]
    exact hc _
  · rw [if_neg (fun h' => h ((Fintype.equivFin ι).symm.injective h').symm), if_neg h, map_zero]
    exact h0

theorem residue_eq_zero_iff' (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = 0 ↔ ϖ ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem corank_diag (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (a : ι → 𝒪[F]) :
    Fintype.card ι -
        (Matrix.diagonal fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i))).rank =
      (Finset.univ.filter fun i => ϖ ∣ a i).card := by
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (Fintype.card ι))))
    (fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i)) ≠ 0)
  have h2 : (Finset.univ.filter fun i : Fin (Fintype.card ι) =>
      ¬ IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i)) ≠ 0).card =
      (Finset.univ.filter fun i : ι => ϖ ∣ a i).card := by
    refine Finset.card_equiv (Fintype.equivFin ι).symm fun i => ?_
    simp [residue_eq_zero_iff' F hϖ]
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem dens_diag_split (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hl : IsNonarchimedeanLocalField F)
    (e : E ≃ₐ[F] F × F) (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F])
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
    (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]) (hπ : IsSplitCoord e H Λ π Ph)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]) :
    H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F))) =
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) 1 (Module.finrank E V) (Fintype.card ι)
        (Finset.univ.filter fun i => ϖ ∣ a i).card := by
  haveI := hl
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  have hdiagO : ∀ i j, (Matrix.diagonal fun i => algebraMap F E (a i : F)) i j ∈ M.L.O := by
    intro i j
    rw [hO, Matrix.diagonal_apply]
    split_ifs
    · rw [AlgEquiv.commutes]
      exact ⟨(a i).2, (a i).2⟩
    · rw [map_zero]
      exact ⟨zero_mem _, zero_mem _⟩
  have hcjfix : ∀ x : E, (e x).1 = (e x).2 → M.L.cj x = x := fun x hx =>
    e.injective (by rw [hes]; exact Prod.ext hx.symm hx)
  have hdiagH : ∀ i j, (Matrix.diagonal fun i => algebraMap F E (a i : F)) j i =
      M.L.cj ((Matrix.diagonal fun i => algebraMap F E (a i : F)) i j) := by
    intro i j
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact (hcjfix _ (by rw [AlgEquiv.commutes]; rfl)).symm
    · rw [if_neg (Ne.symm h), if_neg h]
      exact (hcjfix 0 (by rw [map_zero]; rfl)).symm
  have hcnt := count_split_gen F E M hl e hes hO V H Λ π Ph hπ ϖ hϖ ι _ hdiagO hdiagH
  rw [diag_red F E e ι a] at hcnt
  have hunit : IsUnit (Ph.map (IsLocalRing.residue 𝒪[F])).det := by
    have h3 := hπ.2.2.1.map (IsLocalRing.residue 𝒪[F])
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h3
  have hDE := PI.DensSplitW.densExactSplit_of PI.DensSplitW.fiberCard_holds 𝓀[F]
    (Module.finrank E V) (Fintype.card ι) (Ph.map (IsLocalRing.residue 𝒪[F]))
    (Matrix.diagonal fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i))) hunit
  rw [corank_diag F hϖ ι a] at hDE
  rw [Nat.card_eq_fintype_card] at hcnt ⊢
  rw [← hDE, ← hcnt]
  have hQ : (Fintype.card 𝓀[F] : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hk : (Fintype.card 𝓀[F] : ℝ) ^
      ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
      (Fintype.card 𝓀[F] : ℝ) ^ (2 * Module.finrank E V * Fintype.card ι) /
        (Fintype.card 𝓀[F] : ℝ) ^ (Fintype.card ι ^ 2) := by
    rw [zpow_sub₀ hQ]
    norm_cast
  rw [hk, mul_div_assoc, div_self (div_ne_zero (pow_ne_zero _ hQ) (pow_ne_zero _ hQ)), mul_one]

theorem splitCount_holds : SplitCount := by
  intro F E _ _ _ _ _ _ _ M hl hc ⟨e, hes⟩ V _ _ H Λ hΛ ϖ hϖ ι _ _ a hle
  have hO := PI.UnitaryGroupMassFormula.CntFormula.integral_split_count F E M.L hl e
  obtain ⟨π, Ph, hπ⟩ := PI.UnitaryGroupMassFormula.CntFormula.adapted_coords_self_dual F E M hl hc e hes V H Λ hΛ
  exact dens_diag_split F E M hl e hes hO V H Λ π Ph hπ ϖ hϖ ι a

end PI.UnitaryGroupMassFormula.LocDensCorank
