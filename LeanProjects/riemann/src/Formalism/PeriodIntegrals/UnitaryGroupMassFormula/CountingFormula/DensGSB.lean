import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramIff

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

theorem count_bijection : CountBij := by
  intro F E _ _ _ _ _ _ _ M hl _ e hes hO V _ _ H Λ π Ph hπ ϖ hϖ ι _ _ G₀ h1 h2 h3
  haveI := hl
  have hπa := hπ.1
  have hπL := hπ.2.1
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let lift : (Fin (Module.finrank E V) → 𝓀[F]) → (Fin (Module.finrank E V) → 𝓀[F]) → V := fun X1 Y1 =>
    π.symm ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k))
  have hlift : ∀ X1 Y1, π (lift X1 Y1) = ((fun k => liftF F (X1 k)), fun k => liftF F (Y1 k)) :=
    fun _ _ => AddEquiv.apply_symm_apply _ _
  have hliftL : ∀ X1 Y1, lift X1 Y1 ∈ Λ := fun X1 Y1 =>
    (hπL _).2 (by rw [hlift]; exact ⟨fun k => liftF_mem F _, fun k => liftF_mem F _⟩)
  have hred1 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).1 k) = X1 k := by
    intro X1 Y1 k; rw [hlift]; exact resF_liftF F _
  have hred2 : ∀ X1 Y1 k, resF F ((π (lift X1 Y1)).2 k) = Y1 k := by
    intro X1 Y1 k; rw [hlift]; exact resF_liftF F _
  let Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F] := Matrix.of fun i j => resF F ((e (G₀ (σ.symm j) (σ.symm i))).1)
  let Ph' := Ph.map (IsLocalRing.residue 𝒪[F])
  let g : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) →
      (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ) := fun XY a =>
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (lift (XY.1 (σ a)) (XY.2 (σ a)))
  let S : Set ((Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F])) :=
    {XY | LinearIndependent 𝓀[F] XY.1 ∧ LinearIndependent 𝓀[F] XY.2 ∧
      ∀ i j, ∑ k, ∑ l, XY.1 i k * Ph' k l * XY.2 j l = Gm i j}
  have hL := fun (v : ι → V) (hv : ∀ a, v a ∈ Λ) a => (hπL (v a)).1 (hv a)
  have hR : Set.range (fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) = g '' S := by
    ext c
    constructor
    · rintro ⟨⟨v, hP, hG⟩, rfl⟩
      have hv : ∀ a, v a ∈ Λ := hP.1
      have hpr := (prim_iff e hO H Λ π hπa hπL hϖ v hv).1 hP
      have hgr := (gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).1 hG
      refine ⟨((fun i k => resF F ((π (v (σ.symm i))).1 k)), fun i k => resF F ((π (v (σ.symm i))).2 k)),
        ⟨hpr.1.comp σ.symm σ.symm.injective, hpr.2.comp σ.symm σ.symm.injective, ?_⟩, ?_⟩
      · intro i j
        have := hgr (σ.symm j) (σ.symm i)
        rw [resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph] at this
        exact this
      · funext a
        show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        rw [mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hv a)]
        refine ⟨fun k => ?_, fun k => ?_⟩
        · rw [hred1]; simp
        · rw [hred2]; simp
    · rintro ⟨XY, ⟨hX, hY, hE⟩, rfl⟩
      let v : ι → V := fun a => lift (XY.1 (σ a)) (XY.2 (σ a))
      have hv : ∀ a, v a ∈ Λ := fun a => hliftL _ _
      have hr1 : (redM F fun a => (π (v a)).1) = XY.1 ∘ σ := by
        funext a k; exact hred1 _ _ k
      have hr2 : (redM F fun a => (π (v a)).2) = XY.2 ∘ σ := by
        funext a k; exact hred2 _ _ k
      have hP : H.Prim Λ v := (prim_iff e hO H Λ π hπa hπL hϖ v hv).2
        ⟨by rw [hr1]; exact hX.comp σ σ.injective, by rw [hr2]; exact hY.comp σ σ.injective⟩
      have hG := (gram_iff e hes hO H Λ π Ph hπ hϖ G₀ h1 h2 v hv).2 (by
        intro a b
        rw [resF_bil _ _ (hL v hv _).1 (hL v hv _).2 Ph]
        have := hE (σ b) (σ a)
        simp only [Gm, Matrix.of_apply, Equiv.symm_apply_apply] at this
        rw [← this]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [hred1, hred2]
        rfl)
      exact ⟨⟨v, hP, hG⟩, rfl⟩
  have hinj : Set.InjOn g S := by
    intro XY _ XY' _ heq
    have hc : ∀ a, (∀ k, XY.1 (σ a) k = XY'.1 (σ a) k) ∧ ∀ k, XY.2 (σ a) k = XY'.2 (σ a) k := by
      intro a
      have := (mk_eq_iff e H Λ π hπa hπL hϖ (hliftL _ _) (hliftL _ _)).1 (congrFun heq a)
      simp only [hred1, hred2] at this
      exact this
    refine Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)
    · have := (hc (σ.symm i)).1 k
      simpa using this
    · have := (hc (σ.symm i)).2 k
      simpa using this

  have hrank : Gm.rank = Fintype.card ι := by
    let A : Matrix ι ι 𝒪[F] := Matrix.of fun a b => ⟨(e (G₀ a b)).1, ((hO _).1 (h1 a b)).1⟩
    let φ : E →+* F := (RingHom.fst F F).comp (e : E →+* F × F)
    have hA : ((A.det : 𝒪[F]) : F) = φ G₀.det := by
      rw [← 𝒪[F].coe_subtype, RingHom.map_det, RingHom.map_det]
      congr 1
    obtain ⟨y, hy, hdy⟩ := h3
    have hyO := ((hO y).1 hy).1
    have hAu : IsUnit A.det := by
      refine isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩
      rw [Subring.coe_mul, hA]
      have := congrArg φ hdy
      rw [map_mul, map_one] at this
      simpa [φ] using this
    have hGm : Gm = Matrix.reindex σ σ (A.map (IsLocalRing.residue 𝒪[F])).transpose := by
      ext i j
      simp only [Gm, A, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Matrix.map_apply]
      rw [← resF_coe]
    rw [Matrix.rank_of_isUnit Gm ?_, Fintype.card_fin]
    rw [Matrix.isUnit_iff_isUnit_det, hGm, Matrix.det_reindex_self, Matrix.det_transpose]
    have : (A.map (IsLocalRing.residue 𝒪[F])) = (IsLocalRing.residue 𝒪[F]).mapMatrix A := rfl
    rw [this, ← RingHom.map_det]
    exact hAu.map _
  refine ⟨Gm, hrank, ?_⟩
  have hq : (Nat.card 𝓀[F] : ℝ) ≠ 0 := by
    have : 0 < Nat.card 𝓀[F] := Nat.card_pos
    exact_mod_cast this.ne'
  unfold Loc.HermSp.dens
  rw [div_mul_cancel₀ _ (zpow_ne_zero _ hq), hR, Nat.card_coe_set_eq, hinj.ncard_image]
  rfl

end PI.UnitaryGroupMassFormula.CntFormula
