import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocAdMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnipotentEmbeddingActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSpanColumnInclusionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitProjectionColumnSpanMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitProjectionOrthogonalColumnFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryFixesOrthogonalComplementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalConjugateDisplacementSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleBlockPlacementIndexValueStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix

namespace GlobalTheory.UnipEmb

theorem matHom_emb_mulVec : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) (y : Fin n → AF F ⊗[F] E),
    (matHom (AF F) σ J (emb σ J v x)).1 *ᵥ y =
      y + fun k => GlobalTheory.UnipEmb.locInc F E v ((((matHom (Fv F v) σ J x).1 - 1) *ᵥ fun i => compFin F E v (y i)) k) := GlobalTheory.T.local_unipotent_embedding_action

theorem locInc_splitIncl_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (u : Fin n → Fv F v),
    u ∈ Submodule.span (Fv F v) ((fun i k => τ (X k i)) '' I) →
    (fun k => GlobalTheory.UnipEmb.locInc F E v (splitIncl h τ u k)) ∈ GlobalTheory.StdPar.colSpan F X I := GlobalTheory.T.local_span_column_inclusion

theorem splitProj_compFin_mem_span : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {n r : ℕ} (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r))
    (y : Fin n → AF F ⊗[F] E), y ∈ GlobalTheory.StdPar.colSpan F X I →
    (fun k => splitProj τ (compFin F E v (y k))) ∈ Submodule.span (Fv F v) ((fun i k => τ (X k i)) '' I) := GlobalTheory.T.split_projection_column_span_mem

theorem colPerp_pair_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {r : ℕ} (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r))
    (y : Fin n → AF F ⊗[F] E), y ∈ GlobalTheory.StdPar.colPerp σ J X I → ∀ (i : Fin r), i ∈ I →
    (fun k => splitProj (τ.comp σ) (compFin F E v (y k))) ⬝ᵥ (J.map τ *ᵥ fun k => τ (X k i)) = 0 := GlobalTheory.T.split_projection_orthogonal_column_fixed

theorem splitHom_comp_mulVec_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsHermND σ J → ∀ {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v)
    (x : GLoc σ J v) (W : Submodule (Fv F v) (Fin n → Fv F v)), (∀ z, ((splitHom σ J τ x).1 - 1) *ᵥ z ∈ W) →
    ∀ (u : Fin n → Fv F v), (∀ w ∈ W, u ⬝ᵥ (J.map τ *ᵥ w) = 0) → (splitHom σ J (τ.comp σ) x).1 *ᵥ u = u := GlobalTheory.T.split_unitary_fixes_orthogonal_complement

theorem conj_unip_sub_one_mulVec_mem : ∀ {K : Type} [Field K] {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {N : ℕ} (e : (Σ a, m a) ≃ Fin N) (u : GL (Fin N) K),
    u ∈ GlobalTheory.SmGL.unipRad K e → ∀ (B : GL (Fin N) K) (z : Fin N → K),
    ((B * u * B⁻¹).1 - 1) *ᵥ z ∈ Submodule.span K ((fun k a => B.1 a k) ''
      {k | ∃ j, (e.symm k).1 < (e.symm j).1 ∧ ((B⁻¹).1 *ᵥ z) j ≠ 0}) := GlobalTheory.T.unipotent_radical_conjugate_displacement_span

theorem tripPlace_symm_fst : ∀ {l d N : ℕ} (h : l + d ≤ N) (k : Fin N),
    ((tripPlace h).symm k).1 = if k.val < l then 0 else if k.val < l + d then 1 else 2 := GlobalTheory.T.triple_block_placement_index_value

end GlobalTheory.UnipEmb

namespace GlobalTheory.UnipEmb
theorem tri_lt {l d a b : ℕ}
    (h : (if a < l then (0 : Fin 3) else if a < l + d then 1 else 2) < (if b < l then 0 else if b < l + d then 1 else 2)) :
    a < b ∧ a < l + d ∧ l ≤ b ∧ (b < l + d → a < l) := by
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 <;> first | exact absurd h (by decide) | omega
end GlobalTheory.UnipEmb

namespace GlobalTheory.UnipEmb

theorem emb_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (C : GL (Fin n) E), GlobalTheory.BlockForms.IsAdapted σ J Xf Yf C →
    ∀ (S : Finset (Fin r)) (l d : ℕ), (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) → ∀ (hld : l + d ≤ n),
      ∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld), ∀ x : GLoc σ J v,
        IsCompAt σ J t (Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C) g x → emb σ J v x ∈ GlobalTheory.StdPar.unip σ J Xf S := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hWF v t C hC S l d hgap hk hp hld g hg x hx
  classical
  have hbl' : ∀ k : Fin n, ((tripPlace hld).symm k).1 = if k.val < l then 0 else if k.val < l + d then 1 else 2 :=
    fun k => tripPlace_symm_fst hld k
  obtain ⟨k0, hk0S, hk0⟩ := hk
  have hldr : l + d ≤ r := by have := k0.2; omega
  have hrn : r ≤ n := by have := hC.le; omega
  set B : GL (Fin n) (Fv F v) := Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C with hB
  set tx : Fin r → Fin n → Fv F v := fun i a => t (Xf a i) with htx
  set sx : Fin r → Fin n → Fv F v := fun i a => (t.comp σ) (Xf a i) with hsx

  have hcol : ∀ (k : Fin n) (hk : k.val < r), (fun a => B.1 a k) = tx ⟨k.val, hk⟩ := by
    intro k hk; funext a
    show t (C.1 a k) = _
    rw [hC.colX k ⟨k.val, hk⟩ rfl a]

  let Ann : Submodule (Fv F v) (Fin n → Fv F v) :=
    { carrier := {u | ∀ i : Fin r, i.val < l + d → u ⬝ᵥ (J.map t *ᵥ tx i) = 0}
      add_mem' := fun {a b} ha hb i hi => by rw [add_dotProduct, ha i hi, hb i hi, add_zero]
      zero_mem' := fun i _ => zero_dotProduct _
      smul_mem' := fun c a ha i hi => by rw [smul_dotProduct, ha i hi, smul_zero] }
  have mem_Ann : ∀ u, u ∈ Ann ↔ ∀ i : Fin r, i.val < l + d → u ⬝ᵥ (J.map t *ᵥ tx i) = 0 := fun u => Iff.rfl
  have sx_Ann : ∀ j, sx j ∈ Ann := by
    intro j
    rw [mem_Ann]
    intro i _
    have e := congrFun (congrFun hWF.xx j) i
    have e2 : sx j ⬝ᵥ (J.map t *ᵥ tx i) = t ((Formalism.UG.cT (σ : E →+* E) Xf * J * Xf) j i) := by
      simp only [hsx, htx, dotProduct, mulVec, Matrix.mul_apply, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply,
        map_sum, map_mul, AlgHom.comp_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      rfl
    rw [e2, e]; simp
  have span_Ann : ∀ I : Set (Fin r), Submodule.span (Fv F v) (sx '' I) ≤ Ann :=
    fun I => Submodule.span_le.2 (by rintro _ ⟨j, -, rfl⟩; exact sx_Ann j)

  have F1 : ∀ (g' : GL (Fin n) (Fv F v)), g' ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld) → ∀ z,
      ((B * g' * B⁻¹).1 - 1) *ᵥ z ∈ Submodule.span (Fv F v) (tx '' {i | i.val < l + d}) := by
    intro g' hg' z
    refine Submodule.span_mono ?_ (conj_unip_sub_one_mulVec_mem _ g' hg' B z)
    rintro _ ⟨k, ⟨j, hkj, -⟩, rfl⟩
    rw [hbl' k, hbl' j] at hkj
    have hk2 := (tri_lt hkj).2.1
    exact ⟨⟨k.val, by omega⟩, hk2, (hcol k (by omega)).symm⟩
  have F2 : ∀ (g' : GL (Fin n) (Fv F v)), g' ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld) → ∀ j : Fin r,
      ((B * g' * B⁻¹).1 - 1) *ᵥ tx j ∈ Submodule.span (Fv F v)
        (tx '' {i | i.val < j.val ∧ i.val < l + d ∧ l ≤ j.val ∧ (j.val < l + d → i.val < l)}) := by
    intro g' hg' j
    have hj : tx j = B.1 *ᵥ Pi.single (⟨j.val, by omega⟩ : Fin n) 1 := by
      rw [Matrix.mulVec_single_one, ← hcol ⟨j.val, by omega⟩ j.2]; rfl
    have hBi : (B⁻¹).1 *ᵥ tx j = Pi.single (⟨j.val, by omega⟩ : Fin n) 1 := by
      rw [hj, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    refine Submodule.span_mono ?_ (conj_unip_sub_one_mulVec_mem _ g' hg' B (tx j))
    rintro _ ⟨k, ⟨j', hkj, hne⟩, rfl⟩
    rw [hBi] at hne
    have hj' : j' = ⟨j.val, by omega⟩ := by
      by_contra hc; exact hne (Pi.single_eq_of_ne hc 1)
    rw [hj', hbl' k, hbl' _] at hkj
    have := tri_lt hkj
    simp only [Fin.val_mk] at this
    exact ⟨⟨k.val, by omega⟩, this, (hcol k (by omega)).symm⟩

  have G3 : ∀ (x' : GLoc σ J v) (g' : GL (Fin n) (Fv F v)), g' ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld) →
      (splitHom σ J t x').1 = (B * g' * B⁻¹).1 → ∀ u ∈ Ann, (splitHom σ J (t.comp σ) x').1 *ᵥ u = u := by
    intro x' g' hg' he u hu
    refine splitHom_comp_mulVec_eq hJ t x' _ (fun z => by rw [he]; exact F1 g' hg' z) u ?_
    intro w hw
    let P : Submodule (Fv F v) (Fin n → Fv F v) :=
      { carrier := {w | u ⬝ᵥ (J.map t *ᵥ w) = 0}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at *; rw [Matrix.mulVec_add, dotProduct_add, ha, hb, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c a ha => by
          simp only [Set.mem_setOf_eq] at *; rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero] }
    have : Submodule.span (Fv F v) (tx '' {i | i.val < l + d}) ≤ P :=
      Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact hu i hi)
    exact this hw

  have key : ∀ (x' : GLoc σ J v) (y : Fin n → AF F ⊗[F] E) (I' : Set (Fin r)),
      ((splitHom σ J t x').1 - 1) *ᵥ (fun k => splitProj t (compFin F E v (y k))) ∈ Submodule.span (Fv F v) (tx '' I') →
      ((splitHom σ J (t.comp σ) x').1 - 1) *ᵥ (fun k => splitProj (t.comp σ) (compFin F E v (y k))) = 0 →
      (matHom (AF F) σ J (emb σ J v x')).1 *ᵥ y - y ∈ GlobalTheory.StdPar.colSpan F Xf I' := by
    intro x' y I' h1 h2
    rw [matHom_emb_mulVec, add_sub_cancel_left]
    set w := ((matHom (Fv F v) σ J x').1 - 1) *ᵥ fun i => compFin F E v (y i) with hw0
    have hw : splitIncl hCM t (splitVec t w) + splitIncl hCM (t.comp σ) (splitVec (t.comp σ) w) = w :=
      (splitVecEquiv hCM t).symm_apply_apply w
    have e1 : ∀ τ : E →ₐ[F] Fv F v, splitVec τ w =
        ((splitHom σ J τ x').1 - 1) *ᵥ fun k => splitProj τ (compFin F E v (y k)) := by
      intro τ
      have hm : ((matHom (Fv F v) σ J x').1 - 1).map (splitProj τ) = (splitHom σ J τ x').1 - 1 := by
        ext i j
        rw [splitHom_val]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      rw [hw0, splitVec_mulVec, hm]
      rfl
    rw [e1, e1, h2] at hw
    have h0 : splitIncl hCM (t.comp σ) (0 : Fin n → Fv F v) = 0 := by funext i; simp [splitIncl]
    rw [h0, add_zero] at hw
    rw [← hw]
    exact locInc_splitIncl_mem hCM t Xf I' _ h1

  have Stab : ∀ (x' : GLoc σ J v) (g' : GL (Fin n) (Fv F v)), g' ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld) →
      (splitHom σ J t x').1 = (B * g' * B⁻¹).1 → ∀ (I : Set (Fin r)), (∀ i ∈ I, ∀ i' : Fin r, i'.val < i.val → i' ∈ I) →
      ∀ y, y ∈ GlobalTheory.StdPar.colSpan F Xf I → (matHom (AF F) σ J (emb σ J v x')).1 *ᵥ y - y ∈ GlobalTheory.StdPar.colSpan F Xf I := by
    intro x' g' hg' he I hI y hy
    refine key x' y I ?_ ?_
    · have hq := splitProj_compFin_mem_span t Xf I y hy
      have hle : Submodule.span (Fv F v) (tx '' I) ≤
          (Submodule.span (Fv F v) (tx '' I)).comap (Matrix.mulVecLin ((splitHom σ J t x').1 - 1)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        refine Submodule.mem_comap.2 ?_
        rw [Matrix.mulVecLin_apply, he]
        refine Submodule.span_mono ?_ (F2 g' hg' i)
        rintro _ ⟨i', hi', rfl⟩
        exact ⟨i', hI i hi i' hi'.1, rfl⟩
      exact hle hq
    · have hu : (fun k => splitProj (t.comp σ) (compFin F E v (y k))) ∈ Ann :=
        span_Ann I (splitProj_compFin_mem_span (t.comp σ) Xf I y hy)
      rw [Matrix.sub_mulVec, G3 x' g' hg' he _ hu, Matrix.one_mulVec, sub_self]

  have hx1 : (splitHom σ J t x).1 = (B * g * B⁻¹).1 := hx
  have hxi : (splitHom σ J t x⁻¹).1 = (B * g⁻¹ * B⁻¹).1 := by
    have e : splitHom σ J t x = B * g * B⁻¹ := Units.ext hx
    rw [map_inv, e]; congr 1; group
  have hgi : g⁻¹ ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld) := inv_mem hg
  have back : ∀ y, (matHom (AF F) σ J (emb σ J v x⁻¹)).1 *ᵥ ((matHom (AF F) σ J (emb σ J v x)).1 *ᵥ y) = y := by
    intro y; rw [Matrix.mulVec_mulVec, map_inv, map_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have trivA : ∀ I : Set (Fin r), (∀ i ∈ I, ∀ i' : Fin r, i'.val < i.val → i' ∈ I) → ∀ y,
      y ∈ GlobalTheory.StdPar.colSpan F Xf I ↔ (matHom (AF F) σ J (emb σ J v x)).1 *ᵥ y ∈ GlobalTheory.StdPar.colSpan F Xf I := by
    intro I hI y
    constructor
    · intro hy
      have := add_mem hy (Stab x g hg hx1 I hI y hy)
      rwa [add_sub_cancel] at this
    · intro hy
      have := add_mem hy (Stab x⁻¹ g⁻¹ hgi hxi I hI _ hy)
      rwa [add_sub_cancel, back] at this
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ?_, ?_⟩
  · refine ⟨fun y => trivA _ ?_ y, fun y hy => ?_⟩
    · rintro i ⟨k, hkS, hik, hkj⟩ i' hi'
      exact ⟨k, hkS, Fin.le_iff_val_le_val.2 (by have := Fin.le_iff_val_le_val.1 hik; omega), hkj⟩
    · refine key x y _ ?_ ?_
      · have hq := splitProj_compFin_mem_span t Xf {j} y hy
        have hle : Submodule.span (Fv F v) (tx '' {j}) ≤
            (Submodule.span (Fv F v) (tx '' {i | ∃ k ∈ S, i ≤ k ∧ k < j})).comap
              (Matrix.mulVecLin ((splitHom σ J t x).1 - 1)) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨i, hi, rfl⟩
          rw [Set.mem_singleton_iff] at hi
          subst hi
          refine Submodule.mem_comap.2 ?_
          rw [Matrix.mulVecLin_apply, hx1]
          refine Submodule.span_mono ?_ (F2 g hg i)
          rintro _ ⟨i', ⟨h1, h2, h3, h4⟩, rfl⟩
          refine ⟨i', ?_, rfl⟩
          by_cases hj : i.val < l + d
          · have h5 := h4 hj
            rcases hp with hp | ⟨p, hpS, hp⟩
            · omega
            · exact ⟨p, hpS, Fin.le_iff_val_le_val.2 (by omega), Fin.lt_iff_val_lt_val.2 (by omega)⟩
          · exact ⟨k0, hk0S, Fin.le_iff_val_le_val.2 (by omega), Fin.lt_iff_val_lt_val.2 (by omega)⟩
        exact hle hq
      · have hu : (fun k => splitProj (t.comp σ) (compFin F E v (y k))) ∈ Ann :=
          span_Ann {j} (splitProj_compFin_mem_span (t.comp σ) Xf {j} y hy)
        rw [Matrix.sub_mulVec, G3 x g hg hx1 _ hu, Matrix.one_mulVec, sub_self]
  · refine ⟨fun y => trivA _ ?_ y, fun y hy => ?_⟩
    · rintro i ⟨k, hkS, hik⟩ i' hi'
      exact ⟨k, hkS, Fin.le_iff_val_le_val.2 (by have := Fin.le_iff_val_le_val.1 hik; omega)⟩
    · refine key x y _ ?_ ?_
      · rw [hx1]
        refine Submodule.span_mono ?_ (F1 g hg _)
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨i, ⟨k0, hk0S, Fin.le_iff_val_le_val.2 (by simp only [Set.mem_setOf_eq] at hi; omega)⟩, rfl⟩
      · have hu : (fun k => splitProj (t.comp σ) (compFin F E v (y k))) ∈ Ann := by
          rw [mem_Ann]
          intro i hi
          exact colPerp_pair_eq_zero hCM hJ t Xf _ y hy i ⟨k0, hk0S, Fin.le_iff_val_le_val.2 (by omega)⟩
        rw [Matrix.sub_mulVec, G3 x g hg hx1 _ hu, Matrix.one_mulVec, sub_self]

end GlobalTheory.UnipEmb
