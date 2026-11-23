import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace CornerEmbeddingGL

section Ring

variable {R : Type} [CommRing R] {k m : ℕ}

theorem embM_apply (A : Matrix (Fin k) (Fin k) R) (i c : Fin m) :
    embM m A i c = if h : (i : ℕ) < k ∧ (c : ℕ) < k then A ⟨i, h.1⟩ ⟨c, h.2⟩ else (1 : Matrix (Fin m) (Fin m) R) i c :=
  rfl

theorem embM_castLE (h : k ≤ m) (A : Matrix (Fin k) (Fin k) R) (i c : Fin k) :
    embM m A (Fin.castLE h i) (Fin.castLE h c) = A i c := by
  rw [embM_apply, dif_pos ⟨i.2, c.2⟩]; rfl

theorem embM_out (A : Matrix (Fin k) (Fin k) R) (i c : Fin m) (h : ¬ ((i : ℕ) < k ∧ (c : ℕ) < k)) :
    embM m A i c = (1 : Matrix (Fin m) (Fin m) R) i c := by
  rw [embM_apply, dif_neg h]

theorem one_corner (i c : Fin m) (h : (i : ℕ) < k ∧ (c : ℕ) < k) :
    (1 : Matrix (Fin k) (Fin k) R) ⟨i, h.1⟩ ⟨c, h.2⟩ = (1 : Matrix (Fin m) (Fin m) R) i c := by
  simp only [Matrix.one_apply, Fin.ext_iff]

theorem embM_one : embM m (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  ext i c
  rw [embM_apply]
  split_ifs with h
  · exact one_corner i c h
  · rfl

def eqv (h : k ≤ m) : Fin k ⊕ Fin (m - k) ≃ Fin m := finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

theorem eqv_inl (h : k ≤ m) (x : Fin k) : ((eqv h (Sum.inl x) : Fin m) : ℕ) = x := by simp [eqv]

theorem eqv_inr (h : k ≤ m) (x : Fin (m - k)) : ((eqv h (Sum.inr x) : Fin m) : ℕ) = k + x := by simp [eqv]

theorem embM_eq (h : k ≤ m) (A : Matrix (Fin k) (Fin k) R) :
    embM m A = Matrix.reindex (eqv h) (eqv h) (Matrix.fromBlocks A 0 0 1) := by
  ext i c
  obtain ⟨x, rfl⟩ := (eqv h).surjective i
  obtain ⟨y, rfl⟩ := (eqv h).surjective c
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases x with x | x <;> rcases y with y | y
  · rw [embM_apply, dif_pos (by rw [eqv_inl, eqv_inl]; exact ⟨x.2, y.2⟩), Matrix.fromBlocks_apply₁₁]
    congr 1
  · rw [embM_out _ _ _ (by rw [eqv_inl, eqv_inr]; omega), Matrix.fromBlocks_apply₁₂, Matrix.one_apply_ne]
    · rfl
    · intro e; have := congrArg Fin.val e; rw [eqv_inl, eqv_inr] at this; omega
  · rw [embM_out _ _ _ (by rw [eqv_inl, eqv_inr]; omega), Matrix.fromBlocks_apply₂₁, Matrix.one_apply_ne]
    · rfl
    · intro e; have := congrArg Fin.val e; rw [eqv_inl, eqv_inr] at this; omega
  · rw [embM_out _ _ _ (by rw [eqv_inr, eqv_inr]; omega), Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.one_apply]
    simp only [(eqv h).injective.eq_iff, Sum.inr.injEq]

theorem embM_mul (h : k ≤ m) (A B : Matrix (Fin k) (Fin k) R) : embM m (A * B) = embM m A * embM m B := by
  rw [embM_eq h, embM_eq h, embM_eq h]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem embM_det (h : k ≤ m) (A : Matrix (Fin k) (Fin k) R) : (embM m A).det = A.det := by
  rw [embM_eq h, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

def cor (h : k ≤ m) (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin k) (Fin k) R := M.submatrix (Fin.castLE h) (Fin.castLE h)

theorem cor_embM (h : k ≤ m) (A : Matrix (Fin k) (Fin k) R) : cor h (embM m A) = A := by
  ext i c; exact embM_castLE h A i c

theorem embM_cor (h : k ≤ m) (M : Matrix (Fin m) (Fin m) R)
    (hM : ∀ i c : Fin m, (k ≤ (i : ℕ) ∨ k ≤ (c : ℕ)) → M i c = (1 : Matrix (Fin m) (Fin m) R) i c) :
    embM m (cor h M) = M := by
  ext i c
  rw [embM_apply]
  split_ifs with hic
  · rfl
  · exact (hM i c (by omega)).symm

theorem embM_map {S : Type} [CommRing S] (f : R →+* S) (A : Matrix (Fin k) (Fin k) R) :
    (embM m A).map f = embM m (A.map f) := by
  ext i c
  simp only [Matrix.map_apply, embM_apply]
  split_ifs
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

def embGL (h : k ≤ m) : GL (Fin k) R →* GL (Fin m) R where
  toFun g := ⟨embM m g.val, embM m (g⁻¹).val, by rw [← embM_mul h, Units.mul_inv, embM_one],
    by rw [← embM_mul h, Units.inv_mul, embM_one]⟩
  map_one' := Units.ext embM_one
  map_mul' g g' := Units.ext (by simp only [Units.val_mul]; exact embM_mul h _ _)

theorem isEmb_embGL (h : k ≤ m) : IsEmb (embGL (R := R) h) := fun _ => rfl

variable {ι : GL (Fin k) R →* GL (Fin m) R}

theorem emb_inv (hι : IsEmb ι) (g : GL (Fin k) R) : ((ι g)⁻¹).val = embM m (g⁻¹).val := by
  rw [← map_inv, hι]

theorem map_emb {S : Type} [CommRing S] (p : R →+* S) {ιS : GL (Fin k) S →* GL (Fin m) S} (hι : IsEmb ι)
    (hS : IsEmb ιS) (g : GL (Fin k) R) :
    GeneralLinearGroup.map p (ι g) = ιS (GeneralLinearGroup.map p g) := by
  refine Units.ext ?_
  rw [hS]
  change (ι g).val.map p = _
  rw [hι]
  exact embM_map p _

theorem corner_embM {S : Type} [CommRing S] (s : R →ₙ+* S) (A : Matrix (Fin k) (Fin k) R) :
    (1 - matN m s 1 + matN m s (embM m A) : Matrix (Fin m) (Fin m) S) = embM m (1 - matN k s 1 + matN k s A) := by
  ext i c
  rw [embM_apply (m := m) (1 - matN k s 1 + matN k s A)]
  change (1 : Matrix (Fin m) (Fin m) S) i c - s ((1 : Matrix (Fin m) (Fin m) R) i c) + s (embM m A i c) = _
  rw [embM_apply]
  split_ifs with h
  · change _ = (1 : Matrix (Fin k) (Fin k) S) ⟨i, h.1⟩ ⟨c, h.2⟩ - s ((1 : Matrix (Fin k) (Fin k) R) ⟨i, h.1⟩ ⟨c, h.2⟩) + s (A ⟨i, h.1⟩ ⟨c, h.2⟩)
    rw [one_corner i c h, one_corner i c h]
  · exact sub_add_cancel _ _

theorem cornerGL_emb {S : Type} [CommRing S] (s : R →ₙ+* S) {ιS : GL (Fin k) S →* GL (Fin m) S} (hι : IsEmb ι)
    (hS : IsEmb ιS) (g : GL (Fin k) R) : ιS (cornerGL k s g) = cornerGL m s (ι g) := by
  refine Units.ext ?_
  rw [hS]
  change embM m (1 - matN k s 1 + matN k s g.val) = 1 - matN m s 1 + matN m s (ι g).val
  rw [hι, corner_embM]

theorem blk_emb (hι : IsEmb ι) (g : GL (Fin k) R) : GlobalTheory k (ι g) := fun i c hic => by
  rw [hι]; exact embM_out _ _ _ (by omega)

theorem det_emb (h : k ≤ m) (hι : IsEmb ι) (g : GL (Fin k) R) :
    GeneralLinearGroup.det (ι g) = GeneralLinearGroup.det g := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hι, embM_det h]

theorem surj_emb (h : k ≤ m) (hι : IsEmb ι) (x : GL (Fin m) R) (hx : GlobalTheory k x) : ∃ g, x = ι g := by
  have hx' : embM m (cor h x.val) = x.val := embM_cor h _ hx
  have hd : IsUnit (cor h x.val).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
    rwa [← hx', embM_det h] at this
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hd).unit, Units.ext ?_⟩
  rw [hι, IsUnit.unit_spec, hx']

theorem inj_emb (h : k ≤ m) (hι : IsEmb ι) : Function.Injective ι := fun g g' e => by
  refine Units.ext ?_
  have := congrArg (fun x : GL (Fin m) R => cor h x.val) e
  rw [hι, hι, cor_embM, cor_embM] at this
  exact this

end Ring

section Top

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] {k m : ℕ}

theorem continuous_embM : Continuous (embM (k := k) (R := R) m) := by
  refine continuous_pi fun i => continuous_pi fun c => ?_
  simp only [embM_apply]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const

theorem continuous_cor (h : k ≤ m) : Continuous (cor (R := R) h) :=
  continuous_id.matrix_submatrix _ _

variable {ι : GL (Fin k) R →* GL (Fin m) R}

theorem continuous_emb (hι : IsEmb ι) : Continuous ι := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have e : (Units.val ∘ ι) = embM m ∘ (fun g : GL (Fin k) R => g.val) := funext hι
    rw [e]
    exact continuous_embM.comp Units.continuous_val
  · have e : (fun g => ((ι g)⁻¹ : GL (Fin m) R).val) = embM m ∘ (fun g : GL (Fin k) R => (g⁻¹).val) :=
      funext (emb_inv hι)
    rw [e]
    exact continuous_embM.comp Units.continuous_coe_inv

theorem inducing_emb (h : k ≤ m) (hι : IsEmb ι) : IsInducing ι := by
  let P : Matrix (Fin k) (Fin k) R × (Matrix (Fin k) (Fin k) R)ᵐᵒᵖ → Matrix (Fin m) (Fin m) R × (Matrix (Fin m) (Fin m) R)ᵐᵒᵖ :=
    fun p => (embM m p.1, MulOpposite.op (embM m p.2.unop))
  let Q : Matrix (Fin m) (Fin m) R × (Matrix (Fin m) (Fin m) R)ᵐᵒᵖ → Matrix (Fin k) (Fin k) R × (Matrix (Fin k) (Fin k) R)ᵐᵒᵖ :=
    fun p => (cor h p.1, MulOpposite.op (cor h p.2.unop))
  have hQP : Function.LeftInverse Q P := fun p => by
    simp only [P, Q, cor_embM, MulOpposite.unop_op, MulOpposite.op_unop, Prod.mk.eta]
  have hP : Continuous P :=
    (continuous_embM.comp continuous_fst).prodMk
      (MulOpposite.continuous_op.comp (continuous_embM.comp (MulOpposite.continuous_unop.comp continuous_snd)))
  have hQ : Continuous Q :=
    ((continuous_cor h).comp continuous_fst).prodMk
      (MulOpposite.continuous_op.comp ((continuous_cor h).comp (MulOpposite.continuous_unop.comp continuous_snd)))
  have hPe : IsEmbedding P := hQP.isEmbedding hQ hP
  have e : Units.embedProduct (Matrix (Fin m) (Fin m) R) ∘ ι = P ∘ Units.embedProduct (Matrix (Fin k) (Fin k) R) := by
    funext g
    simp only [Function.comp_apply, Units.embedProduct_apply, P, MulOpposite.unop_op]
    rw [hι, emb_inv hι]
  have h2 : IsInducing (Units.embedProduct (Matrix (Fin m) (Fin m) R) ∘ ι) := by
    rw [e]; exact hPe.isInducing.comp Units.isEmbedding_embedProduct.isInducing
  exact (Units.isEmbedding_embedProduct.isInducing.of_comp_iff).mp h2

theorem closedEmb_emb (h : k ≤ m) (hι : IsEmb ι) : IsClosedEmbedding ι := by
  refine ⟨⟨inducing_emb h hι, inj_emb h hι⟩, ?_⟩
  have e : Set.range ι = ⋂ i : Fin m, ⋂ c : Fin m,
      {x : GL (Fin m) R | (k ≤ (i : ℕ) ∨ k ≤ (c : ℕ)) → x.val i c = (1 : Matrix (Fin m) (Fin m) R) i c} := by
    ext x
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, rfl⟩ i c hic
      exact blk_emb hι g i c hic
    · intro hx
      obtain ⟨g, hg⟩ := surj_emb h hι x hx
      exact ⟨g, hg.symm⟩
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun c => ?_
  by_cases hp : (k ≤ (i : ℕ) ∨ k ≤ (c : ℕ))
  · simp only [hp, true_implies]
    exact isClosed_eq ((Units.continuous_val (M := Matrix (Fin m) (Fin m) R)).matrix_elem i c) continuous_const
  · simp only [hp, false_implies, Set.setOf_true]
    exact isClosed_univ

end Top

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {k m : ℕ}
  {ι : GL (Fin k) F →* GL (Fin m) F}

theorem unip_emb (hι : IsEmb ι) (n : GL (Fin k) F) (hn : n ∈ Iwasawa.unipotent F k) :
    ι n ∈ Iwasawa.unipotent F m := by
  rw [Iwasawa.mem_unipotent] at hn ⊢
  obtain ⟨hu, hd⟩ := hn
  refine ⟨fun i c hlt => ?_, fun i => ?_⟩
  · change (ι n).val i c = 0
    rw [hι, embM_apply]
    split_ifs with h
    · exact hu (show (⟨c, h.2⟩ : Fin k) < ⟨i, h.1⟩ from hlt)
    · exact Matrix.one_apply_ne (ne_of_gt hlt)
  · change (ι n).val i i = 1
    rw [hι, embM_apply]
    split_ifs with h
    · exact hd _
    · exact Matrix.one_apply_eq i

theorem int_emb (hι : IsEmb ι) (κ : GL (Fin k) F) (hκ : κ ∈ GLnLocal.integralGL F k) :
    ι κ ∈ GLnLocal.integralGL F m := by
  rw [GLnLocal.mem_integralGL_iff] at hκ ⊢
  obtain ⟨h1, h2⟩ := hκ
  refine ⟨fun i c => ?_, fun i c => ?_⟩
  · change (ι κ).val i c ∈ _
    rw [hι, embM_apply]
    split_ifs
    · exact h1 _ _
    · rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · rw [← map_inv]
    change (ι κ⁻¹).val i c ∈ _
    rw [hι, embM_apply]
    split_ifs
    · exact h2 _ _
    · rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem torus_emb (hι : IsEmb ι) (l : Fin k → ℤ) :
    ι (Iwasawa.torusPow F k l) = Iwasawa.torusPow F m (pad m l) := by
  refine Units.ext ?_
  rw [hι, Iwasawa.coe_torusPow, Iwasawa.coe_torusPow]
  ext i c
  rw [embM_apply]
  split_ifs with h
  · simp only [Matrix.diagonal_apply, Fin.ext_iff, pad, dif_pos h.1]
  · rw [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with hic
    · subst hic
      rw [pad, dif_neg (fun hi => h ⟨hi, hi⟩), zpow_zero]
    · rfl

end Loc

section Ad

variable {E : Type} [Field E] [NumberField E] {k m : ℕ} {ι : GA E k →* GA E m}

theorem uu_emb (h : k ≤ m) (hι : IsEmb ι) (n : GA E k) : UU 0 (ι n) ↔ UU 0 n := by
  unfold UU
  rw [hι n]
  constructor
  · rintro ⟨h1, h2, -⟩
    refine ⟨fun i c hc => ?_, fun i => ?_, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
    · have := h1 (Fin.castLE h i) (Fin.castLE h c) (show ((Fin.castLE h c : Fin m) : ℕ) < (Fin.castLE h i : Fin m) from hc)
      rwa [embM_castLE] at this
    · have := h2 (Fin.castLE h i)
      rwa [embM_castLE] at this
  · rintro ⟨h1, h2, -⟩
    refine ⟨fun i c hc => ?_, fun i => ?_, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
    · rw [embM_apply]
      split_ifs with hh
      · exact h1 _ _ hc
      · exact Matrix.one_apply_ne (ne_of_gt hc)
    · rw [embM_apply]
      split_ifs with hh
      · exact h2 _
      · exact Matrix.one_apply_eq i

theorem psN_emb (h : k ≤ m) (hι : IsEmb ι) (ψ : AddChar (Ad E) ℂ) (n : GA E k) : psN ψ (ι n) = psN ψ n := by
  unfold psN
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  refine Fintype.sum_of_injective (Prod.map (Fin.castLE h) (Fin.castLE h))
    ((Fin.castLE_injective h).prodMap (Fin.castLE_injective h)) _ _ ?_ ?_
  · rintro ⟨i, c⟩ hx
    dsimp only
    split_ifs with hic
    · rw [hι, embM_out]
      · exact Matrix.one_apply_ne (fun e => by rw [e] at hic; omega)
      · rintro ⟨hi, hc⟩
        exact hx ⟨(⟨i, hi⟩, ⟨c, hc⟩), rfl⟩
    · rfl
  · rintro ⟨i, c⟩
    simp only [Prod.map, Fin.coe_castLE]
    rw [hι, embM_castLE]

end Ad

end CornerEmbeddingGL

theorem corner_embedding_of : jumpWindows.G0 → CornerEmbedding := by
  intro _ E _ _ _ m k hkm
  refine ⟨fun R _ => ⟨CornerEmbeddingGL.embGL hkm, CornerEmbeddingGL.isEmb_embGL hkm⟩, fun ι hι => ?_⟩
  have hce := CornerEmbeddingGL.closedEmb_emb hkm hι
  refine ⟨CornerEmbeddingGL.continuous_emb hι, CornerEmbeddingGL.blk_emb hι, CornerEmbeddingGL.surj_emb hkm hι, fun g => ?_, fun U hU => ?_,
    fun C hC => hce.isCompact_preimage hC, fun ιE hE γ => (CornerEmbeddingGL.map_emb _ hE hι γ).symm, fun w ιw hw => ?_,
    fun κ hκ => ?_, CornerEmbeddingGL.uu_emb hkm hι, fun ψ n => CornerEmbeddingGL.psN_emb hkm hι ψ n⟩
  · unfold Dt
    rw [CornerEmbeddingGL.det_emb hkm hι]
  · rw [hce.isInducing.nhds_eq_comap 1, map_one, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    exact ⟨t, ht, fun g hg => hsub hg⟩
  · refine ⟨fun x => ?_, fun g => CornerEmbeddingGL.map_emb _ hι hw g, fun n hn => CornerEmbeddingGL.unip_emb hw n hn,
      fun κ hκ => CornerEmbeddingGL.int_emb hw κ hκ, fun l => CornerEmbeddingGL.torus_emb hw l⟩
    change ι (cornerGL k (sFin E) (cornerGL k (sLoc E w) x)) = cornerGL m (sFin E) (cornerGL m (sLoc E w) (ιw x))
    rw [CornerEmbeddingGL.cornerGL_emb (sFin E) (CornerEmbeddingGL.isEmb_embGL hkm) hι, CornerEmbeddingGL.cornerGL_emb (sLoc E w) hw (CornerEmbeddingGL.isEmb_embGL hkm)]
  · change GeneralLinearGroup.map (pInf E) (ι κ) = 1
    rw [CornerEmbeddingGL.map_emb (pInf E) hι (CornerEmbeddingGL.isEmb_embGL hkm) κ, show GeneralLinearGroup.map (pInf E) κ = 1 from hκ, map_one]

end PositivityTheory.AdelicQuotientData

end
