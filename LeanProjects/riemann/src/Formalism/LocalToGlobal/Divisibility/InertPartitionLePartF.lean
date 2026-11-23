import Mathlib
import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Joint

open Formalism.L2.Col

variable {K V I I' : Type} [Field K] [AddCommGroup V] [Module K V] (a : I → Module.End K V)
  (b : I' → Module.End K V)

theorem eigAt_elim_le (x : I ⊕ I' → K) :
    eigAt (Sum.elim a b) x ≤ eigAt a (fun i => x (Sum.inl i)) := by
  intro v hv
  simp only [eigAt, Submodule.mem_iInf] at hv ⊢
  intro i
  exact hv (Sum.inl i)

theorem eigSum_elim_le (C : (I → K) → Prop) :
    eigSum (Sum.elim a b) (fun x => C (fun i => x (Sum.inl i))) ≤ eigSum a C := by
  unfold eigSum
  exact iSup₂_le fun x hx =>
    (eigAt_elim_le a b x).trans (le_iSup₂ (f := fun (y : I → K) (_ : C y) => eigAt a y) _ hx)

theorem le_eigSum_elim [FiniteDimensional K V] (hc : PairComm (Sum.elim a b)) (hs : SplitOver (Sum.elim a b))
    (C : (I → K) → Prop) :
    eigSum a C ≤ eigSum (Sum.elim a b) (fun x => C (fun i => x (Sum.inl i))) := by
  have hc' : PairComm a := fun i j => hc (Sum.inl i) (Sum.inl j)
  have hE := eigSum_elim_le a b C
  have hE' := eigSum_elim_le a b (fun y => ¬ C y)
  have hcompl := isCompl_eigSum (op := Sum.elim a b) hc hs (fun x => C (fun i => x (Sum.inl i)))
  have hdis := disjoint_eigSum (op := a) hc' (C := C) (C' := fun y => ¬ C y) (fun x h h' => h' h)
  intro v hv
  have hv' : v ∈ eigSum (Sum.elim a b) (fun x => C (fun i => x (Sum.inl i))) ⊔
      eigSum (Sum.elim a b) (fun x => ¬ C (fun i => x (Sum.inl i))) := by
    rw [hcompl.sup_eq_top]; trivial
  obtain ⟨e, he, e', he', rfl⟩ := Submodule.mem_sup.mp hv'
  have he'A : e' ∈ eigSum a C := by
    have := Submodule.sub_mem _ hv (hE he)
    simpa using this
  have he'0 : e' = 0 := Submodule.disjoint_def.mp hdis e' he'A (hE' he')
  rw [he'0, add_zero]
  exact he

theorem splitOver_elim (ha : SplitOver a) (hb : SplitOver b) : SplitOver (Sum.elim a b) := by
  intro i
  cases i with
  | inl i => exact ha i
  | inr i => exact hb i

end Joint

namespace InertDat3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}
  {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

theorem splitOver_opAll {s : ℕ} (h : B.Ok s) (hD : D.Ok3) : Col.SplitOver D.opAll :=
  splitOver_elim B.op D.opI h.split hD.split

theorem inertPartition_le_partF (p : Typ3 K Pl0 I0 Ty) : D.inertTypeEigenspaceSum p ≤ B.partF p.1 := by
  show Col.eigSum D.opAll (D.HasRes3 p) ≤ Col.eigSum B.op (B.HasRes p.1)
  have h1 : Col.eigSum D.opAll (D.HasRes3 p) ≤
      Col.eigSum D.opAll (fun x => B.HasRes p.1 (fun i => x (Sum.inl i))) :=
    Col.eigSum_mono (op := D.opAll) (fun x hx => hx.1)
  exact h1.trans (eigSum_elim_le B.op D.opI (B.HasRes p.1))

theorem inert_part_eq_comap (p : Typ3 K Pl0 I0 Ty) : D.part3 ℓ Z p = (D.inertTypeEigenspaceSum p).comap (B.toF ℓ Z) := by
  ext v
  simp only [InertDat3.part3, BlockDat.inV0, BlockDat.coord, BlockDat.toF, Submodule.mem_comap,
    Submodule.map_equiv_eq_comap_symm, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]

theorem mem_resSet_of_mem_resSet3 {X : Finset (G → K)} {p : Typ3 K Pl0 I0 Ty} (h : p ∈ D.resSet3 X) :
    p.1 ∈ B.resSet X := by
  simp only [InertDat3.resSet3, Set.mem_setOf_eq] at h
  simp only [BlockDat.resSet, Set.mem_setOf_eq]
  refine ⟨h.1, fun h0 => h.2.2 (eq_bot_iff.mpr ?_)⟩
  rw [← h0]
  exact Submodule.comap_mono (Submodule.map_mono (D.inertPartition_le_partF p))

private theorem blockPoly_eval_zero' {L : Type} [Field L] (ν : L) (q t : ℕ) :
    (Col.blockPoly ν q t).eval 0 = 1 := by
  unfold Col.blockPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_one fun c _ => by simp

theorem excl3 {p p' : Typ3 K Pl0 I0 Ty} (hne : D.DiffAt p p') (x : D.OpIx → K) (hx : D.HasRes3 p x) :
    ¬ D.HasRes3 p' x := by
  rintro ⟨h1, h2⟩
  obtain ⟨hx1, hx2⟩ := hx
  rcases hne with ⟨P, hP⟩ | ⟨k, hk⟩
  · apply hP
    have hbp : B.blockProd P ≠ 0 := by
      unfold BlockDat.blockProd
      rw [Ne, List.prod_eq_zero_iff, List.mem_map]
      rintro ⟨ν, -, hν⟩
      have h0 := congrArg (Polynomial.eval (0 : K)) hν
      rw [blockPoly_eval_zero', Polynomial.eval_zero] at h0
      exact one_ne_zero h0
    have e1 := hx1 P
    have e2 := h1 P
    rw [e1] at e2
    exact mul_right_cancel₀ hbp e2
  · exact hk ((hx2 k).symm.trans (h2 k))

theorem resSet3_finite (hc : Col.PairComm D.opAll) (X : Finset (G → K)) : (D.resSet3 X).Finite := by
  classical
  obtain ⟨F, hF⟩ := Col.exists_finset_occurs hc
  have hex : ∀ p ∈ D.resSet3 X, ∃ x, D.HasRes3 p x ∧ Col.Occurs D.opAll x := by
    intro p hp
    by_contra hcon
    push Not at hcon
    refine hp.2.2 ?_
    have h0 : D.inertTypeEigenspaceSum p = ⊥ := eq_bot_iff.2 (iSup₂_le fun x hx => by
      by_contra hne
      exact hcon x hx fun h0 => hne h0.le)
    rw [h0, B.good_part_coordinates_bot (Lvl.full X)]
  let f : Typ3 K Pl0 I0 Ty → (D.OpIx → K) := fun p =>
    if h : p ∈ D.resSet3 X then (hex p h).choose else 0
  have hf : ∀ p (h : p ∈ D.resSet3 X), D.HasRes3 p (f p) ∧ Col.Occurs D.opAll (f p) := by
    intro p h
    simp only [f, dif_pos h]
    exact (hex p h).choose_spec
  refine Set.Finite.of_injOn (f := f) (t := (F : Set (D.OpIx → K))) ?_ ?_ F.finite_toSet
  · intro p h
    exact Finset.mem_coe.2 ((hF _).1 (hf p h).2)
  · intro p h p' h' e
    have h1 := hf p h
    have h2 := hf p' h'
    rw [e] at h1
    refine Prod.ext (funext fun P0 => ?_) (funext fun k0 => ?_)
    · by_cases hP : P0 ∈ Set.range B.pl
      · obtain ⟨P, rfl⟩ := hP
        exact mul_right_cancel₀ (B.blockProd_ne_zero P) ((h1.1.1 P).symm.trans (h2.1.1 P))
      · rw [h.1 P0 hP, h'.1 P0 hP]
    · obtain ⟨P0, y⟩ := k0
      by_cases hP : P0 ∈ Set.range D.plI
      · obtain ⟨P, rfl⟩ := hP
        exact (h1.1.2 (P, y)).symm.trans (h2.1.2 (P, y))
      · rw [h.2.1 P0 hP y, h'.2.1 P0 hP y]

theorem mem_ixFin3 (hc : Col.PairComm D.opAll) (X : Finset (G → K)) (p : Typ3 K Pl0 I0 Ty) :
    p ∈ D.ixFin3 X ↔ p ∈ D.resSet3 X := by
  unfold InertDat3.ixFin3
  rw [dif_pos (D.resSet3_finite hc X), Set.Finite.mem_toFinset]

theorem mem_resSet3_of_mem_ixFin3 {X : Finset (G → K)} {p : Typ3 K Pl0 I0 Ty} (h : p ∈ D.ixFin3 X) :
    p ∈ D.resSet3 X := by
  unfold InertDat3.ixFin3 at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.mp h
  · simp at h

theorem mem_ixFin_fst (hc : Col.PairComm B.op) {X : Finset (G → K)} {p : Typ3 K Pl0 I0 Ty} (h : p ∈ D.ixFin3 X) :
    p.1 ∈ B.ixFin X := by
  rw [B.mem_ixFin hc]
  exact D.mem_resSet_of_mem_resSet3 (D.mem_resSet3_of_mem_ixFin3 h)

theorem diffAt_of_mem_ixFin3 {X : Finset (G → K)} {p p' : Typ3 K Pl0 I0 Ty} (h : p ∈ D.ixFin3 X)
    (h' : p' ∈ D.ixFin3 X) (hne : p ≠ p') : D.DiffAt p p' := by
  have h1 := D.mem_resSet3_of_mem_ixFin3 h
  have h2 := D.mem_resSet3_of_mem_ixFin3 h'
  simp only [InertDat3.resSet3, Set.mem_setOf_eq] at h1 h2
  by_contra hd
  apply hne
  simp only [InertDat3.DiffAt, not_or, not_exists, not_not] at hd
  obtain ⟨hd1, hd2⟩ := hd
  refine Prod.ext (funext fun P0 => ?_) (funext fun q => ?_)
  · by_cases hP : P0 ∈ Set.range B.pl
    · obtain ⟨P, rfl⟩ := hP
      exact hd1 P
    · rw [h1.1 P0 hP, h2.1 P0 hP]
  · obtain ⟨P0, y⟩ := q
    by_cases hP : P0 ∈ Set.range D.plI
    · obtain ⟨P, rfl⟩ := hP
      exact hd2 (P, y)
    · rw [h1.2.1 P0 hP y, h2.2.1 P0 hP y]

theorem inert_parts_independent (hc : Col.PairComm D.opAll) {ι : Type} (ps : ι → Typ3 K Pl0 I0 Ty)
    (hsep : ∀ i j, i ≠ j → D.DiffAt (ps i) (ps j)) : iSupIndep fun i => D.part3 ℓ Z (ps i) := by
  haveI : FiniteDimensional K B.S.Forms := Module.Finite.of_basis B.S.basis
  have hA : iSupIndep fun i => D.inertTypeEigenspaceSum (ps i) :=
    iSupIndep_eigSum (op := D.opAll) hc (fun i => D.HasRes3 (ps i))
      (fun i j hij x hx => D.excl3 (hsep i j hij) x hx)
  have e : (fun i => D.part3 ℓ Z (ps i)) = fun i => (D.inertTypeEigenspaceSum (ps i)).comap (B.toF ℓ Z) :=
    funext fun i => D.inert_part_eq_comap ℓ Z (ps i)
  rw [e]
  exact iSupIndep_comap (B.toF ℓ Z) (BlockDat.toF_injective (B := B) (ℓ := ℓ) (Z := Z)) hA

theorem commute_gaOp {s : ℕ} (h : B.Ok s) (hD : D.Ok3) (a : MonoidAlgebra K G) (k : D.OpIx) :
    Commute (D.opAll k) (B.S.gaOp B.r a) := by
  have hT : ∀ g, Commute (D.opAll k) (B.r g) := by
    rcases k with i | k
    · exact fun g => h.opG i g
    · exact fun g => hD.opG k g
  unfold CSD.gaOp
  exact Commute.sum_right _ _ _ fun t _ => (hT t).smul_right _

theorem inert_parts_span_top {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hD : D.Ok3)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (hZ : D.Stable3 Z) {ι : Type} [Fintype ι]
    (ps : ι → Typ3 K Pl0 I0 Ty) (hsep : ∀ i j, i ≠ j → D.DiffAt (ps i) (ps j))
    (hsame : B.Z0 ℓ Z ≤ B.inV0 ℓ (Col.eigSum D.opAll fun x => ∃ i, D.HasRes3 (ps i) x)) :
    (⨆ i, D.part3 ℓ Z (ps i)) = ⊤ := by
  have hs := D.splitOver_opAll h hD
  rw [eq_top_iff]
  intro y _
  set a := goodAt ℓ.X ℓ.P ℓ.ψ with ha
  have hidem : a * a = a := (good_at_spec K v0 hv0 G ℓ.X hX ℓ.P ℓ.ψ).idem
  have hmul := (group_action_matrix_hom K B.S G B.r).2
  have hrange : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.S.gaMat B.r a).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r a)).2
  set φ := B.toF ℓ Z y with hφ
  have hex : ∀ i j, i ≠ j → ∀ x, D.HasRes3 (ps i) x → ¬ D.HasRes3 (ps j) x :=
    fun i j hij x hx => D.excl3 (hsep i j hij) x hx
  have h1 : φ ∈ Col.eigSum D.opAll fun x => ∃ i, D.HasRes3 (ps i) x :=
    (B.mem_goodPart_iff ℓ _ _).1 (hsame (B.zE_mem ℓ Z y))
  have hAφ : B.S.gaOp B.r a φ = φ := by
    apply B.S.basis.equivFun.injective
    rw [← CSD.gaMat_mulVec_equivFun, hφ, BlockDat.toF_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨z, hz⟩ : (B.vE ℓ).mulVecLin ((B.zE ℓ Z).mulVec y) ∈
        LinearMap.range (B.S.gaMat B.r a).mulVecLin := by rw [← hrange]; exact ⟨_, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hz
    rw [← hz, Matrix.mulVec_mulVec, ← hmul, hidem]
  have hcomm : ∀ k, Commute (D.opAll k) (B.S.gaOp B.r a) := D.commute_gaOp h hD a
  have key : ∀ i, ∃ yi, B.toF ℓ Z yi = Col.eigProj hD.comm hs (D.HasRes3 (ps i)) φ := by
    intro i
    set ψ := Col.eigProj hD.comm hs (D.HasRes3 (ps i)) φ with hψ
    have hψA : B.S.gaOp B.r a ψ = ψ := by
      have := (Col.commute_eigProj hD.comm hs (D.HasRes3 (ps i)) hcomm).eq
      have h2 := congrArg (fun f : Module.End K B.S.Forms => f φ) this
      simp only [Module.End.mul_apply] at h2
      rw [hψ, ← h2, hAφ]
    obtain ⟨u, hu⟩ : B.S.basis.equivFun ψ ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hrange]
      exact ⟨B.S.basis.equivFun ψ, by
        rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hψA]⟩
    rw [Matrix.mulVecLin_apply] at hu
    have hu0 : u ∈ B.Z0 ℓ Z := by
      rw [BlockDat.Z0, BlockDat.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
      exact eigProj_mem_of_stable hD.comm hs _ hZ ((B.mem_goodPart_iff ℓ _ _).1 (B.zE_mem ℓ Z y))
    obtain ⟨yi, hyi⟩ := B.exists_zE ℓ Z hu0
    exact ⟨yi, by rw [BlockDat.toF_apply, hyi, hu, LinearEquiv.symm_apply_apply]⟩
  choose yy hyy using key
  have hsum : y = ∑ i, yy i := by
    apply B.toF_injective ℓ Z
    rw [map_sum, Finset.sum_congr rfl fun i _ => hyy i]
    exact (sum_eigProj hD.comm hs _ hex h1).symm
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
  rw [inert_part_eq_comap, Submodule.mem_comap, hyy i]
  exact Col.eigProj_apply_mem hD.comm hs _ φ

theorem sameTypes_self3 {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hD : D.Ok3)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) :
    B.invariantGoodPart ℓ ≤ B.inV0 ℓ (Col.eigSum D.opAll fun x => ∃ p ∈ D.ixFin3 ℓ.X, D.HasRes3 p x) := by
  classical
  have hs := D.splitOver_opAll h hD
  intro u hu
  rw [BlockDat.mem_goodPart_iff]
  set φ := B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) with hφ
  have hφZ : φ ∈ B.ZH := (B.mem_goodPart_iff ℓ _ _).1 hu
  have hφZ3 : φ ∈ Col.eigSum D.opAll fun x => Col.HasBlocks B.n B.q B.t B.bl (fun i => x (Sum.inl i)) :=
    le_eigSum_elim B.op D.opI hD.comm hs _ hφZ
  set a := goodAt ℓ.X ℓ.P ℓ.ψ with ha
  set a0 := goodAt ℓ.X (⊥ : Subgroup G) 1 with ha0
  have hidem : a * a = a := (good_at_spec K v0 hv0 G ℓ.X hX ℓ.P ℓ.ψ).idem
  have ha0a : a0 * a = a := by
    rw [ha0, ha, goodAt, goodAt, level_idempotent_bot K G 1, mul_one, ← mul_assoc, idemOf_mul_self ℓ.X hX]
  have hAφ : B.S.gaOp B.r a φ = φ := B.gaOp_fix ℓ hidem u
  have hA0φ : B.S.gaOp B.r a0 φ = φ := by
    conv_lhs => rw [← hAφ]
    rw [← BlockDat.gaOp_mul, ha0a, hAφ]
  have hcomm : ∀ k, Commute (D.opAll k) (B.S.gaOp B.r a0) := D.commute_gaOp h hD a0
  obtain ⟨F, hF⟩ := Col.exists_finset_occurs hD.comm
  let HB : (D.OpIx → K) → Prop := fun x => Col.HasBlocks B.n B.q B.t B.bl (fun i => x (Sum.inl i))
  let ι := {x // x ∈ F.filter HB}
  let C : ι → (D.OpIx → K) → Prop := fun i x => x = i.1
  have hex : ∀ i j : ι, i ≠ j → ∀ x, C i x → ¬ C j x :=
    fun i j hij x hx hx' => hij (Subtype.ext (hx.symm.trans hx'))
  have h1 : φ ∈ Col.eigSum D.opAll fun x => ∃ i, C i x := by
    have e : Col.eigSum D.opAll HB = Col.eigSum D.opAll fun x => ∃ i, C i x :=
      Col.eigSum_congr fun x hx => ⟨fun hb => ⟨⟨x, Finset.mem_filter.2 ⟨(hF x).1 hx, hb⟩⟩, rfl⟩,
        fun ⟨i, hi⟩ => hi ▸ (Finset.mem_filter.1 i.2).2⟩
    rw [← e]; exact hφZ3
  rw [← sum_eigProj hD.comm hs C hex h1]
  refine Submodule.sum_mem _ fun i _ => ?_
  set ψ' := Col.eigProj hD.comm hs (C i) φ with hψ'
  by_cases h0 : ψ' = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hmem : ψ' ∈ Col.eigAt D.opAll i.1 := by
    have h2 : Col.eigSum D.opAll (C i) ≤ Col.eigAt D.opAll i.1 := iSup₂_le fun x hx => by rw [hx]
    exact h2 (Col.eigProj_apply_mem hD.comm hs _ φ)
  have hψA : B.S.gaOp B.r a0 ψ' = ψ' := by
    have h2 := congrArg (fun f : Module.End K B.S.Forms => f φ)
      (Col.commute_eigProj hD.comm hs (C i) hcomm).eq
    simp only [Module.End.mul_apply] at h2
    rw [hψ', ← h2, hA0φ]
  have hb : HB i.1 := (Finset.mem_filter.1 i.2).2
  choose c hc using hb
  let Sg : Pl0 → K[X] := fun P0 => if hP : ∃ P, B.pl P = P0 then c hP.choose else 1
  have hSg : ∀ P, Sg (B.pl P) = c P := by
    intro P
    have hP : ∃ P', B.pl P' = B.pl P := ⟨P, rfl⟩
    simp only [Sg, dif_pos hP]
    rw [h.pl_inj hP.choose_spec]
  let e : I0 × Ty → K := fun k0 => if hP : ∃ P, D.plI P = k0.1 then i.1 (Sum.inr (hP.choose, k0.2)) else 0
  have he : ∀ (P : D.PlI) (y : Ty), e (D.plI P, y) = i.1 (Sum.inr (P, y)) := by
    intro P y
    have hP : ∃ P', D.plI P' = D.plI P := ⟨P, rfl⟩
    simp only [e, dif_pos hP]
    rw [hD.plI_inj hP.choose_spec]
  have hres : D.HasRes3 (Sg, e) i.1 := by
    refine ⟨fun P => ?_, fun k => (he k.1 k.2).symm⟩
    show _ = Sg (B.pl P) * B.blockProd P
    rw [hSg P, mul_comm]
    exact hc P
  refine Col.eigAt_le_eigSum (C := fun x => ∃ p ∈ D.ixFin3 ℓ.X, D.HasRes3 p x) ⟨(Sg, e), ?_, hres⟩ hmem
  rw [D.mem_ixFin3 hD.comm]
  refine ⟨fun P0 hP0 => ?_, fun P0 hP0 y => ?_, ?_⟩
  · have hP : ¬ ∃ P, B.pl P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
    show Sg P0 = 1
    simp only [Sg, dif_neg hP]
  · have hP : ¬ ∃ P, D.plI P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
    show e (P0, y) = 0
    simp only [e, dif_neg hP]
  · obtain ⟨u0, hu0⟩ := B.exists_vE_of_fix (Lvl.full ℓ.X) hψA
    intro hbot
    have hu0mem : u0 ∈ B.inV0 (Lvl.full ℓ.X) (D.inertTypeEigenspaceSum (Sg, e)) := by
      rw [BlockDat.mem_goodPart_iff, hu0]
      exact Col.eigAt_le_eigSum (C := D.HasRes3 (Sg, e)) hres hmem
    rw [hbot, Submodule.mem_bot] at hu0mem
    apply h0
    rw [← hu0, hu0mem, Matrix.mulVec_zero, map_zero]

end InertDat3

namespace DefFam3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 I0 Ty T J : Type} [Fintype J] (F3 : DefFam3 K G Pl0 I0 Ty T J)

variable {F3} in

theorem toSub2_stable {Zs : DefSub F3.amb3} (hst : Zs.Stable) : (F3.toSub2 Zs).Stable := by
  show (∀ t i, _) ∧ ∀ j t i, _
  refine ⟨fun t i => ?_, fun j t i => ?_⟩
  · rcases i with q | g
    · exact hst.1 t (Sum.inl (Sum.inl q))
    · exact hst.1 t (Sum.inr g)
  · rcases i with q | g
    · exact hst.2 j t (Sum.inl (Sum.inl q))
    · exact hst.2 j t (Sum.inr g)

variable {F3} in
theorem toSub2_inBlock {Zs : DefSub F3.amb3} (hin : Zs.InBlock) : (F3.toSub2 Zs).InBlock := hin

variable {F3} in
theorem stable3_rows {Zs : DefSub F3.amb3} (hst : Zs.Stable) (t : T) : (F3.RI t).Stable3 (Zs.Z t) :=
  fun i => Submodule.map_le_iff_le_comap.mp (hst.1 t (Sum.inl i))

variable {F3} in
theorem stable3_lifts {Zs : DefSub F3.amb3} (hst : Zs.Stable) (j : J) (t : T) : (F3.LI j t).Stable3 (Zs.Zl j t) :=
  fun i => Submodule.map_le_iff_le_comap.mp (hst.2 j t (Sum.inl i))

theorem sameTypes_base3 {s : ℕ} (h : F3.Ok3 s) (P : Subgroup G) (ψ : P →* Kˣ) {Zs : DefSub F3.amb3}
    (hin : Zs.InBlock) :
    (F3.F.R F3.F.μ0).Z0 (F3.F.lvl P ψ) (Zs.Z F3.F.μ0) ≤
      (F3.F.R F3.F.μ0).inV0 (F3.F.lvl P ψ) (Col.eigSum (F3.RI F3.F.μ0).opAll (F3.IsType3 (F3.RI F3.F.μ0) id)) :=
  ((F3.F.R F3.F.μ0).good_part_coordinates_mono _ (DefFam.inBlock_rows (F := F3.F) (Zs := F3.toSub2 Zs) hin F3.F.μ0)).trans
    ((F3.RI F3.F.μ0).sameTypes_self3 (F3.F.lvl P ψ) h.ok2.conj (h.ok2.what₂ F3.F.μ0) (h.what₂ F3.F.μ0) h.ok2.irr)

theorem side_well_formed {s : ℕ} (h : F3.Ok3 s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F3.amb3) (hst : Zs.Stable)
    (hin : Zs.InBlock) (hsep : F3.TypesSep3) : (F3.side3 P ψ Zs).WF where
  cm := isCMSub_cmMax' K
  conj := h.ok2.conj
  HV_rat t := BlockDat.HV_rat (ℓ := F3.F.lvl P ψ) h.ok2.conj (h.ok2.what₂ t) h.ok2.irr
  HV_pos t := BlockDat.HV_pos (ℓ := F3.F.lvl P ψ) h.ok2.conj (h.ok2.what₂ t) h.ok2.irr
  Mt_lat t := BlockDat.Mt_lat (ℓ := F3.F.lvl P ψ) h.ok2.conj (h.ok2.what₂ t) h.ok2.irr
  Pq_surj t := BlockDat.Pq_surj (ℓ := F3.F.lvl P ψ) (Z := Zs.Z t) h.ok2.conj (h.ok2.what₂ t) h.ok2.irr
  XQ_quot t := BlockDat.XQ_quot (ℓ := F3.F.lvl P ψ) (Z := Zs.Z t) h.ok2.conj (h.ok2.what₂ t) h.ok2.irr
  Lam_lat t := BlockDat.Lam_lat (ℓ := F3.F.lvl P ψ) (Z := Zs.Z t) h.ok2.conj (h.ok2.what₂ t) h.ok2.irr
  Qp_indep := (F3.RI F3.F.μ0).inert_parts_independent (F3.F.lvl P ψ) (Zs.Z F3.F.μ0) (h.what₂ F3.F.μ0).comm
    (fun p : F3.base3.Ix => p.1)
    fun p p' hpp => (F3.RI F3.F.μ0).diffAt_of_mem_ixFin3 p.2 p'.2 fun e => hpp (Subtype.ext e)
  Qp_top := (F3.RI F3.F.μ0).inert_parts_span_top (F3.F.lvl P ψ) (Zs.Z F3.F.μ0) h.ok2.conj (h.ok2.what₂ F3.F.μ0)
    (h.what₂ F3.F.μ0) h.ok2.irr (stable3_rows hst F3.F.μ0) (fun p : F3.base3.Ix => p.1)
    (fun p p' hpp => (F3.RI F3.F.μ0).diffAt_of_mem_ixFin3 p.2 p'.2 fun e => hpp (Subtype.ext e))
    ((F3.sameTypes_base3 h P ψ hin).trans ((F3.F.R F3.F.μ0).good_part_coordinates_mono _
      (Col.eigSum_mono fun _ ⟨p, hp, hx⟩ => ⟨⟨p, hp⟩, hx⟩)))
  XT_herm j t := BlockDat.XQ_herm (ℓ := F3.F.lvlA P ψ) (Z := Zs.Zl j t) h.ok2.conj (h.ok2.lifts j t) h.ok2.irr
  Tl_lat j t := BlockDat.Tl_lat (ℓ := F3.F.lvlA P ψ) (Z := Zs.Zl j t) h.ok2.conj (h.ok2.lifts j t) h.ok2.irr
  Zp_indep j := (F3.LI j F3.F.μ0).inert_parts_independent (F3.F.lvlA P ψ) (Zs.Zl j F3.F.μ0) (h.lifts j F3.F.μ0).comm
    (fun p : F3.base3.Ix => F3.tr3 j p.1) fun p p' hpp => hsep p.1 p.2 p'.1 p'.2 (fun e => hpp (Subtype.ext e)) j

theorem side_positive (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F3.amb3) (hrow : F3.F.RowsExist P ψ (F3.toSub2 Zs)) :
    (F3.side3 P ψ Zs).Pos := hrow

theorem side_Types3 {s : ℕ} (h : F3.Ok3 s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F3.amb3) (hst : Zs.Stable)
    (hsep : F3.TypesSep3) (hsame : F3.SameTypes3 P ψ Zs) : (F3.side3 P ψ Zs).Types :=
  fun j => (F3.LI j F3.F.μ0).inert_parts_span_top (F3.F.lvlA P ψ) (Zs.Zl j F3.F.μ0) h.ok2.conj (h.ok2.lifts j F3.F.μ0)
    (h.lifts j F3.F.μ0) h.ok2.irr (stable3_lifts hst j F3.F.μ0) (fun p : F3.base3.Ix => F3.tr3 j p.1)
    (fun p p' hpp => hsep p.1 p.2 p'.1 p'.2 (fun e => hpp (Subtype.ext e)) j)
    ((hsame j).trans ((F3.F.L j F3.F.μ0).good_part_coordinates_mono _
      (Col.eigSum_mono fun _ ⟨p, hp, hx⟩ => ⟨⟨p, hp⟩, hx⟩)))

def toIx2 (hc : Col.PairComm (F3.F.R F3.F.μ0).op) (p : F3.base3.Ix) : F3.F.base.Ix :=
  ⟨p.1.1, (F3.RI F3.F.μ0).mem_ixFin_fst hc p.2⟩

def TrISep : Prop :=
  ∀ j, ∀ p ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X, ∀ p' ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X,
    (∃ k : (F3.RI F3.F.μ0).PlI × Ty, p.2 ((F3.RI F3.F.μ0).plI k.1, k.2) ≠ p'.2 ((F3.RI F3.F.μ0).plI k.1, k.2)) →
      ∃ k : (F3.LI j F3.F.μ0).PlI × Ty,
        F3.trI j p.2 ((F3.LI j F3.F.μ0).plI k.1, k.2) ≠ F3.trI j p'.2 ((F3.LI j F3.F.μ0).plI k.1, k.2)

theorem typesSep3_of (hc : Col.PairComm (F3.F.R F3.F.μ0).op) (hsep2 : F3.F.TypesSep) (hI : F3.TrISep) :
    F3.TypesSep3 := by
  unfold DefFam3.TypesSep3
  intro p hp p' hp' hne j
  rcases (F3.RI F3.F.μ0).diffAt_of_mem_ixFin3 hp hp' hne with ⟨P, hP⟩ | ⟨k, hk⟩
  · have h1 : p.1 ≠ p'.1 := fun e => hP (congrFun e _)
    obtain ⟨P', hP'⟩ := hsep2 p.1 ((F3.RI F3.F.μ0).mem_ixFin_fst hc hp) p'.1
      ((F3.RI F3.F.μ0).mem_ixFin_fst hc hp') h1 j
    exact Or.inl ⟨P', hP'⟩
  · exact Or.inr (hI j p hp p' hp' ⟨k, hk⟩)

end DefFam3

end Formalism.L2.DIV

namespace Formalism.L2.DIV.Test3

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Col Formalism.L2.NCov Formalism.L2.DIV Formalism.L2.DIV.Test

def tD : InertDat3 tB Unit Unit where
  PlI := Unit
  plI := id
  opI := fun _ => (1 : ℚ) • 1

theorem tD_ok : tD.Ok3 where
  comm i j := by
    rcases i with i | i <;> rcases j with j | j
    · exact tB_ok.comm i j
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.one_left _).smul_left _).smul_right _
  split i := top_unique (le_iSup_of_le 1 (maxGen_smul_one (V := tB.S.Forms) (1 : ℚ)).ge)
  opG _ _ := (Commute.one_left _).smul_left _
  plI_inj := Function.injective_id

def exampleRationalFamily : DefFam3 ℚ G3 Unit Unit Unit Unit Unit where
  F := tF
  RI _ := tD
  LI _ _ := tD
  trI _ := id

theorem example_family_ok : exampleRationalFamily.Ok3 1 := ⟨tF_ok, fun _ => tD_ok, fun _ _ => tD_ok⟩

def tZs3 : DefSub exampleRationalFamily.amb3 := ⟨fun _ => tB.goodF tX, fun _ _ => tB.goodF tX⟩

theorem tD_stable (k : tD.PlI × Unit) : tB.goodF tX ≤ (tB.goodF tX).comap (tD.opI k) := by
  intro v hv
  rw [Submodule.mem_comap]
  simpa [tD] using hv

theorem tZs3_stable : tZs3.Stable := by
  have h2 := tZs_stable
  show (∀ t i, _) ∧ ∀ j t i, _
  refine ⟨fun t i => ?_, fun j t i => ?_⟩
  · rcases i with (q | k) | g
    · exact h2.1 t (Sum.inl q)
    · exact Submodule.map_le_iff_le_comap.mpr (tD_stable k)
    · exact h2.1 t (Sum.inr g)
  · rcases i with (q | k) | g
    · exact h2.2 j t (Sum.inl q)
    · exact Submodule.map_le_iff_le_comap.mpr (tD_stable k)
    · exact h2.2 j t (Sum.inr g)

theorem tZs3_inBlock : tZs3.InBlock := tZs_inBlock

def x1 : tD.OpIx → ℚ := Sum.elim x0 fun _ => 1

def p1 : Typ3 ℚ Unit Unit Unit := (fun _ => 1, fun _ => 1)

theorem tD_eigAt : eigAt tD.opAll x1 = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ eigAt tB.op x0 := by
    rw [tB_eigAt]
    trivial
  simp only [eigAt, Submodule.mem_iInf] at hv ⊢
  rintro (i | k)
  · exact hv i
  · show v ∈ ((1 : ℚ) • (1 : Module.End ℚ tB.S.Forms)).maxGenEigenspace 1
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp⟩

theorem tD_hasRes : tD.HasRes3 p1 x1 := ⟨tB_hasRes, fun _ => rfl⟩

theorem tD_inertTypeEigenspaceSum_eq_top : tD.inertTypeEigenspaceSum p1 = ⊤ := by
  rw [eq_top_iff, ← tD_eigAt]
  exact eigAt_le_eigSum (op := tD.opAll) tD_hasRes

theorem tD_mem : p1 ∈ tD.ixFin3 tX := by
  rw [tD.mem_ixFin3 tD_ok.comm]
  have h1 : (fun _ : Unit => (1 : ℚ[X])) ∈ tB.resSet tX := by
    rw [tB_resSet]
    exact Set.mem_singleton _
  simp only [BlockDat.resSet, Set.mem_setOf_eq] at h1
  simp only [InertDat3.resSet3, Set.mem_setOf_eq]
  refine ⟨fun _ _ => rfl, fun P0 hP0 => (hP0 (Set.mem_range_self (f := tD.plI) P0)).elim, ?_⟩
  have h2 := h1.2
  rw [tB_partF] at h2
  rw [tD_inertTypeEigenspaceSum_eq_top]
  exact h2

theorem example_types_separated : exampleRationalFamily.TypesSep3 :=
  exampleRationalFamily.typesSep3_of tB_ok.comm tF_sep (fun _ _ _ _ _ h => h)

theorem example_same_types (P : Subgroup G3) : exampleRationalFamily.SameTypes3 P 1 tZs3 := by
  intro j
  have h : Col.eigSum (exampleRationalFamily.LI j exampleRationalFamily.F.μ0).opAll (exampleRationalFamily.IsType3 (exampleRationalFamily.LI j exampleRationalFamily.F.μ0) (exampleRationalFamily.tr3 j)) = ⊤ := by
    apply eq_top_iff.mpr
    exact (eq_top_iff.mp tD_eigAt).trans (eigAt_le_eigSum (op := tD.opAll)
      (C := exampleRationalFamily.IsType3 tD (exampleRationalFamily.tr3 j)) ⟨p1, tD_mem, tB_hasRes, fun _ => rfl⟩)
  rw [h]
  exact le_top.trans_eq (example_good_coordinates_top _).symm

theorem example_rows_exist (P : Subgroup G3) : exampleRationalFamily.F.RowsExist P 1 (exampleRationalFamily.toSub2 tZs3) := tF_rows P

theorem example_card_types_one : Fintype.card exampleRationalFamily.base3.Ix = 1 := by
  haveI : FiniteDimensional ℚ tB.S.Forms := Module.Finite.of_basis tB.S.basis
  have hbot : tB.inV0 (Lvl.full tX) ⊥ = ⊥ := by
    have h0 : (fun _ : Unit => (0 : ℚ[X])) ≠ fun _ => 1 := fun e => zero_ne_one (congrFun e ())
    have hpart : tB.partF (fun _ : Unit => (0 : ℚ[X])) = ⊥ := by
      by_contra hne
      exact h0 (tB_res_eq hne)
    have hnot : (fun _ : Unit => (0 : ℚ[X])) ∉ tB.resSet tX := by
      rw [tB_resSet]
      exact h0
    simp only [BlockDat.resSet, Set.mem_setOf_eq, not_and, not_not] at hnot
    rw [← hpart]
    exact hnot (fun P0 hP0 => (hP0 (Set.mem_range.mpr ⟨(), rfl⟩)).elim)
  have huniq : ∀ p ∈ tD.ixFin3 tX, p = p1 := by
    intro p hp
    by_contra hne
    have hd := tD.diffAt_of_mem_ixFin3 hp tD_mem hne
    have hdis : Disjoint (tD.inertTypeEigenspaceSum p) (tD.inertTypeEigenspaceSum p1) :=
      disjoint_eigSum (op := tD.opAll) tD_ok.comm (C := tD.HasRes3 p) (C' := tD.HasRes3 p1)
        (fun x h h' => tD.excl3 hd x h h')
    rw [tD_inertTypeEigenspaceSum_eq_top, disjoint_top] at hdis
    have hr := tD.mem_resSet3_of_mem_ixFin3 hp
    simp only [InertDat3.resSet3, Set.mem_setOf_eq] at hr
    apply hr.2.2
    rw [hdis, hbot]
  have hset : tD.ixFin3 tX = {p1} := by
    ext p
    rw [Finset.mem_singleton]
    exact ⟨huniq p, fun e => e ▸ tD_mem⟩
  show Fintype.card ↥(tD.ixFin3 tX) = 1
  rw [Fintype.card_coe, hset, Finset.card_singleton]

theorem example_side_well_formed (P : Subgroup G3) :
    (exampleRationalFamily.side3 P 1 tZs3).WF ∧ (exampleRationalFamily.side3 P 1 tZs3).Pos ∧ (exampleRationalFamily.side3 P 1 tZs3).Proviso ∧ (exampleRationalFamily.side3 P 1 tZs3).Types :=
  ⟨exampleRationalFamily.side_well_formed example_family_ok P 1 tZs3 tZs3_stable tZs3_inBlock example_types_separated,
    exampleRationalFamily.side_positive P 1 tZs3 (example_rows_exist P), (tF_WF P).2.2.1,
    exampleRationalFamily.side_Types3 example_family_ok P 1 tZs3 tZs3_stable example_types_separated (example_same_types P)⟩

end Formalism.L2.DIV.Test3
