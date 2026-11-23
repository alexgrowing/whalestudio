import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingObjectsExist
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.DeltaRing
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.DensityPointOfCornerSimple
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Density
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CornerSimple
import Formalism.CharacterColumnKernels.IdempotentNormalForms.MemCcIdealIffForall
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem x0 : DensityPointExists := density_point_of_corner_simple density cornerSimple

theorem bridge : StatBridge := by
  intro O _ _ X T d _ _ G _ r π eB heB hid m jj a h c
  have hx : ∀ x, eB x * eB x = eB x := fun x => congrFun hid x
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (fun x => c • ∑ i, jj i x • (eB x * a i x * eB x)) =
        c • ∑ i, (fun x => jj i x • (eB * a i * eB) x) := by
      funext x; simp [Finset.sum_apply]
    rw [h1]
    refine (spanSub T r).smul_mem ((spanSub T r).sum_mem fun i _ => ?_) c
    have h2 : (fun x => jj i x • (eB * a i * eB) x) = term r (jj i) 1 * (eB * a i * eB) := by
      funext x; simp [term]
    rw [h2]
    exact mul_mem_tSpan T r (term_mem T r (h i).1 1)
      (mul_mem_tSpan T r (mul_mem_tSpan T r heB (h i).2.2) heB)
  · funext x
    simp only [Pi.mul_apply, Matrix.mul_smul, Finset.mul_sum, ← mul_assoc, hx]
  · funext x
    simp only [Pi.mul_apply, Matrix.smul_mul, Finset.sum_mul, mul_assoc, hx]
  · simp [(h _).2.1]

theorem bcSpan : StatBcSpan := by
  intro O O' _ _ _ X T
  let φ : (X → O) →+* (X → O') := (algebraMap O O').compLeft X
  have h1 : ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O))) =
      ((T.toSubsemiring.toSubmonoid.map φ.toMonoidHom : Submonoid (X → O')) : Set (X → O')) := rfl
  have h2 := Algebra.adjoin_eq_span O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O)))
  have h3 : (bcT O' T : Set (X → O')) = (Subalgebra.toSubmodule (bcT O' T) : Set (X → O')) := rfl
  rw [h3]
  unfold bcT
  rw [h2, h1, Submonoid.closure_eq]

theorem mem_bcT {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X : Type}
    (T : Subalgebra O (X → O)) {f : X → O} (hf : f ∈ T) :
    (fun x => algebraMap O O' (f x)) ∈ bcT O' T :=
  Algebra.subset_adjoin ⟨f, hf, rfl⟩

theorem bcLocal : StatBcLocal := by
  intro O O' _ _ _ _ _ _ X _ _ T hT
  have hres : ∀ f ∈ bcT O' T, ∀ x y : X,
      IsLocalRing.residue O' (f x) = IsLocalRing.residue O' (f y) := by
    intro f hf x y
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨f0, hf0, rfl⟩ := hf
      have h := resConst O X T hT f0 hf0 x y
      have h2 := congrArg (IsLocalRing.ResidueField.map (algebraMap O O')) h
      exact h2
    | algebraMap c => rfl
    | add f g _ _ hf hg => simp only [Pi.add_apply, map_add, hf, hg]
    | mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]
  have : Algebra.IsIntegral O' (X → O') := inferInstance
  have : Algebra.IsIntegral (bcT O' T) (X → O') := Algebra.IsIntegral.tower_top O'
  have : FaithfulSMul (bcT O' T) (X → O') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  have hloc : IsLocalHom (algebraMap (bcT O' T) (X → O')) := inferInstance
  obtain ⟨π⟩ := ‹Nonempty X›
  have hunit : ∀ a : bcT O' T, IsUnit (a.1 π) → IsUnit a := by
    intro a ha
    refine hloc.map_nonunit a ?_
    show IsUnit a.1
    rw [Pi.isUnit_iff]
    intro x
    have h1 : IsLocalRing.residue O' (a.1 x) ≠ 0 := by
      rw [hres a.1 a.2 x π]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr ha
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1
  have : Nontrivial (bcT O' T) := inferInstance
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (a.1 π) with h | h
  · exact Or.inl (hunit a h)
  · exact Or.inr (hunit (1 - a) h)

theorem absIrr_of_span {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {G : Type}
    (ρ : G → Matrix n n k) (h : ∀ i j, Matrix.single i j (1 : k) ∈ Submodule.span k (Set.range ρ)) :
    AbsIrr ρ := by
  constructor
  · intro W hW
    have hall : ∀ A ∈ Submodule.span k (Set.range ρ), ∀ v ∈ W, A.mulVec v ∈ W := by
      intro A hA
      induction hA using Submodule.span_induction with
      | mem A hA => obtain ⟨g, rfl⟩ := hA; exact hW g
      | zero => intro v _; rw [Matrix.zero_mulVec]; exact W.zero_mem
      | add A B _ _ hA hB => intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hA v hv) (hB v hv)
      | smul c A _ hA => intro v hv; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hA v hv)
    by_cases hb : W = ⊥
    · exact Or.inl hb
    right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp hb
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra hc
      exact hv0 (funext fun j => by_contra fun hj => hc ⟨j, hj⟩)
    have hs : ∀ i, Pi.single i (1 : k) ∈ W := by
      intro i
      have h1 := W.smul_mem (v j)⁻¹ (hall _ (h i j) v hv)
      have h2 : (v j)⁻¹ • (Matrix.single i j (1 : k)).mulVec v = Pi.single i (1 : k) := by
        funext a
        by_cases ha : a = i
        · subst ha
          simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hj]
        · simp [Matrix.mulVec, dotProduct, ha, Ne.symm ha]
      rwa [h2] at h1
    refine eq_top_iff.mpr fun w _ => ?_
    have h3 : w = ∑ i, w i • Pi.single i (1 : k) := by
      funext a
      simp [Finset.sum_apply, Pi.single_apply]
    rw [h3]
    exact W.sum_mem fun i _ => W.smul_mem _ (hs i)
  · intro M hM
    have hall : ∀ A ∈ Submodule.span k (Set.range ρ), M * A = A * M := by
      intro A hA
      induction hA using Submodule.span_induction with
      | mem A hA => obtain ⟨g, rfl⟩ := hA; exact hM g
      | zero => simp
      | add A B _ _ hA hB => rw [mul_add, add_mul, hA, hB]
      | smul c A _ hA => rw [Matrix.mul_smul, Matrix.smul_mul, hA]
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
      (fun i j => (hall _ (h i j)).symm)
    exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem absIrrExt : StatAbsIrrExt := by
  intro k k' _ _ f n _ _ G _ ρ hρ
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨fun W _ => Or.inl (Subsingleton.elim _ _), fun M _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have hspan := burnsideMat k n G ρ hρ
  have hmap : ∀ A ∈ Submodule.span k (Set.range ρ),
      A.map f ∈ Submodule.span k' (Set.range fun g => (ρ g).map f) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA => obtain ⟨g, rfl⟩ := hA; exact Submodule.subset_span ⟨g, rfl⟩
    | zero => rw [Matrix.map_zero f f.map_zero]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.map_add f f.map_add]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA =>
      have h1 : (c • A).map f = f c • A.map f := by
        ext i j; simp
      rw [h1]; exact Submodule.smul_mem _ _ hA
  refine absIrr_of_span _ fun i j => ?_
  have h1 := hmap (Matrix.single i j (1 : k)) (hspan ▸ Submodule.mem_top)
  have h2 : (Matrix.single i j (1 : k)).map f = Matrix.single i j (1 : k') := by
    ext a b
    by_cases hab : i = a ∧ j = b <;> simp [hab]
  rwa [h2] at h1

theorem bcRank : StatBcRank := by
  intro O _ _ F F' _ _ f f' d _ _ e he
  obtain ⟨P, Q, dd, hdd, hPQ, hQP, rfl⟩ := idem_normal_form e he
  rw [rank_map_conj f' P Q dd hdd hPQ hQP, rank_map_conj f P Q dd hdd hPQ hQP]

theorem bcSplit : StatBcSplit := by
  intro K _ d _ _ e a t he hea hae hrk
  obtain ⟨S, _, _, U, W, hUW, hWU⟩ := idem_factor e he
  have hcard : Fintype.card S = t := by
    rw [← hrk, ← hUW]
    apply le_antisymm
    · calc Fintype.card S = (1 : Matrix S S K).rank := (Matrix.rank_one).symm
        _ = (W * (U * W) * U).rank := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hWU, Matrix.mul_one, hWU]
        _ ≤ (U * W).rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width U)
  have ha : a = U * (W * a * U) * W := by
    calc a = e * a * e := by rw [hea, hae]
      _ = _ := by rw [← hUW]; simp only [Matrix.mul_assoc]
  have hpoly : blockPoly e a = (W * a * U).charpoly := by
    conv_lhs => rw [ha, ← hUW]
    exact blockPoly_factor U W hWU _
  have hmon : (blockPoly e a).Monic := hpoly ▸ Matrix.charpoly_monic _
  have hdeg : (blockPoly e a).natDegree = t := by
    rw [hpoly, Matrix.charpoly_natDegree_eq_dim, hcard]
  refine ⟨hmon, hdeg, fun hsep hspl => ?_⟩
  set Q := blockPoly e a with hQ
  have hnd : Q.roots.Nodup := Polynomial.nodup_roots hsep
  have hc : Q.roots.toFinset.card = t := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← hspl.natDegree_eq_card_roots, hdeg]
  let en := Q.roots.toFinset.equivFinOfCardEq hc
  refine ⟨fun i => (en.symm i).1, fun i j hij => en.symm.injective (Subtype.ext hij), ?_⟩
  rw [Equiv.prod_comp en.symm (fun z : Q.roots.toFinset => Polynomial.X - Polynomial.C z.1),
    Finset.prod_coe_sort Q.roots.toFinset (fun z => Polynomial.X - Polynomial.C z)]
  conv_lhs => rw [hspl.eq_prod_roots_of_monic hmon]
  rw [Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

theorem bcM_mem {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X d G : Type} [Fintype d]
    [DecidableEq d] [Group G] (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O))
    {a : X → Matrix d d O} (ha : a ∈ tSpan T r) : bcM O' a ∈ tSpan (bcT O' T) (bcR O' r) := by
  obtain ⟨S, c, hc, rfl⟩ := ha
  refine ⟨S, fun g x => algebraMap O O' (c g x), fun g => mem_bcT O' T (hc g), ?_⟩
  funext x; ext i j
  simp [bcM, bcR, Finset.sum_apply, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun g _ => (Algebra.smul_def _ _).symm

theorem bcM_mul {O : Type} (O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] {X d : Type} [Fintype d]
    (a b : X → Matrix d d O) : bcM O' (a * b) = bcM O' a * bcM O' b := by
  funext x
  simp [bcM, Matrix.map_mul]

theorem sep_ext {O : Type} [CommRing O] [IsDomain O] {F : Type} [Field F] (f : O →+* F)
    (hf : Function.Injective f) (P : Polynomial O)
    (h : (P.map (algebraMap O (FractionRing O))).Separable) : (P.map f).Separable := by
  have hκ : (IsFractionRing.lift hf : FractionRing O →+* F).comp (algebraMap O (FractionRing O)) = f :=
    RingHom.ext (IsFractionRing.lift_algebraMap hf)
  rw [← hκ, ← Polynomial.map_map, Polynomial.separable_map]
  exact h

set_option maxHeartbeats 1000000 in
theorem stageC : StatStageC := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X _ T d _ _ G _ r π t bl χ₁ ε hP hA eB e₁ hI g₀ s hsm hes hse hsπ
    hsep hspl
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  obtain ⟨heBm, he1m, heBB, he11, heB1, he1B, hrkB, hrk1, heBπ, he1π⟩ := hI
  let j : O →+* O' := algebraMap O O'
  have hj : Function.Injective j := FaithfulSMul.algebraMap_injective O O'
  have hjl : IsLocalHom (algebraMap O O') := inferInstance
  let ι : O →+* FractionRing O := algebraMap O (FractionRing O)
  let ι' : O' →+* FractionRing O' := algebraMap O' (FractionRing O')
  have hι' : Function.Injective ι' := IsFractionRing.injective O' (FractionRing O')
  have : Nonempty X := ⟨π⟩
  refine ⟨⟨bcLocal O O' X T hloc, ?_, ?_, ?_, hc1, ?_⟩, ?_, ⟨bcM_mem O' T r heBm, bcM_mem O' T r he1m,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨bcM_mem O' T r hsm, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    obtain ⟨f, hf, hne⟩ := hpts x y hxy
    exact ⟨_, mem_bcT O' T hf, fun h => hne (hj h)⟩
  · intro g k
    have h1 : (fun x => (Matrix.charpolyRev (bcR O' r g x)).coeff k) =
        fun x => algebraMap O O' ((Matrix.charpolyRev (r g x)).coeff k) := by
      funext x
      show (Matrix.charpolyRev ((r g x).map j)).coeff k = _
      rw [← charpolyRev_map, Polynomial.coeff_map]
    rw [h1]
    exact mem_bcT O' T (hG1 g k)
  · intro g a b hab
    show j (r g π a b) = 0
    rw [hbd g a b hab, map_zero]
  · intro g a ha
    show j (r g π a a) = _
    rw [hχ g a ha, map_mul]
    simp [bcChar, j]
  ·
    let ρ0 : G →* Matrix {a // bl a = 0} {a // bl a = 0} (IsLocalRing.ResidueField O) :=
      { toFun := fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)
        map_one' := by
          rw [map_one]
          ext a b
          by_cases h : a = b
          · subst h; simp [Matrix.toSquareBlock_def]
          · have h' : a.1 ≠ b.1 := fun e => h (Subtype.ext e)
            simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, h']
        map_mul' := fun g h => by
          rw [map_mul, Pi.mul_apply, blk_mul bl (hbd g) 0, Matrix.map_mul] }
    exact absIrrExt _ _ (IsLocalRing.ResidueField.map (algebraMap O O')) _ G ρ0 hA
  · rw [← bcM_mul, heBB]
  · rw [← bcM_mul, he11]
  · rw [← bcM_mul, heB1]; funext x; simp [bcM]
  · rw [← bcM_mul, he1B]; funext x; simp [bcM]
  · intro x
    show (((eB x).map j).map ι').rank = t
    rw [Matrix.map_map, ← hrkB x]
    exact bcRank O _ _ ι (ι'.comp j) d (eB x) (congrFun heBB x)
  · intro x
    show (((e₁ x).map j).map ι').rank = 1
    rw [Matrix.map_map, ← hrk1 x]
    exact bcRank O _ _ ι (ι'.comp j) d (e₁ x) (congrFun he11 x)
  · show (eB π).map j = _
    rw [heBπ]
    ext a b
    by_cases hab : a = b
    · subst hab; by_cases h0 : bl a = 0 <;> simp [h0]
    · simp [Matrix.diagonal_apply_ne _ hab]
  · intro a b hab
    show j (e₁ π a b) = 0
    rw [he1π a b hab, map_zero]
  · rw [← bcM_mul, hes]
  · rw [← bcM_mul, hse]
  · show (s π).map j = 0
    rw [hsπ]; ext a b; simp
  · intro x
    let X0 : Matrix d d O := eB x * r g₀ x * eB x + s x
    have hX0 : (bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x) = X0.map j := by
      show (eB x).map j * (r g₀ x).map j * (eB x).map j + (s x).map j = _
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add j j.map_add]
    have hpoly : blockPoly ((bcM O' eB x).map ι') ((X0.map j).map ι') =
        (blockPoly (eB x) X0).map (ι'.comp j) := by
      show blockPoly (((eB x).map j).map ι') _ = _
      rw [Matrix.map_map, Matrix.map_map]
      exact (blockPoly_map (ι'.comp j) _ _).symm
    have hinj : Function.Injective (ι'.comp j) := hι'.comp hj
    have hsep' : ((blockPoly (eB x) X0).map (ι'.comp j)).Separable := by
      refine sep_ext _ hinj _ ?_
      rw [blockPoly_map]
      exact hsep x
    have hmm : ∀ u v w : Matrix d d O, u * v = w →
        (u.map j).map ι' * (v.map j).map ι' = (w.map j).map ι' := by
      intro u v w h
      rw [← Matrix.map_mul, ← Matrix.map_mul, h]
    have hbb : eB x * eB x = eB x := congrFun heBB x
    have hbs : eB x * s x = s x := congrFun hes x
    have hsb : s x * eB x = s x := congrFun hse x
    have heX0 : eB x * X0 = X0 := by
      show eB x * (eB x * r g₀ x * eB x + s x) = _
      rw [mul_add, ← mul_assoc, ← mul_assoc, hbb, hbs]
    have hX0e : X0 * eB x = X0 := by
      show (eB x * r g₀ x * eB x + s x) * eB x = _
      rw [add_mul, mul_assoc, hbb, hsb]
    have hrk : ((bcM O' eB x).map ι').rank = t := by
      show (((eB x).map j).map ι').rank = t
      rw [Matrix.map_map, ← hrkB x]
      exact bcRank O _ _ ι (ι'.comp j) d (eB x) (congrFun heBB x)
    obtain ⟨-, -, h3⟩ := bcSplit (FractionRing O') d ((bcM O' eB x).map ι') ((X0.map j).map ι') t
      (hmm _ _ _ (congrFun heBB x)) (hmm _ _ _ heX0) (hmm _ _ _ hX0e) hrk
    rw [hX0]
    exact h3 (hpoly ▸ hsep') (hpoly ▸ hspl x)
  · intro Z
    exact vccBaseChange O O' e he X T (bcT O' T) (bcSpan O O' X T) Z π

theorem deltaO_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
    [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)}
    {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}
    {D : RingData O X d G t bl} (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) :
    D.δO = ∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O)) := by
  obtain ⟨-, -, -, -, -, hrr, -⟩ := hD
  have h2 : D.δO = ∏ i ∈ Finset.Ioo 0 t,
      ((D.rr 0 : D.X' → O) D.π' - (D.rr i : D.X' → O) D.π') := by
    show ((Pi.evalRingHom (fun _ : D.X' => O) D.π').comp D.T'.val.toRingHom) D.δ = _
    unfold RingData.δ
    rw [map_prod]; rfl
  rw [h2]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_Ioo] at hi
  rw [hrr 0 (by omega), hrr i hi.2]
  simp

theorem deltaBc : StatDeltaBc := by
  intro O O' _ _ _ _ _ _ _ e he
  refine ⟨?_, fun ℓ => ?_⟩
  · intro X d G _ _ _ t bl T r π χ₁ ε g₀ eB e₁ s D' hD'
    have h1 : D'.δO = algebraMap O O'
        (∏ i ∈ Finset.Ioo 0 t, ((χ₁ g₀ : O) - (χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ i : Oˣ) : O))) := by
      rw [deltaO_eq hD', map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [bcChar]
    exact ⟨h1, by rw [h1, he]⟩
  · rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, ← he, map_natCast (algebraMap O O')]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
