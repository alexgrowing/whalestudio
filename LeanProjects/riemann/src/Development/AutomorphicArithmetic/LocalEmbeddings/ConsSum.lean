import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumbersAgreeModel
import Development.AutomorphicArithmetic.DivisorFrames.DegreeMatchingFamilies
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumberBaseChange
import Development.AutomorphicArithmetic.DivisorFrames.GenericFibreOpenProjective
import Development.AutomorphicArithmetic.DivisorFrames.PointsGenericFibreComponents
import Development.AutomorphicArithmetic.DivisorFrames.FunctionFieldEssFiniteTypeInt
import Development.AutomorphicArithmetic.DivisorFrames.NonemptyLevelStructure
import Development.AutomorphicArithmetic.DivisorFrames.LevelPointCount
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagCompactPoint
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingFlag
import Development.AutomorphicArithmetic.DivisorFrames.LevelUnfoldingMetric
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagMultiplicity
import Development.AutomorphicArithmetic.DivisorFrames.LevelFlagPrime

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Vert

namespace GlobalTheory.ConsGeo

theorem cancel_subtype {K : Type} [Field K] (V : ValuationSubring K) {k : Type} [Field k] {a b : Sp k ⟶ Sp K}
    (h : a ≫ spMap V.subtype = b ≫ spMap V.subtype) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (nonZeroDivisors V) h'

theorem embDeg_equiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) : embDeg e.toRingHom = 1 := by
  letI := e.toRingHom.toAlgebra
  exact (LinearEquiv.ofBijective (Algebra.linearMap K L) e.bijective).finrank_eq.symm.trans (Module.finrank_self K)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {O : Type} [CommRing O] {β : O →+* i₀.c.F} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β}
  {F : Type} [Field F] {e : F ≃+* i₀.c.F}

theorem embDeg_incl_pos (Z : LocM.Mdl Y i₀) : 0 < embDeg (incl Z) := by
  letI := (incl Z).toAlgebra
  have := Z.i.c.fin
  have : IsScalarTower ℚ i₀.c.F Z.i.c.F := .of_algebraMap_eq fun a => by simp
  have : Module.Finite i₀.c.F Z.i.c.F := .of_restrictScalars_finite ℚ _ _
  exact Module.finrank_pos

theorem π_genStr (C : FlagCpt T e) : C.π ≫ genStr T = C.Y.str ≫ spMap e.symm.toRingHom := by
  rw [← C.π_str, Category.assoc, Category.assoc, spMap, spMap, ← Spec.map_comp]
  have : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom = 𝟙 _ := by
    ext a; simp
  rw [this, Spec.map_id, Category.comp_id]

theorem generic_mem (C : FlagCpt T e) : C.π (genericPoint C.Y.X) ∈ Set.range T.jQ := by
  letI := (constF e C.Y).toAlgebra
  have e1 := Scheme.Hom.comp_apply (genericPt C.Y) C.π (closedPoint C.Y.Fn)
  have e2 := Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.jQ (closedPoint C.Y.Fn)
  rw [C.y0_x] at e2
  have h1 := e1.symm.trans e2
  have h2 : (genericPt C.Y) (closedPoint C.Y.Fn) = genericPoint C.Y.X := Scheme.fromSpecStalk_closedPoint
  rw [h2] at h1
  exact ⟨_, h1.symm⟩

variable {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N}

theorem card_match (h1 : 1 ≤ Dw.p + Dw.q) (z : admitted Y i₀) (L : Lev z.Z T) (C : FlagCpt T e) (q : Sp ℂ ⟶ C.Y.X)
    (hq : q ≫ C.π ≫ genStr T = spMap i₀.c.F.val.toRingHom) (hm : C.π (q (closedPoint ℂ)) ∈ Set.range T.jQ) :
    Nat.card {w : Sp ℂ ⟶ z.Z.X // Match L C w q} = cov z * embDeg (incl z.Z) := by
  have := T.jQ_open
  have hr : Set.range (q ≫ C.π) ⊆ Set.range T.jQ := by
    rintro _ ⟨w, rfl⟩
    rw [show w = closedPoint ℂ from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
    exact hm
  obtain ⟨y, hy⟩ : ∃ y, y ≫ T.jQ = q ≫ C.π := ⟨_, IsOpenImmersion.lift_fac T.jQ (q ≫ C.π) hr⟩
  obtain ⟨eq⟩ := UpperTheory.level_flag_multiplicity L C z.full q _ hy.symm
  rw [Nat.card_congr eq]
  exact UpperTheory.level_point_count L h1 ⟨y, by rw [← T.jQ_over, ← Category.assoc, hy, Category.assoc, hq]⟩

set_option maxHeartbeats 1000000 in

theorem exists_match (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (h1 : 1 ≤ Dw.p + Dw.q) (z : admitted Y i₀) (L : Lev z.Z T)
    (Φ : FlagTor T e U) [DecidableEq U.Comp] [IsDiscreteValuationRing (z.Z.i.c.V W)] (d : ℕ)
    (hY : ∀ c, (Φ.C c).Y.dim = d) [∀ C, IsIntegral ((nmodel z.Z).comp C).toBase.genFibre]
    [∀ C, IsOpenImmersion ((nmodel z.Z).comp C).toBase.genFibreι]
    (hX : ∀ C, topologicalKrullDim ((nmodel z.Z).comp C).toBase.genFibre = d)
    (hr : ∀ C, Set.range ((nmodel z.Z).comp C).toBase.genFibreι = ((nmodel z.Z).comp C).gen)
    (s : ∀ C, ((nmodel z.Z).comp C).toBase.genFibre ⟶ Sp z.Z.i.c.F) [∀ C, LocallyOfFiniteType (s C ≫ spMap (incl z.Z))]
    (hs : ∀ C, (((nmodel z.Z).comp C).toBase.genFibreι ≫ (nmodel z.Z).compι C) ≫ z.Z.s =
      s C ≫ spMap (z.Z.i.c.V W).subtype) :
    ∃ (b : (nmodel z.Z).Comp → U.Comp) (θ : ∀ C, (Φ.C (b C)).Y.X.functionField →+*
        ((nmodel z.Z).comp C).toBase.genFibre.functionField),
      (∀ C, Match L (Φ.C (b C)) (gpt _ ≫ ((nmodel z.Z).comp C).toBase.genFibreι ≫ (nmodel z.Z).compι C)
        (spMap (θ C) ≫ gpt _) ∧ spMap (θ C) ≫ gpt _ ≫ (Φ.C (b C)).π ≫ genStr T = gpt _ ≫ s C ≫ spMap (incl z.Z)) ∧
      (∀ C, 0 < embDeg (θ C)) ∧
      ∀ c, ∑ C ∈ Finset.univ.filter (fun C => b C = c), embDeg (θ C) = cov z * embDeg (incl z.Z) := by
  have := i₀.c.fin
  have : NumberField i₀.c.F := {}
  let ι (C : (nmodel z.Z).Comp) : ((nmodel z.Z).comp C).toBase.genFibre ⟶ z.Z.X :=
    ((nmodel z.Z).comp C).toBase.genFibreι ≫ (nmodel z.Z).compι C
  have (c : U.Comp) : LocallyOfFiniteType ((Φ.C c).π ≫ genStr T) := by
    rw [π_genStr]
    have : IsIso (spMap e.symm.toRingHom) :=
      inferInstanceAs (IsIso (Spec.map e.symm.toCommRingCatIso.hom))
    infer_instance
  have hover (k : Type) [Field k] (C c) (w : Sp k ⟶ _) (q) (h : Match L (Φ.C c) (w ≫ ι C) q) :
      w ≫ s C ≫ spMap (incl z.Z) = q ≫ (Φ.C c).π ≫ genStr T ∧ w (closedPoint k) ∈ ι C ⁻¹' z.Z.opn ∧
        q (closedPoint k) ∈ (Φ.C c).π ⁻¹' Set.range T.jQ := by
    obtain ⟨a₁, a₂, ⟨f, a₃, a₄⟩, -⟩ := UpperTheory.level_flag_compact_point L _ _ _ h
    refine ⟨?_, a₁, a₂⟩
    rw [a₄, ← Category.assoc, cancel_subtype (z.Z.i.c.V W) (a := w ≫ s C) (b := spMap f)]
    rw [← a₃, Category.assoc, Category.assoc, ← hs]
  obtain ⟨b, θ, a₁, a₂, a₃⟩ := UpperTheory.degree_matching_families i₀.c.F i₀.c.F.val.toRingHom (nmodel z.Z).Comp U.Comp
    (fun C => ((nmodel z.Z).comp C).toBase.genFibre) (fun c => (Φ.C c).Y.X) (fun C => s C ≫ spMap (incl z.Z))
    (fun c => (Φ.C c).π ≫ genStr T) d (cov z * embDeg (incl z.Z)) (fun C => ι C ⁻¹' z.Z.opn)
    (fun c => (Φ.C c).π ⁻¹' Set.range T.jQ) (fun k _ C c w q => Match L (Φ.C c) (w ≫ ι C) q) hX
    (fun c => by rw [(Φ.C c).Y.topologicalKrullDim_eq, hY]) (Nat.mul_pos (cov_pos z) (embDeg_incl_pos _))
    (fun C => by
      have : IsOpenImmersion ((nmodel z.Z).compι C) := inferInstanceAs (IsOpenImmersion C.opens.ι)
      have ho : IsOpen z.Z.opn := z.Z.cover ▸ isOpen_iUnion fun a => (z.Z.U a).1.isOpen
      obtain ⟨_, ⟨x, rfl⟩, hx⟩ := z.Z.dense.inter_open_nonempty _ (ι C).isOpenEmbedding.isOpen_range
        ⟨_, genericPoint _, rfl⟩
      exact (genericPoint_specializes x).mem_open (ho.preimage (ι C).continuous) hx)
    (fun c => generic_mem _) hover
    (fun k _ C w hw => UpperTheory.level_unfolding_flag Φ L (w ≫ ι C) hw)
    (fun k _ C c c' w q q' h h' => UpperTheory.level_unfolding_metric Φ L z.full _ c c' q q' h h')
    (fun k k' _ _ ψ C c w q h => by
      have := (UpperTheory.level_flag_compact_point L _ _ _ h).2.2.2 k' ψ
      rwa [← Category.assoc] at this)
    (fun c q hq hm => by
      rw [← card_match h1 z L (Φ.C c) q hq hm]
      obtain ⟨f₁, f₂⟩ := UpperTheory.points_generic_fibre_components _ (nmodel z.Z) ℂ
      refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.2 ≫ ι w.1.1, w.2⟩) ⟨fun w w' h => ?_, fun w => ?_⟩)
      · exact Subtype.ext (f₁ (congrArg Subtype.val h))
      · obtain ⟨C, w', h⟩ := f₂ w.1 (opn_subset_gen hp hW (UpperTheory.level_flag_compact_point L _ _ _ w.2).1)
        exact ⟨⟨⟨C, w'⟩, h ▸ w.2⟩, Subtype.ext h⟩)
  exact ⟨b, θ, fun C => ⟨a₁ C, by simpa using (hover _ _ _ _ _ (a₁ C)).1.symm⟩, a₂, a₃⟩

set_option maxHeartbeats 1000000 in

theorem sum_fibreDeg (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (h1 : 1 ≤ Dw.p + Dw.q) (z : admitted Y i₀)
    (Φ : FlagTor T e U) [Fintype U.Comp] [IsDiscreteValuationRing (z.Z.i.c.V W)] (d : ℕ)
    (hY : ∀ c, (Φ.C c).Y.dim = d) (hd : ∀ C, ((nmodel z.Z).comp C).relDim = d) (M : Fin d → FinLB z.Z.X)
    (Δ : ∀ c, Fin d → (Φ.C c).Y.Dv)
    (hag : ∀ (L : Lev z.Z T) (c : U.Comp) (X : Scheme.{0}) [IsIntegral X] (ι : X ⟶ z.Z.X) (sX : X ⟶ Sp z.Z.i.c.F),
      ι ≫ z.Z.s = sX ≫ spMap (z.Z.i.c.V W).subtype → Algebra.EssFiniteType ℤ X.functionField →
      ∀ θ : (Φ.C c).Y.X.functionField →+* X.functionField, Match L (Φ.C c) (gpt X ≫ ι) (spMap θ ≫ gpt (Φ.C c).Y.X) →
      ∀ i, ∃ D : CartierDiv X, toPic D = pull ι (M i).cls ∧ DvrAgree θ D (Δ c i)) :
    ∑ C, ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C) (∏ i, (M i).c1)) =
      (cov z : ℚ) * ∑ c, (interNum F (GlobalTheory.structureModule (Φ.C c).Y.X) (fun i => toLB (Δ c i)) : ℚ) := by
  classical
  have := i₀.c.fin
  have : NumberField i₀.c.F := {}
  obtain ⟨L⟩ := UpperTheory.nonempty_level_structure z.Z T h1
  choose g₁ g₂ g₃ g₄ g₅ ε g₆ using fun C => UpperTheory.generic_fibre_open_projective (z.Z.i.c.V W) z.Z.i.c.F ((nmodel z.Z).comp C)
  let s (C : (nmodel z.Z).Comp) : ((nmodel z.Z).comp C).toBase.genFibre ⟶ Sp z.Z.i.c.F :=
    ((nmodel z.Z).comp C).toBase.genFibreStr ≫ spMap (ε C).toRingHom
  have hs (C) : (((nmodel z.Z).comp C).toBase.genFibreι ≫ (nmodel z.Z).compι C) ≫ z.Z.s =
      s C ≫ spMap (z.Z.i.c.V W).subtype := by
    rw [Category.assoc, Category.assoc]
    exact (g₆ C).symm
  have p₁ (C) := UpperTheory.intersection_number_base_change _ _ (ε C).toRingHom _ _ (by rw [embDeg_equiv]; exact one_pos) (g₄ C)
  have p₂ (C) := UpperTheory.intersection_number_base_change _ _ (incl z.Z) _ (s C) (embDeg_incl_pos _) (p₁ C).1
  have p₃ (c) := UpperTheory.intersection_number_base_change _ _ e.symm.toRingHom _ _ (by rw [embDeg_equiv]; exact one_pos) (Φ.C c).Y.isProjOver
  have : ∀ C, LocallyOfFiniteType (s C ≫ spMap (incl z.Z)) := fun C => by
    have := (isProper_and_exists_isAmpleLB_of_isProjOver (p₂ C).1).1
    infer_instance
  obtain ⟨b, θ, a₁, a₂, a₃⟩ := exists_match hp hW h1 z L Φ d hY (fun C => by rw [g₅, hd]) g₃ s hs
  let I (c : U.Comp) : ℤ := interNum F (GlobalTheory.structureModule (Φ.C c).Y.X) fun i => toLB (Δ c i)
  have key (C : (nmodel z.Z).Comp) : (embDeg (incl z.Z) : ℚ) *
      ((nmodel z.Z).comp C).toBase.fibreDeg (picSymPull ((nmodel z.Z).compι C) (∏ i, (M i).c1)) =
      embDeg (θ C) * I (b C) := by
    choose D hD hD' using hag L (b C) _ _ (s C) (hs C) (UpperTheory.functionField_essFiniteType_int _ _ (s C ≫ spMap (incl z.Z))) (θ C) (a₁ C).1
    have h₁ := UpperTheory.intersection_numbers_agree_model _ _ _ (s C ≫ spMap (incl z.Z)) _ (θ C) d (p₂ C).1 (p₃ (b C)).1 (by rw [g₅, hd])
      (by rw [(Φ.C (b C)).Y.topologicalKrullDim_eq, hY]) (by rw [← π_genStr]; exact (a₁ C).2) (a₂ C) D (Δ (b C)) hD'
    rw [(p₂ C).2 d _ fun i => isLB_toLB _, (p₁ C).2 d _ fun i => isLB_toLB _, (p₃ (b C)).2 d _ fun i => isLB_toLB _,
      embDeg_equiv, embDeg_equiv, Nat.cast_one, one_mul, one_mul] at h₁
    have h₂ := ((nmodel z.Z).comp C).toBase.fibreDeg_prod (L := fun i => ((M i).pull ((nmodel z.Z).compι C)).lb)
      fun i => FinLB.isLB _
    rw [if_pos (by rw [Fintype.card_fin, Vert.Model.relDim_toBase, hd])] at h₂
    rw [map_prod]
    simp only [FinLB.pullback_firstChern]
    refine (congrArg _ h₂).trans ?_
    have h₃ := interNum_congr_cls ((nmodel z.Z).comp C).toBase.fnField
      (GlobalTheory.structureModule ((nmodel z.Z).comp C).toBase.genFibre)
      (L := fun i => (((M i).pull ((nmodel z.Z).compι C)).lb).pull ((nmodel z.Z).comp C).toBase.genFibreι)
      (L' := fun i => toLB (D i)) (fun i => LB.isLB_pull (FinLB.isLB _) _) (fun i => isLB_toLB _) fun i => by
        rw [← toPic_apply, hD, cls_pull (FinLB.isLB _), pull_comp]
        exact congrArg _ (FinLB.cls_pull _ _)
    rw [h₃]
    exact_mod_cast h₁
  refine mul_left_cancel₀ (Nat.cast_ne_zero.2 (embDeg_incl_pos z.Z).ne' : (embDeg (incl z.Z) : ℚ) ≠ 0) ?_
  rw [Finset.mul_sum, Finset.sum_congr rfl fun C _ => key C, ← Finset.sum_fiberwise Finset.univ b, ← mul_assoc,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (Finset.sum_congr rfl fun C hC =>
    congrArg (fun c => (embDeg (θ C) : ℚ) * I c) (Finset.mem_filter.1 hC).2).trans ?_
  rw [← Finset.sum_mul, ← Nat.cast_sum, a₃, Nat.cast_mul, mul_comm (cov z : ℚ)]

open Classical in

theorem divOf_single (C : FlagCpt T e) (a : ℕ → Bool) (R : Option ℝ) (x : Letter Dw) (n : ℤ) :
    divOf C (expo Dw (Finsupp.single (a, R, .inl (x.1, (x.2 : ℕ))) n)) = n • C.gr x.1 x.2 := by
  have h : letterOf Dw (.inl (x.1, (x.2 : ℕ))) = some x := dif_pos x.2.2
  rw [divOf, Finset.sum_eq_single x]
  · simp [expo, h]
  · intro y _ hy
    simp [expo, h, hy.symm]
  · simp

theorem root_agree (hS : GlobalTheory.Published.SemiAbelianHomExtension) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (z : admitted Y i₀)
    (L : Lev z.Z T) (C : FlagCpt T e) (X : Scheme.{0}) [IsIntegral X] (ι : X ⟶ z.Z.X) (sX : X ⟶ Sp z.Z.i.c.F)
    (hs : ι ≫ z.Z.s = sX ≫ spMap (z.Z.i.c.V W).subtype) (hE : Algebra.EssFiniteType ℤ X.functionField)
    (θ : C.Y.X.functionField →+* X.functionField) (h : Match L C (gpt X ≫ ι) (spMap θ ≫ gpt C.Y.X))
    (τ : E →+* ℂ) (hτ : Dw.mult τ = Dw.p) (i : ℕ) (hi : i < Dw.p + Dw.q) :
    ∃ D : CartierDiv X, toPic D = pull ι (z.rootLB false τ i).cls ∧
      DvrAgree θ D (divOf C (expo Dw (rootSym Dw (fun _ => false) none τ i))) := by
  unfold admitted.rootLB rootSym
  split_ifs with h₁
  · let x : Letter Dw := ⟨τ, i, hτ ▸ h₁⟩
    have hx : letterOf Dw (.inl (x.1, (x.2 : ℕ))) = some x := dif_pos x.2.2
    obtain ⟨D, a, b⟩ := UpperTheory.level_flag_prime hS hp hW z.full L C X ι sX hs hE θ h x (z.line false _ x hx)
    refine ⟨D, by rw [a]; exact congrArg (fun M => pull ι M.cls) (z.stepLB_of_some false hx).symm, ?_⟩
    exact ((divOf_single C _ _ x 1).trans (one_smul _ _)).symm ▸ b
  · have h₂ := GlobalTheory.Proof.LetterConjugation.mult_add Dw τ
    let x : Letter Dw := ⟨conjEmb τ, Dw.p + Dw.q - 1 - i, by omega⟩
    have hx : letterOf Dw (.inl (x.1, (x.2 : ℕ))) = some x := dif_pos x.2.2
    obtain ⟨D, a, b⟩ := UpperTheory.level_flag_prime hS hp hW z.full L C X ι sX hs hE θ h x (z.line false _ x hx)
    refine ⟨-D, ?_, ?_⟩
    · rw [map_neg, a, FinLB.cls_dual, map_neg]
      exact congrArg (fun M => -pull ι M.cls) (z.stepLB_of_some false hx).symm
    · exact ((divOf_single C _ _ x (-1)).trans (neg_one_zsmul _)).symm ▸ b.neg

end GlobalTheory.ConsGeo

end
