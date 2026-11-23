import Development.WeilBound.CoreStatements.HodgeTatePoints.RfTors
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FiniteAlgebraSplitLocal
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
open ReciprocityTheory.ChartRestriction.G.Chart (spMap_left spMap_id)

namespace PositivityTheory.HtPt.Rf

section Pull
variable {R₀ O : Type} [CommRing R₀] [CommRing O] [Algebra R₀ O]
  {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G]
  {G' : Over (Spec (CommRingCat.of O))} [GrpObj G'] {ψ : G'.left ⟶ G.left}

theorem sp_hom_comp (S : Type) [CommRing S] [Algebra O S] [Algebra R₀ S] [IsScalarTower R₀ O S] :
    (sp (R₀ := O) S).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ O)) = (sp (R₀ := R₀) S).hom := by
  simp only [sp, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

noncomputable def down (h : Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ O))) ψ)
    {S : Type} [CommRing S] [Algebra O S] [Algebra R₀ S] [IsScalarTower R₀ O S]
    (x : sp (R₀ := O) S ⟶ G') : sp (R₀ := R₀) S ⟶ G :=
  Over.homMk (x.left ≫ ψ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    exact sp_hom_comp S)

variable (h : Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ O))) ψ)
  {S : Type} [CommRing S] [Algebra O S] [Algebra R₀ S] [IsScalarTower R₀ O S]

theorem down_left (x : sp (R₀ := O) S ⟶ G') : (down h x).left = x.left ≫ ψ := rfl

theorem down_bij : Function.Bijective (down h (S := S)) := by
  constructor
  · intro x y hxy
    have h1 : x.left ≫ ψ = y.left ≫ ψ := by
      rw [← down_left h x, ← down_left h y, hxy]
    have h2 : x.left ≫ G'.hom = y.left ≫ G'.hom := by
      rw [Over.w x, Over.w y]
    exact Over.OverMorphism.ext (h.1.hom_ext h1 h2)
  · intro z
    refine ⟨Over.homMk (h.1.lift z.left (sp (R₀ := O) S).hom ?_) (h.1.lift_snd _ _ _), ?_⟩
    · rw [Over.w z]
      exact (sp_hom_comp (R₀ := R₀) (O := O) S).symm
    · apply Over.OverMorphism.ext
      rw [down_left]
      exact h.1.lift_fst _ _ _

theorem down_mul (x y : sp (R₀ := O) S ⟶ G') : down h (x * y) = down h x * down h y := by
  have hw : ∀ z : sp (R₀ := O) S ⟶ G', (z.left ≫ ψ) ≫ G.hom =
      (Over.mk ((sp (R₀ := O) S).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ O)))).hom := by
    intro z
    change (z.left ≫ ψ) ≫ G.hom = (sp (R₀ := O) S).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ O))
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w z]
  let e : sp (R₀ := R₀) S ⟶ Over.mk ((sp (R₀ := O) S).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ O))) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ (sp (R₀ := O) S).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ O)) = _
      rw [Category.id_comp]
      exact sp_hom_comp (R₀ := R₀) (O := O) S)
  have hd : ∀ z, down h z = e ≫ Over.homMk (z.left ≫ ψ) (hw z) := by
    intro z
    apply Over.OverMorphism.ext
    simp [e, down_left]
  rw [hd, hd, hd, ← MonObj.comp_mul]
  congr 1
  apply Over.OverMorphism.ext
  exact (h.2 _ x y (Over.homMk (x.left ≫ ψ) (hw x)) (Over.homMk (y.left ≫ ψ) (hw y)) rfl rfl).symm

theorem down_pow_eq_one (x : sp (R₀ := O) S ⟶ G') (n : ℕ) : down h x ^ n = 1 ↔ x ^ n = 1 := by
  have h1 : down h (1 : sp (R₀ := O) S ⟶ G') = 1 := by
    have hm := down_mul h (1 : sp (R₀ := O) S ⟶ G') 1
    rw [_root_.one_mul] at hm
    have hm' : down h (1 : sp (R₀ := O) S ⟶ G') * down h 1 = down h 1 * 1 := by
      rw [_root_.mul_one, ← hm]
    exact mul_left_cancel hm'
  have hp : ∀ m : ℕ, down h (x ^ m) = down h x ^ m := by
    intro m
    induction m with
    | zero => rw [_root_.pow_zero, _root_.pow_zero, h1]
    | succ m ih => rw [_root_.pow_succ, _root_.pow_succ, down_mul, ih]
  rw [← hp, ← h1, (down_bij h).1.eq_iff]

theorem down_nat {S' : Type} [CommRing S'] [Algebra O S'] [Algebra R₀ S'] [IsScalarTower R₀ O S']
    (f : S →ₐ[O] S') (x : sp (R₀ := O) S ⟶ G') :
    down h (spMap f ≫ x) = spMap (f.restrictScalars R₀) ≫ down h x := by
  apply Over.OverMorphism.ext
  rw [down_left, Over.comp_left, Over.comp_left, down_left, spMap_left, spMap_left, Category.assoc]
  rfl

end Pull

theorem isLocalHom_of_finite (O S : Type) [CommRing O] [IsLocalRing O] [CommRing S] [IsLocalRing S]
    [Algebra O S] [Module.Finite O S] : IsLocalHom (algebraMap O S) := by
  constructor
  intro a ha
  by_contra hna
  have hm : (IsLocalRing.maximalIdeal S).comap (algebraMap O S) = IsLocalRing.maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal S))
  have hmem : a ∈ (IsLocalRing.maximalIdeal S).comap (algebraMap O S) := by
    rw [hm]
    exact hna
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem ha

theorem e_pow {R₀ : Type} [CommRing R₀] {B : BX R₀} {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G]
    {e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)}
    (hb : ∀ R, Function.Bijective (e R)) (ha : ∀ R x y, e R (x + y) = e R x * e R y)
    (R : LAlg R₀) (x : B.G R) (n : ℕ) : e R x ^ n = 1 ↔ n • x = 0 := by
  have h0 : e R 0 = 1 := by
    have hm := ha R 0 0
    rw [add_zero] at hm
    have hm' : e R 0 * e R 0 = e R 0 * 1 := by
      rw [_root_.mul_one, ← hm]
    exact mul_left_cancel hm'
  have hp : ∀ m : ℕ, e R (m • x) = e R x ^ m := by
    intro m
    induction m with
    | zero => rw [zero_smul, _root_.pow_zero, h0]
    | succ m ih => rw [succ_nsmul, ha, ih, _root_.pow_succ]
  rw [← hp, ← h0, (hb R).1.eq_iff]

theorem ptOf_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g p : ℕ} [NeZero p]
    (τ : Ix g → ℕ → B.G O) (hτ : ∀ j, p • τ j 0 = 0) (s t : Ix g → ZMod p) :
    ptOf B τ (s + t) = ptOf B τ s + ptOf B τ t := by
  unfold ptOf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.add_apply, ZMod.val_add, ← add_nsmul]
  conv_rhs => rw [← Nat.mod_add_div ((s j).val + (t j).val) p]
  rw [add_nsmul, mul_nsmul, hτ j, nsmul_zero, add_zero]

theorem htd_tie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) {R₀ : Type} [CommRing R₀] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) [Algebra (Tw.O : Type) C], v.Integers (Tw.O : Type) → v (p : C) < 1 → ∀ [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt Oe σ cp) (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (G' : Over (Spec (CommRingCat.of (Tw.O : Type)))) [GrpObj G'] [IsCommMonObj G'] (ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Tw.O : Type)))) ψ → ∃ pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G'), (∀ t, (pt t).left ≫ ψ = (e Tw.O (ptOf B D.L.τ t)).left) ∧ IsTorsPts G' p pt ∧ ∀ T : TorsRep G' p, D.evImg C = torsFun C T pt := by
  intro p _ C _ _ _ v R₀ _ g B Tw Dt _ hv hp _ Oe _ _ σ cp D G _ _ e hb ha hn G' _ _ ψ h
  have hτ : ∀ j, p • D.L.τ j 0 = 0 := by
    intro j
    simpa using D.L.τ_tors j 0
  have hinj : ∀ s t : Nb p g, ptOf B D.L.τ s = ptOf B D.L.τ t → s = t := by
    intro s t hst
    apply D.L.τ_basis.1
    exact Subtype.ext hst
  let pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G') := fun t =>
    Function.surjInv (down_bij h (S := (Tw.O : Type))).2 (e Tw.O (ptOf B D.L.τ t))
  have hdpt : ∀ t, down h (pt t) = e Tw.O (ptOf B D.L.τ t) := fun t =>
    Function.surjInv_eq (down_bij h (S := (Tw.O : Type))).2 _
  have hpts : IsTorsPts G' p pt := by
    refine ⟨?_, ?_, ?_⟩
    · intro s t hst
      have hd := congrArg (down h) hst
      rw [hdpt, hdpt] at hd
      exact hinj s t ((hb _).1 hd)
    · intro s t
      apply (down_bij h).1
      rw [down_mul, hdpt, hdpt, hdpt, ptOf_add _ hτ, ha]
    · intro z
      constructor
      · intro hz
        rw [← down_pow_eq_one h] at hz
        obtain ⟨w, hw⟩ := (hb Tw.O).2 (down h z)
        rw [← hw, e_pow hb ha] at hz
        obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨w, hz⟩
        refine ⟨t, (down_bij h).1 ?_⟩
        rw [hdpt, ← hw]
        exact congrArg (e Tw.O) (congrArg Subtype.val ht)
      · rintro ⟨t, rfl⟩
        rw [← down_pow_eq_one h, hdpt, e_pow hb ha]
        exact D.pt_p t
  refine ⟨pt, fun t => ?_, hpts, ?_⟩
  · rw [← down_left h, hdpt]
  · intro T
    have hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
        B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t := fun t =>
      ⟨(Classical.choose_spec (Classical.choose_spec
          (D.fin.univ Tw.O (LHom.id Tw.O) _ (D.pt_p t)))).1,
        (Classical.choose_spec (Classical.choose_spec
          (D.fin.univ Tw.O (LHom.id Tw.O) _ (D.pt_p t)))).2.1⟩
    obtain ⟨φT, hφT⟩ := exists_pts T hpts
    letI instA : ∀ i, Algebra (Tw.O : Type) (D.fin.AAx i).carrier := fun i =>
      ((D.fin.sO i).1 : (Tw.O : Type) →+* (D.fin.AAx i).carrier).toAlgebra
    haveI instT : ∀ i, IsScalarTower R₀ (Tw.O : Type) (D.fin.AAx i).carrier := fun i =>
      IsScalarTower.of_algebraMap_eq (fun r => ((D.fin.sO i).1.commutes r).symm)
    have hy : ∀ i, ∃ z : sp (R₀ := (Tw.O : Type)) (D.fin.AAx i).carrier ⟶ G',
        down h z = e (D.fin.AAx i) (D.fin.y i) := fun i => (down_bij h).2 _
    choose y' hy' using hy
    have hyp : ∀ i, y' i ^ p = 1 := by
      intro i
      rw [← down_pow_eq_one h, hy', e_pow hb ha]
      exact D.fin.y_p i
    choose χ hχ using fun i => (T.univ _ (y' i) (hyp i)).exists
    have hfac : ∀ t (a : T.A), φT t a = (D.ptMap t).1 (χ (D.ptIdx t) a) := by
      intro t a
      let f : (D.fin.AAx (D.ptIdx t)).carrier →ₐ[(Tw.O : Type)] (Tw.O : Type) :=
        { toRingHom := (D.ptMap t).1.toRingHom
          commutes' := fun r => by
            have hr := congrArg (fun φ : LHom Tw.O Tw.O => φ.1 r) (hspec t).1
            exact hr }
      have hf : φT t = f.comp (χ _) := by
        apply tors_ext T
        rw [hφT, spc, hχ]
        apply (down_bij h).1
        rw [hdpt, down_nat, hy', ← (hspec t).2, hn]
        rfl
      exact DFunLike.congr_fun hf a
    haveI hTfin : Module.Finite (Tw.O : Type) T.A := T.fin
    haveI hAfin : ∀ i, Module.Finite (Tw.O : Type) (D.fin.AAx i).carrier := fun i => (D.fin.free i).2
    have hloc : ∀ (A S : LAlg R₀) [Algebra (Tw.O : Type) A.carrier] [Algebra (Tw.O : Type) S.carrier]
        [Module.Finite (Tw.O : Type) A.carrier] [IsLocalHom (algebraMap (Tw.O : Type) S.carrier)]
        (f : A.carrier →ₐ[(Tw.O : Type)] S.carrier), IsLocalHom (f : A.carrier →+* S.carrier) := by
      intro A S _ _ _ _ f
      have hc : (IsLocalRing.maximalIdeal S.carrier).comap (f : A.carrier →+* S.carrier) =
          IsLocalRing.maximalIdeal A.carrier := by
        apply IsLocalRing.eq_maximalIdeal
        apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := (Tw.O : Type))
        rw [Ideal.comap_comap, AlgHom.comp_algebraMap, IsLocalRing.maximalIdeal_comap]
        exact IsLocalRing.maximalIdeal.isMaximal _
      constructor
      intro a ha
      by_contra hna
      have hmem : a ∈ (IsLocalRing.maximalIdeal S.carrier).comap (f : A.carrier →+* S.carrier) := by
        rw [hc]
        exact hna
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem ha
    have key : ∀ (S : LAlg R₀) [Algebra (Tw.O : Type) S.carrier] [IsScalarTower R₀ (Tw.O : Type) S.carrier]
        [Module.Finite (Tw.O : Type) S.carrier] (α : T.A →ₐ[(Tw.O : Type)] S.carrier),
        ∃ i, ∃ β : (D.fin.AAx i).carrier →ₐ[(Tw.O : Type)] S.carrier, β.comp (χ i) = α ∧
          (∀ j (β' : (D.fin.AAx j).carrier →ₐ[(Tw.O : Type)] S.carrier), β'.comp (χ j) = α → j = i) ∧
          ∀ β' : (D.fin.AAx i).carrier →ₐ[(Tw.O : Type)] S.carrier, β'.comp (χ i) = α → β' = β := by
      intro S _ _ _ α
      haveI hOS : IsLocalHom (algebraMap (Tw.O : Type) S.carrier) := isLocalHom_of_finite _ _
      let s : LHom Tw.O S := ⟨IsScalarTower.toAlgHom R₀ (Tw.O : Type) S.carrier, hOS⟩
      have hcomp : ∀ j (β' : (D.fin.AAx j).carrier →ₐ[(Tw.O : Type)] S.carrier),
          down h (spMap (β'.comp (χ j)) ≫ T.y) =
            e S (B.map ⟨β'.restrictScalars R₀, hloc _ _ β'⟩ (D.fin.y j)) := by
        intro j β'
        rw [spc, hχ, down_nat, hy']
        exact (hn ⟨β'.restrictScalars R₀, hloc _ _ β'⟩ (D.fin.y j)).symm
      obtain ⟨w, hw⟩ := (hb S).2 (down h (spMap α ≫ T.y))
      have hwp : p • w = 0 := by
        rw [← e_pow hb ha, hw, down_pow_eq_one h]
        exact tors_pow T α
      obtain ⟨i, β, hβs, hβy, huniq⟩ := D.fin.univ S s w hwp
      let βO : (D.fin.AAx i).carrier →ₐ[(Tw.O : Type)] S.carrier :=
        { toRingHom := β.1.toRingHom
          commutes' := fun r => congrArg (fun φ : LHom Tw.O S => φ.1 r) hβs }
      refine ⟨i, βO, ?_, ?_, ?_⟩
      · apply tors_ext T
        apply (down_bij h).1
        rw [hcomp, ← hw, ← hβy]
        rfl
      · intro j β' hβ'
        have h1 : LHom.comp (⟨β'.restrictScalars R₀, hloc _ _ β'⟩ : LHom (D.fin.AAx j) S) (D.fin.sO j) = s := by
          apply Subtype.ext
          apply AlgHom.ext
          intro r
          exact β'.commutes r
        have h2 : B.map (⟨β'.restrictScalars R₀, hloc _ _ β'⟩ : LHom (D.fin.AAx j) S) (D.fin.y j) = w := by
          apply (hb S).1
          rw [← hcomp, hβ', hw]
        exact (huniq j _ h1 h2).1
      · intro β' hβ'
        have h1 : LHom.comp (⟨β'.restrictScalars R₀, hloc _ _ β'⟩ : LHom (D.fin.AAx i) S) (D.fin.sO i) = s := by
          apply Subtype.ext
          apply AlgHom.ext
          intro r
          exact β'.commutes r
        have h2 : B.map (⟨β'.restrictScalars R₀, hloc _ _ β'⟩ : LHom (D.fin.AAx i) S) (D.fin.y i) = w := by
          apply (hb S).1
          rw [← hcomp, hβ', hw]
        have h3 := eq_of_heq (huniq i _ h1 h2).2
        apply AlgHom.ext
        intro a
        exact DFunLike.congr_fun (congrArg Subtype.val h3) a
    have hidem : ∀ i (β' : (D.fin.AAx i).carrier →ₐ[(Tw.O : Type)] (D.fin.AAx i).carrier),
        β'.comp (χ i) = χ i → β' = AlgHom.id _ _ := by
      intro i β' hβ'
      obtain ⟨i0, β0, -, hu1, hu2⟩ := key (D.fin.AAx i) (χ i)
      have hi := hu1 i (AlgHom.id _ _) (AlgHom.id_comp _)
      subst hi
      rw [hu2 β' hβ', hu2 (AlgHom.id _ _) (AlgHom.id_comp _)]
    have hidx : ∀ i j (β' : (D.fin.AAx j).carrier →ₐ[(Tw.O : Type)] (D.fin.AAx i).carrier),
        β'.comp (χ j) = χ i → j = i := by
      intro i j β' hβ'
      obtain ⟨i0, β0, -, hu1, -⟩ := key (D.fin.AAx i) (χ i)
      rw [hu1 j β' hβ', hu1 i (AlgHom.id _ _) (AlgHom.id_comp _)]
    have hsurj : ∀ i, Function.Surjective (χ i) := by
      intro i
      let Rg := (χ i).range
      have hint : (algebraMap Rg (D.fin.AAx i).carrier).IsIntegral := fun a =>
        (Algebra.IsIntegral.isIntegral (R := (Tw.O : Type)) a).tower_top
      haveI hlh : IsLocalHom (algebraMap Rg (D.fin.AAx i).carrier) :=
        hint.isLocalHom Subtype.val_injective
      haveI hRl : IsLocalRing Rg := by
        refine { isUnit_or_isUnit_of_add_one := fun {a b} hab => ?_ }
        have hab' : algebraMap Rg (D.fin.AAx i).carrier a + algebraMap Rg (D.fin.AAx i).carrier b = 1 := by
          rw [← map_add, hab, map_one]
        rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab' with hu | hu
        · exact Or.inl (isUnit_of_map_unit _ _ hu)
        · exact Or.inr (isUnit_of_map_unit _ _ hu)
      haveI hRf : Module.Finite (Tw.O : Type) Rg :=
        Module.Finite.of_surjective (χ i).rangeRestrict.toLinearMap (AlgHom.rangeRestrict_surjective _)
      obtain ⟨i', β, hβ, -, -⟩ := key (LAlg.mk Rg) (χ i).rangeRestrict
      have hc : (Rg.val.comp β).comp (χ i') = χ i := by
        rw [AlgHom.comp_assoc, hβ]
        rfl
      have hi' := hidx i i' _ hc
      subst hi'
      have hid := hidem i' _ hc
      intro a
      have ha' : (Rg.val.comp β) a = a := by
        rw [hid]
        rfl
      obtain ⟨x, hx⟩ := (AlgHom.mem_range (χ i')).mp (β a).2
      exact ⟨x, hx.trans ha'⟩
    have hmax : ∀ i (M : Ideal T.A), M.IsMaximal → RingHom.ker (χ i) ≤ M →
        M = (IsLocalRing.maximalIdeal (D.fin.AAx i).carrier).comap (χ i) := by
      intro i M hM hK
      have hle : M ≤ (IsLocalRing.maximalIdeal (D.fin.AAx i).carrier).comap (χ i) := by
        intro x hx
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨u, hu'⟩ := hu.exists_right_inv
        obtain ⟨y, rfl⟩ := hsurj i u
        have h1 : x * y - 1 ∈ RingHom.ker (χ i) := by
          rw [RingHom.mem_ker, map_sub, map_mul, hu', map_one, sub_self]
        have h2 : (1 : T.A) ∈ M := by
          have h3 := M.sub_mem (M.mul_mem_right y hx) (hK h1)
          simpa using h3
        exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr h2)
      exact hM.eq_of_le (Ideal.comap_isMaximal_of_surjective _ (hsurj i)).ne_top hle
    have hcop : ∀ i j, i ≠ j → IsCoprime (RingHom.ker (χ i)) (RingHom.ker (χ j)) := by
      intro i j hij
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      obtain ⟨M, hM, hMle⟩ := Ideal.exists_le_maximal _ hne
      have hMi := hmax i M hM (le_trans le_sup_left hMle)
      have hMj := hmax j M hM (le_trans le_sup_right hMle)
      let I := RingHom.ker (χ i) ⊓ RingHom.ker (χ j)
      letI : Algebra R₀ T.A := ((algebraMap (Tw.O : Type) T.A).comp (algebraMap R₀ (Tw.O : Type))).toAlgebra
      haveI : IsScalarTower R₀ (Tw.O : Type) T.A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hIne : I ≠ ⊤ := by
        intro hI
        have h1 : (1 : T.A) ∈ RingHom.ker (χ i) := by
          have h2 : (1 : T.A) ∈ I := by
            rw [hI]
            exact Submodule.mem_top
          exact (Ideal.mem_inf.mp h2).1
        rw [RingHom.mem_ker, map_one] at h1
        exact one_ne_zero h1
      haveI : Nontrivial (T.A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
      haveI hQl : IsLocalRing (T.A ⧸ I) := by
        obtain ⟨N0, hN0⟩ := Ideal.exists_maximal (T.A ⧸ I)
        have hall : ∀ N : Ideal (T.A ⧸ I), N.IsMaximal →
            N.comap (Ideal.Quotient.mk I) = (IsLocalRing.maximalIdeal (D.fin.AAx i).carrier).comap (χ i) := by
          intro N hN
          have hc := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (K := N)
          have hIle : I ≤ N.comap (Ideal.Quotient.mk I) := by
            intro x hx
            rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
            exact N.zero_mem
          rcases (hc.isPrime.inf_le).mp hIle with h1 | h1
          · exact hmax i _ hc h1
          · rw [hmax j _ hc h1, ← hMj, hMi]
        refine IsLocalRing.of_unique_max_ideal ⟨N0, hN0, fun N hN => ?_⟩
        apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
        rw [hall N hN, hall N0 hN0]
      haveI : Module.Finite (Tw.O : Type) (T.A ⧸ I) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ (Tw.O : Type) I).toLinearMap
          (Ideal.Quotient.mkₐ_surjective (Tw.O : Type) I)
      obtain ⟨k, β, hβ, -, -⟩ := key (LAlg.mk (T.A ⧸ I)) (Ideal.Quotient.mkₐ (Tw.O : Type) I)
      have hπ : ∀ l, l = i ∨ l = j → k = l := by
        intro l hl
        have hIl : ∀ a ∈ I, χ l a = 0 := by
          intro a ha
          rcases hl with rfl | rfl
          · exact (Ideal.mem_inf.mp ha).1
          · exact (Ideal.mem_inf.mp ha).2
        apply hidx l k ((Ideal.Quotient.liftₐ I (χ l) hIl).comp β)
        rw [AlgHom.comp_assoc, hβ]
        apply AlgHom.ext
        intro a
        rfl
      exact hij ((hπ i (Or.inl rfl)).symm.trans (hπ j (Or.inr rfl)))
    haveI := D.fin.fι
    have hcrt : ∀ F : (i : D.fin.ι) → (D.fin.AAx i).carrier, ∃ a : T.A, ∀ i, χ i a = F i := by
      intro F
      choose b hb' using fun i => hsurj i (F i)
      obtain ⟨r, hr⟩ := Ideal.quotientInfToPiQuotient_surj (I := fun i => RingHom.ker (χ i))
        (fun i j hij => hcop i j hij) (fun i => Ideal.Quotient.mk _ (b i))
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨a, fun i => ?_⟩
      have hri := congrFun hr i
      rw [Ideal.quotientInfToPiQuotient_mk', Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero] at hri
      rw [hri, hb']
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨F, rfl⟩
      obtain ⟨a, ha'⟩ := hcrt F
      rw [SetLike.mem_coe, mem_torsFun T hφT]
      refine ⟨a, funext fun t => ?_⟩
      simp only [Dat.evAll]
      rw [hfac, ha']
    · intro f hf
      rw [mem_torsFun T hφT] at hf
      obtain ⟨a, rfl⟩ := hf
      apply Submodule.subset_span
      refine ⟨fun i => χ i a, funext fun t => ?_⟩
      simp only [Dat.evAll]
      rw [hfac]

end PositivityTheory.HtPt.Rf
