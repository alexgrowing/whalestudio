import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesOfFgFieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleHeightProperSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.HtForm

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (GlobalTheory.AbLaw.rs_rs h₁ h₂ _)

theorem res_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (u : Γ(X, U)ˣ) : res h u = u :=
  Units.ext (GlobalTheory.AbLaw.rs_self h _)

theorem gen_reindex {X Y : Scheme.{0}} (L : LB X) {I J : Type} [Fintype I] [Fintype J] (e : J ≃ I)
    (φ : I → (Y ⟶ X)) (ε : I → ℤ) (h : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun i => φ (e i)) (fun i => ε (e i))), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  have hle : ∀ j : J → L.ι, LB.wchart L (fun i => φ (e i)) j ≤ LB.wchart L φ (fun i => j (e.symm i)) :=
    fun j y hy => Set.mem_iInter.2 fun i => by
      have := Set.mem_iInter.1 hy (e.symm i)
      simpa using this
  refine ⟨⟨fun j => res (hle j) (t.s _)⟩, fun j j' => ?_⟩
  have h1 := congrArg (res (inf_le_inf (hle j) (hle j'))) (ht (fun i => j (e.symm i)) (fun i => j' (e.symm i)))
  refine ((res_res _ _ _).trans (res_res _ _ _).symm).trans (h1.trans ((map_mul _ _ _).trans ?_))
  refine congrArg₂ (· * ·) ?_ ((res_res _ _ _).trans (res_res _ _ _).symm)
  refine (map_prod (res (inf_le_inf (hle j) (hle j'))) _ _).trans ?_
  simp only [LB.LinComb, map_zpow, res_res]
  refine Fintype.prod_equiv e.symm _ _ fun i => ?_
  obtain ⟨i, rfl⟩ := e.surjective i
  have key : ∀ (i' : J) (hi : i' = i) (a : LB.wchart L (fun i => φ (e i)) j ⊓ LB.wchart L (fun i => φ (e i)) j' ≤ φ (e i) ⁻¹ᵁ (L.U (j i') ⊓ L.U (j' i')))
      (b : LB.wchart L (fun i => φ (e i)) j ⊓ LB.wchart L (fun i => φ (e i)) j' ≤ φ (e i') ⁻¹ᵁ (L.U (j i') ⊓ L.U (j' i'))),
      res a (pullU (φ (e i)) _ (L.g (j i') (j' i'))) ^ ε (e i) = res b (pullU (φ (e i')) _ (L.g (j i') (j' i'))) ^ ε (e i') := by
    rintro _ rfl _ _
    rfl
  exact (congrArg (· ^ ε (e i)) (res_res _ _ _)).trans (key _ (e.symm_apply_apply i) _ _)

theorem gen_field {k : Type} [Field k] (M : LB (Sp k)) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by
  have hm : (IsLocalRing.closedPoint k : Sp k) ∈ (⨆ i, M.U i) := by
    rw [hM.cover]; trivial
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have htop : M.U i₀ = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi₀
  have hle : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl (htop ▸ le_top)
  refine ⟨⟨fun i => res (hle i) (M.g i i₀)⟩, fun i j => ?_⟩
  have h3 : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i₀ := le_inf le_rfl (htop ▸ le_top)
  have hc := congrArg (res h3) (hM.cocycle i j i₀)
  rw [map_mul, res_res, res_res, res_res, res_self] at hc
  rw [res_res, res_res]
  exact hc.symm

theorem comp_psum {S : Scheme.{0}} (A : Over S) [GrpObj A] {T T' : Over S} {n : ℕ} (h : T' ⟶ T) (x : Fin n → (T ⟶ A))
    (I : Finset (Fin n)) : h ≫ psum A x I =
      (((List.finRange n).filter (· ∈ I)).map fun k => h ≫ x k).prod := by
  simp only [psum]
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact MonObj.comp_one h
  | cons k l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons] at ih ⊢
    rw [← ih]
    exact MonObj.comp_mul h _ _

theorem sum_subsets_fin_three_expand (F : Finset (Fin 3) → ℤ) : ∑ I : ULift.{0} (Finset (Fin 3)), F I.down =
    F ∅ + F {0} + F {1} + F {2} + F {0, 1} + F {0, 2} + F {1, 2} + F {0, 1, 2} := by
  refine (Equiv.ulift.sum_comp F).trans ?_
  have : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
    decide
  rw [this]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  ring

theorem factor_of_const {k K : Type} [Field k] [Field K] [Algebra k K] (B : Over (Sp k))
    (x : Over.mk (spMap (algebraMap k K)) ⟶ B) {D : B.left.Opens} (hD : IsAffineOpen D)
    {I : Type} (O : I → ValuationSubring K) (hO : ∀ a : K, (∀ i, a ∈ O i) → a ∈ Set.range (algebraMap k K))
    (hx : Set.range x.left ⊆ D)
    (hb : ∀ i, ∃ b : Sp (O i) ⟶ B.left, spMap (O i).subtype ≫ b = x.left ∧ Set.range b ⊆ D) :
    ∃ c : 𝟙_ (Over (Sp k)) ⟶ B, x = toUnit _ ≫ c := by
  let ψ : Γ(B.left, D) ⟶ CommRingCat.of K :=
    Spec.preimage (IsOpenImmersion.lift hD.fromSpec x.left (by rw [hD.range_fromSpec]; exact hx))
  have hψ : Spec.map ψ ≫ hD.fromSpec = x.left := by
    simp only [ψ, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hmem : ∀ a, ψ.hom a ∈ Set.range (algebraMap k K) := fun a => hO _ fun i => by
    obtain ⟨b, hb1, hb2⟩ := hb i
    let χ : Γ(B.left, D) ⟶ CommRingCat.of (O i) :=
      Spec.preimage (IsOpenImmersion.lift hD.fromSpec b (by rw [hD.range_fromSpec]; exact hb2))
    have hχ : Spec.map χ ≫ hD.fromSpec = b := by
      simp only [χ, Spec.map_preimage]
      exact IsOpenImmersion.lift_fac _ _ _
    have : ψ = χ ≫ CommRingCat.ofHom (O i).subtype := by
      apply Spec.map_injective
      rw [← cancel_mono hD.fromSpec, hψ, Spec.map_comp, Category.assoc, hχ, hb1]
    rw [this]
    exact (χ.hom a).2
  let e : k ≃+* (algebraMap k K).range := RingEquiv.ofBijective (algebraMap k K).rangeRestrict
    ⟨fun a b h => (algebraMap k K).injective (congrArg Subtype.val h), (algebraMap k K).rangeRestrict_surjective⟩
  let ρ : Γ(B.left, D) →+* k := e.symm.toRingHom.comp (ψ.hom.codRestrict (algebraMap k K).range hmem)
  have hρ : ψ = CommRingCat.ofHom ρ ≫ CommRingCat.ofHom (algebraMap k K) := by
    ext a
    exact (congrArg Subtype.val (e.apply_symm_apply (ψ.hom.codRestrict (algebraMap k K).range hmem a))).symm
  have h1 : spMap (algebraMap k K) ≫ Spec.map (CommRingCat.ofHom ρ) ≫ hD.fromSpec = x.left := by
    rw [← hψ, hρ, Spec.map_comp, Category.assoc]
  have h2 : (Spec.map (CommRingCat.ofHom ρ) ≫ hD.fromSpec) ≫ B.hom = 𝟙 _ := by
    have : IsDominant (spMap (algebraMap k K)) := by
      rw [isDominant_iff]
      show DenseRange (PrimeSpectrum.comap (algebraMap k K))
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap k K).injective]
      exact bot_le
    refine ext_of_isDominant (spMap (algebraMap k K)) ?_
    rw [← Category.assoc, h1, Category.comp_id]
    exact Over.w x
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ρ) ≫ hD.fromSpec) h2, Over.OverMorphism.ext ?_⟩
  rw [← h1]
  rfl

theorem exists_generic {k : Type} [Field k] (B : Over (Sp k)) [IsIntegral B.left] [LocallyOfFiniteType B.hom] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra k K), (⊤ : IntermediateField k K).FG ∧
      ∃ P : Over.mk (spMap (algebraMap k K)) ⟶ B, IsDominant P.left := by
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let A : Type := Γ(B.left, U)
  letI : Algebra k A := (cstK B U).toAlgebra
  have hft : Algebra.FiniteType k A :=
    (B.hom.finiteType_appLE (isAffineOpen_top _) hU le_top).comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let K := FractionRing A
  have h1 : Algebra.EssFiniteType A K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors A)
  have h2 : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k A K
  refine ⟨K, inferInstance, inferInstance, IntermediateField.fg_top_iff.2 h2,
    Over.homMk (spMap (algebraMap A K) ≫ hU.fromSpec) ?_, ?_⟩
  · have h := IsAffineOpen.SpecMap_appLE_fromSpec B.hom (isAffineOpen_top _) hU le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    show (spMap (algebraMap A K) ≫ hU.fromSpec) ≫ B.hom = spMap (algebraMap k K)
    rw [Category.assoc, ← h, IsScalarTower.algebraMap_eq k A K, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  · have : IsDominant (spMap (algebraMap A K)) := by
      rw [isDominant_iff]
      show DenseRange (PrimeSpectrum.comap (algebraMap A K))
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective A K)]
      exact bot_le
    have : IsDominant hU.fromSpec := by
      rw [isDominant_iff, DenseRange, hU.range_fromSpec]
      exact U.isOpen.dense ⟨x, hxU⟩
    show IsDominant (spMap (algebraMap A K) ≫ hU.fromSpec)
    infer_instance

end GlobalTheory.SS.HtForm

namespace GlobalTheory.SS
open HtForm

theorem exists_quadraticForm_end : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∃ Q : (B ⟶ B) → ℤ, (∀ f g, Q (f * g) + Q (f * g⁻¹) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ (∀ f, IsMonHom f → Q f = 0 → f = 1) ∧ ∀ (F : B ⟶ B) (q : ℤ), PullPow F.left L q → ∀ f, Q (f ≫ F) = q * Q f := by
  intro k _ _ B _ hB L ⟨hL, hΘ, hsym, N, hN, hamp⟩
  have := hB.comm
  have := hB.smooth
  have hpr := hB.proper
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  obtain ⟨K, _, _, hK, P, hP⟩ := exists_generic B
  obtain ⟨Pl, hPl⟩ := GlobalTheory.T.exists_productFormula_places_of_fg_field k K hK
  obtain ⟨h, hrel, hpos⟩ := GlobalTheory.T.exists_lineBundle_height_properScheme k K Pl B hpr L hL
  have hrel' : ∀ (Z : Over (Sp k)), IsProper Z.hom → ∀ (I : Type) [Fintype I] (φ : I → (Z ⟶ B)) (ε : I → ℤ),
      (∃ t : LB.Gen (LB.LinComb L (fun i => (φ i).left) ε), t.IsGen) →
      ∀ z : Over.mk (spMap (algebraMap k K)) ⟶ Z, ∑ i, ε i * h (z ≫ φ i) = 0 := by
    intro Z hZ I _ φ ε ht z
    have := hrel Z hZ _ (fun i => φ ((Fintype.equivFin I).symm i)) (fun i => ε ((Fintype.equivFin I).symm i))
      (gen_reindex L (Fintype.equivFin I).symm (fun i => (φ i).left) ε ht) z
    rwa [(Fintype.equivFin I).symm.sum_comp fun i => ε i * h (z ≫ φ i)] at this
  have h1 : h 1 = 0 := by
    have := hrel (𝟙_ _) (by show IsProper (𝟙 _); infer_instance) 1 (fun _ => η[B]) (fun _ => 1)
      (gen_field (k := k) _ (LB.isLB_linComb hL _ _)) (toUnit _)
    rw [Fin.sum_univ_one, _root_.one_mul] at this
    exact this
  have hpull : ∀ (F : B ⟶ B) (q : ℤ), PullPow F.left L q → ∀ x, h (x ≫ F) = q * h x := by
    intro F q hF x
    have e : (fun i => ((![F, 𝟙 B] : Fin 2 → (B ⟶ B)) i).left) = ![F.left, 𝟙 B.left] := by
      funext i; fin_cases i <;> rfl
    have := hrel B hpr 2 ![F, 𝟙 B] ![1, -q] (by rw [e]; exact hF) x
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at this
    linarith
  have hinv : ∀ x, h x⁻¹ = h x := fun x => by
    have := hpull ι[B] 1 hsym x
    rw [_root_.one_mul] at this
    exact this
  have hpar : ∀ x y, h (x * y) + h (x * y⁻¹) = 2 * h x + 2 * h y := by
    intro x y
    have hp3 : IsProper (G3 B).hom := by
      have : IsProper (B ⊗ B).hom := by show IsProper (pullback.fst _ _ ≫ B.hom); infer_instance
      show IsProper (pullback.fst _ _ ≫ B.hom); infer_instance
    have := hrel' (G3 B) hp3 (ULift.{0} (Finset (Fin 3))) (fun I => psum B (x3 B) I.down)
      (fun I => (-1) ^ (3 - I.down.card)) hΘ (lift x (lift y y⁻¹))
    rw [sum_subsets_fin_three_expand fun I => (-1) ^ (3 - I.card) * h (lift x (lift y y⁻¹) ≫ psum B (x3 B) I)] at this
    have e0 : lift x (lift y y⁻¹) ≫ x3 B 0 = x := by simp [x3]
    have e1 : lift x (lift y y⁻¹) ≫ x3 B 1 = y := by simp [x3]
    have e2 : lift x (lift y y⁻¹) ≫ x3 B 2 = y⁻¹ := by simp [x3]
    have l0 : (List.finRange 3).filter (· ∈ (∅ : Finset (Fin 3))) = [] := by decide
    have l1 : (List.finRange 3).filter (· ∈ ({0} : Finset (Fin 3))) = [0] := by decide
    have l2 : (List.finRange 3).filter (· ∈ ({1} : Finset (Fin 3))) = [1] := by decide
    have l3 : (List.finRange 3).filter (· ∈ ({2} : Finset (Fin 3))) = [2] := by decide
    have l4 : (List.finRange 3).filter (· ∈ ({0, 1} : Finset (Fin 3))) = [0, 1] := by decide
    have l5 : (List.finRange 3).filter (· ∈ ({0, 2} : Finset (Fin 3))) = [0, 2] := by decide
    have l6 : (List.finRange 3).filter (· ∈ ({1, 2} : Finset (Fin 3))) = [1, 2] := by decide
    have l7 : (List.finRange 3).filter (· ∈ ({0, 1, 2} : Finset (Fin 3))) = [0, 1, 2] := by decide
    have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
    have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
    have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
    simp only [comp_psum] at this
    rw [l0, l1, l2, l3, l4, l5, l6, l7, c4, c5, c6, c7] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, e0, e1, e2, _root_.mul_one,
      mul_inv_cancel, h1, hinv, Finset.card_singleton, Finset.card_empty] at this
    norm_num at this
    linarith
  have hchart : ∀ x : Over.mk (spMap (algebraMap k K)) ⟶ B, ∃ s : LB.Sec (GlobalTheory.AbLaw.pw L N),
      Set.range x.left ⊆ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
    intro x
    obtain ⟨s, hs, ha⟩ := hamp (x.left (IsLocalRing.closedPoint K))
    refine ⟨s, ?_, ha⟩
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]
    exact hs
  refine ⟨fun f => h (P ≫ f), fun f g => ?_, fun f => ?_, fun f hf h0 => ?_, fun F q hF f => ?_⟩
  · simp only [MonObj.comp_mul, GrpObj.comp_inv]
    exact hpar _ _
  · obtain ⟨s, hs, -⟩ := hchart (P ≫ f)
    exact (hpos N s _ hN hs).1
  · obtain ⟨s, hs, ha⟩ := hchart (P ≫ f)
    obtain ⟨c, hc⟩ := factor_of_const B (P ≫ f) ha Pl.O hPl hs ((hpos N s _ hN hs).2 h0)
    have hf' : f = toUnit B ≫ c := by
      refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.hom
        ((Over.w f).trans (Over.w _).symm) P.left ?_)
      rw [← Over.comp_left, ← Over.comp_left, hc, ← Category.assoc, toUnit_unique (P ≫ toUnit B) (toUnit _)]
    have hc' : c = η[B] := by
      have := IsMonHom.one_hom f
      rw [hf', ← Category.assoc, toUnit_unique (η[B] ≫ toUnit B) (𝟙 _), Category.id_comp] at this
      exact this
    rw [hf', hc']
    rfl
  · show h (P ≫ f ≫ F) = q * h (P ≫ f)
    rw [← Category.assoc]
    exact hpull F q hF _
end GlobalTheory.SS
end
