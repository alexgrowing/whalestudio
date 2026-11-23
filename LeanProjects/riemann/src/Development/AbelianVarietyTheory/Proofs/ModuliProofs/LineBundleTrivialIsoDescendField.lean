import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsExtensionAffine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace FieldDescentGen

variable {X₀ X : Scheme.{0}}

theorem pull_le (M : LB X₀) (φ : X ⟶ X₀) (j : PUnit → M.ι) : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit) :=
  fun _ hy => mem_pull.1 hy

def secPull (M : LB X₀) (φ : X ⟶ X₀) (s : M.Sec) : (M.pull φ).Sec where
  f j := (φ.appLE _ _ (pull_le M φ j)).hom (s.f (j PUnit.unit))
  compat i j := by
    have h : (M.pull φ).U i ⊓ (M.pull φ).U j ≤ φ ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
      fun _ hy => ⟨pull_le M φ i hy.1, pull_le M φ j hy.2⟩
    have e := congrArg (φ.appLE _ _ h).hom (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at e
    have g : ((M.pull φ).g i j : Γ(X, (M.pull φ).U i ⊓ (M.pull φ).U j)) =
        (φ.appLE _ _ h).hom (M.g (i PUnit.unit) (j PUnit.unit)) := by
      have gu : (M.pull φ).g i j = res h (pullU φ _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
        (Fintype.prod_unique fun k : PUnit => (res h (pullU φ _ (M.g (i k) (j k)))) ^ (1 : ℤ)).trans (zpow_one _)
      exact congrArg Units.val gu
    rw [g]
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at e ⊢
    exact e

theorem exists_ratio {L : LB X} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) (s : L.Sec) :
    ∃ u : Γ(X, ⊤), ∀ j, s.f j =
      (X.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom u * (t.s j).val := by
  obtain ⟨u, hu⟩ := Out.TLinPf.glue L.U hL.cover (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e : res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j)⁻¹ =
        L.g i j * res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i)⁻¹ := by
      rw [map_inv, map_inv, ht i j, mul_inv, mul_inv_cancel_left]
    have e' : (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom ((t.s j)⁻¹).val =
        (L.g i j).val * (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom ((t.s i)⁻¹).val :=
      congrArg Units.val e
    rw [map_mul, map_mul, s.compat i j, e']
    ring)
  exact ⟨u, fun j => by rw [hu j, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]⟩

theorem isUnit_of_surjective (φ : X ⟶ X₀) [Surjective φ] {U : X₀.Opens} {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ U ≤ V) (a : Γ(X₀, U)) (ha : IsUnit ((φ.appLE U V h).hom a)) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X₀.toLocallyRingedSpace.toRingedSpace U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hy : y ∈ X.basicOpen ((φ.appLE U V h).hom a) := by
    rw [X.basicOpen_of_isUnit ha]; exact h' hx
  rw [Scheme.basicOpen_appLE] at hy
  exact (X₀.mem_basicOpen a _ hx).1 hy.2

def chartDiv (M N : LB X₀) (φ : X ⟶ X₀) :
    ChartPull ((LB.div N M).pull φ) (LB.div (N.pull φ) (M.pull φ)) (𝟙 X) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have a' := mem_pull.1 hj'
    refine (gm_pull_g (LB.div N M) φ (𝟙 X) y J J' hj hj').trans
      ((gm_div M N (𝟙 X ≫ φ) y (J PUnit.unit) (J' PUnit.unit) ⟨a, a'⟩).trans (Eq.symm ?_))
    refine (gm_div (M.pull φ) (N.pull φ) (𝟙 X) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, mem_pull.2 a'.1, mem_pull.2 a'.2⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹)
      (gm_pull_g N φ (𝟙 X) y _ _ (mem_pull.2 a.1) (mem_pull.2 a'.1))
      (gm_pull_g M φ (𝟙 X) y _ _ (mem_pull.2 a.2) (mem_pull.2 a'.2))

theorem exists_gen {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K)
    (φ : X ⟶ X₀) [Smooth p₀] [IsProper p₀] [GeometricallyConnected p₀] (H : IsPullback φ p p₀ (spMap i))
    (M : LB X₀) (hM : M.IsLB) (t : (M.pull φ).Gen) (ht : t.IsGen) : ∃ t : M.Gen, t.IsGen := by
  have hb : Function.Bijective p.appTop.hom := GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K X p
    (MorphismProperty.of_isPullback (P := @Smooth) H inferInstance)
    (MorphismProperty.of_isPullback (P := @IsProper) H inferInstance)
    (MorphismProperty.of_isPullback (P := @GeometricallyConnected) H inferInstance)
  have hF : IsField Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective p.appTop.hom hb)).symm.toMulEquiv.isField (Field.toIsField K)
  have : Surjective φ := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).1 X₀ X p₀ p φ H).2.2.1
  have hP := pull_isLB hM φ
  let ts : (M.pull φ).Sec := ⟨fun j => (t.s j).val, fun a b => congrArg Units.val (ht a b)⟩
  obtain ⟨n, c, s, hs⟩ := GlobalTheory.SectionsDescent.main K₀ K i X₀ X p₀ p φ M hM H ts
  choose u hu using fun a => exists_ratio hP t ht (secPull M φ (s a))
  have hne : ∃ a, u a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hF.nontrivial
    refine one_ne_zero (Out.TLinPf.eq_local (M.pull φ).U hP.cover 1 0 fun j => ?_)
    have h0 : (t.s j).val = 0 := by
      refine (hs j (pull_le M φ j)).trans (Finset.sum_eq_zero fun a _ => ?_)
      have e : (φ.appLE _ _ (pull_le M φ j)).hom ((s a).f (j PUnit.unit)) = _ := hu a j
      rw [e, hcon a, map_zero, zero_mul, mul_zero]
    rw [map_one, map_zero, ← (t.s j).mul_inv, h0, zero_mul]
  obtain ⟨a, ha⟩ := hne
  obtain ⟨v, hv⟩ := hF.mul_inv_cancel ha
  have hua : IsUnit (u a) := IsUnit.of_mul_eq_one v hv
  have hunit : ∀ k, IsUnit ((s a).f k) := fun k =>
    isUnit_of_surjective φ (pull_le M φ fun _ => k) (fun _ hy => mem_pull.2 hy) _ (by
      have e : (φ.appLE _ _ (pull_le M φ fun _ => k)).hom ((s a).f k) = _ := hu a fun _ => k
      rw [e]
      exact (hua.map _).mul (Units.isUnit _))
  exact ⟨⟨fun k => (hunit k).unit⟩, fun k l => Units.ext ((s a).compat k l)⟩

end FieldDescentGen

open FieldDescentGen in

theorem lb_gen_iso_descend_field : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  intro K₀ K _ _ i X₀ X p₀ p φ h₁ h₂ h₃ H
  refine ⟨fun M hM ⟨t, ht⟩ => exists_gen i p₀ p φ H M hM t ht, fun M N hM hN ⟨w, hw⟩ => ?_⟩
  exact exists_gen i p₀ p φ H (LB.div N M) (LB.isLB_div hN hM) _
    (GtBaseChange.genPull_isGen (chartDiv M N φ) hw)

end GlobalTheory
