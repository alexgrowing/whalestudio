import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen

namespace GlobalTheory.Biadditive

section Tools

variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {L : LB X}

theorem triv_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : Triv (LB.LinComb L φ ε))
    (h : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (φ i) ^ ε i = ∏ i, k (φ' i) ^ ε' i) :
    Triv (LB.LinComb L φ' ε') := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := φ') (ε' := ε') h t ht
  exact ⟨t', ht'⟩

theorem triv_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : Triv (LB.LinComb L φ ε)) (H' : Triv (LB.LinComb L φ' ε')) :
    Triv (LB.LinComb L (K := K ⊕ K') (Sum.elim φ φ') (Sum.elim ε ε')) := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht'⟩ := H'
  exact ⟨_, DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht'⟩

theorem triv_inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : Triv (LB.LinComb L φ ε)) :
    Triv (LB.LinComb L φ (fun k => - ε k)) := by
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.invGen_isGen _ _ _ _ ht⟩

theorem triv_pull_comp {f : Y ⟶ X} (H : Triv (L.pull f)) {Z : Scheme.{0}} (r : Z ⟶ Y) :
    Triv (L.pull (r ≫ f)) := by
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.pullGen_isGen _ _ _ t ht r⟩

end Tools

section Cube

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem triv_of_faces (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {H₀ : LB A.left} (hH : H₀.IsLB)
    (hamp : Out.RelAmple A H₀) {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    (φ : K → ((G3 A).left ⟶ X)) (ε : K → ℤ)
    (face : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S),
      r ≫ (x3 A i).left = b ≫ η[A].left → TrivAt M φ ε r)
    (formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (b : Z ⟶ S),
      r ≫ (x3 A 0).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
        ∏ i, k (r ≫ φ i) ^ ε i = 1) :
    Triv (LB.LinComb M φ ε) := by
  have := hA.geomConnected
  have H := fibTriv_clopen M φ ε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom :=
      (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A H₀ hA hH hamp R (j ≫ A.hom) _ _ _
        (IsPullback.of_hasPullback _ _)).1
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ φ k) ε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ _ sm (isProjBy_tensor R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' => CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine face _ 1 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine face _ 0 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M φ ε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M φ ε (x3 A 2).left := fun t => by
    have hr : Set.range (S.fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := S.fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = S.fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec (S.residueField (A.hom t)) ⟶ S => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨S.residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      face _ 2 (pullback.snd _ g ≫ S.fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm)⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM φ ε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => formal _ (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

variable {B : Over S} (F : A ⊗ A ⟶ B)

def fourPts {T : Over S} (x x' y : T ⟶ A) : Fin 4 → (T.left ⟶ B.left) :=
  ![(lift (x * x') y ≫ F).left, (lift x y ≫ F).left, (lift x' y ≫ F).left, (lift 1 y ≫ F).left]

theorem comp_fourPts {T T' : Over S} (r : T' ⟶ T) (x x' y : T ⟶ A) (i : Fin 4) :
    r.left ≫ fourPts F x x' y i = fourPts F (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [fourPts, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, ← Category.assoc, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

theorem exists_over {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S)
    (h : r ≫ (x3 A i).left = b ≫ η[A].left) :
    ∃ x : Over.mk (r ≫ (G3 A).hom) ⟶ G3 A, x.left = r ∧ x ≫ x3 A i = 1 := by
  have hb : b = r ≫ (G3 A).hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  refine ⟨Over.homMk r rfl, rfl, ?_⟩
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

theorem prod_fourPts {T : Over S} {x x' : T ⟶ A} (y : T ⟶ A) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (T.left ⟶ B.left) → U) :
    ∏ i, k (fourPts F x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, fourPts, -Over.comp_left]
  · simp [Fin.prod_univ_four, fourPts, -Over.comp_left, mul_comm]

theorem triv_add (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {H₀ : LB A.left} (hH : H₀.IsLB)
    (hamp : Out.RelAmple A H₀) {M : LB B.left} (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (1 : A ⟶ A) (𝟙 A) ≫ F).left))
    (h₂ : Triv (M.pull (lift (𝟙 A) (1 : A ⟶ A) ≫ F).left)) {T : Over S} (x x' y : T ⟶ A) :
    Triv (LB.LinComb M (K := Fin 3)
      ![(lift (x * x') y ≫ F).left, (lift x y ≫ F).left, (lift x' y ≫ F).left] ![1, -1, -1]) := by
  have a₁ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift 1 y ≫ F).left) := fun y => by
    have := triv_pull_comp h₁ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have a₂ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift y 1 ≫ F).left) := fun y => by
    have := triv_pull_comp h₂ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S), i = 0 ∨ i = 1 →
      r ≫ (x3 A i).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ B.left) → U),
        ∏ i, k (r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
    intro Z r i b hi h U _ k
    obtain ⟨w, hw, h'⟩ := exists_over r i b h
    have := prod_fourPts F (x := w ≫ x3 A 0) (x' := w ≫ x3 A 1) (w ≫ x3 A 2)
      (hi.imp (fun e => e ▸ h') (fun e => e ▸ h')) U k
    simp only [← comp_fourPts, hw] at this
    exact this
  have cube := triv_of_faces hG hA hH hamp hM (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1]
    (fun r i b h => by
      by_cases hi : i = 0 ∨ i = 1
      · exact trivAt_of_formal hM r (formal r i b hi h)
      · obtain rfl : i = 2 := by omega
        obtain ⟨w, hw, h'⟩ := exists_over r 2 b h
        have e : (fun k => r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
            fourPts F (w ≫ x3 A 0) (w ≫ x3 A 1) 1 := funext fun k => by
          rw [← h', ← comp_fourPts, hw]
        unfold TrivAt
        rw [e]
        refine triv_of_formal hM (triv_mul (triv_mul (a₂ (w ≫ x3 A 0 * w ≫ x3 A 1)) (triv_inv (a₂ (w ≫ x3 A 0))))
          (triv_mul (triv_inv (a₂ (w ≫ x3 A 1))) (a₂ (T := Over.mk (r ≫ (G3 A).hom)) 1))) fun U _ k => ?_
        simp [Fin.prod_univ_four, fourPts, -Over.comp_left, Fintype.prod_sum_type, _root_.mul_assoc])
    (fun r b h => formal r 0 b (Or.inl rfl) h)
  have c₀ : TrivAt M (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1] (lift x (lift x' y)).left := by
    obtain ⟨t, ht⟩ := cube
    exact ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  have e : (fun k => (lift x (lift x' y)).left ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
      fourPts F x x' y := funext fun k => by
    rw [comp_fourPts]
    simp [x3]
  unfold TrivAt at c₀
  rw [e] at c₀
  refine triv_of_formal hM (triv_mul c₀ (triv_inv (a₁ y))) fun U _ k => ?_
  simp [Fin.prod_univ_four, Fin.prod_univ_three, fourPts, -Over.comp_left, Fintype.prod_sum_type]

end Cube

theorem biadditive_of_triv_axes :
    Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → ∀ (Pb : LB (G2 A).left), Pb.IsLB → (∃ t : (Pb.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Pb.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen := by
  intro hG S A _ _ H₀ hA hH hamp Pb hP h₁ h₂ T x x' y
  constructor
  · have := triv_add (𝟙 (A ⊗ A)) hG hA hH hamp hP (by rw [Category.comp_id]; exact h₁)
      (by rw [Category.comp_id]; exact h₂) x x' y
    simp only [Category.comp_id] at this
    exact this
  · have sw : ∀ {T : Over S} (a b : T ⟶ A), lift a b ≫ lift (snd A A) (fst A A) = lift b a := fun a b => by
      rw [comp_lift, lift_snd, lift_fst]
    have := triv_add (lift (snd A A) (fst A A)) hG hA hH hamp hP (by rw [sw]; exact h₂)
      (by rw [sw]; exact h₁) x x' y
    simp only [sw] at this
    exact this

end GlobalTheory.Biadditive
