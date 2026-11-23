import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU exists_gen_transfer germ_pull germ_div)

section Div

variable {X Y : Scheme.{0}}

private theorem mem_pull_lemma (M : LB X) (a : Y ⟶ X) (p : PUnit.{1} → M.ι) (y : Y)
    (h : y ∈ (M.pull a).U p) : a.base y ∈ M.U (p PUnit.unit) :=
  Set.mem_iInter.mp (show y ∈ (⋂ k, a.base ⁻¹' (M.U (p k) : Set X)) from h) PUnit.unit

private theorem mem_pull_of_lemma_2 (M : LB X) (a : Y ⟶ X) (p : PUnit.{1} → M.ι) (y : Y)
    (h : a.base y ∈ M.U (p PUnit.unit)) : y ∈ (M.pull a).U p :=
  show y ∈ (⋂ k, a.base ⁻¹' (M.U (p k) : Set X)) from
    Set.mem_iInter.mpr (fun k => by cases k; exact h)

theorem gen_div_pull (M N : LB X) (a : Y ⟶ X) (h : ∃ t : LB.Gen (LB.div M N), t.IsGen) :
    ∃ t : LB.Gen (LB.div (M.pull a) (N.pull a)), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  have hU : ∀ p : (LB.div (M.pull a) (N.pull a)).ι,
      (LB.div (M.pull a) (N.pull a)).U p ≤
        ((LB.div M N).pull a).U (fun u => (p.1 u, p.2 u)) := by
    intro p y hy
    obtain ⟨h1, h2⟩ := hy
    exact mem_pull_of_lemma_2 (LB.div M N) a (fun u => (p.1 u, p.2 u)) y
      (And.intro (mem_pull_lemma M a p.1 y h1) (mem_pull_lemma N a p.2 y h2))
  refine exists_gen_transfer (L := (LB.div M N).pull a) (L' := LB.div (M.pull a) (N.pull a))
    (fun p u => (p.1 u, p.2 u)) hU ?_ ⟨LB.genPull _ t a, LB.isGen_genPull _ t ht a⟩
  intro i j y hy
  obtain ⟨⟨hMi, hNi⟩, ⟨hMj, hNj⟩⟩ := id hy
  have hMi' := mem_pull_lemma M a i.1 y hMi
  have hNi' := mem_pull_lemma N a i.2 y hNi
  have hMj' := mem_pull_lemma M a j.1 y hMj
  have hNj' := mem_pull_lemma N a j.2 y hNj
  have hM : y ∈ a ⁻¹ᵁ (M.U (i.1 PUnit.unit) ⊓ M.U (j.1 PUnit.unit)) := And.intro hMi' hMj'
  have hN : y ∈ a ⁻¹ᵁ (N.U (i.2 PUnit.unit) ⊓ N.U (j.2 PUnit.unit)) := And.intro hNi' hNj'
  have hD : y ∈ a ⁻¹ᵁ ((LB.div M N).U (i.1 PUnit.unit, i.2 PUnit.unit) ⊓
      (LB.div M N).U (j.1 PUnit.unit, j.2 PUnit.unit)) :=
    And.intro (And.intro hMi' hNi') (And.intro hMj' hNj')
  refine (germ_div _ _ i j y hy).trans ?_
  refine Eq.trans (congrArg₂ (fun u v => u * v⁻¹)
    ((germ_pull M a i.1 j.1 y (And.intro hMi hMj) hM).trans (gU_pullU a _ y hM _))
    ((germ_pull N a i.2 j.2 y (And.intro hNi hNj) hN).trans (gU_pullU a _ y hN _))) ?_
  refine Eq.trans ?_ ((germ_pull (LB.div M N) a (fun u => (i.1 u, i.2 u))
    (fun u => (j.1 u, j.2 u)) y _ hD).trans (gU_pullU a _ y hD _)).symm
  refine Eq.trans ?_ (congrArg (Units.map _) (germ_div M N _ _ _ hD)).symm
  simp only [map_mul, map_inv]

end Div

section Div2

variable {X Y : Scheme.{0}}

theorem gen_div_div_pull (A B C : LB X) (a : Y ⟶ X)
    (h : ∃ t : LB.Gen (LB.div (LB.div A B) C), t.IsGen) :
    ∃ t : LB.Gen (LB.div (LB.div (A.pull a) (B.pull a)) (C.pull a)), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  have hU : ∀ p : (LB.div (LB.div (A.pull a) (B.pull a)) (C.pull a)).ι,
      (LB.div (LB.div (A.pull a) (B.pull a)) (C.pull a)).U p ≤
        ((LB.div (LB.div A B) C).pull a).U (fun u => ((p.1.1 u, p.1.2 u), p.2 u)) := by
    intro p y hy
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    exact mem_pull_of_lemma_2 (LB.div (LB.div A B) C) a (fun u => ((p.1.1 u, p.1.2 u), p.2 u)) y
      (And.intro (And.intro (mem_pull_lemma A a p.1.1 y h1) (mem_pull_lemma B a p.1.2 y h2))
        (mem_pull_lemma C a p.2 y h3))
  refine exists_gen_transfer (L := (LB.div (LB.div A B) C).pull a)
    (L' := LB.div (LB.div (A.pull a) (B.pull a)) (C.pull a))
    (fun p u => ((p.1.1 u, p.1.2 u), p.2 u)) hU ?_ ⟨LB.genPull _ t a, LB.isGen_genPull _ t ht a⟩
  intro i j y hy
  obtain ⟨⟨⟨hAi, hBi⟩, hCi⟩, ⟨⟨hAj, hBj⟩, hCj⟩⟩ := id hy
  have hAi' := mem_pull_lemma A a i.1.1 y hAi
  have hBi' := mem_pull_lemma B a i.1.2 y hBi
  have hCi' := mem_pull_lemma C a i.2 y hCi
  have hAj' := mem_pull_lemma A a j.1.1 y hAj
  have hBj' := mem_pull_lemma B a j.1.2 y hBj
  have hCj' := mem_pull_lemma C a j.2 y hCj
  have hA : y ∈ a ⁻¹ᵁ (A.U (i.1.1 PUnit.unit) ⊓ A.U (j.1.1 PUnit.unit)) := And.intro hAi' hAj'
  have hB : y ∈ a ⁻¹ᵁ (B.U (i.1.2 PUnit.unit) ⊓ B.U (j.1.2 PUnit.unit)) := And.intro hBi' hBj'
  have hC : y ∈ a ⁻¹ᵁ (C.U (i.2 PUnit.unit) ⊓ C.U (j.2 PUnit.unit)) := And.intro hCi' hCj'
  have hD : y ∈ a ⁻¹ᵁ ((LB.div (LB.div A B) C).U ((i.1.1 PUnit.unit, i.1.2 PUnit.unit), i.2 PUnit.unit) ⊓
      (LB.div (LB.div A B) C).U ((j.1.1 PUnit.unit, j.1.2 PUnit.unit), j.2 PUnit.unit)) :=
    And.intro (And.intro (And.intro hAi' hBi') hCi') (And.intro (And.intro hAj' hBj') hCj')
  have hE : a.base y ∈ (LB.div A B).U (i.1.1 PUnit.unit, i.1.2 PUnit.unit) ⊓
      (LB.div A B).U (j.1.1 PUnit.unit, j.1.2 PUnit.unit) :=
    And.intro (And.intro hAi' hBi') (And.intro hAj' hBj')
  refine (germ_div _ _ i j y hy).trans ?_
  refine Eq.trans (congrArg₂ (fun u v => u * v⁻¹)
    ((germ_div _ _ i.1 j.1 y (And.intro (And.intro hAi hBi) (And.intro hAj hBj))).trans
      (congrArg₂ (fun u v => u * v⁻¹)
        ((germ_pull A a i.1.1 j.1.1 y (And.intro hAi hAj) hA).trans (gU_pullU a _ y hA _))
        ((germ_pull B a i.1.2 j.1.2 y (And.intro hBi hBj) hB).trans (gU_pullU a _ y hB _))))
    ((germ_pull C a i.2 j.2 y (And.intro hCi hCj) hC).trans (gU_pullU a _ y hC _))) ?_
  refine Eq.trans ?_ ((germ_pull (LB.div (LB.div A B) C) a (fun u => ((i.1.1 u, i.1.2 u), i.2 u))
    (fun u => ((j.1.1 u, j.1.2 u), j.2 u)) y _ hD).trans (gU_pullU a _ y hD _)).symm
  refine Eq.trans ?_ (congrArg (Units.map _) ((germ_div (LB.div A B) C _ _ _ hD).trans
    (congrArg (fun u => u * _) (germ_div A B _ _ _ hE)))).symm
  simp only [map_mul, map_inv]

end Div2

section Ext

attribute [local instance] SplitExt.free SplitExt.finite

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)

instance commB : IsCommMonObj E.B := E.isAbelian.comm

instance commB' : IsCommMonObj ((Over.pullback f).obj E.B) := Functor.isCommMonObj_obj

def mB : CubeMap ((Over.pullback f).obj E.B) E.B := cubeMapOf (isGrpPullback_pullback E.B f)

theorem mB_F : (mB f E).F = pullback.fst E.B.hom f := rfl

def O' (χ : E.X) : RigLB ((Over.pullback f).obj E.B) :=
  (mB f E).rigLB (E.O χ) (LB.isLB_pull (E.O χ).isLB _)
    (LBxP.isGen_pullAlong (E.O χ).L (mB f E).F (mB f E).e (fun _ : PUnit => eSec E.B) (fun _ => 1)
      (fun _ => eSec _) (fun _ => (mB f E).e_comm) (E.O χ).rig (E.O χ).rigGen)

def F2 : (G2 ((Over.pullback f).obj E.B)).left ⟶ (G2 E.B).left :=
  (lift (pushPt (isGrpPullback_pullback E.B f).1.w (x2 ((Over.pullback f).obj E.B) 0))
    (pushPt (isGrpPullback_pullback E.B f).1.w (x2 ((Over.pullback f).obj E.B) 1))).left

theorem pullbackSquare_partialSum (I : Finset (Fin 2)) :
    (psum ((Over.pullback f).obj E.B) (x2 ((Over.pullback f).obj E.B)) I).left ≫ (mB f E).F =
      F2 f E ≫ (psum E.B (x2 E.B) I).left := by
  refine psum_push (isGrpPullback_pullback E.B f) _ _ _ (fun i => ?_) I
  fin_cases i <;> simp [x2]

def pullExt : SplitExt S' where
  B := (Over.pullback f).obj E.B
  isAbelian := TLinPf.isAb_pullback f E.B E.isAbelian
  X := E.X
  O := O' f E
  addIso := fun χ χ' => gen_div_div_pull _ _ _ _ (E.addIso χ χ')
  zeroTriv := by
    obtain ⟨t, ht⟩ := E.zeroTriv
    exact ⟨LB.genPull _ t _, LB.isGen_genPull _ t ht _⟩
  primitive := fun χ => by
    obtain ⟨t, ht⟩ := E.primitive χ
    exact ⟨GeneratorPullback.pullAlong (E.O χ).L (mB f E).F (F2 f E) _ _ _ (fun I => pullbackSquare_partialSum f E I.down) t,
      LBxP.isGen_pullAlong _ _ _ _ _ _ _ t ht⟩

end Ext

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
