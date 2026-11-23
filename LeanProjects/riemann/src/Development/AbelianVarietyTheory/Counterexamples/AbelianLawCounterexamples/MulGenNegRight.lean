import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.TrivialBiextension

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

universe u

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BiextSignTwist

theorem res_neg {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    res h (-a) = -res h a := by
  ext; simp [res]

theorem pullU_neg {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)ˣ) :
    pullU f U (-a) = -pullU f U a := by
  ext; simp [pullU]

def negGen {X : Scheme.{u}} {L : LB X} (t : LB.Gen L) : LB.Gen L := ⟨fun i => -t.s i⟩

theorem negGen_isGen {X : Scheme.{u}} {L : LB X} {t : LB.Gen L} (h : t.IsGen) :
    (negGen t).IsGen := fun i j => by
  simp only [negGen, res_neg, mul_neg]
  rw [h i j]

section
variable {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

theorem negGen_negGen (t : LB.Gen L) : negGen (negGen t) = t := by
  cases t; simp [negGen]

theorem pullGen_neg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen L φ ε (negGen t) h = negGen (LB.pullGen L φ ε t h) :=
  congrArg LB.Gen.mk (funext fun _ => (congrArg (res _) (pullU_neg _ _ _)).trans (res_neg _ _))

theorem mulGen_neg_left (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.mulGen L φ ε φ' ε' (negGen t) t' = negGen (LB.mulGen L φ ε φ' ε' t t') :=
  congrArg LB.Gen.mk (funext fun _ => (congrArg (· * _) (res_neg _ _)).trans (neg_mul _ _))

theorem mulGen_neg_right (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.mulGen L φ ε φ' ε' t (negGen t') = negGen (LB.mulGen L φ ε φ' ε' t t') :=
  congrArg LB.Gen.mk (funext fun _ => (congrArg (_ * ·) (res_neg _ _)).trans (mul_neg _ _))

theorem corr_neg {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') : LB.Gen.Corr L φ ε φ' ε' (negGen t) (negGen t') :=
  fun j j' a b c => (res_neg _ _).trans ((congrArg Neg.neg (h j j' a b c)).trans (res_neg _ _).symm)

end

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def negBiext {P : LB (G2 G).left} (β : IsBiext G P) : IsBiext G P where
  isLB := β.isLB
  law1 := negGen β.law1
  law2 := negGen β.law2
  isGen1 := negGen_isGen β.isGen1
  isGen2 := negGen_isGen β.isGen2
  assoc1 := by
    simp only [pullGen_neg, mulGen_neg_left, mulGen_neg_right, negGen_negGen]; exact β.assoc1
  comm1 := by simp only [pullGen_neg]; exact corr_neg _ β.comm1
  assoc2 := by
    simp only [pullGen_neg, mulGen_neg_left, mulGen_neg_right, negGen_negGen]; exact β.assoc2
  comm2 := by simp only [pullGen_neg]; exact corr_neg _ β.comm2
  compat := by
    simp only [pullGen_neg, mulGen_neg_left, mulGen_neg_right, negGen_negGen]
    exact corr_neg _ β.compat

abbrev lamφ : ULift.{u} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) :=
  fun I => (psum G (x2 G) I.down).left

def LawIsCube (L : RigLB G) (c : CubicalStr G L)
    (ψ : ULift.{u} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (law : LB.Gen (LB.LinComb (abelian₂ G L.L) ψ lawε)) : Prop :=
  ∀ (J : ULift.{u} (Fin 3) → ULift.{u} (Finset (Fin 2)) → L.L.ι) (j : thK → L.L.ι),
    (∀ k I k' I', ψ k ≫ lamφ G I = ψ k' ≫ lamφ G I' → J k I = J k' I') →
    LB.Coh L.L (thφ G (x3 G)) j →
    (∀ k I I', ψ k ≫ lamφ G I = thφ G (x3 G) I' → J k I = j I') →
    res (inf_le_left : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (law.s J) =
    res (inf_le_right : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (c.t.s j)

def AbelianLawCounterexample : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L),
    ∃ β : IsBiext G (abelian₂ G L.L), LawIsCube G L c _ β.law1 ∧ LawIsCube G L c _ β.law2

theorem not_both (h2 : IsUnit (2 : Γ(S, ⊤))) [Nonempty S] (L : RigLB G) (c : CubicalStr G L)
    (ψ : ULift.{u} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (law : LB.Gen (LB.LinComb (abelian₂ G L.L) ψ lawε)) (h : LawIsCube G L c ψ law) :
    ¬ LawIsCube G L c ψ (negGen law) := by
  intro h'
  obtain ⟨s⟩ : Nonempty S := inferInstance
  let e : 𝟙_ (Over S) ⟶ G3 G := lift η[G] (lift η[G] η[G])
  let z : (G3 G).left := e.left s
  have hc : ∀ x : G.left, ∃ i, x ∈ L.L.U i := fun x => by
    have : x ∈ (⨆ i, L.L.U i) := by rw [L.isLB.cover]; trivial
    exact Opens.mem_iSup.1 this
  choose idx hidx using hc
  let J : ULift.{u} (Fin 3) → ULift.{u} (Finset (Fin 2)) → L.L.ι :=
    fun k I => idx ((ψ k ≫ lamφ G I) z)
  let j : thK → L.L.ι := fun I => idx ((thφ G (x3 G) I) z)
  have a1 : ∀ k I k' I', ψ k ≫ lamφ G I = ψ k' ≫ lamφ G I' → J k I = J k' I' :=
    fun k I k' I' e => by simp only [J, e]
  have a2 : LB.Coh L.L (thφ G (x3 G)) j := fun I I' e => by simp only [j, e]
  have a3 : ∀ k I I', ψ k ≫ lamφ G I = thφ G (x3 G) I' → J k I = j I' :=
    fun k I I' e => by simp only [J, j, e]
  have e1 := h J j a1 a2 a3
  have e2 := h' J j a1 a2 a3
  rw [← e1] at e2
  replace e2 := (res_neg _ _).symm.trans e2
  set W := LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j with hW
  have hz : z ∈ W := by
    refine ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun I => ?_, Set.mem_iInter.2 fun I => hidx _⟩
    have := hidx ((ψ k ≫ lamφ G I) z)
    rw [Scheme.Hom.comp_apply] at this
    exact this
  haveI : Nonempty W := ⟨⟨z, hz⟩⟩
  have h2' : IsUnit (2 : Γ((G3 G).left, W)) := by
    have := (h2.map ((G3 G).hom.appTop).hom).map
      ((G3 G).left.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
    simpa only [map_ofNat] using this
  have key : ∀ a : Γ((G3 G).left, W)ˣ, -a = a → False := fun a e2 => by
    have e3 : (2 : Γ((G3 G).left, W)) * (a : Γ((G3 G).left, W)) = 0 := by
      have := congrArg Units.val e2
      rw [Units.val_neg] at this
      linear_combination -this
    exact (h2'.mul a.isUnit).ne_zero e3
  exact key _ e2

section Trivial
open GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension (trivLB pull_one mul_one' corr_one isGen_one)

theorem linComb_g_one {X Y : Scheme.{u}} (L : LB X) (hL : ∀ i j, L.g i j = 1) {K : Type u}
    [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j) : (LB.LinComb L φ ε).g i j = 1 :=
  Finset.prod_eq_one fun k _ =>
    (congrArg (· ^ ε k) ((congrArg _ ((congrArg _ (hL _ _)).trans (map_one _))).trans
      (map_one _))).trans (one_zpow _)

theorem isGen_one' {X : Scheme.{u}} (L : LB X) (hL : ∀ i j, L.g i j = 1) :
    LB.Gen.IsGen (L := L) ⟨fun _ => 1⟩ := fun i j => by
  rw [hL]
  exact (map_one _).trans ((_root_.one_mul _).trans (map_one _)).symm

theorem isLB_of_g_one {X : Scheme.{u}} (L : LB X) (hL : ∀ i j, L.g i j = 1)
    (hc : ⨆ i, L.U i = ⊤) : L.IsLB :=
  ⟨hc, fun _ => by rw [hL, map_one], fun _ _ _ => by
    rw [hL, hL, hL, map_one, map_one, map_one, _root_.mul_one]⟩

def oneRig : RigLB G :=
  ⟨trivLB _, ⟨fun _ => 1⟩, isLB_of_g_one _ (fun _ _ => rfl) (@iSup_const _ PUnit _ _ _), isGen_one _ _⟩

def oneCub : CubicalStr G (oneRig G) where
  t := ⟨fun _ => 1⟩
  isGen := isGen_one _ _
  face := fun _ => corr_one _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (fun _ => rfl)
  cubeSymmetric_swap_first := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  cubeSymmetric_swap_last := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  cocycle := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))

theorem lam_g_one (i j) : (abelian₂ G (oneRig G).L).g i j = 1 :=
  linComb_g_one (trivLB _) (fun _ _ => rfl) _ _ i j

def oneBiext : IsBiext G (abelian₂ G (oneRig G).L) where
  isLB := isLB_of_g_one _ (lam_g_one G) (top_le_iff.1 fun _ _ =>
    Opens.mem_iSup.2 ⟨fun _ => PUnit.unit, Set.mem_iInter.2 fun _ => trivial⟩)
  law1 := ⟨fun _ => 1⟩
  law2 := ⟨fun _ => 1⟩
  isGen1 := isGen_one' _ (linComb_g_one _ (lam_g_one G) _ _)
  isGen2 := isGen_one' _ (linComb_g_one _ (lam_g_one G) _ _)
  comm1 := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  comm2 := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  assoc1 := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
  assoc2 := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
  compat := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _
      (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
      (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _
      (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
      (pull_one _ _ _ _ _ fun _ => rfl))

theorem main (h2 : IsUnit (2 : Γ(S, ⊤))) [Nonempty S] :
    (LawIsCube G _ (oneCub G) _ (oneBiext G).law1 ∧ LawIsCube G _ (oneCub G) _ (oneBiext G).law2) ∧
    ¬ LawIsCube G _ (oneCub G) _ (negBiext G (oneBiext G)).law1 :=
  have h1 : LawIsCube G _ (oneCub G) _ (oneBiext G).law1 :=
    fun _ _ _ _ _ => (map_one _).trans (map_one _).symm
  ⟨⟨h1, fun _ _ _ _ _ => (map_one _).trans (map_one _).symm⟩, not_both G h2 _ _ _ _ h1⟩

end Trivial

end GlobalTheory.BiextSignTwist
