import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.HostConjugateIdeal

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback

open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal

section Mumford

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev LamK : Type := ULift.{0} (Finset (Fin 2))

def lamPt {T : Over S} (x z : T ⟶ G) : LamK → (T.left ⟶ G.left) :=
  fun I => (psum G ![x, z] I.down).left

def lamExp : LamK → ℤ := fun I => (-1) ^ (2 - I.down.card)

def lamAt (L : LB G.left) {T : Over S} (x z : T ⟶ G) : LB T.left :=
  LB.LinComb L (lamPt G x z) lamExp

theorem lamAt_fst_snd (L : LB G.left) : lamAt G L (fst G G) (snd G G) = abelian₂ G L := rfl

theorem lamPt_comp {T T' : Over S} (h : T' ⟶ T) (x z : T ⟶ G) (I : LamK) :
    h.left ≫ lamPt G x z I = lamPt G (h ≫ x) (h ≫ z) I := by
  simp only [lamPt, psum]
  rw [← Over.comp_left, ← foldr_padd_pre]
  congr 2
  funext k acc
  fin_cases k <;> rfl

def adjPt (a b : G ⟶ G) : LamK ⊕ LamK → ((G ⊗ G).left ⟶ G.left) :=
  Sum.elim (lamPt G (fst G G) (snd G G ≫ b)) (lamPt G (fst G G ≫ a) (snd G G))

def adjExp : LamK ⊕ LamK → ℤ := Sum.elim lamExp (fun I => -lamExp I)

def IsAdjointPair (L : LB G.left) (a b : G ⟶ G) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L (adjPt G a b) adjExp), t.IsGen ∧
    LB.Gen.Corr L _ _ _ _
      (LB.pullGen L (adjPt G a b) adjExp t (lift (pzero G G) (𝟙 G)).left) (LB.oneGen L) ∧
    LB.Gen.Corr L _ _ _ _
      (LB.pullGen L (adjPt G a b) adjExp t (lift (𝟙 G) (pzero G G)).left) (LB.oneGen L)

def primPt (w : G ⟶ G) : PUnit.{1} ⊕ LamK → (G.left ⟶ G.left) :=
  Sum.elim (fun _ => 𝟙 G.left) (lamPt G (𝟙 G) w)

def primExp : PUnit.{1} ⊕ LamK → ℤ := Sum.elim (fun _ => 1) (fun I => -lamExp I)

def IsPrimitiveFor (L : RigLB G) (w : G ⟶ G) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L.L (primPt G w) primExp), t.IsGen ∧
    LB.Gen.Corr L.L _ _ (fun _ : PUnit.{1} => eSec G) (fun _ => 1)
      (LB.pullGen L.L (primPt G w) primExp t (eSec G)) L.rig

theorem sum_lamK (f : LamK → ℤ) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.sum_comp]
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]
  rfl

theorem lamPt_values {T : Over S} (x z : T ⟶ G) :
    lamPt G x z ⟨∅⟩ = (1 : T ⟶ G).left ∧ lamPt G x z ⟨{0}⟩ = x.left ∧
      lamPt G x z ⟨{1}⟩ = z.left ∧ lamPt G x z ⟨{0, 1}⟩ = (x * z).left := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change (x * 1).left = _
    rw [_root_.mul_one]
  · change (z * 1).left = _
    rw [_root_.mul_one]
  · change (x * (z * 1)).left = _
    rw [_root_.mul_one]

open scoped Classical in
theorem sum_lam {T : Over S} (x z : T ⟶ G) (h : x = 1 ∨ z = 1) (ψ : T.left ⟶ G.left) :
    (∑ I, if lamPt G x z I = ψ then lamExp I else 0) = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := lamPt_values G x z
  have e0 : lamExp ⟨∅⟩ = 1 := rfl
  have e1 : lamExp ⟨{0}⟩ = -1 := rfl
  have e2 : lamExp ⟨{1}⟩ = -1 := rfl
  have e3 : lamExp ⟨{0, 1}⟩ = 1 := rfl
  rw [sum_lamK, h0, h1, h2, h3, e0, e1, e2, e3]
  rcases h with rfl | rfl
  · rw [_root_.one_mul]; split_ifs <;> simp
  · rw [_root_.mul_one]; split_ifs <;> simp

theorem sameSum_adj (a b : G ⟶ G) [IsMonHom a] [IsMonHom b] {T : Over S} (h : T ⟶ G ⊗ G)
    (hh : h ≫ fst G G = 1 ∨ h ≫ snd G G = 1) :
    LB.SameSum (fun k => h.left ≫ adjPt G a b k) adjExp
      (PEmpty.elim : PEmpty.{1} → (T.left ⟶ G.left)) PEmpty.elim := by
  classical
  intro ψ
  have ha : (1 : T ⟶ G) ≫ a = 1 := by simp [Hom.one_def]
  have hb : (1 : T ⟶ G) ≫ b = 1 := by simp [Hom.one_def]
  have h1 := sum_lam G (h ≫ fst G G) (h ≫ snd G G ≫ b)
    (hh.imp id fun e => by rw [← Category.assoc, e, hb]) ψ
  have h2 := sum_lam G (h ≫ fst G G ≫ a) (h ≫ snd G G)
    (hh.imp (fun e => by rw [← Category.assoc, e, ha]) id) ψ
  rw [Fintype.sum_sum_type]
  simp only [adjPt, adjExp, Sum.elim_inl, Sum.elim_inr, lamPt_comp, Finset.univ_eq_empty,
    Finset.sum_empty]
  have h3 : ∀ (p : Prop) [Decidable p] (n : ℤ), (if p then -n else 0) = -(if p then n else 0) := by
    intro p _ n; split_ifs <;> simp
  simp only [h3, Finset.sum_neg_distrib]
  rw [h1, h2]; rfl

theorem sameSum_prim (w : G ⟶ G) :
    LB.SameSum (fun k => eSec G ≫ primPt G w k) primExp
      (fun _ : PUnit.{1} => eSec G) (fun _ => 1) := by
  classical
  intro ψ
  have h1 := sum_lam G (η[G] ≫ 𝟙 G) (η[G] ≫ w) (Or.inl (by simp [Hom.one_def])) ψ
  rw [Fintype.sum_sum_type]
  simp only [primPt, primExp, Sum.elim_inl, Sum.elim_inr, eSec, lamPt_comp, Category.comp_id] at h1 ⊢
  have h3 : ∀ (p : Prop) [Decidable p] (n : ℤ), (if p then -n else 0) = -(if p then n else 0) := by
    intro p _ n; split_ifs <;> simp
  simp only [h3, Finset.sum_neg_distrib]
  erw [h1]
  rw [neg_zero, add_zero]
  rfl

end Mumford

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Triple (H : Host E) (S : Scheme.{0}) where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semiAbelian : IsSemiAbelian G

  iota : OAct (𝓞 E) G

  L : RigLB G

  cube : CubicalStr G L
  symm : L.IsSymmetric
  adjoint : ∀ a : 𝓞 E, IsAdjointPair G L.L (iota.act a) (iota.act (conjO E a))
  primitive : IsPrimitiveFor G L (iota.act H.w₀)

attribute [instance] Triple.grp Triple.comm

namespace Triple

variable {H : Host E} {S S' : Scheme.{0}}

def P (t : Triple H S) : LB (t.G ⊗ t.G).left := abelian₂ t.G t.L.L

structure Pull (t' : Triple H S') (t : Triple H S) (f : S' ⟶ S) where

  φ : t'.G.left ⟶ t.G.left
  isGrpPullback : IsGrpPullback t'.G t.G f φ
  act_comm : ∀ a : 𝓞 E, (t'.iota.act a).left ≫ φ = φ ≫ (t.iota.act a).left
  bundle : ∃ m : CubeMap t'.G t.G, m.F = φ ∧ m.e = f ∧ m.IsPullCubical t'.cube t.cube

structure PullIso (t' : Triple H S') (t : Triple H S) (f : S' ⟶ S) where

  m : CubeMap t'.G t.G
  base : m.e = f
  isGrpPullback : IsGrpPullback t'.G t.G f m.F
  act_comm : ∀ a : 𝓞 E, (t'.iota.act a).left ≫ m.F = m.F ≫ (t.iota.act a).left

  w : LB.Iso t'.L.L (t.L.L.pull m.F)
  isGen : w.IsGen
  rig : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec t'.G) (fun _ => 1))
    t'.L.rig (m.rigPull t.L.L t.L.rig)
  cube : LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cube.t
    (m.thetaPull t.L.L t.cube.t)

def PullIso.toPull {t' : Triple H S'} {t : Triple H S} {f : S' ⟶ S} (p : PullIso t' t f) :
    Pull t' t f :=
  ⟨p.m.F, p.isGrpPullback, p.act_comm, p.m, rfl, p.base, p.w, p.isGen, p.rig, p.cube⟩

theorem PullIso.toPull_surjective {t' : Triple H S'} {t : Triple H S} {f : S' ⟶ S} :
    Function.Surjective (PullIso.toPull (t' := t') (t := t) (f := f)) := by
  rintro ⟨φ, h1, h2, m, rfl, h3, w, h4, h5, h6⟩
  exact ⟨⟨m, h3, h1, h2, w, h4, h5, h6⟩, rfl⟩

theorem cubeMap_coord {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (i : Fin 3) :
    m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := by
  have h := m.psum_comm {i}
  have e : psum G (x3 G) {i} = x3 G i := by
    fin_cases i <;> exact _root_.mul_one (M := G3 G ⟶ G) _
  have e' : psum G' (x3 G') {i} = x3 G' i := by
    fin_cases i <;> exact _root_.mul_one (M := G3 G' ⟶ G') _
  rw [e, e'] at h
  exact h.symm

theorem cubeMap_tripleProduct_unique {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m m' : CubeMap G' G) (h : m.F = m'.F) : m.F3 = m'.F3 := by
  have h0 := (cubeMap_coord m 0).trans (h ▸ (cubeMap_coord m' 0).symm)
  have h1 := (cubeMap_coord m 1).trans (h ▸ (cubeMap_coord m' 1).symm)
  have h2 := (cubeMap_coord m 2).trans (h ▸ (cubeMap_coord m' 2).symm)
  apply pullback.hom_ext
  · exact h0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact h1
    · rw [Category.assoc, Category.assoc]; exact h2

theorem res_eq_one {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {x : Γ(X, U)ˣ} (hx : x = 1) :
    res h x = 1 := by rw [hx, map_one]

theorem pullU_eq_one {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {x : Γ(X, U)ˣ} (hx : x = 1) :
    pullU f U x = 1 := by rw [hx, map_one]

theorem mul_eq_one_of_both {M : Type} [Monoid M] {x y : M} (hx : x = 1) (hy : y = 1) :
    x * y = 1 := by rw [hx, hy, _root_.one_mul]

theorem zpow_eq_one_of {M : Type} [Group M] {x : M} (hx : x = 1) (n : ℤ) : x ^ n = 1 := by
  rw [hx, one_zpow]

theorem isGen_one {X : Scheme.{0}} (L : LB X) (hg : ∀ i j, L.g i j = 1) :
    (⟨fun _ => 1⟩ : LB.Gen L).IsGen := fun i j => by
  rw [hg, res_eq_one _ rfl, res_eq_one _ rfl, _root_.one_mul]

theorem linComb_g_one {X Y : Scheme.{0}} (L : LB X) (hg : ∀ i j, L.g i j = 1) {K : Type}
    [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j) : (LB.LinComb L φ ε).g i j = 1 :=
  Finset.prod_eq_one fun _ _ =>
    zpow_eq_one_of (res_eq_one _ (pullU_eq_one _ _ (hg _ _))) _

theorem linCombIso_one {X Y : Scheme.{0}} (L M : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p) :
    (LB.linCombIso (L := L) (M := M) ⟨fun _ => 1⟩ φ ε).s p = 1 := by
  unfold LB.linCombIso
  refine Finset.prod_eq_one fun k _ => ?_
  refine zpow_eq_one_of ?_ _
  refine res_eq_one _ ?_
  exact map_one (pullU (φ k) (M.U (p.1 k) ⊓ L.U (p.2 k)))

theorem corr_one {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ j, t.s j = 1) (h' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' :=
  fun j j' _ _ _ => (res_eq_one _ (h j)).trans (res_eq_one _ (h' j')).symm

def trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

def trivRig (G : Over S) [GrpObj G] [IsCommMonObj G] : RigLB G where
  L := trivLB G.left
  rig := ⟨fun _ => 1⟩
  isLB := ⟨by simp [trivLB], fun _ => res_eq_one _ rfl, fun _ _ _ =>
    (mul_eq_one_of_both (res_eq_one _ rfl) (res_eq_one _ rfl)).trans (res_eq_one _ rfl).symm⟩
  rigGen := isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _)

def ofTrivial (H : Host E) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : IsSemiAbelian G)
    (act : OAct (𝓞 E) G) : Triple H S where
  G := G
  semiAbelian := h
  iota := act
  L := trivRig G
  cube :=
    { t := ⟨fun _ => 1⟩
      isGen := isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _)
      face := fun _ => corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl
      cubeSymmetric_swap_first := corr_one _ (fun _ => rfl) fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)
      cubeSymmetric_swap_last := corr_one _ (fun _ => rfl) fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)
      cocycle := corr_one _
        (fun _ => mul_eq_one_of_both (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl)))
          (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl))))
        (fun _ => mul_eq_one_of_both (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl)))
          (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl)))) }
  symm := ⟨by
      rw [Category.id_comp, eSec, ← Over.comp_left]; simp,
    ⟨fun _ => 1⟩, isGen_one _ (fun _ _ => mul_eq_one_of_both
      (res_eq_one _ (linComb_g_one _ (fun _ _ => rfl) _ _ _ _))
      (inv_eq_one.mpr (res_eq_one _ rfl))),
    fun _ => (res_eq_one _ (res_eq_one _ (pullU_eq_one _ _ rfl))).trans
      (Eq.symm <| mul_eq_one_of_both (linCombIso_one _ _ _ _ _) (res_eq_one _ rfl))⟩
  adjoint := fun _ => ⟨⟨fun _ => 1⟩, isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _),
    corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl,
    corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl⟩
  primitive := ⟨⟨fun _ => 1⟩, isGen_one _ (linComb_g_one _ (fun _ _ => rfl) _ _),
    corr_one _ (fun _ => res_eq_one _ (pullU_eq_one _ _ rfl)) fun _ => rfl⟩

end Triple

end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
