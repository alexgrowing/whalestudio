import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZH

export ReciprocityTheory.ChartRestriction.G.Geo.Tor (valR)

def Crd {X : Scheme.{0}} (H : LB X) {J : Type} (s : J → H.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (v : J → R) : Prop :=
  ∃ (l : H.ι) (c : Rˣ), ⊤ ≤ x ⁻¹ᵁ H.U l ∧ ∀ j, v j = (c : R) * valR x (H.U l) ((s j).f l)

def IsRatio {X : Scheme.{0}} {H : LB X} (s t : H.Sec) (W : X.Opens) (r : Γ(X, W)) : Prop :=
  ∀ l, resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) =
    resG X (inf_le_left : W ⊓ H.U l ≤ W) r * resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l)

def IsLin {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → k) (φ : H.Sec) : Prop :=
  ∀ l, φ.f l = ∑ j, constFn p (H.U l) (a j) * (s j).f l

def ImmBy {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type} (s : J → H.Sec)
    (J₀ : Set J) : Prop :=
  (⨆ i ∈ J₀, Out.nonzeroLocus (s i) = ⊤) ∧ ∀ i ∈ J₀, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
    ∃ r : J → Γ(X, Out.nonzeroLocus (s i)), (∀ j, IsRatio (s j) (s i) _ (r j)) ∧
      Subring.closure (Set.range (constFn p (Out.nonzeroLocus (s i))) ∪ Set.range r) = ⊤

def cone {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type} (s : J → H.Sec) :
    Set (J → k) := {v | ∃ x : Sp k ⟶ X, x ≫ p = 𝟙 _ ∧ Crd H s x v}

def npw {X : Scheme.{0}} (H : LB X) (d : ℕ) : LB X := ⟨H.ι, H.U, fun i j => H.g i j ^ d⟩

def Short {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (N : ℕ) (α : X) : Prop :=
  ∀ m : X, q α ≤ q (α + N • m)

def hilb {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) : ℕ :=
  Module.finrank k ((MvPolynomial.homogeneousSubmodule J k d).map
    (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap))

attribute [local instance] SplitExt.free SplitExt.finite

structure FibPre (k : Type) [Field k] where
  E : SplitExt (Sp k)
  G : Over (Sp k)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  D : E.GtDatum G
  N₀ : LB E.B.left
  isLB : N₀.IsLB
  aff : ∀ l, IsAffineOpen (N₀.U l)
  ch : N₀.ι → E.ChartIdx
  le : ∀ l, N₀.U l ≤ E.chart (ch l)
attribute [instance] FibPre.grp FibPre.comm
namespace FibPre
variable {k : Type} [Field k] (Φ : FibPre k)

def H (d : ℕ) : LB Φ.G.left :=
  ⟨Φ.N₀.ι, fun l => Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l, fun l l' => pullU Φ.D.q.left (Φ.N₀.U l ⊓ Φ.N₀.U l') (Φ.N₀.g l l') ^ d⟩

def wt {d : ℕ} (φ : (Φ.H d).Sec) (α : Φ.E.X) (l : Φ.N₀.ι) : Γ(Φ.E.B.left, Φ.N₀.U l) :=
  Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l)

def supp {d : ℕ} (φ : (Φ.H d).Sec) : Set Φ.E.X := {α | ∃ l, Φ.wt φ α l ≠ 0}

def Pure {d : ℕ} (α : Φ.E.X) (φ : (Φ.H d).Sec) : Prop := Φ.supp φ ⊆ {α}

def IsPart {d : ℕ} (α : Φ.E.X) (φ ψ : (Φ.H d).Sec) : Prop := Φ.Pure α ψ ∧ ∀ l, Φ.wt ψ α l = Φ.wt φ α l

abbrev Pt : Type := Out.baseOver (Sp k) ⟶ Φ.G

structure Pol (N : ℕ) where
  PB : Out.PolAV (Sp k)
  β : Φ.E.B ≅ PB.A
  hom : IsMonHom β.hom
  c : Φ.E.X → (Out.baseOver (Sp k) ⟶ PB.A)
  w₀ : LBIso Φ.N₀ ((lbPow PB.L N).pull β.hom.left)
  wO : ∀ α, LBIso (Φ.E.O α).L (LB.LinComb PB.L (K := Fin 2)
    ![(β.hom * (Over.homMk Φ.E.B.hom (Category.comp_id _) ≫ c α)).left, β.hom.left] ![1, -1])

structure Good (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) {J : Type} [Fintype J] (cls : J → Φ.E.X)
    (F : J → (Φ.H 1).Sec) : Prop where
  pos : Filter.Tendsto q Filter.cofinite Filter.atTop
  short : ∀ i, Short q N (cls i)
  supp : ∀ i, ∀ β ∈ Φ.supp (F i), Short q N β ∧ ∃ m, β = cls i + N • m
  onto : ∀ α, Short q N α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ a : J → k,
    (∀ i, a i ≠ 0 → ∃ m, α = cls i + N • m) ∧
    ∀ l, Φ.wt φ α l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l
  inj : ∀ α, Short q N α → ∀ a : J → k, (∀ i, a i ≠ 0 → ∃ m, α = cls i + N • m) →
    (∀ l, ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l = 0) → a = 0
end FibPre

structure Big (g N N' : ℕ) : Prop where
  four : 4 ≤ N
  lll : 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N
  sep : 2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)) * N < N'

theorem valR_of_field {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valR x U f = valF x U f := rfl

theorem npw_isLB {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (d : ℕ) : (npw H d).IsLB where
  cover := hH.cover
  g_self i := (map_pow _ _ _).trans ((congrArg (· ^ d) (hH.g_self i)).trans (one_pow d))
  cocycle i j l := by
    refine (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)).trans ((mul_pow _ _ _).symm.trans
      ((congrArg (· ^ d) (hH.cocycle i j l)).trans (map_pow _ _ _).symm))

theorem pullU_res_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    pullU f V (res h u) = res (Scheme.Hom.preimage_mono f h) (pullU f U u) := by
  ext
  exact congrArg (fun φ => φ.hom (u : Γ(X, U))) (f.naturality (homOfLE h).op)

theorem pullChart_isLB {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} (hL : L.IsLB) :
    (⟨L.ι, fun l => f ⁻¹ᵁ L.U l, fun l l' => pullU f (L.U l ⊓ L.U l') (L.g l l')⟩ : LB Y).IsLB := by
  refine ⟨?_, fun i => ?_, fun i j l => ?_⟩
  · show ⨆ l, f ⁻¹ᵁ L.U l = ⊤
    rw [← Scheme.Hom.preimage_iSup, hL.cover, Scheme.Hom.preimage_top]
  · have e := congrArg (pullU f _) (hL.g_self i)
    rw [map_one, pullU_res_eq] at e
    exact e
  · have e := congrArg (pullU f _) (hL.cocycle i j l)
    rw [map_mul, pullU_res_eq, pullU_res_eq, pullU_res_eq] at e
    exact e

theorem FibPre.H_isLB {k : Type} [Field k] (Φ : FibPre k) (d : ℕ) : (Φ.H d).IsLB :=
  npw_isLB (pullChart_isLB Φ.D.q.left Φ.isLB) d

theorem finite_forms {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    Module.Finite k ((MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap)) :=
  Module.Finite.iff_fg.2 ((MvPolynomial.homogeneousSubmodule_fg J k d).map _)

example {R : Type} [CommRing R] (a : R) : valR (𝟙 (Sp R)) ⊤ (constFn (𝟙 (Sp R)) ⊤ a) = a := by
  have e : ∀ (h : (⊤ : (Sp R).Opens) ≤ ⊤) (x : Γ(Sp R, ⊤)), ((Sp R).presheaf.map (homOfLE h).op).hom x = x :=
    fun h x => congrArg (fun φ => CommRingCat.Hom.hom φ x) ((Sp R).presheaf.map_id _)
  simp only [valR, constFn, Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  refine (dif_pos (fun _ _ => trivial)).trans ?_
  erw [e, e]
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply a

example {k J : Type} [Field k] [Finite J] (d : ℕ) : hilb (∅ : Set (J → k)) d = 0 :=
  Module.finrank_zero_of_subsingleton

example {X : Type} [AddCommGroup X] (N : ℕ) (α : X) : Short (0 : QuadraticMap ℤ X ℝ) N α := fun _ => le_rfl

example (g N' : ℕ) : ¬ Big g 3 N' := fun h => absurd h.four (by norm_num)

end GlobalTheory.ZH
end
