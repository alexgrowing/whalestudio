import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CoefficientFieldBaseChange

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange

section Push

variable {X : Scheme.{0}} (G : Over X) (L : LB G.left)

structure IsPushGen (V : X.Opens) (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) : Prop where
  mem : θ ∈ secOn L (G.hom ⁻¹ᵁ V)
  basis : ∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! c : Γ(X, W), ∀ i,
    s i = resG G.left (inf_le_left : G.hom ⁻¹ᵁ W ⊓ L.U i ≤ G.hom ⁻¹ᵁ W) ((G.hom.app W).hom c) *
      resG G.left (inf_le_inf_right _ (fun _ hy => hW hy) : G.hom ⁻¹ᵁ W ⊓ L.U i ≤ G.hom ⁻¹ᵁ V ⊓ L.U i) (θ i)

def NonzeroOnFibre {V : X.Opens} (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) (x : X) : Prop :=
  ∃ i, ((Scheme.Hom.fiberι G.hom x).app (G.hom ⁻¹ᵁ V ⊓ L.U i)).hom (θ i) ≠ 0

structure PushInvertible : Prop where
  invertible : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ, IsPushGen G L V θ
  nonzero : ∀ (V : X.Opens) θ, IsPushGen G L V θ → ∀ x ∈ V, NonzeroOnFibre G L θ x

theorem nonzeroOnFibre_iff {V : X.Opens} (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) (x : X)
    [IsReduced (Scheme.Hom.fiber G.hom x)] :
    NonzeroOnFibre G L θ x ↔ ∃ (i : L.ι) (g : G.left), G.hom g = x ∧ g ∈ G.left.basicOpen (θ i) := by
  refine exists_congr fun i => ?_
  rw [Ne, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  constructor
  · intro hne
    obtain ⟨y, hy⟩ : ∃ y, y ∈ Scheme.Hom.fiberι G.hom x ⁻¹ᵁ G.left.basicOpen (θ i) := by
      by_contra hh
      push_neg at hh
      exact hne (le_bot_iff.mp fun y hy => (hh y hy).elim)
    refine ⟨_, ?_, hy⟩
    have : Scheme.Hom.fiberι G.hom x y ∈ Set.range (Scheme.Hom.fiberι G.hom x) := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · rintro ⟨g, hg, hb⟩ h0
    have : g ∈ Set.range (Scheme.Hom.fiberι G.hom x) := by
      rw [Scheme.Hom.range_fiberι]; exact hg
    obtain ⟨y, rfl⟩ := this
    have : y ∈ Scheme.Hom.fiberι G.hom x ⁻¹ᵁ G.left.basicOpen (θ i) := hb
    rw [h0] at this
    exact this

end Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Model {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀)
    {O : Type} [CommRing O] (φ : O →+* F₀) where

  X : Scheme.{0}

  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s

  j : baseChange str h ⟶ pullback s (spMap φ)
  j_over : j ≫ pullback.snd s (spMap φ) = baseChangeStr str h
  j_open : IsOpenImmersion j
  j_dense : Dense (Set.range j)

  t : SAB H X

  t₀ : SAB H (baseChange str h)

  toUniv : SABMap t₀ univ.t (baseChangeFst str h)

  toModel : SABMap t₀ t (j ≫ pullback.fst s (spMap φ))
  ab : ∀ y : ↥(pullback s (spMap φ)), pullback.fst s (spMap φ) y ∈ abLocus t.G ↔ y ∈ Set.range j

namespace Model

variable {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
  {univ : Obj D l (baseKA l) str} {F₀ : IntermediateField ℚ ℂ} {h : IsCoeffField l F₀}
  {O : Type} [CommRing O] {φ : O →+* F₀} (m : Model univ h φ)

def incl : baseChange str h ⟶ m.X := m.j ≫ pullback.fst m.s (spMap φ)

theorem incl_over : m.incl ≫ m.s = baseChangeStr str h ≫ spMap φ := by
  rw [incl, Category.assoc, pullback.condition, ← Category.assoc, m.j_over]

def liftSec (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : baseChange str h ⟶ m.t₀.G.left :=
  m.toUniv.cart.1.lift σ.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w σ)

def secMap (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : baseChange str h ⟶ m.t.G.left :=
  m.liftSec σ ≫ m.toModel.φ

theorem secMap_over (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) : m.secMap σ ≫ m.t.G.hom = m.incl := by
  rw [secMap, Category.assoc, m.toModel.cart.1.w, ← Category.assoc, liftSec, IsPullback.lift_snd, Category.id_comp, incl]

def Extends (σ : Over.mk (baseChangeFst str h) ⟶ univ.t.G) (U : m.X.Opens) : Prop :=
  ∃ τ : Over.mk U.ι ⟶ m.t.G, (m.incl ∣_ U) ≫ τ.left = (m.incl ⁻¹ᵁ U).ι ≫ m.secMap σ

theorem extends_one (U : m.X.Opens) : m.Extends (toUnit _ ≫ MonObj.one) U := by
  have h1 : m.liftSec (toUnit _ ≫ MonObj.one) = eSec m.t₀.G := by
    apply m.toUniv.cart.1.hom_ext
    · rw [liftSec, IsPullback.lift_fst, m.toUniv.cm.e_comm, m.toUniv.base]; rfl
    · rw [liftSec, IsPullback.lift_snd]; exact (Over.w (MonObj.one (X := m.t₀.G))).symm
  refine ⟨toUnit _ ≫ MonObj.one, ?_⟩
  have h2 : m.secMap (toUnit _ ≫ MonObj.one) = m.incl ≫ eSec m.t.G := by
    rw [secMap, h1]
    have := m.toModel.cm.e_comm
    rw [m.toModel.base] at this
    exact this
  rw [h2, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rfl

def PPPushInvertible : Prop := PushInvertible m.t.G m.t.PP.L

theorem incl_mem_abLocus (y : ↥(baseChange str h)) : m.incl y ∈ abLocus m.t.G := by
  have := (m.ab (m.j y)).mpr ⟨y, rfl⟩
  simpa [incl] using this

end Model

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) : Type 1 :=
  Model univ h (algebraMap (𝓞 F₀) F₀)

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) [NumberField F₀]
    (lam : IsDedekindDomain.HeightOneSpectrum (𝓞 F₀)) : Type 1 :=
  Model univ h (lam.valuation F₀).valuationSubring.subtype

example {D : Datum H} {l : Level H} {X₀ : Scheme.{0}} {str : X₀ ⟶ Sp (KA l)}
    (univ : Obj D l (baseKA l) str) {F₀ : IntermediateField ℚ ℂ} (h : IsCoeffField l F₀) (a : D.La) :
    Over.mk (baseChangeFst str h) ⟶ univ.t.G := toUnit _ ≫ univ.eta a

end GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
