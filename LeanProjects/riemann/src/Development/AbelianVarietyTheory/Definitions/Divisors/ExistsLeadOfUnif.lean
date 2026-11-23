import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaArc
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotIsThetaOfNonunit

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

structure Ext (D : DegPre R) : Type 1 where

  H : Over (Sp R)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]

  Φ : ∀ T, (T ⟶ H) ≃ GtPt D T
  isGt : (GlobalTheory.TorusModel.splitExt D).IsGt H
  rep : GlobalTheory.TorusModel.Represents Φ

attribute [instance] Ext.grp Ext.comm

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre in

instance (D : DegPre R) : Nonempty (Ext D) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (GlobalTheory.TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.TorusModel.exists_points hL hH
  exact ⟨{ H := H, Φ := Φ, isGt := hH, rep := hΦ }⟩

def Ext.q {D : DegPre R} (Y : Ext D) : Y.H ⟶ D.P.A := (Y.Φ Y.H (𝟙 _)).b

def IsTermOf {D : DegPre R} (Y : Ext D) {k : ℕ} {α : D.X} (b : D.SecB k α) (τ : SecK D.P.L Y.q.left k) : Prop :=
  ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good D.P.L y J →
    sval τ x.left y J = sval b (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val

def VanMod (I : Ideal R) {D : DegPre R} {k : ℕ} {α : D.X} (b : D.SecB k α) (e : ℕ) : Prop :=
  ∀ j : Fin 4 → D.P.L.ι, ((pullback.fst D.P.A.hom (thick R I e)).app _).hom (b.f j) = 0

structure IntFam (I : Ideal R) (D : DegPre R) (k : ℕ) where

  F : Fam D (FractionRing R) k

  f : ∀ α : D.X, D.SecB k α
  ext : ∀ α : D.X, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α)
    (D.famφB α) (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left
    (scal (DegPre.BF D (FractionRing R)).hom 1)
  small : ∀ e : ℕ, {α | ¬ VanMod I (f α) e}.Finite

def IntFam.Lead {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k) (α : D.X) (b : D.SecB k α) : Prop :=
  F.f α = b ∧ ∀ β, β ≠ α → VanMod I (F.f β) 0

def PullB {R' : Type} [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    {k : ℕ} (x : D'.X) (b : D.SecB k (hD.xe x)) (b' : D'.SecB k x) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
    (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) →
    (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) →
    gs (r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p) (b.f p) =
      (∏ κ, gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (D'.famφB x) q) (b'.f q)

end

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

structure Trait (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] where
  cdvr : GlobalTheory.LN.CDvr W

  φ : R →+* W
  inj : Function.Injective φ
  loc : IsLocalHom φ

  ξ : Sp W ⟶ C.S
  ξ_π : ξ ≫ C.π = spMap φ

  G : Over (Sp W)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]

  β : G.left ⟶ C.G.left
  cart : IsGrpPullback G C.G ξ β

  D' : DegData W (maximalIdeal W)

  A : PolAV (Sp (FractionRing W))

  U : Unif (maximalIdeal W) D' A G

  hD : IsPullDeg φ D.toPre D'.toPre

  ℓ : LB.Iso U.LG.L (C.P.L.L.pull β)
  ℓ_gen : ℓ.IsGen
  lab : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing R) F]
    (em : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] F),
    (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r))) →
    ∀ (j : ℕ) (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j))
      (p' : QkPt D'.toPre F (C.n ^ j)) (x' : TFK (R := W) F ⟶ A.A),
      QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD F p₁.g p'.g →
      x'.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W) ≫ β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α →
      QkToAkU U.toUnifPre F (C.n ^ j) p' x'

attribute [instance] Trait.grp Trait.comm

def Trait.Carries {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u : W) {k : ℕ}
    (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) J J', Good C.P.L.L z J → Good T.U.LG.L z J' →
    sval σ r z J = gs r z ⊤ (scal T.G.hom u) * (gw T.ℓ r z (J (r ≫ T.β)) (J' r) ^ k).val * sval σ' r z J'

def Trait.ExpBy {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u : W) {k : ℕ}
    (σ : SecK C.P.L.L T.β k) (F : IntFam (maximalIdeal R) D.toPre k) : Prop :=
  ∃ (σ' : H0 T.U.LG.L k) (f' : ∀ x, T.D'.toPre.SecB k x),
    T.Carries u σ' σ ∧ (∀ x, PullB T.hD x (F.f (T.hD.xe x)) (f' x)) ∧ ∀ e, T.U.ExpandsAt e k σ' f'

def Trait.Exp {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) {k : ℕ}
    (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) : Prop :=
  ∃ σ : SecK C.P.L.L T.β k, T.ExpBy b σ F ∧
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J

theorem LabCover.exists_trait (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    (φ : R →+* W) (ξ : Sp W ⟶ C.S) (hφ : Function.Injective φ) (hl : IsLocalHom φ) (hξ : ξ ≫ C.π = spMap φ) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (T : Trait C W'),
      Function.Injective io ∧ io.Finite ∧ T.φ = io.comp φ ∧ T.ξ = spMap io ≫ ξ := by
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hD, hW', hi, hf, hc, ⟨ℓ, hℓ⟩, hlab⟩ := C.trait W hW φ ξ hφ hl hξ
  have hio : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hf
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hi
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  refine ⟨W', inferInstance, inferInstance, inferInstance, io,
    { cdvr := hW', φ := io.comp φ, inj := hi.comp hφ, loc := inferInstance, ξ := spMap io ≫ ξ, ξ_π := ?_, G := G', β := β,
      cart := hc, D' := D', A := A', U := U', hD := hD, ℓ := ℓ, ℓ_gen := hℓ, lab := hlab }, hi, hf, rfl, rfl⟩
  rw [Category.assoc, hξ, ← Spec.map_comp]; rfl

theorem Trait.exists_toric_rank_one : ∃ (D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ))) (C : LabCover D)
    (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Module.finrank ℤ D.toPre.X = 1 ∧ Nonempty (Trait C W) := by
  obtain ⟨D, hr, h, -, -⟩ := LabCover.exists_toric_rank_one
  have hu : IsUnit ((3 : ℕ) : PowerSeries ℚ) := by
    rw [← map_natCast (algebraMap ℚ (PowerSeries ℚ))]
    exact (IsUnit.mk0 _ (by norm_num)).map _
  obtain ⟨C, h₁, -⟩ := h.labCover base_powerSeries 3 Nat.prime_three (by decide) hu
  have hW : GlobalTheory.LN.CDvr (PowerSeries ℚ) := ⟨inferInstance, base_powerSeries.1.2.2.2, base_powerSeries.2⟩
  have hx : ∃ ξ : Sp (PowerSeries ℚ) ⟶ C.toModif.S, ξ ≫ C.toModif.π = spMap (RingHom.id _) := by
    rw [h₁]; exact ⟨spMap (RingHom.id _), Category.comp_id _⟩
  obtain ⟨ξ, hξ⟩ := hx
  obtain ⟨W', _, _, _, io, T, -⟩ := C.exists_trait _ hW (RingHom.id _) ξ Function.injective_id inferInstance hξ
  exact ⟨D, C, W', _, _, _, hr, ⟨T⟩⟩

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG in

theorem IntFam.exists_lead_of_unif {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) :
    ∃ F : IntFam (maximalIdeal V) D.toPre 1, F.Lead 0 (F.f 0) ∧ ¬ VanMod (maximalIdeal V) (F.f 0) 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨ϑ, hϑ, -⟩ := GlobalTheory.ThetaSectionTest.exists_isTheta_of_dvr GlobalTheory.allSixLaws.1 V D A G U
  obtain ⟨F, g, -, x, f⟩ := integral_exp rfl U ϑ
  have hv := terms_vanish hϖ rfl F g f
  have h1 : Out.scal (DegPre.BF D.toPre (FractionRing V)).hom (1 : V) = 1 := by unfold Out.scal; rw [map_one, map_one]
  refine ⟨⟨F, g, fun α => h1 ▸ f α, fun e => ?_⟩, ⟨rfl, hv⟩, leading_expansion_term_ne_zero rfl U ϑ (nonzero_of_isTheta rfl U hϑ) g (x 0) hv⟩
  obtain ⟨S, hS, -⟩ := x e
  refine S.finite_toSet.subset fun α hα => by_contra fun h => hα fun j => ?_
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  apply app_injective_of_flat_surj (U.gt e).q.left
  rw [map_zero]
  have h' := hS α h j
  have e' : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick V (maximalIdeal V) e) := rfl
  rw [e', Scheme.Hom.comp_app] at h'
  exact h'

theorem IntFam.exists_toric_rank_one : ∃ (D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)))
    (F : IntFam (maximalIdeal (PowerSeries ℚ)) D.toPre 1), Module.finrank ℤ D.toPre.X = 1 ∧ F.Lead 0 (F.f 0) ∧
      ¬ VanMod (maximalIdeal (PowerSeries ℚ)) (F.f 0) 0 := by
  obtain ⟨A, G, _, _, D, U, -, -, hr, -⟩ := GlobalTheory.TateUnif.exists_unif_rank_one
  obtain ⟨F, h⟩ := IntFam.exists_lead_of_unif U
  exact ⟨D, F, hr, h⟩

example (D : DegPre (PowerSeries ℚ)) : Nonempty (Ext D) := inferInstance

end GlobalTheory.Mum
