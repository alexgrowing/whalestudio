import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem spMap_jFK (σ : Kb R →ₐ[FractionRing R] Kb R) :
    spMap σ.toRingHom ≫ jFK (R := R) (Kb R) = jFK (R := R) (Kb R) := by
  rw [spMap, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact σ.comp_algebraMap

def twK (σ : Kb R →ₐ[FractionRing R] Kb R) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (spMap_jFK σ)

@[simp] theorem twK_left (σ : Kb R →ₐ[FractionRing R] Kb R) : (twK σ).left = spMap σ.toRingHom := rfl

def mTw (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⊗ A.A ⟶ TFK (R := R) (Kb R) ⊗ A.A :=
  lift (fst _ _ ≫ twK σ) (snd _ _)

theorem mTw_fst (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    mTw A σ ≫ fst _ _ = fst _ _ ≫ twK σ := lift_fst _ _

theorem mTw_snd (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    mTw A σ ≫ snd _ _ = snd _ _ := lift_snd _ _

theorem mTw_fst_left (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    (mTw A σ).left ≫ (fst (TFK (R := R) (Kb R)) A.A).left =
      (fst (TFK (R := R) (Kb R)) A.A).left ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  rw [← Over.comp_left, mTw_fst, Over.comp_left]; rfl

theorem mTw_snd_left (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    (mTw A σ).left ≫ (snd (TFK (R := R) (Kb R)) A.A).left = (snd (TFK (R := R) (Kb R)) A.A).left := by
  rw [← Over.comp_left, mTw_snd]

def secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N :=
  GlobalTheory.FieldBaseChange.pullOver (π := (fst (TFK (R := R) (Kb R)) A.A).left) (π' := (fst (TFK (R := R) (Kb R)) A.A).left)
    A.L (fun _ : Fin 1 => (N : ℤ)) (mTw_fst_left A σ) (fun _ => (mTw_snd_left A σ).symm) t

def TwF (σ : Kb R →ₐ[FractionRing R] Kb R) : Type := Kb R

instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Field (TwF σ) := inferInstanceAs (Field (Kb R))
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Algebra (FractionRing R) (TwF σ) :=
  inferInstanceAs (Algebra (FractionRing R) (Kb R))
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Algebra (Kb R) (TwF σ) := σ.toRingHom.toAlgebra
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : IsScalarTower (FractionRing R) (Kb R) (TwF σ) :=
  IsScalarTower.of_algebraMap_eq fun r => (σ.commutes r).symm

def famTw (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s : Fam D (Kb R) N) : Fam D (Kb R) N :=
  (GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N s : Fam D (TwF σ) N)

def genCast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) :=
  h ▸ t

theorem genCast_isGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) : (genCast h t).IsGen := by
  subst h; exact ht

theorem val_genCast {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (genCast h t) r z J = val t r z J := by
  subst h; rfl

theorem thetaφ_mTw (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (x : TFK (R := R) (Kb R) ⟶ A.A) :
    (fun i => (mTw A σ).left ≫ (![(snd (TFK (R := R) (Kb R)) A.A).left, (translPt A.A x).left] : Fin 2 → _) i) =
      ![(snd (TFK (R := R) (Kb R)) A.A).left, (translPt A.A (twK σ ≫ x)).left] := by
  funext i
  fin_cases i
  · exact mTw_snd_left A σ
  · show (mTw A σ).left ≫ (translPt A.A x).left = (translPt A.A (twK σ ≫ x)).left
    rw [← Over.comp_left, translPt, translPt, ← Category.assoc, comp_lift, ← Category.assoc, mTw_fst, mTw_snd,
      Category.assoc]

def thTw (A : PolAV (Sp (FractionRing R))) (k : ℤ) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (θ : ThetaGrp A.A A.L k (TFK (R := R) (Kb R))) : ThetaGrp A.A A.L k (TFK (R := R) (Kb R)) where
  pt := twK σ ≫ θ.pt
  φ := genCast (thetaφ_mTw A σ θ.pt) (LB.pullGen A.L _ _ θ.φ (mTw A σ).left)
  isGen := genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen A.L _ _ θ.φ θ.isGen _)

theorem spMap_jFKR (σ : Kb R →ₐ[FractionRing R] Kb R) :
    spMap σ.toRingHom ≫ (jFK (R := R) (Kb R) ≫ jK R) = jFK (R := R) (Kb R) ≫ jK R := by
  rw [← Category.assoc, spMap_jFK]

def twF (σ : Kb R →ₐ[FractionRing R] Kb R) : TF (R := R) (Kb R) ⟶ TF (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (spMap_jFKR σ)

theorem lineφ_tw (D : DegPre R) {N : ℕ} (τ : Kb R →ₐ[FractionRing R] Kb R) {p p₀ : QkPt D (Kb R) N}
    (h : QkExt τ.toRingHom p p₀) :
    (fun k => spMap τ.toRingHom ≫ DegPre.lineφ D (Kb R) p.g.b k) = DegPre.lineφ D (Kb R) p₀.g.b := by
  funext k
  fin_cases k
  · show (twF τ).left ≫ (toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · exact h.2.1.symm

def frTw (D : DegPre R) {N : ℕ} (τ : Kb R →ₐ[FractionRing R] Kb R) {p p₀ : QkPt D (Kb R) N}
    (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.Frm D (Kb R) N p₀.g.b :=
  genCast (lineφ_tw D τ h) (LB.pullGen D.P.L _ _ w (spMap τ.toRingHom))

end GlobalTheory.Mum.Conj
