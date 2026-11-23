import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace.MoveModel

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

def subH (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun x := ((εT⁻¹).val * x * εS.val).submatrix σT σS
  invFun z := εT.val * z.submatrix σT.symm σS.symm * (εS⁻¹).val
  left_inv x := by
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv z := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Equiv.symm_comp_self, Matrix.submatrix_id_id]
  continuous_toFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_submatrix _ _
  continuous_invFun := ((continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul continuous_const)

theorem subH_apply (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x : Matrix Y Y' k) :
    subH εS εT σS σT x = ((εT⁻¹).val * x * εS.val).submatrix σT σS := rfl

theorem subH_add (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x y : Matrix Y Y' k) :
    subH εS εT σS σT (x + y) = subH εS εT σS σT x + subH εS εT σS σT y := by
  simp only [subH_apply, Matrix.mul_add, Matrix.add_mul]
  rfl

def pullS (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : SB (Matrix Z Z' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => Φ.1 (subH εS εT σS σT x),
    ⟨Φ.2.1.comp_continuous (subH εS εT σS σT).continuous, Φ.2.2.comp_homeomorph (subH εS εT σS σT)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sub_mul_sub {n m : Type} [Fintype n] [Fintype m] (P : Matrix Y n k) (Q : Matrix n m k) (R : Matrix m Y' k)
    (σS : Z' ≃ Y') (σT : Z ≃ Y) : P.submatrix σT id * Q * R.submatrix id σS = (P * Q * R).submatrix σT σS := by
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.FlatPlace.MoveModel

namespace GlobalTheory.FlatPlace.MoveModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

theorem map_mt_inv_mul {S : HSp D} (g : GA D S) : (mt S g⁻¹).map p.π * (mt S g).map p.π = 1 := by
  rw [← Matrix.map_mul]
  have : mt S g⁻¹ * mt S g = 1 := by
    rw [show mt S g⁻¹ * mt S g = mt S (g⁻¹ * g) by simp [Formalism.L2.Theta.mt], inv_mul_cancel]
    simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_up_mvFr {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (a : GA D S) (b : GA D T)
    (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x : Matrix Y Y' k) :
    actO S T a b (p.up FS FT x) = p.up (mvFr p a FS εS σS) (mvFr p b FT εT σT) (subH εS εT σS σT x) := by
  have h1 : IsHalf p.e (actO S T a b (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO a b (Witness.up_half p FS FT x)
  rw [← Witness.up_down p (mvFr p a FS εS σS) (mvFr p b FT εT σT) h1]
  congr 1
  have hu : (p.up FS FT x).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  have hA := map_mt_inv_mul p a
  have hB := map_mt_inv_mul p b
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, subH_apply]
  change ((εT⁻¹).val * FT.γ * (mt T b⁻¹).map p.π).submatrix σT id * _ * ((mt S a).map p.π * FS.β * εS.val).submatrix id σS = _
  rw [sub_mul_sub]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((mt T b⁻¹).map p.π), hB, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul,
    ← Matrix.mul_assoc ((mt S a⁻¹).map p.π), hA, Matrix.one_mul, ← Matrix.mul_assoc FS.γ FS.β, FS.γβ, Matrix.one_mul]

end GlobalTheory.FlatPlace.MoveModel

namespace GlobalTheory.FlatPlace

open GlobalTheory.FlatPlace.MoveModel in

theorem exists_isModel_mvFr : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z Z' : Type) [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) Tm, p.IsModel ψ FS FT Tm → ∀ (a : GA D S) (b : GA D T) (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y), ∃ Tm', p.IsModel ψ (mvFr p a FS εS σS) (mvFr p b FT εT σT) Tm' ∧ ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)), (∀ x, Φ.1 x = Φ'.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS)) → Tm' Φ' = ω (a, b) (Tm Φ) := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW Y Y' _ _ _ _ Z Z' _ _ _ _ FS FT Tm hm a b εS εT σS σT
  let L := pullS (k := k) εS εT σS σT
  let W₀ : Module.End ℂ (WO S T → ℂ) := ω (a, b)
  have hA := actO_up_mvFr p FS FT a b εS εT σS σT
  refine ⟨W₀ ∘ₗ Tm ∘ₗ L, ⟨fun Φ => hW.om_pres _ _ (hm.theta _), fun z Φ Φ₁ hΦ => ?_, fun y hy Φ Φ₁ hΦ => ?_⟩, fun Φ Φ' e => ?_⟩
  · set x := (subH εS εT σS σT).symm z with hx
    have hz : subH εS εT σS σT x = z := (subH εS εT σS σT).apply_symm_apply z
    have h1 : ∀ t, (L Φ₁).1 t = (L Φ).1 (t + x) := fun t => by
      change Φ₁.1 (subH εS εT σS σT t) = Φ.1 (subH εS εT σS σT (t + x))
      rw [hΦ, subH_add, hz]
    have h2 := hm.trans x (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (a, b) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hA, hz]
  · set y₀ := actO S T a⁻¹ b⁻¹ y
    have hy₀ : IsHalf (cA D p.e) y₀ := GlobalTheory.SplitHecke.isHalf_actO a⁻¹ b⁻¹ hy
    have hyy : actO S T a b y₀ = y := by
      have := GlobalTheory.SplitHecke.actO_inv_actO a⁻¹ b⁻¹ y
      rwa [inv_inv, inv_inv] at this
    have h1 : ∀ t, (L Φ₁).1 t = ψ (symplO S T (p.up FS FT t) y₀) * (L Φ).1 t := fun t => by
      change Φ₁.1 (subH εS εT σS σT t) = _ * Φ.1 (subH εS εT σS σT t)
      rw [hΦ, ← hA, ← hyy, GlobalTheory.SplitHecke.symplO_actO]
    have h2 := hm.modul y₀ hy₀ (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (a, b) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hyy]
  · have : L Φ' = Φ := Subtype.ext (funext fun x => (e x).symm)
    show ω (a, b) (Tm (L Φ')) = _
    rw [this]

end GlobalTheory.FlatPlace
