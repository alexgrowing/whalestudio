import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace NormMulUniv

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem rigPow_isGen {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (k : ℤ) : (rigPow A L ρ k).IsGen := by
  refine isGen_of_gm _ fun y i j hi hj => ?_
  have e := gen_trans (L := L) (φ := fun _ : PUnit.{1} => eSec A) (ε := fun _ => 1) hρ (𝟙 S) y hi hj
  rw [trF, Fintype.prod_unique, zpow_one] at e
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (map_zpow _ _ _)).symm)
  rw [trF, Fintype.prod_unique, ← mul_zpow]
  exact congrArg (· ^ k) e

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have h : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by simp [Hom.one_def]
  have : (η[A] : 𝟙_ (Over S) ⟶ A) ≫ mulA A n = η[A] := by
    rw [MonObj.comp_pow, Category.comp_id, h, one_pow]
  exact congrArg (fun q => q.left) this

theorem exists_normalised (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (n : ℕ)
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])) (hβ : β.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      IsNormMul A L ρ n α := by
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -(n : ℤ) ^ 2 + - -1 + ((n : ℤ) ^ 2 + -1) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L _ _ _ _ β (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ β (eSec A)))
      (LB.mulGen L _ _ _ _ (rigPow A L ρ ((n : ℤ) ^ 2)) (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) ρ))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (rigPow_isGen hρ _) (DVR.invGen_isGen _ _ _ _ hρ))) _))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

theorem normalised_unique (hL : L.IsLB) (hp : Function.Surjective A.hom.appTop.hom)
    {ρ : LB.Gen (L.pull (eSec A))} {n : ℕ}
    {α β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])}
    (hα : α.IsGen) (hβ : β.IsGen) (nα : IsNormMul A L ρ n α) (nβ : IsNormMul A L ρ n β) :
    LB.Gen.Corr L _ _ _ _ α β :=
  corr_of_val hL fun z J hJ => gen_unique hL A.hom (eSec A) eSec_hom hp hα hβ (fun w I hI => by
    have a := val_corr hI nα (𝟙 _)
    have b := val_corr hI nβ (𝟙 _)
    rw [val_pull hI, Category.id_comp] at a b
    exact a.trans b.symm) _ _ z J hJ

theorem exists_pull (hL : L.IsLB) {n : ℕ}
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])) (hβ : β.IsGen)
    (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      LB.Gen.Corr L _ _ _ _ α (LB.pullGen L _ _ β (snd T A).left) := by
  have e₁ : (snd T A).left ≫ (mulA A n).left = (snd T A ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((n : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen L ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1] β (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hβ _)
  exact ⟨α, hα, corr_of_val hL fun y J hJ => hv _ _ y J hJ⟩

end NormMulUniv

theorem moduli_univ_normMul :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧ IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ ∧ (∀ α₁, α₁.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₁ → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α₁ α₀) ∧ ∀ T : Over Xo.X, ∃ α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![(snd T Xo.univ.t.G).left, (snd T Xo.univ.t.G ^ N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd T Xo.univ.t.G).left) := by
  intro hLaw E _ _ _ H Dw l Xo N
  have := UnivPol.isLocallyNoetherian Xo
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨β, hβ⟩ := hLaw.mulPull _ (UnivPol.pol Xo) N
  obtain ⟨α₀, h₀, n₀⟩ := NormMulUniv.exists_normalised hL Xo.univ.t.PP.rigGen N β hβ
  exact ⟨α₀, h₀, n₀, fun α₁ h₁ n₁ => NormMulUniv.normalised_unique hL
    (hLaw.globalFns _ _ (ObjDim.isAbelianScheme Xo.univ)).2 h₁ h₀ n₁ n₀, NormMulUniv.exists_pull hL α₀ h₀⟩

end GlobalTheory
