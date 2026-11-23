import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem gam1_eq_prod_card_div_cardU (TR : TypedRed X) :
    Gam1 TR = ∏ v, ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) := by
  have h1 : Formalism.L2.SG.GGMirabolic.gamProd TR.psi0 (1 : Iof TR) =
      ((∏ v, ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) : ℝ) : ℂ) := by
    simp only [Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, Formalism.L2.SG.GGMirabolic.gam_one]
    push_cast
    rfl
  unfold Gam1
  rw [h1, Complex.ofReal_re]

theorem cardU_pos (F : Type) [Field F] [Fintype F] (k : ℕ) : 0 < Formalism.L2.SG.GGMirabolic.cardU F k := by
  unfold Formalism.L2.SG.GGMirabolic.cardU
  have h1 : Formalism.L2.SG.GGMirabolic.IsUni k (1 : GL (Fin k) F) := by
    simp [Formalism.L2.SG.GGMirabolic.IsUni, Matrix.one_apply]
    intro i j h e
    subst e
    exact lt_irrefl _ h
  have : Nonempty {x : GL (Fin k) F // Formalism.L2.SG.GGMirabolic.IsUni k x} := ⟨⟨1, h1⟩⟩
  exact Nat.card_pos

theorem gamma_one_pos (TR : TypedRed X) : 0 < Gam1 TR := by
  rw [gam1_eq_prod_card_div_cardU]
  apply Finset.prod_pos
  intro v _
  apply div_pos
  · exact_mod_cast Fintype.card_pos
  · exact_mod_cast cardU_pos _ _

variable {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem card_classes_eq (hK : X.LevelSubgroupCharacter) (cs : ColSys X u what₂) (hR : ColReps hK cs) :
    Nat.card (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK)) = Fintype.card cs.Cl := by
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective
    (fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u hK) (cs.h ρ)) ⟨?_, ?_⟩
  · intro ρ ρ' he
    obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ _ _).1 he
    obtain ⟨γ, rfl⟩ := ha
    obtain ⟨ρ₀, _, hu⟩ := hR (cs.h ρ')
    have e1 := hu ρ' ⟨1, 1, by simp⟩
    have e2 := hu ρ ⟨γ, ⟨b, hb⟩, hab⟩
    exact e2.trans e1.symm
  · intro q
    induction q using Quotient.inductionOn' with
    | h h =>
      obtain ⟨ρ, ⟨γ, κ, hh⟩, _⟩ := hR h
      refine ⟨ρ, ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ _
      rw [DoubleCoset.eq]
      exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hh⟩

theorem classFin_of (hK : X.LevelSubgroupCharacter) (cs : ColSys X u what₂) (hR : ColReps hK cs) :
    Formalism.L2.SG.PoincareInHH.Cut.ClassFin X u hK := by
  have hs : Function.Surjective
      (fun ρ : cs.Cl => DoubleCoset.mk (iotaF X u).range (Ku X u hK) (cs.h ρ)) := by
    intro q
    induction q using Quotient.inductionOn' with
    | h h =>
      obtain ⟨ρ, ⟨γ, κ, hh⟩, _⟩ := hR h
      refine ⟨ρ, ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ _
      rw [DoubleCoset.eq]
      exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hh⟩
  exact Finite.of_surjective _ hs

theorem duC_eq (Y : Full X) (u : D.what₂.Word) (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) :
    Formalism.L2.SG.RowsConc.duC X Y u = Formalism.L2.SG.KappaOffDiagonal.dpiC X u * (Fintype.card (Y.cs u).Cl : ℝ) := by
  unfold Formalism.L2.SG.RowsConc.duC Formalism.L2.SG.KappaOffDiagonal.dpiC
  rw [(Formalism.L2.SG.PoincareInHH.Cut.cols_dim_of_neat X u Y.hK hN
      (classFin_of Y.hK (Y.cs u) (Y.colReps u))).2, card_classes_eq Y.hK (Y.cs u) (Y.colReps u)]
  push_cast; ring

def fib (cs : ColSys X u what₂) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Finset cs.Cl :=
  Finset.univ.filter fun ρ => cs.lamOf ρ = Λ

theorem card_cl_eq_sum (cs : ColSys X u what₂) :
    (Fintype.card cs.Cl : ℝ) = ∑ Λ ∈ what₂, ((fib cs Λ).card : ℝ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset cs.Cl)) (t := what₂) (f := cs.lamOf)
    (fun ρ _ => cs.lam_mem ρ)
  rw [Finset.card_univ] at h
  rw [h, Nat.cast_sum]
  rfl

def FibreBound : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ Λ ∈ Y.what₂ u, Gam1 Y.TR * wRow D (X.Fu u) Λ ≤ ((fib (Y.cs u) Λ).card : ℝ)

theorem dimFormC_of (h4 : FibreBound) : Formalism.L2.SG.KappaOffDiagonal.DimFormC := by
  intro D X Y u hT
  have hG : (Y.tO u u).Gam1 = Gam1 Y.TR := rfl
  rw [hG]
  refine ⟨(gamma_one_pos Y.TR).le, ?_⟩
  rw [duC_eq Y u (hT.2.1 u), card_cl_eq_sum]
  have hd : 0 ≤ Formalism.L2.SG.KappaOffDiagonal.dpiC X u := by unfold Formalism.L2.SG.KappaOffDiagonal.dpiC; positivity
  have hm : Gam1 Y.TR * Formalism.L2.SG.KappaOffDiagonal.massC Y u ≤ ∑ Λ ∈ Y.what₂ u, ((fib (Y.cs u) Λ).card : ℝ) := by
    unfold Formalism.L2.SG.KappaOffDiagonal.massC massRows
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun Λ hΛ => h4 D X Y u hT Λ hΛ
  calc Gam1 Y.TR * Formalism.L2.SG.KappaOffDiagonal.massC Y u * Formalism.L2.SG.KappaOffDiagonal.dpiC X u
      ≤ (∑ Λ ∈ Y.what₂ u, ((fib (Y.cs u) Λ).card : ℝ)) * Formalism.L2.SG.KappaOffDiagonal.dpiC X u :=
        mul_le_mul_of_nonneg_right hm hd
    _ = _ := by ring

end PI.UnitaryDimensionFormula
