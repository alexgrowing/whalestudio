import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpTorsionDefOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def sharpPair (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (a b : Fin 8) : D.P.A.left ⟶ (G2 Q.B).left :=
  (lift (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr a))
    (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr b))).left

theorem sharp_cls_pair (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (a b : Fin 8) :
    (∏ I : ULift.{0} (Finset (Fin 2)), GlobalTheory.PrimNorm.cls Q.M.L (sharpPair ρ Q D pr a b ≫ (psum Q.B (x2 Q.B) I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card))) ^ W a b =
      ∏ k : Fin 4, GlobalTheory.PrimNorm.cls Q.M.L (lamPts (pr a) (pr b) k ≫ pullback.fst Q.B.hom (spMap ρ)) ^
        (-(W a b * negε k)) := by
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  set xa := pushPt h.1.w (pr a) with hxa
  set xb := pushPt h.1.w (pr b) with hxb
  have e := GlobalTheory.PrimNorm.prod_square (lift xa xb) (fst Q.B Q.B) (snd Q.B Q.B) (GlobalTheory.PrimNorm.cls Q.M.L)
  rw [lift_fst, lift_snd] at e
  have e' : sharpPair ρ Q D pr a b = (lift xa xb).left := rfl
  rw [e', show x2 Q.B = ![fst Q.B Q.B, snd Q.B Q.B] from rfl, e]
  have m : (pr a * pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = (xa * xb).left :=
    (h.2 D.P.A (pr a) (pr b) xa xb rfl rfl).symm
  have o : (1 : D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B).left ≫ pullback.fst Q.B.hom (spMap ρ) =
      (1 : Over.mk (D.P.A.hom ≫ spMap ρ) ⟶ Q.B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h D.P.A))
  rw [Fin.prod_univ_four]
  simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, m, o]
  change GlobalTheory.PrimNorm.diff₂ _ xa xb ^ W a b = _
  simp only [GlobalTheory.PrimNorm.diff₂]
  have ha : (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = xa.left := rfl
  have hb : (pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) = xb.left := rfl
  rw [ha, hb]
  simp only [mul_neg, neg_neg, zpow_neg, mul_zpow, inv_zpow]
  ac_rfl

theorem sharp_bundle {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : w.IsGen) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (hM₀ : M₀.IsLB)
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)) (hw₀ : w₀.IsGen) :
    LBIso D.P.L (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
      (fun p => W p.1 p.2)) := by
  have hL : Q.M.L.IsLB := Q.M.isLB
  have hLam : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hLam₀ : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  have hS : (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))).IsLB := DVR.linComb_isLB _ hL _ _
  have h₂ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
      (fun k => -(W k.1.1 k.1.2 * negε k.2))) := by
    refine GlobalTheory.PrimNorm.lbIso_nested hL _ _ _ _ _ _ ?_
    refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
    exact Finset.prod_congr rfl fun p _ => sharp_cls_pair W ρ Q D pr p.1 p.2
  have h₃ : LBIso (LB.LinComb (abelian₂ Q.B Q.M.L) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2)
      (fun p => W p.1 p.2)) (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb ⟨w₀, hw₀⟩ _ _
  have h₄ : LBIso (LB.LinComb ((abelian₂ B₀ M₀).pull β₂) (K := Fin 8 × Fin 8)
      (fun p => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2))
      (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
        (fun p => W p.1 p.2)) :=
    LBIso.chartPull (chartPullLinComb (abelian₂ B₀ M₀) β₂ _ _ _ (𝟙 _) fun p => (Category.id_comp _).symm)
      (chartPullId _) ((GlobalTheory.PrimNorm.lbIso_iff hLam₀ _ _ _ _).2 rfl)
  have hN₁ := DVR.linComb_isLB (abelian₂ Q.B Q.M.L) hLam (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₂ := DVR.linComb_isLB _ (pull_isLB hLam₀ β₂) (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2)
    (fun p => W p.1 p.2)
  have hN₃ := DVR.linComb_isLB (abelian₂ B₀ M₀) hLam₀ (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
    (fun p => W p.1 p.2)
  exact LBIso.trans D.P.isLB hS hN₃ ⟨w, hw⟩
    (LBIso.trans hS hN₁ hN₃ h₂.symm (LBIso.trans hN₁ hN₂ hN₃ h₃ h₄))

example {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (τ₀ : Gens Q) (ib : W₀ →+* V) (h₁ : SharpRef W Q ρ D e) (h₂ : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (B₀ : Over (Sp W₀)) (_ : GrpObj B₀)
      (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left),
      LBIso D.P.L (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
        (fun p => W p.1 p.2)) := by
  obtain ⟨pr, w, -, -, hw, -, -⟩ := h₁
  obtain ⟨B₀, iG, iC, M₀, -, -, -, β₂, w₀, -, hM₀, -, -, hw₀, -, -, -⟩ := h₂
  exact ⟨pr, B₀, iG, iC, M₀, β₂, sharp_bundle W ρ Q D pr w hw B₀ M₀ hM₀ β₂ w₀ hw₀⟩

end GlobalTheory.Poinc.Sep
