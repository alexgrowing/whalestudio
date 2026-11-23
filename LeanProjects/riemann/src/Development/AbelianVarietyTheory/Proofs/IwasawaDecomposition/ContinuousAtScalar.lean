import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactor
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaScalar

open GlobalTheory.HolGen Formalism.L2.PjFree GlobalTheory.Frames

theorem continuousAt_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (x : (Fin m → ℂ) → (Fin T.m → ℂ)) (a : (Fin m → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B P → (∀ b ∈ B, x b ∈ T.co ⁻¹' (M.X k).dom ∧ T.Pf (T.co (x b)) = P b ∧ IsThetaPt T (x b) (a b) (y b)) → ∀ b₀ ∈ B, ContinuousAt x b₀ → ContinuousAt a b₀ := by
  intro E _ _ _ H Dw l Xo c σ g e F r M k T A _ _ yA m B ψ y P x a hB hψ hb hP hx b₀ hb₀ hx₀
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hxu : ∀ b ∈ B, (y b).x = F.u k (P b) := fun b h => by
    rw [← (hx b h).2.1]
    exact (hx b h).2.2.1
  let φ : (Fin m → ℂ) → (A →+* ℂ) := fun b => (ψ b).toRingHom
  have hux : ∀ b ∈ B, F.u k (P b) = (y b).x := fun b h => (hxu b h).symm
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) yA.x (y b₀).x _ (hux b₀ hb₀) yA.s (y b₀).s pm₀ p₁ p₂ p₃ (y b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx yA.x, q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (P b) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx yA.x, b ∈ B → q ≫ Formalism.L2.PjFree.gxFst yA.x = (F.ex k (P b) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd yA.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin m → ℂ => ((b, w₀) : (Fin m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (Formalism.L2.PjFree.gxSnd yA.x) (Formalism.L2.PjFree.gxFst yA.x) yA.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback yA.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx yA.x).basicOpen (yA.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx yA.x).basicOpen (yA.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx yA.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (P b) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have m₃ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co (x b))) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [(hx b h.1).2.1]
    exact m₂ b h
  have hO : IsOpen (T.co ⁻¹' (M.X k).dom) := (FourierCoefficientDomain.isOpen_dom (M.X k)).preimage T.co.continuous
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m _ T.h T.ta hO
    (fun b h => ⟨(T.norm b h).2.1, (T.norm b h).2.2.1⟩) T.hol
  have hκ : ContinuousWithinAt (fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) W b₀ :=
    (hx₀.prodMk continuousAt_const).continuousWithinAt
  have d₁ : ContinuousWithinAt (fun b => thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀)) W b₀ :=
    ContinuousWithinAt.comp (f := fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      (hθ.continuousOn _ ⟨(hx b₀ hb₀).1, trivial⟩) hκ fun b h => ⟨(hx b h.1).1, trivial⟩
  have d₂ : ContinuousWithinAt (fun b => T.fr j (x b, w₀)) W b₀ :=
    ContinuousWithinAt.comp (f := fun b : Fin m → ℂ => ((x b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      ((T.fr_hol j).continuousOn _ ⟨(hx b₀ hb₀).1, m₃ b₀ hb₀W⟩) hκ fun b h => ⟨(hx b h.1).1, m₃ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, valAt' (q b) ((PPx yA.x).U (fun _ => j)) (yA.s.f (fun _ => j)) =
      a b * (thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀) * T.fr j (x b, w₀)) := fun b h => by
    obtain ⟨-, -, pm, p₁, p₂, p₃⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (P b) w₀).left
      (((Category.id_comp _).trans (hxu b h.1)).trans (Over.w (F.ex k (P b) w₀)).symm)
    have e₁' : pt ≫ Formalism.L2.PjFree.gxFst (y b).x = (F.ex k (T.Pf (T.co (x b))) w₀).left := by
      rw [(hx b h.1).2.1]
      exact e₁
    rw [← mul_assoc]
    refine Eq.trans ?_ ((hx b h.1).2.2.2.2 j w₀ pt e₁' e₂ (m₃ b h))
    refine (val_pull (φ b) yA.x (y b).x yA.s (y b).s pm p₁ p₂ p₃ _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)).symm
    rw [e₁]
    exact m₂ b h
  have nz : ∀ b ∈ W, thetaChar (T.ta (x b)) T.c₁ T.c₂ (T.h (x b) *ᵥ w₀) * T.fr j (x b, w₀) ≠ 0 := fun b h =>
    right_ne_zero_of_mul (key b h ▸ vnz b h)
  have d : ContinuousWithinAt a W b₀ :=
    ((d₃.continuousOn b₀ hb₀W).mul ((d₁.mul d₂).inv₀ (nz b₀ hb₀W))).congr
      (fun b h => ((mul_inv_eq_iff_eq_mul₀ (nz b h)).2 (key b h)).symm)
      ((mul_inv_eq_iff_eq_mul₀ (nz b₀ hb₀W)).2 (key b₀ hb₀W)).symm
  exact d.continuousAt (hW.mem_nhds hb₀W)

end GlobalTheory.ThetaScalar
