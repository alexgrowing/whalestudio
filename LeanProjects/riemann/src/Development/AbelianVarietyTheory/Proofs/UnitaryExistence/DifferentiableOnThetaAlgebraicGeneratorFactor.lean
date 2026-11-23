import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem chart_iff {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (q : Sp ℂ ⟶ Gx x) (j : Xo.univ.t.PP.L.ι) :
    ⊤ ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ ⊤ ≤ (q ≫ gxFst x) ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
  rw [top_le_preimage_iff_mem, top_le_preimage_iff_mem]
  constructor
  · intro hp
    exact Set.mem_iInter.1 hp (0 : Fin 1)
  · intro hp
    exact Set.mem_iInter.2 fun _ => hp

theorem exists_pt {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (s : Sp ℂ ⟶ Sp R) (p : Sp ℂ ⟶ Xo.univ.t.G.left)
    (h : s ≫ x = p ≫ Xo.univ.t.G.hom) : ∃ q : Sp ℂ ⟶ Gx x, q ≫ gxFst x = p ∧ q ≫ gxSnd x = s :=
  ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) s p h, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem val_pull {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X) (x : Sp ℂ ⟶ Xo.X)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀) (h₁ : pm ≫ gxFst x₀ = gxFst x)
    (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx x) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst x)
    (e₂ : pt ≫ gxSnd x = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U i) :
    valAt' pt ((PPx x).U i) (s.f i) = valAt' q ((PPx x₀).U i) (s₀.f i) := by
  have hq : q = pt ≫ pm := SecCalc.pm_ext _ _
    (e₁.trans (show pt ≫ gxFst x = (pt ≫ pm) ≫ gxFst x₀ by rw [Category.assoc, h₁]))
    (e₃.trans (show spMap φ = (pt ≫ pm) ≫ gxSnd x₀ by
      rw [Category.assoc, h₂, ← Category.assoc, e₂, Category.id_comp]))
  rw [← h₃ i (SecCalc.ppx_le pm h₁ i), hq]
  exact valAt'_appLE pt pm _ _ _ _ hp

theorem val_mul_pull (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (a : ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x y : Sp ℂ ⟶ Xo.X) (hxy : y = x)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (t : LB.Sec (PPx y)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hst : SecBC (RingHom.id ℂ) a x y s t)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx y) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ gxFst x₀ = pt ≫ gxFst y)
    (e₂ : pt ≫ gxSnd y = 𝟙 _) (e₃ : q ≫ gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i) :
    valAt' pt ((PPx y).U i) (t.f i) = a * valAt' q ((PPx x₀).U i) (s₀.f i) := by
  subst hxy
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [SecCalc.spMap_id', Category.id_comp]
  have ht := ((SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ _ _ y y y hy hy).2.1 a s t).1 hst i
  rw [ht, (sec_values_complex_fibre hT E H Dw l Xo y s).1 a i pt e₂,
    val_pull φ x₀ y s₀ s pm h₁ h₂ h₃ i pt q e₁ e₂ e₃ hp]

theorem exists_val_ne (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x u : Sp ℂ ⟶ Xo.X) (hu : u = x) (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ gxFst x₀ = gxFst x) (h₂ : pm ≫ gxSnd x₀ = gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hs : SecGen x s) :
    ∃ (e : Over.mk u ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι), ∀ q : Sp ℂ ⟶ Gx x₀, q ≫ gxFst x₀ = e.left →
      q ≫ gxSnd x₀ = spMap φ → valAt' q ((PPx x₀).U (fun _ => j)) (s₀.f (fun _ => j)) ≠ 0 := by
  subst hu
  obtain ⟨i, pt, hpt, hv⟩ := (sec_values_complex_fibre hT E H Dw l Xo u s).2.1.1 hs
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k : Fin 1 => congrArg i (Subsingleton.elim _ _)⟩
  have hc : gxSnd u ≫ u = gxFst u ≫ Xo.univ.t.G.hom := pullback.condition (f := u) (g := Xo.univ.t.G.hom)
  refine ⟨Over.homMk (pt ≫ gxFst u) ?_, j, fun q e₁ e₃ => ?_⟩
  · show (pt ≫ gxFst u) ≫ Xo.univ.t.G.hom = u
    rw [Category.assoc, ← hc, ← Category.assoc, hpt, Category.id_comp]
  · rw [← val_pull φ x₀ u s₀ s pm h₁ h₂ h₃ _ pt q e₁ hpt e₃ (top_le_preimage_of_valAt'_ne_zero _ hv)]
    exact hv

end

theorem differentiableOn_generator_factor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → DifferentiableOn ℂ κ B → DifferentiableOn ℂ (fun b => toC (a b)) B := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hBd hψ hb hκ b₀ hb₀
  let φ : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  have hP : IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hBd hb), fun x => (T.holPer.2 x).mono hBd⟩
  have hux : ∀ b ∈ B, F.u k (T.Pf (T.co b)) = (z b).x := fun b h =>
    (hb b h).2.2.1.symm.trans (hb b h).2.1.1
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).1.2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) y₀.x (z b₀).x _ (hux b₀ hb₀) y₀.s (z b₀).s pm₀ p₁ p₂ p₃ (z b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx y₀.x, q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx y₀.x, b ∈ B → q ≫ gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ gxSnd y₀.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (gxSnd y₀.x) (gxFst y₀.x) y₀.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback y₀.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx y₀.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co b)) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m B T.h T.ta hB
    (fun b h => ⟨(T.norm b (hBd h)).2.1, (T.norm b (hBd h)).2.2.1⟩)
    (fun i i' => ⟨(T.hol i i').1.mono hBd, (T.hol i i').2.mono hBd⟩)
  have d₀ : DifferentiableOn ℂ κ W := hκ.mono fun b h => h.1
  have d₁ : DifferentiableOn ℂ (fun b => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      hθ hι.differentiableOn fun b h => ⟨h.1, trivial⟩
  have d₂ : DifferentiableOn ℂ (fun b => T.fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      (T.fr_hol j) hι.differentiableOn fun b h => ⟨hBd h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, κ b * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀) * T.fr j (b, w₀) =
      toC (a b) * valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) := fun b h => by
    obtain ⟨⟨-, -, pm, p₁, p₂, p₃⟩, ⟨hyz, -, hbc⟩, hyu, -, hth⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (T.Pf (T.co b)) w₀).left
      (((Category.id_comp _).trans hyu).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
    refine (hth j w₀ pt e₁ e₂ (m₂ b h)).symm.trans ?_
    refine val_mul_pull hT (φ b) (toC (a b)) y₀.x (z b).x (y b).x hyz y₀.s (z b).s (y b).s pm p₁ p₂ p₃ hbc _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)
    rw [e₁]
    exact m₂ b h
  have d : DifferentiableOn ℂ (fun b => toC (a b)) W := (((d₀.mul d₁).mul d₂).mul (d₃.inv vnz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (vnz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.HolGen
