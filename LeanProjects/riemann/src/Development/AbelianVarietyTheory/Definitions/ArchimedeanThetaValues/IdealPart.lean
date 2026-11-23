import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Wit
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}

abbrev gen : Sp ℂ⸨X⸩ ⟶ Sp ℂ⟦X⟧ := spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)

abbrev selfR : Over (Sp ℂ⟦X⟧) := Over.mk (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))

structure ConstPts (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) where
  g : Λ.A.V → Out.GtPt W.P.D.toPre selfR
  g_rel : ∀ v x, GenRelR (A := ℂ⟦X⟧) W.w ((g v).s (W.e x))
    (LB.pullGen _ _ _ ((Λ.ex0 v).s x) (spMap (PowerSeries.C (R := ℂ))))
  x : Λ.A.V → (selfR ⟶ W.t.G)
  x_pt : ∀ v, FormalPoint.IsPointOf W.P.U.toUnifPre (g v) (x v)
  x_fm : ∀ v, FormalValue.IsFormalPt W.P.U.toUnifPre
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) (g v) (x v).left
  τ : Λ.A.V → W.P.U.LG.L.ι → ℂ⟦X⟧
  τ_eq : ∀ v (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι), ⊤ ≤ (x v).left ⁻¹ᵁ W.P.U.LG.L.U jL →
    ⊤ ≤ (g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) →
    valR (A := ℂ⟦X⟧) (g v).b.left _ (W.w.s (fun _ => j₀, jM)).val * τ v jL =
      (FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
        (x v).left jL jM).val * PowerSeries.C (Λ.u.fr j₀ v.2)

def ConstPts.Vals {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a} (Ξ : ConstPts W Λ) {j : ℕ} (σ : Out.H0 W.P.U.LG.L j)
    (f : Λ.A.V → ℂ⸨X⸩) : Prop :=
  ∀ v jL, ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U jL →
    (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x v).left jL) =
      f v * (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) (Ξ.τ v jL) ^ j

def ConstPts.IsGen {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a} (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) : Prop :=
  ∀ v, (Φ.x v).left = gen ≫ (Ξ.x v).left ∧ ∀ (jL : W.P.U.LG.L.ι) (j : W.t.PP.L.ι), HEq jL j →
    ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U jL → Φ.τ v j = (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) (Ξ.τ v jL)

def DiffHyp (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) {g : ℕ} (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ)
    (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) : Prop :=
    IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex₀ z).b.left)) z₀ ν.b.left ∧
    (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j →
      valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val =
        TrivSqZeroExt.inl (chiVal (ex₀ 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex₀ z) x j) 0 z₀)) ∧
    (∀ (n : ℕ) (ρ : DualNumber (PowerSeries ℂ) →+* DualNumber (PowerSeries ℂ ⧸ Ideal.span {PowerSeries.X} ^ (n + 1)))
      (κ : DualNumber ℂ →+* DualNumber (PowerSeries ℂ ⧸ Ideal.span {(PowerSeries.X : PowerSeries ℂ)} ^ (n + 1)))
      (vn : Sp (DualNumber (PowerSeries ℂ ⧸ Ideal.span {(PowerSeries.X : PowerSeries ℂ)} ^ (n + 1))) ⟶
        (Out.thickObj (PowerSeries ℂ) (Ideal.span {PowerSeries.X}) n W.t.G).left),
      (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ r)) → ρ DualNumber.eps = DualNumber.eps →
      (∀ r, κ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (PowerSeries.C r))) →
      κ DualNumber.eps = DualNumber.eps →
      vn ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap ρ ≫ v.left →
      ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn) (LB.pullGen _ _ _ (ν.s x) (spMap κ)))

def ThetaHyp (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) : Prop :=
    (∃ j, th.f j ≠ 0) ∧ (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) ∧
    (∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j))

def PullHyp (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (σ : Out.H0 W.P.U.LG.L 1) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (U : Y.X.Opens)
    (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ) : Prop :=
      (∀ (j : Y.t.PP.L.ι) (k : W.P.U.LG.L.ι) (V : W.t.G.left.Opens)
        (h₁ : V ≤ W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j))
        (h₂ : V ≤ (LB.div (Y.t.PP.L.pull W.m.φ) W.P.U.LG.L).U (fun _ => j, k))
        (h₃ : V ≤ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k)),
        (W.m.φ.appLE _ _ h₁).hom (s j) =
          resG _ h₂ (w₂.s (fun _ => j, k)).val * constFn W.t.G.hom V r * resG _ h₃ (σ.f (fun _ => k)))

structure Chain {bF : c.F →+* ℂ} {a : ArcIn D l β ℂ (bF.comp β)} (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) where
  Ξ : ConstPts W Λ
  ΦW : GenPts Λ.A W.t gen
  isGen : Ξ.IsGen ΦW
  yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c
  yF_j : yF ≫ Y.j = gen ≫ χ
  yF_over : yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF)
  ΦY : GenPts Λ.A Y.t (gen ≫ χ)
  ΦF : GenPts Λ.A Y.oF.t yF
  Φ : GenPts Λ.A Xo.univ.t (yF ≫ pullback.fst _ _)
  w₂ : LB.Iso W.t.PP.L (Y.t.PP.L.pull W.m.φ)
  w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)
  w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)
  rig₂ : IsRigIso W.m.cm W.t.PP Y.t.PP w₂
  rig₁ : IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁
  rig₀ : IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀
  rel₂ : GenPts.Rel W.m w₂ ΦW ΦY
  rel₁ : GenPts.Rel Y.m w₁ ΦF ΦY
  rel₀ : GenPts.Rel Y.m0.toSABMap w₀ ΦF Φ

end Wit

abbrev idealPart (D : Datum H) (l : Level H) : Submodule (𝓞 E) D.La :=
  l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)

structure Cmp {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E))
    (yw : ℂ → (Sp ℂ ⟶ Xo.X)) (π : ∀ w, A.V → (Over.mk (yw w) ⟶ Xo.univ.t.G)) (laA laM : D.La → A.La) where
  i : Fin Fu.n
  T : ℝ
  gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La
  h : A.V ≃L[ℂ] (Fin g → ℂ)
  EF_eq : ∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v
  h_act : ∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k
  Pw : ℂ → ((Fu.Di i).La →+ (Fin g → ℂ))
  Pw_eq : ∀ w u, Pw w u = h (A.Pw w (gam u))
  period : ∀ w : ℂ, T < w.im → IsPeriod (Fu.Di i) ty (Pw w)
  u_eq : ∀ w : ℂ, T < w.im → Fu.u i (Pw w) = yw w
  ex_eq : ∀ w : ℂ, T < w.im → ∀ v, (Fu.ex i (Pw w) (h v)).left = (π w v).left
  levA : ∀ v, ∃ e, gam (Fu.t i v) = laA v + l.A • e
  levM : ∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = laM v + l.M • e

end GlobalTheory.ArcPts
