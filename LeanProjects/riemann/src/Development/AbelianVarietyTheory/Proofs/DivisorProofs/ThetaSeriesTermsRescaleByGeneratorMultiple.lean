import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section
namespace GlobalTheory.Mum.Rescale

theorem valF_resTop_scal {R F : Type} [CommRing R] [Field F] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : R →+* F)
    (y : Sp F ⟶ X) (hy : y ≫ p = spMap f) (W : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ W) (r : R) :
    valF y W (resTop W (scal p r)) = f r := by
  have e1 : resTop W (scal p r) = (p.appLE ⊤ W (le_top.trans (by simp))).hom (ZH.fn r) := rfl
  rw [e1]
  refine (GlobalTheory.MatchCoord.valF_appLE p ⊤ _ h (ZH.fn r)).trans ?_
  rw [hy]
  exact GlobalTheory.OriginFrame.valF_spMap_fn f r

theorem sF_scal {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (s t : H0 D.P.L 1) (r : R) (hs : ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * t.f j)
    (y : TF (R := R) F ⟶ D.P.A) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) :
    GlobalTheory.Ex.sF s y.left J = algebraMap (FractionRing R) F (algebraMap R _ r) * GlobalTheory.Ex.sF t y.left J := by
  unfold GlobalTheory.Ex.sF
  have hs' := hs (fun k => J (y.left ≫ (fun _ : Fin 1 => 𝟙 D.P.A.left) k))
  erw [hs']
  by_cases h : ⊤ ≤ y.left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun k => J (y.left ≫ (fun _ : Fin 1 => 𝟙 D.P.A.left) k))
  · erw [GlobalTheory.MatchCoord.valF_mul h]
    congr 1
    refine valF_resTop_scal D.P.A.hom ((algebraMap (FractionRing R) F).comp (algebraMap R _)) y.left ?_ _ h r
    rw [Over.w y, GlobalTheory.Ex.spMap_comp']
    rfl
  · simp only [valF, dif_neg h, mul_zero]

end GlobalTheory.Mum.Rescale

noncomputable section
namespace GlobalTheory.Mum.Rescale

theorem txT_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F]
    [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D F N) (th : H0 D.P.L 1) (r : R),
    (∀ j, ν.th.f j = resTop _ (scal D.P.A.hom r) * th.f j) →
    (∀ s : H0 D.P.L 1, ∃ r' : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r') * th.f j) →
    ∃ (N' : GlobalTheory.Ex.NumD F) (ν' : GlobalTheory.Ex.NumOf D F N') (e : N'.X ≃+ N.X), ν'.th = th ∧
      ∀ (m : ℕ) (p : QkPt D F (m ^ 2)) (q : N.QT (m ^ 2)) (q' : N'.QT (m ^ 2)), ν.QPt p q → ν'.QPt p q' →
        ∀ χ, N.txT m q (e χ) = algebraMap (FractionRing R) F (algebraMap R _ r) * N'.txT m q' χ := by
  intro R _ _ D _ _ F _ _ N ν th r h1 h2
  have hrg := GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν
  have key : ∀ x, GlobalTheory.Ex.sF ν.th (ν.eA x).left ν.J =
      algebraMap (FractionRing R) F (algebraMap R _ r) * GlobalTheory.Ex.sF th (ν.eA x).left ν.J :=
    fun x => sF_scal D ν.th th r h1 (ν.eA x) ν.J
  let N' : GlobalTheory.Ex.NumD F := { N with th := fun x => GlobalTheory.Ex.sF th (ν.eA x).left ν.J / ν.rg }
  let ν' : GlobalTheory.Ex.NumOf D F N' :=
    { ν with th := th, th_gen := h2, th_eq := fun x => div_mul_cancel₀ _ hrg }
  have hth : ∀ x, N.th x = algebraMap (FractionRing R) F (algebraMap R _ r) * N'.th x := fun x => by
    show N.th x = _ * (GlobalTheory.Ex.sF th (ν.eA x).left ν.J / ν.rg)
    rw [mul_div_assoc', ← key, eq_div_iff hrg]
    exact ν.th_eq x
  refine ⟨N', ν', AddEquiv.refl _, rfl, ?_⟩
  intro m p q q' hq hq' χ
  let φ : N'.Gt →* N.Gt :=
    { toFun := fun g => ⟨g.b, g.s, g.mult⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hb : φ q'.1.2 = q.1.2 := ν.pt_unique (show ν.Pt p.g (φ q'.1.2) from hq'.2) hq.2
  have hb1 : q'.1.2.b = q.1.2.b := congrArg GlobalTheory.Ex.NumD.Gt.b hb
  have hs1 : q'.1.2.s = q.1.2.s := congrArg GlobalTheory.Ex.NumD.Gt.s hb
  have hpm : φ (q'.1.2 ^ m) = q.1.2 ^ m := (map_pow φ _ m).trans (congrArg (· ^ m) hb)
  have hpb : (q'.1.2 ^ m).b = (q.1.2 ^ m).b := congrArg GlobalTheory.Ex.NumD.Gt.b hpm
  have hps : (q'.1.2 ^ m).s = (q.1.2 ^ m).s := congrArg GlobalTheory.Ex.NumD.Gt.s hpm
  have hy : q'.1.1.toAdd = q.1.1.toAdd := ν.eX.injective (hq'.1.trans hq.1.symm)
  have lhs : N.txT m q (AddEquiv.refl N'.X χ) = ((N.wS (m ^ 2) q.1.2.b (N.ψ q.1.1.toAdd) (q.1.2.s q.1.1.toAdd) /
      GlobalTheory.Ex.mulq N.θ N.σ m q.1.2.b : Fˣ) : F) * (((N.ψ χ * (q.1.2 ^ m).s χ : Fˣ) : F) * N.th (N.c χ * (q.1.2 ^ m).b)) := rfl
  have rhs : N'.txT m q' χ = ((N.wS (m ^ 2) q'.1.2.b (N.ψ q'.1.1.toAdd) (q'.1.2.s q'.1.1.toAdd) /
      GlobalTheory.Ex.mulq N.θ N.σ m q'.1.2.b : Fˣ) : F) * (((N.ψ χ * (q'.1.2 ^ m).s χ : Fˣ) : F) * N'.th (N.c χ * (q'.1.2 ^ m).b)) := rfl
  rw [lhs, rhs, hy, hb1, hs1, hpb, hps, hth]
  ring

end GlobalTheory.Mum.Rescale
