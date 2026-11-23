import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocSec

theorem exists_secTie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)
    (σ : LB.Sec t.PP.L) : ∃ s : LB.Sec (PPx x), SecTie m σ s := by
  obtain ⟨w, g1, r1, -⟩ := m.lin
  obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w).1 g1) Xo.univ.t.PP.isLB t.PP.isLB σ
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t.G.left := m.cart.1.lift _ _ cond
  have hφ : h ≫ m.φ = (snd (Over.mk x) A).left := m.cart.1.lift_fst _ _ cond
  have hh : h ≫ t.G.hom = (fst (Over.mk x) A).left := m.cart.1.lift_snd _ _ cond
  have uniq : ∀ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m.φ → g ≫ (fst (Over.mk x) A).left = t.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  refine ⟨thfPull1 Xo.univ.t.PP.L h hφ s1, w, s1, ⟨g1, r1⟩,
    (TieCalc.isoMaps_iff w σ s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    fun g e₁ e₂ (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩
  exact Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))

theorem exists_unit_secInt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → ∃ a : T.Frˣ, ∀ (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (y' : FrPt Xo c T.Fr), FrChg g (a : T.Fr) y y' → SecInt T m1 m2 y'.s := by
  intro E _ _ _ H Dw l Xo c T io G t' x m1 m2
  let _ := io.toAlgebra
  intro y hy
  subst hy
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨θ, hne, -⟩ := KeyOnPol.exists_generator hS G.pol
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  obtain ⟨hθ, σ, hσ, -, hgen⟩ := SectionBaseChange.generates_and_baseChange hS T.V T.Fr (algebraMap T.V T.Fr) G.pol t'.G
    m2.φ t'.PP.L w2 θ m2.cart.1 t'.PP.isLB g2 hne
  obtain ⟨s, hs⟩ := exists_secTie m1 σ
  obtain ⟨a, ha, -⟩ := y.gen s
  have a0 : a ≠ 0 := by
    rintro rfl
    have z0 : ∀ i, s.f i = scal y.x 0 i * s.f i := fun i => by
      rw [ha i]
      simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_zero, zero_mul]
    have e0 := (TieCalc.secTie_scale m1 hs 0 z0).1 hs
    have e1 := (TieCalc.secTie_scale m1 hs 1 (fun i => by rw [SecCalc.scal_one', _root_.one_mul])).1 hs
    obtain ⟨b, -, hb⟩ := hgen σ
    exact zero_ne_one ((hb 0 e0).trans (hb 1 e1).symm)
  refine ⟨Units.mk0 a a0, fun g y' hc => ⟨θ, hθ, w2, σ, thfPull G.t.PP.L m2.φ θ, ⟨g2, r2⟩,
    fun (j : PUnit → G.t.PP.L.ι) k => Eq.trans (fn_ext fun p hp => (gs_res _ p _ hp _).trans
      ((gs_appLE m2.φ _ _ _ (𝟙 _) p hp.1 _).trans (gs_appLE m2.φ _ _ _ (𝟙 _) p hp _).symm))
      (hσ j k (inf_le_left.trans (LB.wchart_le G.t.PP.L _ j PUnit.unit))), fun j hj => rfl, ?_⟩⟩
  obtain ⟨hx, -, pm, p₁, p₂, hp⟩ := hc
  refine ((TieCalc.secTie_calc E H Dw l Xo T.Fr y.x t' m1 σ s hs).1 1 y'.x y'.s σ hx ⟨pm, p₁, p₂, fun i h => ?_⟩).2
    ((TieCalc.secTie_scale m1 hs 1 (fun i => by rw [SecCalc.scal_one', _root_.one_mul])).1 hs)
  have e : scal y.x 1 i * s.f i = scal y.x a i * y.s.f i :=
    ((congrArg (· * s.f i) (SecCalc.scal_one' y.x i)).trans (_root_.one_mul _)).trans (ha i)
  exact (congrArg _ e).trans (hp i h)

end GlobalTheory.LamT.LocSec
