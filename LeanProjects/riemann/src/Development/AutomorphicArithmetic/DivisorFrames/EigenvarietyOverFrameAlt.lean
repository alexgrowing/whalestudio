import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.FrameGenericComplex
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

theorem UpperTheory.eigenvariety_over_frame_alt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (B Y : Var F) (ρB : B.X ⟶ gen Z) (ρ : Y.X ⟶ gen Z) (f : Y.X ⟶ B.X) (φ : B.Fn →+* Y.Fn), IsOver e ρB ρ f φ → ρB ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∀ (g : GenFrame e ρB) (g' g₁ : GenFrame e ρ), g.IsMap φ g' → ∀ (τ : E →+* ℂ) (XB X : Scheme.{0}) (jB : B.X ⟶ XB) (j : Y.X ⟶ X) (π : X ⟶ XB), j ≫ π = f ≫ jB → ∀ (M : XB.Modules) (hM : IsVB M (Dw.mult τ)) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B.Fn) (A' : Chart ((Scheme.Modules.pullback π).obj M) (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), IsLie g τ jB dual A → IsLie g₁ τ j dual A' → IsPullCo jB π hM dual φ g' g₁ A A' → ∀ (q : XB ⟶ Sp (𝓞 F)) (q' : X ⟶ Sp (𝓞 F)) (hq : π ≫ q = q') (G : ∀ σ : c.F →+* ℂ, EigMet Z σ) (h : VMetric q M (Dw.mult τ)), IsMet g τ jB dual A G h → IsMet g₁ τ j dual A' G (h.pull π hq) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e B Y ρB ρ f φ hov hB g g' g₁ hg τ XB X jB j π hj M hM dual A A' hA hA' hco
    q q' hq G h hmet
  have hY : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str := by
    rw [← hov.1, Category.assoc, hB, hov.2.1]
  refine UpperTheory.frame_generic_complex E H Dw l Xo c O β Z F e Y ρ hY g₁ τ X j _ (hM.pullback π) dual A' q' G _ hA' fun x => ?_
  obtain ⟨U, s, hU, hs⟩ := hM (π x)
  let ch : Chart M (Dw.mult τ) := ⟨U, s, hs⟩
  refine ⟨ch.pull hM π, hU, ?_⟩
  intro σ p z hz hzU φ₁ f₁ hf₁ yc hyc gg hgg
  let p' : Pts B σ := ⟨p.1 ≫ f, by rw [Category.assoc, hov.2.1]; exact p.2⟩
  have hz' : (Points.PtsOver.map π hq _ z).1 = p'.1 ≫ jB := by
    change z.1 ≫ π = (p.1 ≫ f) ≫ jB
    rw [hz, Category.assoc, hj, Category.assoc]
  have hzU' : Points.PtsOver.map π hq _ z ∈ CxPts.ptsIn q _ ch.U := hzU
  have hb : jB (f (Var.base p)) ∈ ch.U := by
    have := CxPts.mem_ptsIn.1 hzU'
    rw [hz'] at this
    exact this
  obtain ⟨φ₀, k, hk⟩ := hA.2 ch (f (Var.base p)) hb
  obtain ⟨k₁, hkk, hk₁⟩ := hk.pull hov hg g₁
  rw [hco ch (gen_le jB hb), lieMat_mul, lieMat_lieMat _ (g₁.isUnit_det_co g' τ),
    lieMat_map _ _ (hA.1.1 ch (gen_le jB hb))] at hf₁
  obtain rfl := hf₁.φ_eq hk₁
  have hone : k₁.co f₁ τ = 1 := hk₁.co_eq (by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]; exact hf₁)
  have hp : spMap (Var.evStalk p) ≫ stalkPt Y (Var.base p) = p.1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk p.1
  have hev : (Var.evStalk p).comp (f.stalkMap (Var.base p)).hom = Var.evStalk p' :=
    (congrArg CommRingCat.Hom.hom (Scheme.stalkClosedPointTo_comp p.1 f)).symm
  have hφ : embOf e σ = (Var.evStalk p).comp ((f.stalkMap (Var.base p)).hom.comp φ₀) := RingHom.ext fun a => by
    have h3 : ((f.stalkMap (Var.base p)).hom.comp φ₀) a = algebraMap F _ (e.symm a) := toFn_injective _
      ((RingHom.congr_fun hk₁.1 a).symm.trans ((Y.stalkIncl (Var.base p)).commutes _).symm)
    rw [RingHom.comp_apply, RingHom.comp_apply, h3]
    exact ((Var.evStalk_germ (U := ⊤) trivial _).trans (CxPts.ev_algX CxPts.mem_ptsIn_top _)).symm
  have hx : yc.1 ≫ genι Z = spMap (Var.evStalk p) ≫ stalkPt Y (Var.base p) ≫ ρ ≫ genι Z := by
    rw [← Category.assoc, hp, hyc, Category.assoc]
  obtain ⟨g₂, hg₂⟩ := k₁.exists_isMap (Var.evStalk p) hφ hx
  have hkg : k.IsMap (Var.evStalk p') g₂ := fun τ i => by
    rw [hg₂ τ i, hkk τ i, ← hev, GlobalTheory.GradedPieces.dual_comp]
  have hgram : (G _).gram yc gg τ = (G _).gram yc g₂ τ := by
    rw [(G _).change yc g₂ gg τ, hg₂.co τ hgg hx, hone, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have := hmet ch σ p' _ hz' hzU' φ₀ k hk yc (by rw [hyc, ← hov.1]; exact (Category.assoc _ _ _).symm) g₂ hkg
  rw [hgram, ← this]
  exact (h.met _).pull_G π hq ch hzU'
