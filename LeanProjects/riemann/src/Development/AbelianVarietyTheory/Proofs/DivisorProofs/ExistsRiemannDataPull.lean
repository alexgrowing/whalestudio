import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

noncomputable section

namespace GlobalTheory.HodgePull

open GlobalTheory.Points GlobalTheory.HermFrame

theorem sqMap_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : A'.left ⟶ A.left} {φ' : A''.left ⟶ A'.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) (w' : φ' ≫ A'.hom = A''.hom ≫ g)
    (w'' : (φ' ≫ φ) ≫ A.hom = A''.hom ≫ (g ≫ f)) :
    sqMap w' ≫ sqMap w = sqMap w'' := by
  unfold sqMap
  exact Limits.pullback.map_comp ..

theorem exists_dChart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (P : PPAS X) (y : CxPts p σ) :
    ∃ (c : Chart (LieVB.omega P.A) P.g) (W : P.A.left.Opens)
      (hW : c.U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Fin P.g → Γ(P.A.left, W)),
      y ∈ ptsIn p σ c.U ∧ ∀ a, c.e a = LieVB.dUnit P.A hW (f a) := by
  obtain ⟨U, W, hx, hle, c⟩ := Conormal.exists_isChart (LieVB.sec_hom (MonObj.one (X := P.A)))
    (mem_ptsIn.1 (P.isVB_omega.mem_pick y))
  choose f hf using fun a => c.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A)))
    (GlobalTheory.Twist.resM (LieVB.omega P.A) hle ((P.isVB_omega.pick y).e a))
  exact ⟨⟨U, fun a => GlobalTheory.Twist.resM _ hle ((P.isVB_omega.pick y).e a),
    (P.isVB_omega.pick y).isFrame.res hle⟩, W, c.le, f, mem_ptsIn.2 hx, fun a => (hf a).symm⟩

theorem exists_riemannData_pull {X Y : Scheme.{0}} {π : Y ⟶ X} {P : PPAS X} {P' : PPAS Y}
    {φ : P'.A.left ⟶ P.A.left} (hφ : IsGrpPullback P'.A P.A π φ) (hg : P'.g = P.g)
    (hc : P'.c = CechPic.pull (sqMap hφ.1.w) P.c) {z : Sp ℂ ⟶ Y} (d' : P'.RiemannData z) (t : ℂ) :
    ∃ d : P.RiemannData (z ≫ π), ∀ (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)),
      form (dualGram (t • d.H)) (d.cov W f) (d.cov W f') =
        form (dualGram (t • d'.H)) (d'.cov (φ ⁻¹ᵁ W) (φ.app W f))
          (d'.cov (φ ⁻¹ᵁ W) (φ.app W f')) := by
  obtain ⟨A', isAb', g', sd', c', pol'⟩ := P'
  change g' = P.g at hg
  subst hg
  have hp := d'.isPull.comp hφ
  refine ⟨⟨d'.B, d'.φ ≫ φ, hp, d'.L, d'.isLB, ?_, d'.u, d'.H, d'.χ, d'.isAH⟩, fun W f f' => ?_⟩
  · rw [← sqMap_comp hφ.1.w d'.isPull.1.w hp.1.w, CechPic.pull_comp]
    change (CechPic.pull (sqMap d'.isPull.1.w)) (CechPic.pull (sqMap hφ.1.w) P.c) = _
    rw [← hc]
    exact d'.pol
  · have e (f : Γ(P.A.left, W)) (w : Fin P.g → ℂ) :
        valR ((d'.u.ex w).left ≫ d'.φ ≫ φ) W f =
          valR ((d'.u.ex w).left ≫ d'.φ) (φ ⁻¹ᵁ W) (φ.app W f) := by
      rw [← Category.assoc]
      exact valR_comp _ _ _ _
    exact congrArg₂ (form (dualGram (t • d'.H)))
      (funext fun a => congrArg (fun F => fderiv ℂ F 0 (Pi.single a 1)) (funext (e f)))
      (funext fun a => congrArg (fun F => fderiv ℂ F 0 (Pi.single a 1)) (funext (e f')))

theorem form_eq_of_frames {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {σ : k →+* ℂ} {π : Y ⟶ X} (hπ : π ≫ p = q) {E : X.Modules} {E' : Y.Modules} {r r' : ℕ}
    (hr : r' = r) (h : Met p σ E r) (h' : Met q σ E' r')
    (α : (Scheme.Modules.pullback π).obj E ⟶ E') [IsIso α]
    (H : ∀ z : CxPts q σ, ∃ c : Chart E r, PtsOver.map π hπ _ z ∈ ptsIn p σ c.U ∧ ∀ a b,
      h'.form (α.app _ (QCoh.pullbackSections π E (le_refl (π ⁻¹ᵁ c.U)) (c.e a)))
        (α.app _ (QCoh.pullbackSections π E (le_refl (π ⁻¹ᵁ c.U)) (c.e b))) z =
        h.form (c.e a) (c.e b) (PtsOver.map π hπ _ z))
    {U : Y.Opens} (s s' : Γ((Scheme.Modules.pullback π).obj E, U)) {z : CxPts q σ}
    (hz : z ∈ ptsIn q σ U) :
    h'.form (α.app U s) (α.app U s') z = (h.pull π hπ).form s s' z := by
  subst hr
  have key : h' = (h.pull π hπ).map (asIso α) := Met.ext_of_exists fun z => by
    obtain ⟨c, hy, e⟩ := H z
    have hz' : z ∈ ptsIn q σ ((c.pull h.isVB π).map (asIso α)).U := hy
    refine ⟨_, hz', Matrix.ext fun a b => ?_⟩
    have e₁ := ((h.pull π hπ).map_G (asIso α) (c.pull h.isVB π) hz').trans (h.pull_G π hπ c hy)
    exact ((h'.form_frame _ hz' a b).symm.trans (e a b)).trans
      ((h.form_frame c hy a b).trans (congrFun₂ e₁ a b).symm)
  rw [key]
  exact Met.form_map _ (asIso α) s s' hz

theorem form_omegaBase : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Y : Scheme.{0}) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (P : PPAS X) (P' : PPAS Y) (φ : P'.A.left ⟶ P.A.left) (hφ : IsGrpPullback P'.A P.A π φ), P'.g = P.g → P'.IsPull P π φ → ∀ (t : ℝ) (h : VMetric p (LieVB.omega P.A) P.g) (h' : VMetric q (LieVB.omega P'.A) P'.g), P.IsDualRiemann t h → P'.IsDualRiemann t h' → ∀ (σ : k →+* ℂ) (U : Y.Opens) (s s' : Γ((Scheme.Modules.pullback π).obj (LieVB.omega P.A), U)), ∀ z ∈ ptsIn q σ U, (h'.met σ).form ((LieVB.omegaBase hφ).app U s) ((LieVB.omegaBase hφ).app U s') z = ((h.pull π hπ).met σ).form s s' z := by
  intro k _ X p Y q π hπ P P' φ hφ hg hpull t h h' H H' σ U s s' z hz
  obtain ⟨_, hc⟩ := hpull
  refine form_eq_of_frames hπ hg (h.met σ) (h'.met σ) (LieVB.omegaBase hφ) (fun z => ?_) s s' hz
  obtain ⟨c, W, hW, f, hy, hf⟩ := exists_dChart (σ := σ) P (PtsOver.map π hπ _ z)
  refine ⟨c, hy, fun a b => ?_⟩
  have hz' : z ∈ ptsIn q σ (π ⁻¹ᵁ c.U) := hy
  have hW' := Conormal.le_of_sq (LieVB.unitSec_comp hφ) hW (le_refl (π ⁻¹ᵁ c.U))
  obtain ⟨d'⟩ := (H' σ z).1
  obtain ⟨d, hd⟩ := exists_riemannData_pull hφ hg hc d' (t : ℂ)
  rw [hf a, hf b, LieVB.omegaBase_dUnit hφ hW le_rfl hW' le_rfl,
    LieVB.omegaBase_dUnit hφ hW le_rfl hW' le_rfl, Scheme.Hom.appLE_eq_app]
  exact ((H' σ z).2 d' _ _ hW' _ _ hz').trans
    ((hd W _ _).symm.trans ((H σ (PtsOver.map π hπ _ z)).2 d c.U W hW (f a) (f b) hy).symm)

end GlobalTheory.HodgePull
