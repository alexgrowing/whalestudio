import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionCoefficientsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ChainPts.PtPull

theorem kerAt_pull {X X' : Scheme.{0}} (g : X' ⟶ X) {R : Type} [CommRing R] (w : Sp R ⟶ X') {F Q : X.Modules}
    (u : F ⟶ Q) {Q' : X'.Modules} (u' : (Scheme.Modules.pullback g).obj F ⟶ Q')
    (e : Q' ≅ (Scheme.Modules.pullback g).obj Q) (hu : u' ≫ e.hom = (Scheme.Modules.pullback g).map u)
    {V : X.Opens} (hV : ⊤ ≤ (w ≫ g) ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ g ⁻¹ᵁ V) {r : ℕ} (s : Fin r → Γ(F, V)) :
    kerAt w u' hV' (fun l => pullbackSections g F le_rfl (s l)) = kerAt (w ≫ g) u hV s := by
  ext c
  simp only [kerAt, Set.mem_setOf_eq]
  have hx : ((Scheme.Modules.pullbackComp w g).inv.app F).app ⊤
      (∑ l, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c l) • pullbackSections (w ≫ g) F hV (s l)) =
      ∑ l, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c l) •
        pullbackSections w _ hV' (pullbackSections g F le_rfl (s l)) := by
    simp only [map_sum, Scheme.Modules.Hom.app_smul, GlobalTheory.Vert.DivPull.pullbackComp_inv_app w g F le_rfl hV' hV]
  rw [← hx]
  let I : (Scheme.Modules.pullback (w ≫ g)).obj Q ≅ (Scheme.Modules.pullback w).obj Q' :=
    ((Scheme.Modules.pullbackComp w g).app Q).symm ≪≫ (Scheme.Modules.pullback w).mapIso e.symm
  have hu' : u' = (Scheme.Modules.pullback g).map u ≫ e.inv := by
    rw [← hu, Category.assoc, e.hom_inv_id, Category.comp_id]
  have nat : (Scheme.Modules.pullbackComp w g).inv.app F ≫ (Scheme.Modules.pullback w).map u' =
      (Scheme.Modules.pullback (w ≫ g)).map u ≫ I.hom := by
    rw [hu', Functor.map_comp]
    exact ((Scheme.Modules.pullbackComp w g).inv.naturality_assoc u _).symm
  generalize (∑ l, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c l) • pullbackSections (w ≫ g) F hV (s l)) = t
  have key : ((Scheme.Modules.pullback w).map u').app ⊤ (((Scheme.Modules.pullbackComp w g).inv.app F).app ⊤ t) =
      I.hom.app ⊤ (((Scheme.Modules.pullback (w ≫ g)).map u).app ⊤ t) := congr(($nat).app ⊤ t)
  refine key ▸ ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have h1 : I.inv.app ⊤ (I.hom.app ⊤ (((Scheme.Modules.pullback (w ≫ g)).map u).app ⊤ t)) =
        ((Scheme.Modules.pullback (w ≫ g)).map u).app ⊤ t :=
      congr(($(I.hom_inv_id)).app ⊤ (((Scheme.Modules.pullback (w ≫ g)).map u).app ⊤ t))
    rw [← h1, h0, map_zero]
  · rw [h0, map_zero]

theorem valF_appTop {k : Type} [Field k] {X X' : Scheme.{0}} (w : Sp k ⟶ X') (g : X' ⟶ X) (c : Γ(X, ⊤)) :
    valF w ⊤ (g.appTop c) = valF (w ≫ g) ⊤ c := by
  rw [← PullHT.valF_appLE w g (U := ⊤) (U' := g ⁻¹ᵁ ⊤) le_rfl le_rfl c, Scheme.Hom.appLE_eq_app]
  rfl

theorem valF_coef_pull {k : Type} [Field k] {X X' : Scheme.{0}} (w : Sp k ⟶ X') (g : X' ⟶ X) {F : X.Modules}
    [F.IsQuasicoherent] {r : ℕ} (d : Bool) {V V' : X.Opens} {U' : X'.Opens} (hU' : U' = g ⁻¹ᵁ V')
    {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')} (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s)
    (hs' : GlobalTheory.VB.IsFrame fun i => pullbackSections g F hU'.le (s i)) (l i : Fin r) :
    valF w _ (coef d (PullHT.isFrame_pullS g le_rfl he) hs' l i) = valF (w ≫ g) _ (coef d he hs l i) := by
  rw [show coef d (PullHT.isFrame_pullS g le_rfl he) hs' l i = _ from
    PullHT.coef_pulled_frames g d le_rfl hU'.le he hs l i]
  exact PullHT.valF_appLE w g _ (by subst hU'; exact le_rfl) _

theorem pt_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {X X' : Scheme.{0}} (g : X' ⟶ X) (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (F Q : X.Modules) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) (hs' : ∀ a, GlobalTheory.VB.IsFrame (pullS g s a)) (u : F ⟶ Q) (Q' : X'.Modules) (u' : (Scheme.Modules.pullback g).obj F ⟶ Q') (e : Q' ≅ (Scheme.Modules.pullback g).obj Q), GlobalTheory.VB.IsVB F r → u' ≫ e.hom = (Scheme.Modules.pullback g).map u → (∀ π : Γ(X, ⊤), PtJ Z h x hs π u → PtJ Z (g ≫ h) x hs' (g.appTop π) u') ∧ (PtR Z h x hs u → PtR Z (g ≫ h) x hs' u') := by
  intro E _ _ _ H Dw Xo p _ W Y i₀ Z X X' g h r x F Q s hs hs' u Q' u' e hF hu
  haveI := hF.isQuasicoherent
  refine ⟨fun π hJ y w hw a φ hφ => ?_, fun hR y w hw a φ hφ => ?_⟩
  · obtain ⟨V, f, hf, hV, hc⟩ := hJ y (w ≫ g) (by rw [Category.assoc]; exact hw) a φ hφ
    refine ⟨g ⁻¹ᵁ V, _, PullHT.isFrame_pullS g le_rfl hf, hV, ?_⟩
    rw [kerAt_pull g w u u' e hu hV hV f]
    intro cf v hv
    have h1 := hc cf v hv
    have h2 := fun l i => valF_coef_pull (spMap (intO ↥y.C.S).subtype ≫ w) g false
      (Scheme.Hom.comp_preimage g h (Z.U a).1) hf (hs a) (hs' a) l i
    simp only [← Category.assoc, ← h2, ← valF_appTop (spMap (intO ↥y.C.S).subtype ≫ w) g π] at h1
    exact h1
  · obtain ⟨V, f, hf, hV, hc⟩ := hR y (w ≫ g) (by rw [Category.assoc]; exact hw) a φ hφ
    refine ⟨g ⁻¹ᵁ V, _, PullHT.isFrame_pullS g le_rfl hf, hV, ?_⟩
    rw [kerAt_pull g w u u' e hu hV hV f]
    intro cf v hv
    have h1 := hc cf v hv
    have h2 := fun l i => valF_coef_pull (spMap (intO ↥y.C.S).subtype ≫ w) g true
      (Scheme.Hom.comp_preimage g h (Z.U a).1) hf (hs a) (hs' a) l i
    simp only [← Category.assoc, ← h2] at h1
    exact h1

end GlobalTheory.ChainPts.PtPull
