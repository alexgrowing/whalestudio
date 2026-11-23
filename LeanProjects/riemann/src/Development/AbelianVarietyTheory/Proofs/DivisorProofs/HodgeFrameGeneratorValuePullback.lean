import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem gm_eq_of_appLE {T Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {U : T.Opens} {W : Z.Opens} (hW : W ≤ r ⁻¹ᵁ U)
    (hz : z ∈ W) (u : Γ(T, U)ˣ) (v : Γ(Z, W)ˣ) (e : v.val = (r.appLE U W hW).hom u.val) :
    gm r z U u = gm (𝟙 Z) z W v := by
  refine Units.ext ?_
  rw [gm_val r z U (hW hz), gm_val (𝟙 Z) z W hz, e]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hW) z hz _).symm

theorem val_gen_pull : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  intro S' T Z G _ H _ x ψ _ g h a ha r B _ ρ q x' ψ' h' e e' b hb hab z J hJ
  have : QuasiSeparated H.hom := MorphismProperty.of_isPullback h.1 ‹_›
  rw [val_of (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J (fun _ => J x')
      (fun _ => by rw [e]),
    val_of (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J (fun _ => J x')
      (fun _ => by rw [Category.id_comp])]
  have hW : LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') ≤
      r ⁻¹ᵁ LB.wchart (hodge G g) (fun _ : PUnit => x) (fun _ => J x') := fun y hy =>
    Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      rw [← e] at this ⊢
      exact this
  have hz : z ∈ LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') := Set.mem_iInter.2 fun _ => hJ x'
  have k {U : T.Opens} {V W : Z.Opens} (hV : V ≤ r ⁻¹ᵁ U) (h₁ : W ≤ V) (s : Γ(omega H, U)) :
      GlobalTheory.Twist.resM _ h₁ ((omegaBase q).app V (pullbackSections r _ hV s)) =
        (omegaBase q).app W (pullbackSections r _ (h₁.trans hV) s) := by
    rw [← GlobalTheory.QCoh.res_pullbackSections r _ hV h₁ s]
    exact congr($((omegaBase q).mapPresheaf.naturality (homOfLE h₁).op) (pullbackSections r _ hV s)).symm
  refine gm_eq_of_appLE r z hW hz _ _ ?_
  have hc := isFrame_chart h (fun _ => J x')
  refine Eq.trans ?_ (hc.val_detUnit_pullback ha r le_rfl le_top hW)
  refine congrArg Units.val ?_
  refine Eq.trans ?_ (IsFrame.detUnit_map_iso _ _ (omegaBase q) _ _)
  refine GlobalTheory.Vert.DivPull.detUnit_congr _ _ _ _ _ _ _ _ (fun i => ?_) (fun i => ?_)
  · refine Eq.trans (GlobalTheory.Twist.resM_self _ _) (Eq.trans ?_ (k _ _ _).symm)
    exact (GlobalTheory.BadPt.Fibre.omegaBase_comp h q h' e e' _ _ _ _).symm
  · rw [hab]
    exact (k _ _ _).trans (k _ _ _).symm

end GlobalTheory.HodgeFrameGen
