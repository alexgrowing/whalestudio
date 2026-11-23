import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDualRiemann
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRiemannDataPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB Formalism.BasicNotions

namespace GlobalTheory.IsometryPullback

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
  {t : Z ⟶ Sp k} {r : ℕ}

section Isometry

variable {E E' E'' : X.Modules} {h : VMetric p E r} {h' : VMetric p E' r} {h'' : VMetric p E'' r}

theorem isIsometry_symm {φ : E ≅ E'} (H : h.IsIsometry h' φ) : h'.IsIsometry h φ.symm := by
  intro σ V s s' y hy
  have e (u : Γ(E', V)) : φ.hom.app V (φ.inv.app V u) = u := congr(($(φ.inv_hom_id)).app V u)
  have := H σ V (φ.inv.app V s) (φ.inv.app V s') y hy
  rw [e, e] at this
  exact this.symm

theorem isIsometry_trans {φ : E ≅ E'} {ψ : E' ≅ E''} (H : h.IsIsometry h' φ)
    (H' : h'.IsIsometry h'' ψ) : h.IsIsometry h'' (φ ≪≫ ψ) := fun σ V s s' y hy =>
  (H' σ V (φ.hom.app V s) (φ.hom.app V s') y hy).trans (H σ V s s' y hy)

theorem isIsometry_pull {φ : E ≅ E'} (H : h.IsIsometry h' φ) (π : Y ⟶ X) (w : π ≫ p = q) :
    (h.pull π w).IsIsometry (h'.pull π w) ((Scheme.Modules.pullback π).mapIso φ) := by
  intro σ V s s' z hz
  refine HodgePull.form_eq_of_frames w rfl (h.met σ) ((h'.met σ).pull π w)
    ((Scheme.Modules.pullback π).map φ.hom) (fun z => ?_) s s' hz
  have hc := h.isVB.mem_pick (PtsOver.map π w _ z)
  refine ⟨_, hc, fun a b => ?_⟩
  rw [QCoh.pullback_map_app_pullbackSections, QCoh.pullback_map_app_pullbackSections]
  exact ((h'.met σ).form_pull π w _ _ le_rfl hc).trans (H σ _ _ _ _ hc)

theorem exists_isIsometry_pull_congr {π π' : Y ⟶ X} (e : π = π') (w : π ≫ p = q)
    (w' : π' ≫ p = q) : ∃ φ, (h.pull π w).IsIsometry (h.pull π' w') φ := by
  subst e
  exact ⟨Iso.refl _, fun _ _ _ _ _ _ => rfl⟩

end Isometry

variable {E : X.Modules} {E' : Y.Modules} {h : VMetric p E r} {h' : VMetric q E' r}

theorem exists_isIsometry_inv (e : Y ≅ X) (w : e.hom ≫ p = q) (w' : e.inv ≫ q = p)
    {α : (Scheme.Modules.pullback e.hom).obj E ≅ E'} (H : (h.pull e.hom w).IsIsometry h' α) :
    ∃ β, (h'.pull e.inv w').IsIsometry h β := by
  obtain ⟨h₁, h₂⟩ := VMetric.isIsometry_pull_id_comp k X p E r h
  have w₁ : (e.inv ≫ e.hom) ≫ p = p := by simp
  obtain ⟨γ, hγ⟩ := exists_isIsometry_pull_congr (h := h) e.inv_hom_id w₁ (Category.id_comp p)
  exact ⟨_, isIsometry_trans (isIsometry_symm (isIsometry_pull H e.inv w'))
    (isIsometry_trans (h₂ Y X q p e.hom e.inv w w' w₁) (isIsometry_trans hγ h₁))⟩

variable [IsIntegral X] [IsIntegral Y]

omit [IsIntegral Y] in

theorem exists_flagModel_of_eq [IsIntegral Z] (ρ : Z ⟶ X) (w : ρ ≫ p = t) (hZ : IsRegSurf t)
    (hg : ρ (genericPoint Z) = genericPoint X) (hf : ρ.residueDegree (genericPoint Z) ≠ 0)
    (H : (h.pull ρ w).IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback ρ).obj E) r) :
    ∃ M : h.FlagModel, M.deg = ρ.residueDegree (genericPoint Z) ∧
      ∀ a, VMetric.IsFlagCh2 M.cInf M.flag a ↔ VMetric.IsFlagCh2 H fl a := by
  subst w
  exact ⟨⟨⟨Z, ρ, hZ, hg, hf⟩, H, fl⟩, rfl, fun _ => Iff.rfl⟩

theorem exists_flagModel_of_isIsometry (π : Y ⟶ X) [IsIso π] (w : π ≫ p = q)
    {α : (Scheme.Modules.pullback π).obj E ≅ E'} (H : (h.pull π w).IsIsometry h' α)
    (M' : h'.FlagModel) : ∃ M : h.FlagModel, M.deg = M'.deg ∧
      ∀ a, VMetric.IsFlagCh2 M.cInf M.flag a ↔ VMetric.IsFlagCh2 M'.cInf M'.flag a := by
  have w₁ : (M'.ρ ≫ π) ≫ p = M'.ρ ≫ q := by rw [Category.assoc, w]
  have I := isIsometry_trans (isIsometry_symm (isIsometry_pull H M'.ρ rfl))
    ((VMetric.isIsometry_pull_id_comp k X p E r h).2 Y M'.Y q _ π M'.ρ w rfl w₁)
  have hC : (h.pull (M'.ρ ≫ π) w₁).IsCInf := by
    rw [(VMetric.isIsometry_iff _).1 I]
    exact M'.cInf.map _
  have hd : (M'.ρ ≫ π).residueDegree (genericPoint M'.Y) = M'.deg := by
    rw [CurveDegreesCompare.residueDegree_comp,
      CurveDegreesCompare.residueDegree_of_isOpenImmersion π]
    simp [RegCover.deg]
  obtain ⟨M, h₁, h₂⟩ := exists_flagModel_of_eq (M'.ρ ≫ π) w₁ M'.reg
    (by rw [Scheme.Hom.comp_apply, M'.generic, genericPoint_eq_of_isOpenImmersion])
    (hd.trans_ne M'.deg_pos.ne') hC (M'.flag.ofIso _)
  exact ⟨M, h₁.trans hd, fun a => (h₂ a).trans
    (VMetric.isFlagCh2_ofIso k _ _ _ _ r _ _ _ M'.cInf hC M'.flag a I).symm⟩

theorem isCh2Deg_of_isIsometry (π : Y ⟶ X) [IsIso π] (w : π ≫ p = q) (π' : X ⟶ Y) [IsIso π']
    (w' : π' ≫ q = p) {α : (Scheme.Modules.pullback π).obj E ≅ E'}
    (H : (h.pull π w).IsIsometry h' α) {β : (Scheme.Modules.pullback π').obj E' ≅ E}
    (H' : (h'.pull π' w').IsIsometry h β) {a : ℝ} (ha : h.IsCh2Deg a) : h'.IsCh2Deg a := by
  obtain ⟨⟨M⟩, ha⟩ := ha
  obtain ⟨M₀, -⟩ := exists_flagModel_of_isIsometry π' w' H' M
  refine ⟨⟨M₀⟩, fun M' => ?_⟩
  obtain ⟨N, h₁, h₂⟩ := exists_flagModel_of_isIsometry π w H M'
  exact (h₂ _).1 (h₁ ▸ ha N)

theorem isCh2Deg_iff_of_isIsometry (e : Y ≅ X) (w : e.hom ≫ p = q)
    {α : (Scheme.Modules.pullback e.hom).obj E ≅ E'} (H : (h.pull e.hom w).IsIsometry h' α)
    (a : ℝ) : h'.IsCh2Deg a ↔ h.IsCh2Deg a := by
  have w' : e.inv ≫ q = p := by rw [← w, e.inv_hom_id_assoc]
  obtain ⟨β, H'⟩ := exists_isIsometry_inv e w w' H
  exact ⟨isCh2Deg_of_isIsometry e.inv w' e.hom w H' H, isCh2Deg_of_isIsometry e.hom w e.inv w' H H'⟩

end GlobalTheory.IsometryPullback

namespace GlobalTheory

end GlobalTheory
