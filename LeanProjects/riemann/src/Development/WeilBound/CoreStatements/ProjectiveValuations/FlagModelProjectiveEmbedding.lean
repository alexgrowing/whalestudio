import Development.WeilBound.CoreStatements.ProjectiveValuations.InitSpanEqOfTri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChartStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints

noncomputable section

namespace DifferentiableLines.FlagIso

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str pm)
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.CompHS
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {S : Type} [CommRing S]

theorem step_congr {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {z z' : Sp S ⟶ Z} (e : z = z')
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π = x) (σ : E →+* ℂ) (i : ℕ) :
    F.step z hx σ i = F.step z' hx' σ i := by
  subst e; rfl

theorem dense_interior {Z : Scheme.{0}} (π : Z ⟶ Y.X) (h : Dense (genMap π ⁻¹' Set.range Y.jQ)) :
    Dense ((π ⁻¹ᵁ LogKS.interior Y : Z.Opens) : Set Z) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  let r := pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F))
  refine (r.surjective.denseRange.dense_image r.continuous h).mono ?_
  rintro _ ⟨z, ⟨x, hx⟩, rfl⟩
  refine ⟨x, ?_⟩
  rw [Model.j, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, FlagMod.genMap,
    pullback.lift_fst]

theorem lies_of_step [Algebra c.F S] (X : FlagCover Y) (z : Sp S ⟶ X.YY) (Q : FrPt Xo c S) (k : X.F.J)
    (hk : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hx : z ≫ X.π = frX Q ≫ Y.j)
    (h : ∀ σ i, initSpan S (frVec Y Q rfl σ) i = X.F.step z hx σ i) : X.F.Lies z Q := by
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y Q rfl σ i = ∑ j, b j i • X.F.vecAt k z hk hx σ j := fun σ =>
    exists_tri_of_eq (X.F.linearIndependent_vecAt k z hk hx σ) fun i => (h σ i).trans (X.F.step_eq k z hk hx σ i)
  choose U hU hu hv using ex
  exact GlobalTheory.T.carries_framedPoint_of_unitTriangular_chart E H Dw l Xo c c.F (RingHom.id c.F) Y X.YY X.π X.F X.top S Q z k hk hx U hU hu hv

theorem step_eq_of_rfl {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {z z' : Sp S ⟶ Z} (hx' : z' ≫ π = z ≫ π)
    (h : ∀ σ i, F.step z' hx' σ i = F.step z rfl σ i) {x : Sp S ⟶ Y.X} (e : z ≫ π = x) (e' : z' ≫ π = x)
    (σ : E →+* ℂ) (i : ℕ) : F.step z' e' σ i = F.step z e σ i := by
  subst e
  exact h σ i

theorem eq_of_step [IsLocalRing S] (X : FlagCover Y) (z z' : Sp S ⟶ X.YY) (hx' : z' ≫ X.π = z ≫ X.π)
    (hi : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ LogKS.interior Y) (h : ∀ σ i, X.F.step z' hx' σ i = X.F.step z rfl σ i) : z' = z := by
  obtain ⟨_, y, hy, hx⟩ := exists_y _ hi
  obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing X.F.cover z
  obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing X.F.cover z'
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hx k hk
  have hl : X.F.Lies z Q := hQ.lies
  have e : z ≫ X.π = frX Q ≫ Y.j := hl.1
  have e' : z' ≫ X.π = frX Q ≫ Y.j := hx'.trans e
  have hl' : X.F.Lies z' Q := lies_of_step X z' Q k' hk' e' fun σ i =>
    (hl.initSpan_eq hk e rfl σ i).trans (step_eq_of_rfl X.F hx' h e e' σ i).symm
  exact (X.rep S Q).unique hl' hl

variable {p : Proj (RingHom.id c.F)} {A : Atlas Y p} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
  {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)
  (ht : FlagCellFrameChangeTriangular hZ)

theorem Rel.step_eq {X : FlagCover Y} {z : Sp S ⟶ X.YY} {z' : Sp S ⟶ Z} (h : Rel hZ ht X z z') {x : Sp S ⟶ Y.X}
    (hx : z ≫ X.π = x) (hx' : z' ≫ π = x) (σ : E →+* ℂ) (i : ℕ) :
    (cellFrames hZ ht).step z' hx' σ i = X.F.step z hx σ i := by
  subst hx
  exact h.2 σ i

include hZ in

theorem exists_iso (M : FlagModel Y) : ∃ h : M.YY ⟶ Z, IsIso h ∧ h ≫ π = M.π := by
  have ht := GlobalTheory.T.flagCellFrameChangeTriangular_of_cells E H Dw l Xo c Y p A Z π g κ hZ
  have hT := GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht
  have hu := GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing E H Dw l Xo c Y p A Z π g κ hZ ht
  obtain ⟨h, hR⟩ := exists_glue (fun S _ _ z z' => Rel hZ ht M.toFlagCover z z')
    (fun S _ _ t z z' h h' => hu S z z' _ h.1 h'.1 fun σ i => (h.2 σ i).trans (h'.2 σ i).symm)
    (exists_local hZ ht M.toFlagCover)
  have hπ : h ≫ π = M.π := hom_ext_local fun S _ _ t => (Category.assoc _ _ _).symm.trans (hR S t).1
  have two : ∀ (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ M.YY), z' ≫ h = z ≫ h →
      ∃ hx : z' ≫ M.π = z ≫ M.π, ∀ σ i, M.F.step z' hx σ i = M.F.step z rfl σ i := fun S _ _ z z' e => by
    have hx : z' ≫ M.π = z ≫ M.π := by rw [← hπ, ← Category.assoc, e, Category.assoc]
    refine ⟨hx, fun σ i => ?_⟩
    rw [← (hR S z').step_eq hZ ht hx ((hR S z').1.trans hx), ← (hR S z).step_eq hZ ht rfl (hR S z).1]
    exact step_congr _ e _ _ σ i
  refine ⟨h, ?_, hπ⟩
  have := hZ.proper
  have : IsProper (h ≫ π) := hπ ▸ M.proper
  have : IsProper h := IsProper.of_comp h π
  have : LocallyQuasiFinite h := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points h fun Ω _ _ y => by
    rcases isEmpty_or_nonempty {x : Spec (.of Ω) ⟶ M.YY // x ≫ h = y} with h0 | ⟨⟨z, hz⟩⟩
    · infer_instance
    · exact ((M.fin Ω z).subset fun z' (hz' : z' ≫ h = y) => two Ω z z' (hz'.trans hz.symm)).to_subtype
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (π ≫ Y.s)
  have : IsReduced M.YY := isReduced_flag M.toFlagCover
  refine isIso_of_normal h hZ.normal (π ⁻¹ᵁ LogKS.interior Y)
    (dense_interior π (GlobalTheory.T.dense_flagBundle_preimage_moduli E H Dw l Xo c Y p A Z π g κ hZ)) ?_ (fun W a a' ha e => ?_) fun w hw => ?_
  · rw [← Scheme.Hom.comp_preimage, hπ]
    exact dense_interior M.π M.dense
  · refine hom_ext_local fun S _ _ t => ?_
    obtain ⟨hx, hs⟩ := two S (t ≫ a) (t ≫ a') (by rw [Category.assoc, Category.assoc, e])
    refine (eq_of_step M.toFlagCover _ _ hx (fun q _ => ?_) hs).symm
    have := ha (t q)
    rw [← hπ]
    exact this
  · let K : Type := Z.residueField w
    let t : Sp K ⟶ Z := Z.fromSpecResidueField w
    have hi : ⊤ ≤ (t ≫ π) ⁻¹ᵁ LogKS.interior Y := fun q _ => by
      have e : t q = w := Scheme.fromSpecResidueField_apply w q
      change π (t q) ∈ LogKS.interior Y
      rw [e]
      exact hw
    obtain ⟨_, y, hy, hx⟩ := exists_y _ hi
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover t
    obtain ⟨Q, hQ⟩ := hT.exists_chartFr hy hx k' hk'
    have hl' := hQ.lies
    have hl := M.lies_ptY Q
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing M.F.cover (M.ptY Q)
    have e : M.ptY Q ≫ h = t := hu K _ _ _ ((hR K _).1.trans hl.1) hl'.1 fun σ i => by
      rw [(hR K _).step_eq hZ ht hl.1, ← hl.initSpan_eq hk hl.1 rfl, hl'.initSpan_eq hk' hl'.1 rfl]
    let q : Sp K := IsLocalRing.closedPoint K
    refine ⟨M.ptY Q q, ?_⟩
    rw [← Scheme.Hom.comp_apply, e]
    exact Scheme.fromSpecResidueField_apply w _

end DifferentiableLines.FlagIso

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem DifferentiableLines.flag_model_projective_embedding_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (M' : GlobalTheory.FlagMod.FlagModel Y) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, M'.YY ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ M'.YY)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A M'.π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∀ M : GlobalTheory.FlagMod.FlagModel Y, ∃ h : M.YY ⟶ M'.YY, IsIso h ∧ h ≫ M'.π = M.π := by
  intro E _ _ _ H Dw l Xo c Y p A M' g κ hκ hZ _ M
  exact DifferentiableLines.FlagIso.exists_iso hZ M
