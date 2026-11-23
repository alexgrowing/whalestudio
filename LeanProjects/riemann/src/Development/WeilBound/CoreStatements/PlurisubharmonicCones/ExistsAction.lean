import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemOfEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointAltBis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
  {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ 𝔐.X}
  {P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)} {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V] {MV : LieModel P.tK.G (𝟙 (Sp L)) V} {A : LinPt E L (CMType H) V}

theorem finrank_eig' (h : 𝔐.IsLinPtOf z P MV A) (s : CMType H ⊕ CMType H) :
    Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s := by
  obtain ⟨U, hU, b, -, hb⟩ := 𝔐.vb s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ trivial
  have h1 := hb _ trivial hU
  have h2 : (𝔐.dR s).IsFrameAt b ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ :=
    ⟨h1.1, (Lat.patch_of_not _ _ _ fun p hp => PtHt.FrameVal.not_inFibre _ _ p (𝔐.S_prime p hp)).symm.trans h1.2⟩
  obtain ⟨sL, -, hi, hs⟩ := GlobalTheory.T.abelian_part_integral_point_alt E H D l Xo c Y S Ω K J y 𝔐 L z P V MV A s _ b h h2
  rw [← hs, finrank_span_eq_card hi, Fintype.card_fin]

omit [∀ k, Fintype (J k)] in
theorem exists_action (h : 𝔐.IsLinPtOf z P MV A) :
    ∃ (t' : SAB H (Sp (𝓞 L))) (_ : SABMap P.tB t' (spMap (algebraMap (𝓞 L) L)))
      (MB : LieModel t'.G (𝟙 _) A.Bq.carrier) (ρM : 𝓞 E →+* Module.End (𝓞 L) A.Bq.carrier),
      IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) A.Bq MB ∧ MB.IsActOf t'.act.act ρM ∧
        ∀ (a : 𝓞 E) (x : A.Λ), A.f ⟨A.ρ a x, A.stable a x x.2⟩ = ρM a (A.f x) := by
  obtain ⟨hact, -, -, -, -, t', m', MB, hfib, hl⟩ := h
  obtain ⟨ρM, hρ, -⟩ := lieModel_exists_unique_act _ t'.G (𝓞 L) (𝟙 _) _ MB (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  refine ⟨t', m', MB, ρM, hfib, hρ, fun a x => ?_⟩
  have := t'.semi.separated
  refine MB.inj (Over.OverMorphism.ext (LieHomOk.ext_of_spMap_injective (dualMap (algebraMap (𝓞 L) L))
    (LieTangent.dualMap_injective (IsFractionRing.injective _ _)) t'.G.hom _ _
    ((Over.w (MB.pt _)).trans (Over.w (MB.pt _)).symm) ?_))
  have h1 : (MV.pt (A.ρ a x) ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = _ := hl ⟨A.ρ a x, A.stable a x x.2⟩
  have h2 : (MV.pt x ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = _ := hl x
  have h3 : MV.pt (A.ρ a x) ≫ P.τ.q ≫ P.e.hom = (MV.pt x ≫ P.τ.q ≫ P.e.hom) ≫ P.tB.act.act a := by
    rw [hact a x, Category.assoc, P.act a]
    simp only [Category.assoc]
  rw [← h1, h3, hρ a (A.f x)]
  generalize MV.pt x ≫ P.τ.q ≫ P.e.hom = w at h2
  have h4 : (P.tB.act.act a).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
  change (w.left ≫ (P.tB.act.act a).left) ≫ m'.φ =
    spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (A.f x)).left ≫ (t'.act.act a).left
  rw [Category.assoc, h4]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (t'.act.act a).left) h2).trans (Category.assoc _ _ _))

end Geo

end LevelTowerAlt
