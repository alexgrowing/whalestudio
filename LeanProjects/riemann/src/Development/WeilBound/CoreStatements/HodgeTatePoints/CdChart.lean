import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartOfBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc

noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Gen
open GlobalTheory.ChartCompare GlobalTheory.FrameTangent
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

def tanModel {S : Type} [CommRing S] (x : Sp S ⟶ X0) : GlobalTheory.CompanionTheory.Ar.LieModel t.G x (TanM x t.G) where
  pt := tv
  tan e := (isTanAtG_of _ (tv_zero' e)).2
  inj := tv_injective
  onto v hv := ⟨mkT (ovT (t := t) ⟨Over.w v, hv⟩) (smT_zero_ovT _), rfl⟩
  add := tv_add
  smul _ _ := rfl

theorem tanBasis_of_basis {S : Type} [CommRing S] (x : Sp S ⟶ X0) {n : ℕ} (b : Module.Basis (Fin n) S (TanM x t.G)) :
    IsTanBasisG t x fun k => (tv (b k)).left := by
  refine ⟨fun k => isTanAtG_of _ (tv_zero' _), fun w hw => ?_⟩
  have key : ∀ a : Fin n → S, IsCombAtG t x (m := Fintype.card (Fin n))
      (fun i => (tv (b ((Fintype.equivFin (Fin n)).symm i))).left) (fun i => a ((Fintype.equivFin (Fin n)).symm i)) w ↔
      b.equivFun.symm a = mkT (ovT hw) (smT_zero_ovT hw) := fun a => by
    rw [comb_iff_sum t x (Fintype.equivFin (Fin n)).symm b a, b.equivFun_symm_apply]
    exact ⟨fun h => tv_injective (Over.OverMorphism.ext h), fun h => by rw [h]; rfl⟩
  exact (existsUnique_congr key).2 (b.equivFun.symm.bijective.existsUnique _)

theorem exists_basis_away {R : Type} [CommRing R] (x : Sp R ⟶ X0) (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (Localization.Away r)
      (TanM (spMap (algebraMap R (Localization.Away r)) ≫ x) t.G)) := by
  have := t.semi.smooth
  obtain ⟨h1, h2, h3⟩ := PositivityTheory.HtPt.Htat.lie_proj X0 t.G R x _ (tanModel t x)
  have : Module.FinitePresentation R (TanM x t.G) := Module.finitePresentation_of_projective _ _
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl (TanM x t.G)) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (TanM x t.G)) (Localization.AtPrime p)
  refine ⟨r, hr, ?_⟩
  let R' := Localization.Away r
  let L' := TanM (spMap (algebraMap R R') ≫ x) t.G
  obtain ⟨j, hj, hs, -⟩ := PositivityTheory.HtPt.Htat.lie_bc X0 t.G R R' x _ L' (tanModel t x) (tanModel t _)
  let _ : Module R L' := Module.compHom L' (algebraMap R R')
  have : IsScalarTower R R' L' := ⟨fun r a l => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let j₀ : TanM x t.G →ₗ[R] L' := { toFun := j, map_add' := j.map_add, map_smul' := fun a v => hs a v }
  have hbc := h3 R' L' (tanModel t _) j₀ hj
  have hbc' := IsLocalizedModule.isBaseChange (Submonoid.powers r) R'
    (LocalizedModule.mkLinearMap (Submonoid.powers r) (TanM x t.G))
  let e := hbc'.equiv.symm.trans hbc.equiv
  have hf' : Module.Free R' (LocalizedModule (Submonoid.powers r) (TanM x t.G)) := hf
  have : Module.Free R' L' := Module.Free.of_equiv e
  have : Module.Finite R' L' := Module.Finite.equiv hbc.equiv
  exact ⟨_, ⟨(Module.Free.chooseBasis R' L').reindex (Fintype.equivFin _)⟩⟩

end Gen

theorem chart_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (z : X0), ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ) (G : Germ.FGLaw A d) (a : Germ.OAct (𝓞 E) G) (tg : Fin d → (Sp (DualNumber A) ⟶ t.G.left)) (x : ∀ m, jOG j d m 1 ⟶ t.G) (c : t.PP.L.ι), IsOpenImmersion j ∧ z ∈ Set.range j ∧ IsChartG t j d G.F a.act tg (fun l i => if l = i then 1 else 0) x ∧ (∀ l, IsTanAtG t j (tg l)) ∧ (∀ w, IsTanAtG t j w → ∃! b : Fin d → A, IsCombAtG t j tg b w) ∧ Set.range (j ≫ eSec t.G) ⊆ (t.PP.L.U c : Set t.G.left) := by
  intro E _ _ _ H X0 t z
  obtain ⟨c, hc⟩ := exists_chart t.PP.isLB (eSec t.G z)
  obtain ⟨V, hV, hzV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X0) (x := z)
    (U := eSec t.G ⁻¹ᵁ t.PP.L.U c) hc
  let R : Type := Γ(X0, V)
  let x : Sp R ⟶ X0 := hV.fromSpec
  let p : PrimeSpectrum R := hV.primeIdealOf ⟨z, hzV⟩
  obtain ⟨r, hr, n, ⟨b⟩⟩ := exists_basis_away t x p.asIdeal
  obtain ⟨G, A, tg, y, h1, h2, h3⟩ := GermInh.chart_of_basis t _ _ (tanBasis_of_basis t _ b)
  have hx : IsOpenImmersion x := hV.isOpenImmersion_fromSpec
  have hj : IsOpenImmersion (spMap (algebraMap R (Localization.Away r))) :=
    IsOpenImmersion.of_isLocalization r
  refine ⟨Localization.Away r, inferInstance, spMap (algebraMap R (Localization.Away r)) ≫ x, _, G, A, tg, y, c,
    inferInstance, ?_, h1, h2, h3, ?_⟩
  · have : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    obtain ⟨q, hq⟩ := this
    refine ⟨q, ?_⟩
    show x (PrimeSpectrum.comap (algebraMap R (Localization.Away r)) q) = z
    rw [hq]
    exact hV.fromSpec_primeIdealOf ⟨z, hzV⟩
  · rintro _ ⟨q, rfl⟩
    have : x (spMap (algebraMap R (Localization.Away r)) q) ∈ (V : Set X0) := by
      rw [← hV.range_fromSpec]
      exact ⟨_, rfl⟩
    exact hVU this

end PositivityTheory.HtPt.Cd
