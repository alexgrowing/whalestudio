import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChangeAltBis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOverLieModelBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianBundleFibreTangentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieValuePullbackFieldExtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedGramDetPositiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenComponentMapCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedFamilyBasisChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

theorem isTan_comp {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {R : Type}
    [CommRing R] {x : Sp R ⟶ S} {v : epsAt x ⟶ G} (h : IsTanAt G x v) : IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at h ⊢
  rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left]
  congr 1
  exact MonObj.one_comp f

theorem geo_height_arch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H → CMType H ⊕ CMType H) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : CMType H → Fin k → A.Λ) (b : CMType H → Fin m → 𝔐.Li) (bL : CMType H → Fin m → V) (T : CMType H → Matrix (Fin m) (Fin m) L), 𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ, IsValues 𝔐 z P MV (b τ) (bL τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ e : L →+* ℂ, (∀ τ, 0 < A.gramDet e (q τ)) ∧ ∃ ν : ℝ, 𝔐.GeoPhi lab (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) b ν ∧ 0 < ν ∧ ν = (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ _ z P V _ _ _ _ MV A lab r k m h v q b bL T hA hv hq hb hT hdet e
  obtain ⟨hact, hlab, hΛ, hcoch, hprin, t', m', MB, hfib, hlift⟩ := hA
  have hgram : ∀ τ, 0 < A.gramDet e (q τ) := fun τ =>
    GlobalTheory.T.adapted_gram_det_positive E L _ V A (lab τ) r k v (q τ) hv (hq τ).1 (hq τ).2 e
  refine ⟨hgram, ?_⟩
  obtain ⟨P', mK, mB, h1, h2, h3⟩ := GlobalTheory.T.abPart_comp_spMap_compat E H _ 𝔐.t L ℂ (spMap (algebraMap (𝓞 L) L) ≫ z) P e
  haveI := P.tK.semi.smooth
  obtain ⟨V', _, _, MV', j, hjs, hji, hjpt, hjspan⟩ := GlobalTheory.T.lie_model_base_change_exists L ℂ e P.tK.G P'.tK.G mK.φ mK.cart V MV
  obtain ⟨ρ', hρa, hρ⟩ := GlobalTheory.T.lie_model_base_change_action L ℂ e _ _ mK.φ mK.cart (𝓞 E) P.tK.act P'.tK.act mK.act V V' MV MV' j hjpt hjspan
    A.ρ hact
  have hcoch' : P'.IsCochars MV' (A.I.map j) :=
    GlobalTheory.T.torus_over_lie_model_base_change L ℂ e _ _ mK.φ P.τ P'.τ mK.cart h3 V V' MV MV' j hjpt A.I hcoch
  letI := P'.τ.grpB
  haveI := P'.τ.q_hom
  haveI := P'.e_hom
  obtain ⟨hbF, hbI, hbv⟩ := GlobalTheory.T.hermitian_bundle_fibre_tangent E H L t' P.tB P'.tB e m' mB A.Bq MB hfib V'
    (fun x => MV'.pt x ≫ P'.τ.q ≫ P'.e.hom) (fun x => isTan_comp _ (MV'.tan x))
  have hover : ∀ x : A.Λ, (MV'.pt (j x) ≫ P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ≫ m'.φ =
      spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt (A.f x)).left := fun x => by
    have e1 := hlift x
    unfold LieModel.Lifts at e1
    rw [dualMap_comp]
    have e3 : spMap ((dualMap e).comp (dualMap (algebraMap (𝓞 L) L))) =
        spMap (dualMap e) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := by
      simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e3, Category.assoc, ← e1, Over.comp_left, Category.assoc]
    rw [← Category.assoc (P'.τ.q ≫ P'.e.hom).left, ← h2, Category.assoc, ← Category.assoc _ mK.φ, hjpt]
    simp [Over.comp_left]
  have heig : ∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a)) := fun τ a => by
    refine GlobalTheory.T.eigen_component_map_compat L ℂ V V' (𝓞 E) e j hjs A.ρ ρ' hρ (A.σ (lab τ)) (v a) ?_
    have h0 := (hq τ).1.1.ne_zero (Fin.castAdd k a)
    simpa [LinPt.fam] using h0
  have hpos : 0 < (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) *
      ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
    refine mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hv.2.2)) (Finset.prod_pos fun τ _ => ?_)
    have hne : e (T τ).det ≠ 0 := fun h0 => hdet τ ((map_eq_zero e).1 h0)
    have hp : (0 : ℝ) < 4 * Real.pi := by positivity
    have := hgram τ
    positivity
  refine ⟨_, ⟨P', V', _, _, MV', ρ', A.I.map j, hbF, fun τ => e.comp (A.σ (lab τ)), fun τ i => j (bL τ i), hρa, hcoch',
    fun τ a => GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_of_field_map _ _ _ e rfl (hlab (lab τ) a), hbI, fun τ i => ?_,
    GlobalTheory.T.adapted_family_basis_change E L _ V A lab r k m h v q bL T hv hq hT hdet e V' j hjs hji ρ' hρ heig hbF (fun τ c c' =>
      hbv _ _ _ _ (hover _) (hover _))⟩, hpos, rfl⟩
  obtain ⟨v₀, hv₀, e₀⟩ := hb τ i
  refine ⟨LieSigma.pullEps e _ ≫ v₀, GlobalTheory.T.lie_value_pullback_field_ext _ _ _ _ _ 𝔐.M _ _ _ e _ _ hv₀, ?_⟩
  rw [← h1, ← Category.assoc, hjpt, Category.assoc, e₀]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch
