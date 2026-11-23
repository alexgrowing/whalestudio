import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionLieLatticeStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TopPt

section Alg

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {r : ℕ}

theorem hom_eq_sum {O : Type} [CommRing O] (δ : X →+ O) :
    δ = ∑ i, δ (Module.Free.chooseBasis ℤ X i) •
      (Int.castAddHom O).comp ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
  ext x
  conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
  simp only [map_zsmul]
  simp [AddMonoidHom.finsetSum_apply, mul_comm]

theorem exists_dual (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) (a : Fin r) :
    ∃ x : X, ∀ φ : X →+ ℤ, φ x = bs.repr φ a := by
  refine ⟨∑ i, bs.repr ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom a • Module.Free.chooseBasis ℤ X i,
    fun φ => ?_⟩
  have e : φ = ∑ i, φ (Module.Free.chooseBasis ℤ X i) •
      ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
    ext x
    conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
    simp only [map_zsmul]
    simp [AddMonoidHom.finsetSum_apply, mul_comm]
  conv_rhs => rw [e]
  simp [map_sum, mul_comm]

theorem indep {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    LinearIndependent O (fun a => (Int.castAddHom O).comp (bs a)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  obtain ⟨x, hx⟩ := exists_dual bs a
  have := DFunLike.congr_fun hg x
  simpa [AddMonoidHom.finsetSum_apply, hx, Finsupp.single_apply] using this

theorem span_top {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) = ⊤ := by
  have key : ∀ φ : X →+ ℤ, (Int.castAddHom O).comp φ ∈
      Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) := by
    intro φ
    have e : (Int.castAddHom O).comp φ = ∑ a, ((bs.repr φ a : ℤ) : O) • (Int.castAddHom O).comp (bs a) := by
      ext x
      have e₀ := DFunLike.congr_fun (bs.sum_repr φ) x
      rw [AddMonoidHom.finsetSum_apply] at e₀
      rw [AddMonoidHom.comp_apply, ← e₀, map_sum]
      simp [AddMonoidHom.finsetSum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  rw [eq_top_iff]
  intro δ _
  rw [hom_eq_sum δ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (key _)

theorem image_basis {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ))
    (io : (X →+ O) →ₗ[O] V) (h : Function.Injective io) :
    LinearIndependent O (fun a => io ((Int.castAddHom O).comp (bs a))) ∧
      LinearMap.range io = Submodule.span O (Set.range fun a => io ((Int.castAddHom O).comp (bs a))) := by
  have hk : LinearMap.ker io = ⊥ := LinearMap.ker_eq_bot_of_injective h
  have hi := (indep (O := O) bs).map' io hk
  refine ⟨hi, ?_⟩
  rw [LinearMap.range_eq_map, ← span_top (O := O) bs, Submodule.map_span, ← Set.range_comp]
  rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem cast_comp {O K : Type} [CommRing O] [CommRing K] (c : O →+* K) (φ : X →+ ℤ) :
    c.toAddMonoidHom.comp ((Int.castAddHom O).comp φ) = (Int.castAddHom K).comp φ := by
  ext x; simp

end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem exists_pull {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (z : S' ⟶ S) :
    ∃ (G₀ : Over S') (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left), IsSemiAbelian G₀ ∧ IsGrpPullback G₀ G z ψ :=
  ⟨(Over.pullback z).obj G, inferInstance, pullback.fst G.hom z, IsSemiAbelian.pullback z G hG,
    isGrpPullback_pullback G z⟩

theorem lifts_iff {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') {X : Scheme.{0}} {z : Sp R ⟶ X} {G : Over X}
    [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (hp : IsGrpPullback G₀ G z ψ)
    {GK : Over (Sp R')} {φ₀ : GK.left ⟶ G₀.left} (hw : φ₀ ≫ G₀.hom = GK.hom ≫ spMap c)
    {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G z V) (M₀ : LieModel G₀ (𝟙 _) V)
    (hM₀ : ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) (e : V) (v : epsAt (𝟙 (Sp R')) ⟶ GK) :
    M₀.Lifts c φ₀ e v ↔ M.Lifts c (φ₀ ≫ ψ) e v := by
  unfold LieModel.Lifts
  constructor
  · intro h
    rw [← Category.assoc, h, Category.assoc, hM₀]
  · intro h
    apply hp.1.hom_ext
    · rw [Category.assoc, h, Category.assoc, hM₀]
    · have w₂ := Over.w (M₀.pt e)
      have w₃ := Over.w v
      rw [Category.assoc, hw, ← Category.assoc, w₃, Category.assoc, w₂]
      show (Spec.map _ ≫ 𝟙 _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem main : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) (G' : Over (Sp (𝓞 L))) [GrpObj G'] (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → IsGrpPullback τ.B G' (spMap (algebraMap (𝓞 L) L)) φ' → ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (V V' : Type) [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup V'] [Module (𝓞 L) V'] (M : LieModel G z V) (M' : LieModel G' (𝟙 _) V') (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∃ (ε : Fin r → V) (f : V →ₗ[𝓞 L] V'), (∀ a, M.Lifts (algebraMap (𝓞 L) L) φ (ε a) (MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i)) ∧ (∀ (e : V) (v : epsAt (𝟙 (Sp L)) ⟶ GK), M.Lifts (algebraMap (𝓞 L) L) φ e v → M'.Lifts (algebraMap (𝓞 L) L) φ' (f e) (v ≫ τ.q)) ∧ LinearIndependent (𝓞 L) ε ∧ LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε) ∧ ∀ e' : V', ∃ (a : 𝓞 L) (e : V), a ≠ 0 ∧ f e = a • e' := by
  intro X G _ _ hG L _ _ z GK _ φ τ G' _ φ'
  let _ := τ.addCommGroup
  let _ := τ.grpB
  have := τ.free
  have := τ.finite
  intro hG' hφ hφ' MT hMT V V' _ _ _ _ M M' r bs
  obtain ⟨G₀, _, ψ, hG₀, hp⟩ := exists_pull G hG z
  obtain ⟨φO, hF, hw⟩ : ∃ φO : GK.left ⟶ G₀.left, φO ≫ ψ = φ ∧
      φO ≫ G₀.hom = GK.hom ≫ spMap (algebraMap (𝓞 L) L) :=
    ⟨hp.1.lift φ (GK.hom ≫ spMap (algebraMap (𝓞 L) L)) (by rw [hφ.1.w, Category.assoc]), hp.1.lift_fst _ _ _,
      hp.1.lift_snd _ _ _⟩
  subst hF
  have hO : IsGrpPullback GK G₀ (spMap (algebraMap (𝓞 L) L)) φO := hp.cancel hφ hw
  obtain ⟨M₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main (𝓞 L) X z G G₀ ψ V hp).1 M
  have hiff := lifts_iff (algebraMap (𝓞 L) L) hp hw M M₀ hM₀
  obtain ⟨io, f, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.torus_extension_lie_lattice (𝓞 L) L G₀ G' GK τ φO φ'
    hG₀ hG' hO hφ' MT hMT V V' M₀ M'
  obtain ⟨b1, b2⟩ := image_basis bs io h3
  refine ⟨fun a => io ((Int.castAddHom (𝓞 L)).comp (bs a)), f, fun a => ?_, fun e v h => h2 e v ((hiff e v).2 h),
    b1, h4.trans b2, h5⟩
  have := h1 ((Int.castAddHom (𝓞 L)).comp (bs a))
  rw [cast_comp] at this
  exact (hiff _ _).1 this

end GlobalTheory.CompanionTheory.Ar.TopPt
