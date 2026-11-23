import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineChartBundleSectionsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PullbackFramesComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_vecs {S : Scheme.{0}} {G : Over S} {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ S) (f : R →+* R')
    (y : Sp R' ⟶ S) (hy : y = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    ∃ u' : Fin n → (epsAt y ⟶ G), ∀ i, (u' i).left = spMap (dualMap f) ≫ (u i).left :=
  ⟨fun i => LieCarrier.epsHom f x y hy.symm ≫ u i, fun i => rfl⟩

theorem extendsUnitAt_resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ b₂ X' π s' d ξ' W' W jW F hβ hpq hτ hσ hΦ hb₁ hs₁ hb₂ hs₂ hπ hsm hsnc hξ hgen hj hjs hWW' hF hgen1 x h hx
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' (Z.ξ₀ ≫ Y.j) π (RingHom.id Z.Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) = 𝟙 _ := Spec.map_id _
    show ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    rw [hξ, e, Category.id_comp]
  obtain ⟨hp, -, hpull⟩ := pull_reg_and_gen _ _ _ _ _ _ π _ hd ⟨centre x, h⟩
  let p₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨π (centre x), hp⟩
  have hp₀ : p₀ ∈ Z.genFib := ⟨pullback.lift π s' hπ (centre x), by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩
  obtain ⟨hVB₁, hVB₂, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨A, hA, EB, _, _, MB, e₁, e₂, v₁, v₂, hp₀A, hfr, heig, hval⟩ :=
    GlobalTheory.T.frame_at_component_point E H D l Xo c O β Y U Z τ σ b₁ b₂ p₀ hβ hτ hb₁ hs₁ hb₂ hs₂ hp₀
  obtain ⟨hv₁, hv₂⟩ := hfr p₀ hp₀A
  obtain ⟨α, κ, hα, hκ, hαe, hκe, hgen0⟩ := GlobalTheory.T.pair_frames_on_set _ _ _ _ (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q _ _ Z.genFib
    b₁ v₁ b₂ v₂ p₀ hp₀ hVB₁ hVB₂ hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  refine ⟨α / κ, hpull _ _ hgen0, ?_⟩
  intro m B y hB hy hyσ b₀ hb₀ hyx
  have hxA : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ A) := fun q _ => by
    have : q = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hp₀A
  obtain ⟨ε, hh, hε, hdiff, hne, key⟩ := GlobalTheory.T.affine_chart_bundle_sections E H D l Xo c O β Y τ σ Φ X' π s' d W' jW A hA EB MB e₁ e₂ x hpq hτ hσ hΦ hπ hsm hsnc hj hjs hx hxA heig m B y hB hy hyσ b₀ hb₀ hyx
  refine ⟨ε, hh, hε, hdiff, hne, fun b hbB hbW r hr => ?_⟩
  obtain ⟨f, hf, hk⟩ := key b hbB
  have hc : genPt ξ' ⤳ centre (y b) := hr.choose
  have hW' : ⊤ ≤ y b ⁻¹ᵁ W' := fun q hq => hWW' (hbW hq)
  have hrange : Set.range (y b) ⊆ Set.range W'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    exact hW' (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  let y₀ : Sp ℂ ⟶ W'.toScheme := IsOpenImmersion.lift W'.ι (y b) hrange
  have e₀ : y₀ ≫ W'.ι = y b := IsOpenImmersion.lift_fac _ _ _
  let yy : Sp ℂ ⟶ Xo.XF c := y₀ ≫ jW
  have hyj : yy ≫ Y.j = y b ≫ π := by
    show (y₀ ≫ jW) ≫ Y.j = _
    rw [Category.assoc, hj, ← Category.assoc, e₀]
  have hys : yy ≫ pullback.snd _ _ = spMap σ := by
    show (y₀ ≫ jW) ≫ _ = _
    rw [Category.assoc, hjs, ← Category.assoc, e₀, hyσ b hbB.1]
  obtain ⟨v, w, hfrvw, ⟨hvv, hww⟩, hFe⟩ := hF (y b) yy (hyσ b hbB.1) hbW hc hyj hys
  have hyf : yy ≫ Y.j = spMap f ≫ hA.fromSpec := hyj.trans hf.symm
  obtain ⟨u₁, hu₁⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₁ i))
  obtain ⟨u₂, hu₂⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₂ i))
  have hover : (yy ≫ Y.j) ≫ Y.s = spMap (σ.comp β) := by
    rw [hyj, Category.assoc, hπ, ← Category.assoc, hyσ b hbB.1, ← Spec.map_comp]
    rfl
  obtain ⟨hE₁, hE₂⟩ := heig f (yy ≫ Y.j) u₁ u₂ hyf hover hu₁ hu₂
  have hspec : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (yy ≫ Y.j) := by
    have e : centre (yy ≫ Y.j) = π (centre (y b)) := by
      rw [hyj]; rfl
    rw [e, ← RegAtDom.map_genPt hd]
    exact hc.map π.continuous
  obtain ⟨hV₁, hV₂⟩ := hval f (yy ≫ Y.j) u₁ u₂ hyf hspec hu₁ hu₂
  choose a₁ ha₁ using fun i => exists_sameVec_left Y yy (u₁ i)
  choose a₂ ha₂ using fun i => exists_sameVec_left Y yy (u₂ i)
  have hfr₀ : IsFramed Set.univ τ σ yy a₁ a₂ := GlobalTheory.T.vectors_at_complex_point E H D l Xo c O β Y τ σ yy a₁ a₂ u₁ u₂ hys ha₁ ha₂ hE₁ hE₂
  have h₁ := (hk hW') yy a₁ a₂ u₁ u₂ hyj hys ha₁ ha₂ hu₁ hu₂
  have hqA : ∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → q.1 ∈ A := fun q hq => by
    rw [hq, hyf, ← SetLike.mem_coe, ← hA.range_fromSpec]
    exact ⟨_, rfl⟩
  have h₂ := GlobalTheory.T.pullback_frames_complex_point E H D l Xo c O β Y U Z τ σ Φ b₁ v₁ b₂ v₂ X' π ξ' (y b) yy v a₁ w a₂ α κ r hξ hgen hyj hΦ hfrvw hfr₀ hvv hww
    (fun i => ⟨_, hV₁ i, ha₁ i⟩) (fun j => ⟨_, hV₂ j, ha₂ j⟩) (fun q hq => hfr q (hqA q hq))
    (fun i => hs₁ ▸ Submodule.subset_span ⟨i, rfl⟩) (fun j => hs₂ ▸ Submodule.subset_span ⟨j, rfl⟩)
    hα hκ hαe hκe hr
  rw [hFe, h₂, h₁]

end GlobalTheory.CompanionTheory.Ar.Flat
