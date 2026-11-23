import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLift
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactSphere
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianFiniteCoverTorusStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveOnOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsFiniteTypeOverIntegersStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticPointsFiniteCompactStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFinitePullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricTorusPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveLiftsPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleClosedIntegralSubschemeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusSplitPullbackGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianSquareNormGramStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem noeth_good {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] (Good : ℝ → T → Prop)
    (mono : ∀ C C' t, C ≤ C' → Good C t → Good C' t)
    (step : ∀ F : Set T, IsClosed F → IsIrreducible F → ∃ F' : Set T, IsClosed F' ∧ F' ⊂ F ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ F, t ∉ F' → Good C t) : ∃ C : ℝ, 1 ≤ C ∧ ∀ t, Good C t := by
  have key : ∀ F : TopologicalSpace.Closeds T, ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ F, Good C t := by
    intro F
    induction F using WellFoundedLT.induction with
    | ind F ih =>
      by_cases hF : IsIrreducible (F : Set T)
      · obtain ⟨F', hc, hlt, C, hC, hg⟩ := step F F.isClosed hF
        obtain ⟨C', hC', hg'⟩ := ih ⟨F', hc⟩ (by
          exact lt_of_le_of_ne (fun x hx => hlt.1 hx) (fun e => hlt.2 (by rw [← e]; exact fun x hx => hx)))
        refine ⟨max C C', le_max_of_le_left hC, fun t ht => ?_⟩
        by_cases h' : t ∈ F'
        · exact mono _ _ _ (le_max_right _ _) (hg' t h')
        · exact mono _ _ _ (le_max_left _ _) (hg t ht h')
      · obtain ⟨S, hS, hirr, hsup⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible F
        have hlt : ∀ s ∈ S, s < F := fun s hs => by
          refine lt_of_le_of_ne (hsup ▸ le_sSup hs) (fun e => hF ?_)
          rw [← e]; exact hirr s hs
        choose! c hc hg using fun s (hs : s ∈ S) => ih s (hlt s hs)
        refine ⟨∑ s ∈ hS.toFinset, c s + 1, ?_, fun t ht => ?_⟩
        · have : 0 ≤ ∑ s ∈ hS.toFinset, c s :=
            Finset.sum_nonneg fun s hs => by linarith [hc s (hS.mem_toFinset.1 hs)]
          linarith
        · have ht' : t ∈ (sSup S : TopologicalSpace.Closeds T) := hsup ▸ ht
          have hsS : ∃ s ∈ S, t ∈ s := by
            have aux : ∀ A : Finset (TopologicalSpace.Closeds T), t ∈ A.sup id → ∃ s ∈ A, t ∈ s := by
              classical
              intro A
              induction A using Finset.induction_on with
              | empty =>
                intro h
                have h' : t ∈ ((⊥ : TopologicalSpace.Closeds T) : Set T) := h
                simp at h'
              | insert a A _ ih' =>
                intro h
                rw [Finset.sup_insert] at h
                have h' : t ∈ ((id a ⊔ A.sup id : TopologicalSpace.Closeds T) : Set T) := h
                rw [TopologicalSpace.Closeds.coe_sup] at h'
                rcases h' with h' | h'
                · exact ⟨a, Finset.mem_insert_self _ _, h'⟩
                · obtain ⟨s, hs, hts⟩ := ih' h'
                  exact ⟨s, Finset.mem_insert_of_mem hs, hts⟩
            have hfin : (sSup S : TopologicalSpace.Closeds T) = hS.toFinset.sup id := by
              rw [Finset.sup_id_eq_sSup, hS.coe_toFinset]
            rw [hfin] at ht'
            obtain ⟨s, hs, hts⟩ := aux _ ht'
            exact ⟨s, hS.mem_toFinset.1 hs, hts⟩
          obtain ⟨s, hs, hts⟩ := hsS
          refine mono _ _ _ ?_ (hg s hs t hts)
          have : c s ≤ ∑ s ∈ hS.toFinset, c s :=
            Finset.single_le_sum (f := c) (fun s hs => by linarith [hc s (hS.mem_toFinset.1 hs)]) (hS.mem_toFinset.2 hs)
          linarith
  obtain ⟨C, hC, h⟩ := key ⊤
  exact ⟨C, hC, fun t => h t trivial⟩

theorem isGrpPullback_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G'.left} (h : IsGrpPullback G' G f φ)
    (h' : IsGrpPullback G'' G' g ψ) : IsGrpPullback G'' G (g ≫ f) (ψ ≫ φ) := by
  refine ⟨h'.1.paste_horiz h.1, fun T x y x₀ y₀ hx hy => ?_⟩
  have key : ∀ (c : T.left ⟶ S) (_ : (T.hom ≫ g) ≫ f = c) (x₀ y₀ : Over.mk c ⟶ G), x₀.left = x.left ≫ ψ ≫ φ →
      y₀.left = y.left ≫ ψ ≫ φ → (x₀ * y₀).left = (x * y).left ≫ ψ ≫ φ := by
    rintro _ rfl x₀ y₀ hx hy
    let x₁ : Over.mk (T.hom ≫ g) ⟶ G' := Over.homMk (x.left ≫ ψ) (by
      have := h'.1.w
      simp only [Over.mk_hom, Category.assoc, this, Over.w_assoc, Over.w])
    let y₁ : Over.mk (T.hom ≫ g) ⟶ G' := Over.homMk (y.left ≫ ψ) (by
      have := h'.1.w
      simp only [Over.mk_hom, Category.assoc, this, Over.w_assoc, Over.w])
    have e₁ := h'.2 T x y x₁ y₁ rfl rfl
    have e₂ := h.2 (Over.mk (T.hom ≫ g)) x₁ y₁ x₀ y₀ (by simpa [x₁] using hx) (by simpa [y₁] using hy)
    rw [e₂, e₁]
    exact CategoryTheory.Category.assoc _ _ _
  exact key _ (Category.assoc _ _ _) x₀ y₀ hx hy

theorem dual_inl {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (a : A) :
    dualMap σ (algebraMap A (DualNumber A) a) = algebraMap B (DualNumber B) (σ a) := by
  show dualMap σ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (σ a)
  apply TrivSqZeroExt.ext <;> simp [dualMap]

def dualEquiv {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) : (B →+ ℤ) ≃ₗ[ℤ] (A →+ ℤ) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun g => g.comp e.toAddMonoidHom
      invFun := fun g => g.comp e.symm.toAddMonoidHom
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp
      map_add' := fun g g' => by ext x; simp }

theorem exists_dual_basis (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ (Xc →+ ℤ)) :=
  ⟨_, ⟨(Module.finBasis ℤ Xc).dualBasis.map (addMonoidHomLequivInt ℤ).symm⟩⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped ComplexOrder in

theorem gram_bound (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hT : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (f : Z' ⟶ XQ X) (hf : IsFinite f) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left)
    (hP : IsGrpPullback G' G (f ≫ XQ.fst X) Φ)
    (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u]
    (hinj : ∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) (r : ℕ) (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (zc : Sp ℂ ⟶ Z') (zX : Sp ℂ ⟶ X) (_ : zc ≫ f ≫ XQ.fst X = zX)
      (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz → ∀ v : Fin r → (epsAt zX ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → ∀ w : Fin r → ℂ,
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ (star w ⬝ᵥ (RootHt.gramAt h zX v *ᵥ w)).re ∧
        (star w ⬝ᵥ (RootHt.gramAt h zX v *ᵥ w)).re ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  set ρ : Z' ⟶ X := f ≫ XQ.fst X with hρ
  have hM : ∀ zc : Sp ℂ ⟶ Z', ∃ Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ), IsCocharLie Mz :=
    fun zc => GlobalTheory.T.exists_cocharacter_lie_model Z' Xc ℂ zc
  choose Mz hMz using hM
  have hv : ∀ (zc : Sp ℂ ⟶ Z') (Mz' : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)) (a : Fin r),
      ∃ v : epsAt (zc ≫ ρ) ⟶ G, v.left = (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ := by
    intro zc Mz' a
    refine ⟨Over.homMk ((Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) ?_, rfl⟩
    have w1 : Φ ≫ G.hom = G'.hom ≫ ρ := hP.1.w
    have w2 := Over.w (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u)
    rw [CategoryTheory.Category.assoc, w1, reassoc_of% w2]
    simp [epsAt]
  choose vv hvv using fun zc => hv zc (Mz zc)
  let H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ := fun zc => RootHt.gramAt h (zc ≫ ρ) (vv zc)
  have hH : ∀ (zc : Sp ℂ ⟶ Z') (Mz' : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz' →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz'.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v := by
    intro zc Mz' hMz' v hv'
    have e : ∀ d, Mz'.pt d = (Mz zc).pt d := fun d =>
      (GlobalTheory.T.charVal_multiplicative Z' Xc (DualNumber ℂ) _).1 _ _ (fun χ => by rw [hMz', hMz])
    have : vv zc = v := by
      funext a
      apply Over.OverMorphism.ext
      rw [hvv, hv', e]
    simp only [H, this]
  have hcont := GlobalTheory.T.gram_matrix_continuous X Ω K J y ξ hall hT G Li M h Z' ρ G' Φ hP Xc u r (fun a => β a) H hH
  letI := anTop Z'
  haveI := GlobalTheory.T.analytic_points_finite_compact X Ω K J y ξ hall hT Z' f hf
  obtain ⟨C, hC, hb⟩ := GlobalTheory.CompanionTheory.GramCompact.exists_bounds (Sp ℂ ⟶ Z') Set.univ (Fin r) H isCompact_univ
    hcont.continuousOn (fun zc _ => GlobalTheory.T.lie_metric_torus_pullback X Ω K J y ξ G Li M h Z' ρ G' Φ hP Xc u r β zc (Mz zc) (hMz zc)
      (hinj zc _ (hMz zc)) (vv zc) (hvv zc))
  refine ⟨C, hC, fun zc zX hz Mz' hMz' v hv' w => ?_⟩
  subst hz
  rw [← hH zc Mz' hMz' v hv']
  exact hb zc trivial w

theorem xq_facts (X : Scheme.{0}) (h : LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X)) :
    LocallyOfFiniteType (XQ.snd X) ∧ QuasiCompact (XQ.snd X) ∧ IsLocallyNoetherian (XQ X) ∧
      TopologicalSpace.NoetherianSpace (XQ X) := by
  obtain ⟨h1, h2⟩ := h
  have a1 : LocallyOfFiniteType (XQ.snd X) := inferInstance
  have a2 : QuasiCompact (XQ.snd X) := inferInstance
  have a3 : IsLocallyNoetherian (XQ X) := LocallyOfFiniteType.isLocallyNoetherian (XQ.snd X)
  have a4 : CompactSpace (XQ X) := QuasiCompact.compactSpace_of_compactSpace (XQ.snd X)
  have a5 : IsNoetherian (XQ X) := {}
  exact ⟨a1, a2, a3, inferInstance⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped CategoryTheory.Obj

theorem stratum_good : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ XQ X), IsClosedImmersion i →
    ∃ (U : Z.Opens) (C : ℝ), (U : Set Z).Nonempty ∧ 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X)
      (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK),
      IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∀ zZ : Sp L ⟶ Z,
      zZ ≫ i = toXQ (spMap (algebraMap (𝓞 L) L) ≫ z) → ⊤ ≤ zZ ⁻¹ᵁ U → GoodAt h C z φ τ := by
  intro hFC X Ω _ K _ J _ y ξ hall hT G _ _ hG Li _ _ M h Z _ i hi
  have hfin := GlobalTheory.T.coords_finite_type_over_integers X Ω K J y ξ hall hT
  obtain ⟨hq1, hq2, hq3, hq4⟩ := xq_facts X hfin
  haveI := hG.smooth
  haveI := hG.separated
  let s : Z ⟶ Sp ℚ := i ≫ XQ.snd X
  haveI : LocallyOfFiniteType s := inferInstance
  haveI : QuasiCompact s := inferInstance
  let io : Z ⟶ X := i ≫ XQ.fst X
  have hGZ : IsSemiAbelian ((Over.pullback io).obj G) := IsSemiAbelian.pullback io G hG
  obtain ⟨Z', hZ', π, G', hG', φ', Xc, _, _, _, u, U, hπf, hπs, hnorm, hpb, hu, hU, hpt⟩ :=
    GlobalTheory.T.semiabelian_finite_cover_torus hFC Z s ((Over.pullback io).obj G) hGZ
  let f : Z' ⟶ XQ X := π ≫ i
  haveI hff : IsFinite f := inferInstance
  have hP : IsGrpPullback G' G (f ≫ XQ.fst X) (φ' ≫ pullback.fst G.hom io) := by
    have := isGrpPullback_comp (isGrpPullback_pullback G io) hpb
    simpa [f, io, CategoryTheory.Category.assoc] using this
  haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsSeparated G'.hom := by
    have h1 : IsSeparated ((Over.pullback io).obj G).hom := (IsSemiAbelian.separated (G := (Over.pullback io).obj G))
    exact MorphismProperty.of_isPullback (P := @IsSeparated) hpb.1 h1
  obtain ⟨r, ⟨β⟩⟩ := exists_dual_basis Xc
  have hU' : ((π ⁻¹ᵁ U : Z'.Opens) : Set Z').Nonempty := by
    obtain ⟨p, hp⟩ := hU
    obtain ⟨q, rfl⟩ := hπs.surj p
    exact ⟨q, hp⟩
  have hinj0 := GlobalTheory.T.torus_injective_on_open Z' G' Xc u (π ⁻¹ᵁ U) hU' (fun k _ x hx A _ g t ht => (hpt k x hx).1 A g t ht)
  obtain ⟨C, hC, hb⟩ := gram_bound X Ω K J y ξ hall hT G Li M h Z' f hff G' _ hP Xc u
    (fun zc Mz hMz δ hδ => hinj0 ℂ zc Mz hMz δ hδ) r β
  refine ⟨U, C, hU, hC, ?_⟩
  intro L _ _ z GK _ φ τ hGK zZ hzZ hzU
  letI := τ.addCommGroup
  let Lb := AlgebraicClosure L
  obtain ⟨x, hx⟩ := GlobalTheory.T.finite_surjective_lifts_points Z' Z π hπf hπs L zZ
  have hxρ : x ≫ f ≫ XQ.fst X = spMap (algebraMap L Lb) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) := by
    have e : zZ ≫ i ≫ XQ.fst X = spMap (algebraMap (𝓞 L) L) ≫ z := by
      rw [← CategoryTheory.Category.assoc, hzZ, toXQ_fst]
    simp only [f, CategoryTheory.Category.assoc]
    rw [reassoc_of% hx, e]
  have hxU : ⊤ ≤ (x ≫ π) ⁻¹ᵁ U := by
    rw [hx]
    intro p _
    have h1 : spMap (algebraMap L (AlgebraicClosure L)) p ∈ zZ ⁻¹ᵁ U := hzU (TopologicalSpace.Opens.mem_top _)
    simpa using h1
  obtain ⟨hi1, hi2⟩ := hpt Lb x hxU
  obtain ⟨e, he⟩ := GlobalTheory.T.torus_split_pullback_generic X Z' G G' (f ≫ XQ.fst X) _ hP Xc u L Lb x _ hxρ GK φ hGK τ hi1 hi2
  refine ⟨r, β.map (dualEquiv e), fun MT hMT B MB hF ε hε σ w => ?_⟩
  letI : Algebra L ℂ := σ.toAlgebra
  let σ' : Lb →+* ℂ := (IsAlgClosed.lift : Lb →ₐ[L] ℂ).toRingHom
  have hσ' : σ'.comp (algebraMap L Lb) = σ := by
    ext a
    exact (IsAlgClosed.lift : Lb →ₐ[L] ℂ).commutes a
  let zc : Sp ℂ ⟶ Z' := spMap σ' ≫ x
  let c : 𝓞 L →+* ℂ := σ.comp (algebraMap (𝓞 L) L)
  let zX : Sp ℂ ⟶ X := spMap c ≫ z
  have hzX : zc ≫ f ≫ XQ.fst X = zX := by
    have e1 : spMap σ' ≫ spMap (algebraMap L Lb) ≫ spMap (algebraMap (𝓞 L) L) = spMap c := by
      rw [LieTangent.spec_comp, LieTangent.spec_comp]
      simp only [c, ← RingHom.comp_assoc, hσ']
    show (spMap σ' ≫ x) ≫ f ≫ XQ.fst X = spMap c ≫ z
    rw [CategoryTheory.Category.assoc, hxρ, ← e1]
    simp only [CategoryTheory.Category.assoc]
  obtain ⟨Mz, hMz⟩ := GlobalTheory.T.exists_cocharacter_lie_model Z' Xc ℂ zc
  let v : Fin r → (epsAt zX ⟶ G) := fun a => LieTangent.epsBase c rfl ≫ MB.pt (ε a)
  have hv : ∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ (φ' ≫ pullback.fst G.hom io) := by
    intro a
    set δ' : τ.X →+ L := (Int.castAddHom L).comp ((β.map (dualEquiv e)) a) with hδ'
    let a0 : Sp (DualNumber L) ⟶ Sp L := (epsAt (𝟙 (Sp L))).hom
    let g1 : DualNumber L →+* DualNumber ℂ := dualMap σ
    let t' : Over.mk (spMap g1 ≫ a0) ⟶ splitTorus (Sp L) τ.X :=
      Over.homMk (spMap g1 ≫ (MT.pt δ').left) (by
        have := Over.w (MT.pt δ')
        simp only [Over.mk_hom, CategoryTheory.Category.assoc] at this ⊢
        rw [this]
        rfl)
    have hchar : ∀ χ, charVal t' χ = charVal (Mz.pt ((Int.castAddHom ℂ).comp (β a))) (e χ) := by
      intro χ
      have e1 := (GlobalTheory.T.charVal_multiplicative (Sp L) τ.X (DualNumber L) a0).2.2.2.2.2 (DualNumber ℂ) g1 (MT.pt δ') t' rfl χ
      rw [e1, hMT, hMz]
      simp only [g1, hδ']
      ext <;> simp [dualMap, dualEquiv]
    have e2 := he (DualNumber ℂ) ((algebraMap ℂ (DualNumber ℂ)).comp σ') (epsAt zc).hom (by
        show _ = Spec.map _ ≫ spMap σ' ≫ x
        rw [← CategoryTheory.Category.assoc, LieTangent.spec_comp]) (spMap g1 ≫ a0) (by
        show _ = spMap g1 ≫ Spec.map (CommRingCat.ofHom (algebraMap L (DualNumber L))) ≫ 𝟙 _
        rw [CategoryTheory.Category.comp_id, LieTangent.spec_comp]
        have e0 : ((algebraMap ℂ (DualNumber ℂ)).comp σ').comp (algebraMap L Lb) = g1.comp (algebraMap L (DualNumber L)) := by
          refine RingHom.ext fun a => ?_
          show algebraMap ℂ (DualNumber ℂ) (σ' (algebraMap L Lb a)) = dualMap σ (algebraMap L (DualNumber L) a)
          rw [dual_inl]
          exact congrArg (algebraMap ℂ (DualNumber ℂ)) (congrArg (fun q => q a) hσ')
        rw [e0]) (Mz.pt ((Int.castAddHom ℂ).comp (β a))) t' hchar
    refine Eq.trans ?_ e2.symm
    have e3 := hε a
    unfold LieModel.Lifts at e3
    have e4 : (v a).left = spMap (dualMap c) ≫ (MB.pt (ε a)).left :=
      (LieTangent.left_eq_iff _ _ _ _).2 rfl
    rw [e4]
    have e5 : spMap (dualMap c) = spMap g1 ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := by
      rw [LieTangent.spec_comp, ← RootHt.dualMap_comp]
    rw [e5, CategoryTheory.Category.assoc, ← e3, Over.comp_left]
    show _ = ((spMap g1 ≫ (MT.pt δ').left) ≫ τ.i.left) ≫ φ
    simp only [CategoryTheory.Category.assoc, Over.comp_left]
    rfl
  obtain ⟨hlo, hhi⟩ := hb zc zX hzX Mz hMz v hv w
  have hΓ : ∀ a b, RootHt.gramAt h zX v a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b) := by
    intro a b
    exact (hF σ (ε a) (ε b) (v a) (v b) rfl rfl).symm
  rw [GlobalTheory.T.hermitian_square_norm_gram L B σ r ε _ hΓ w]
  exact ⟨hlo, hhi⟩

end GlobalTheory.CompanionTheory.Ar.TorusUnif

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

open scoped CategoryTheory.Obj

theorem goodAt_mono {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} (h : LieMetric M y) {C C' : ℝ} (hC : 1 ≤ C) (hCC : C ≤ C') {L : Type} [Field L] [NumberField L]
    {z : Sp (𝓞 L) ⟶ X} {GK : Over (Sp L)} [GrpObj GK] {φ : GK.left ⟶ G.left} {τ : TorusExtension GK}
    (hg : GoodAt h C z φ τ) : GoodAt h C' z φ τ := by
  letI := τ.addCommGroup
  obtain ⟨r, bs, hb⟩ := hg
  refine ⟨r, bs, fun MT hMT B MB hF ε hε σ w => ?_⟩
  obtain ⟨h1, h2⟩ := hb MT hMT B MB hF ε hε σ w
  have hS : 0 ≤ ∑ a, ‖w a‖ ^ 2 := by positivity
  have hC0 : 0 < C := by linarith
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hC0 hCC) hS) h1, le_trans h2 (mul_le_mul_of_nonneg_right hCC hS)⟩

theorem torus_unif : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y), ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK), letI := τ.addCommGroup; IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier, (∀ a, MB.Lifts (algebraMap (𝓞 L) L) φ (ε a) (MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i)) → ∀ (σ : L →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  intro hFC X Ω _ K _ J _ y ξ hc hall hT G _ _ hG Li _ _ M h
  obtain ⟨hq1, hq2, hq3, hq4⟩ := xq_facts X (GlobalTheory.T.coords_finite_type_over_integers X Ω K J y ξ hall hT)
  let Good : ℝ → XQ X → Prop := fun C t => 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X)
      (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK),
      IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ →
      toXQ (spMap (algebraMap (𝓞 L) L) ≫ z) (IsLocalRing.closedPoint L) = t → GoodAt h C z φ τ
  have key := noeth_good (T := XQ X) Good (fun C C' t hCC hg => ⟨hg.1.trans hCC, fun L _ _ z GK _ φ τ hP ht =>
    goodAt_mono h hg.1 hCC (hg.2 L z GK φ τ hP ht)⟩) ?_
  · obtain ⟨C, hC, hg⟩ := key
    exact ⟨C, hC, fun L _ _ z GK _ φ τ hP => (hg _).2 L z GK φ τ hP rfl⟩
  · intro F hF hFi
    obtain ⟨Z, hZ, i, hi, hr, hlift⟩ := GlobalTheory.T.irreducible_closed_integral_subscheme (XQ X) F hF hFi
    obtain ⟨U, C, hU, hC, hgood⟩ := stratum_good hFC X Ω K J y ξ hall hT G hG Li M h Z i hi
    refine ⟨i '' (U : Set Z)ᶜ, hi.base_closed.isClosedMap _ U.isOpen.isClosed_compl, ?_, C, hC, fun t ht hnt => ?_⟩
    · have hsub : i '' (U : Set Z)ᶜ ⊆ F := by
        rintro _ ⟨p, -, rfl⟩
        exact hr ▸ Set.mem_range_self p
      refine ⟨hsub, fun hne => ?_⟩
      obtain ⟨p, hp⟩ := hU
      have hpF : i p ∈ F := hr ▸ Set.mem_range_self p
      obtain ⟨q, hq, hqp⟩ := hne hpF
      exact hq (hi.base_closed.injective hqp ▸ hp)
    · refine ⟨hC, fun L _ _ z GK _ φ τ hP ht' => ?_⟩
      obtain ⟨x', hx'⟩ := hlift L (toXQ (spMap (algebraMap (𝓞 L) L) ≫ z)) (ht' ▸ ht)
      refine hgood L z GK φ τ hP x' hx' ?_
      intro p _
      have hpc : p = IsLocalRing.closedPoint L := Subsingleton.elim _ _
      subst hpc
      by_contra hn
      refine hnt ⟨x' (IsLocalRing.closedPoint L), hn, ?_⟩
      rw [← ht', ← hx']
      rfl

end GlobalTheory.CompanionTheory.Ar.TorusUnif
