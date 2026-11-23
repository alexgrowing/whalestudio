import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideOfTwistedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricForStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfAutomorphismMapsParahoricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterSplitPlaceComponentUniqueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductLevelEqOfLocalAgreementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricLowerDetUnitAndSuperdiagIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAlgebraicModularFormOfTrivialStabiliStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpectedShapeLevelIntegralAndUnipotentAtTypePlacStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlacesUnionRamifiedPlacesFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankAlgebraicModularFormsComplexificationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProductLevelDefiniteFormsRealisationAtTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlacesAllStatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadPlacesSubOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideReadHeckeOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEtaOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellWeightOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorsAvoidExcludedPrimesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisCharacterOfFiniteOrderHeckeCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisCharacterAntiRamifiedExactlyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassGroupDescentOfCoeffFieldTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingClassGroupDescentsDifferByPowerPrimeToLStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistReadingInducesSideEmbeddingFixedFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

variable {D : D7}

theorem grpShape_of {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} {χ : J →* ℂˣ} (h1 : NG.IsProdLevel J)
    (h2 : ParaShape D η J χ)
    (h3 : ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∃ ψ₀ ξ, NG.LevelUni J χ s D.R.r ψ₀ ξ)
    (h4 : NG.HypOutside J χ (gPl D ∪ qPl D η)) : GrpShape D η J :=
  ⟨h1, fun v hv => let ⟨s, _, a, _, c⟩ := h2 v hv; ⟨s, a, c.mem⟩, fun k v s hs => let ⟨_, _, c⟩ := h3 k v s hs; c.mem,
    fun κ hκ => (h4 κ hκ).1⟩

theorem exists_form {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} (hG : GPlaces D) (h : GrpShape D η J)
    (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] (ρ : Representation K (GQ D.host.E D.R.nV) W)
    (hρ : ρ.IsIrreducible) (χ : J →* Kˣ) : ∃ f ∈ NX.TypeSpF D.host.E D.R.nV K ρ J χ, f ≠ 0 := by
  obtain ⟨k, ⟨v⟩⟩ := hG.2.2
  obtain ⟨h1, s, hs⟩ := hG.1 k v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_class_trivial_stabiliser_at_typePlace D k s (hs ▸ h1)
  haveI : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have := hρ
    have h2 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    exact h2 (Subrepresentation.ext (Subsingleton.elim _ _))
  exact GlobalTheory.T.exists_ne_zero_algebraicModularForm_of_trivial_stabiliser _ _ K W ρ J χ g fun γ hγ hm =>
    hg γ hγ (GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces D η J hG h _ hm).1 ((GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces D η J hG h _ hm).2 k v s hs)

theorem para_rigid {L : Type} [Field L] [NumberField L] [IsCMField L] {n r : ℕ} {s : SplitPlace L} {V : Type} [AddCommGroup V]
    [Module ℂ V] {F : GAf L n → V} {J : Subgroup (GAf L n)} {χ χ' : J →* ℂˣ}
    {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ} (hF : F ≠ 0) (h : NG.LevelPara J χ s r ξ)
    (hr : ∃ a : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield L)) = 1 ∧ ξ a ≠ 1)
    (h1 : ∀ κ, χ' κ = 1 ↔ χ κ = 1) (hE : ∀ κ : J, Eig F κ (χ' κ : ℂˣ)) :
    ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  obtain ⟨a, ha, ha'⟩ := hr
  refine GlobalTheory.T.mem_parahoric_of_scalar_action_on_ramifiedParahoricForm L n r s V F J χ' a hF ha h.mem hE (fun κ hκ ht hd => (h1 _).2 ?_) fun κ hκ ht hd e => ha' ?_
  · rw [h.chr κ hκ ht 1 hd.symm, map_one]
  · rw [← h.chr κ hκ ht a hd.symm]
    exact (h1 _).1 e

theorem cx_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ)
    {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) : cx e χ κ = 1 ↔ χ κ = 1 := by
  rw [← Units.val_inj, cx_apply, Units.val_one, map_eq_one_iff e e.injective, Units.val_eq_one]

theorem levEq {η : HChar D.host.E} {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (he : SideRead i b k e) (hG : GPlaces D)
    (hram : ∀ (s : SplitPlace D.host.E) ξ, s.v ∈ qPl D η → NG.IsCompAt η s ξ →
      ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
        Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1)
    (m1 : NG.IsProdLevel m.J) (m2 : ParaShape D η m.J m.χ)
    (m3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ)
    (m4 : NG.HypOutside m.J m.χ (gPl D ∪ qPl D η)) (x0 : NX.badV D i Q ⊆ gPl D ∪ qPl D η)
    (x2 : ParaShape D η (cell X b hA j).J (cx e (cell X b hA j).χ))
    (x3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      ∀ e, SideRead i b k e → NG.LevelUni (cell X b hA j).J (cx e (cell X b hA j).χ) s D.R.r ψ₀ ξ)
    (hJ : Joint η m X b hA j) : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ) := by
  have x1 := GlobalTheory.T.isProductLevel_definiteFormsRealisationAtTwist D X i b k Q ψ hA j
  have x4 : NG.HypOutside (cell X b hA j).J (cx e (cell X b hA j).χ) (gPl D ∪ qPl D η) := fun κ hκ => by
    have h := (cell X b hA j).hyp κ fun v hv => hκ v fun h => hv fun h' => h (x0 h')
    exact ⟨h.1, fun h' => (cx_eq_one _ _ _).2 (h.2 h')⟩
  have gm := grpShape_of m1 m2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := m3 k v s hs; ⟨a, c, d⟩) m4
  have gx := grpShape_of x1 x2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := x3 k v s hs; ⟨a, c, d e he⟩) x4
  obtain ⟨θ, J₁, e', V, _, _, ω, hθ, he', hω, j1, j2, j3⟩ := hJ
  obtain ⟨f, hf, hf0⟩ := exists_form hG gm ℂ _ m.wt.ρ m.wt.irr m.χ
  obtain ⟨f', hf', hf0'⟩ := exists_form hG gx _ _ (cell X b hA j).ρ (cell X b hA j).irr (cell X b hA j).χ
  obtain ⟨y, rfl⟩ : f ∈ LinearMap.range m.real := by
    rw [m.real_range]
    obtain ⟨N, hN, h⟩ := m.J_open
    refine ⟨⟨hf.1, N, hN, fun κ hκ g => ?_⟩, fun κ => funext fun g => hf.2 κ g⟩
    obtain ⟨h1, h2⟩ := h κ hκ
    have := hf.2 ⟨κ, h1⟩ g
    rwa [h2, Units.val_one, one_smul] at this
  obtain ⟨y', hy'⟩ := (cell X b hA j).real.surjective ⟨f', hf'⟩
  set F' : GAf D.host.E D.R.nV → V := fun g => ω (((cell X b hA j).real y').1 g) with hF'
  have hF0 : F' ≠ 0 := fun h => hf0' (funext fun g => hω (by
    have := congrFun h g
    rw [hF'] at this
    simp only [hy'] at this
    exact this.trans (map_zero ω).symm))
  have E1 : ∀ κ : m.J, Eig (m.real y) κ (m.χ κ : ℂˣ) := fun κ g => hf.2 κ g
  have E2 : ∀ κ : (cell X b hA j).J, Eig F' κ (cx e' (cell X b hA j).χ κ : ℂˣ) := fun κ g => by
    have := ((cell X b hA j).real y').2.2 κ g
    simp only [hF', this, map_smulₛₗ, cx_apply]
  have hr0 : 2 ≤ D.R.r := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; unfold Ranks.r; omega
  have hr1 : D.R.r < D.R.nV := by have := D.R.rank_add_five_le; unfold Ranks.nV; omega
  refine GlobalTheory.T.productLevel_eq_of_local_agreement _ _ _ _ _ _ _ (GlobalTheory.T.typePlaces_union_ramifiedPlaces_finite D η) m1 x1 m4 x4 fun u hu => ?_
  rcases hu with hu | hu
  · obtain ⟨kk, v, s, rfl, hs⟩ := hG.2.1 u hu
    obtain ⟨p, ξ, a1, a2, a3⟩ := m3 kk v s hs
    obtain ⟨p', ξ', b1, b2, b3⟩ := x3 kk v s hs
    obtain rfl := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique _ η s ξ ξ' a2 b2
    have hg := D.host.g_prime kk
    have hab : s.Above (D.host.g kk) := by
      have h1 : ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := hs ▸ (hG.1 kk v).1
      show _ ∈ s.v.asIdeal
      rw [← s.w_under]
      show algebraMap _ (𝓞 D.host.E) _ ∈ s.w.asIdeal
      rwa [map_natCast]
    have key := GlobalTheory.T.additiveCharacter_eq_of_common_unipotentLevel_eigenvector _ _ _ s (D.host.g kk) (D.host.g kk - 1) θ _ _ (m.real y) F' _ _ _ _ p p' ξ ξ hg hab
      ((Nat.coprime_self_sub_left hg.one_le).2 (Nat.coprime_one_left _)) hr0 hr1.le hθ hf0 hF0 a1 b1 a3 (b3 e' he') E1 E2
      fun κ hκ hU => let ⟨c, c', h1, h2, h3⟩ := j3 κ (j2 kk v s hs κ hκ hU); ⟨c, c', h1 y, h2 y', h3 kk v s hs hκ⟩
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans ((b3 e he).mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, u2⟩ := GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral _ _ _ s _ ((a3.mem κ hκ).1 h).1
    have hne : NG.detDD s D.R.r (s.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    apply Units.ext
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, (b3 e he).chr κ h' hκ (Units.mk0 _ hne) rfl, key _ u2]
  · obtain ⟨s, ξ, rfl, a2, a3⟩ := m2 u hu
    obtain ⟨s', ξ', b1, b2, b3⟩ := x2 _ hu
    obtain ⟨s₁, c1, c2⟩ := j1 _ hu
    have hU : ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s₁ D.R.r (s₁.loc _ κ) → κ ∈ Umax D.host.E D.R.nV := fun κ hκ hP =>
      (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s₁ (c1 ▸ hκ)).1 hP.1
    have hs : s' = s := GlobalTheory.T.splitPlace_eq_of_automorphism_maps_parahoric _ _ _ s s' s₁ θ (by omega) hr1 b1 c1 hθ fun κ hκ hP => by
      obtain ⟨c, c', h1, h2, -⟩ := j3 κ (c2 κ (c1 ▸ hκ) hP)
      have h3 := (hθ.1 κ).2 (hU κ hκ hP)
      have h4 := (hθ.2 _ κ).2 hκ
      exact ⟨para_rigid hf0 a3 (hram s ξ hu a2) (fun _ => Iff.rfl) E1 _ h3 h4 ⟨c, h1 y⟩,
        para_rigid hF0 b3 (hram s' ξ' (b1 ▸ hu) b2) (fun κ => (cx_eq_one _ _ _).trans (cx_eq_one _ _ _).symm) E2 _ h3
          (b1 ▸ h4) ⟨c', h2 y'⟩⟩
    subst hs
    obtain rfl := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique _ η s' ξ ξ' a2 b2
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans (b3.mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, -⟩ := GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral _ _ _ s' _ ((a3.mem κ hκ).1 h)
    have hne : NG.detDD s' D.R.r (s'.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, b3.chr κ h' hκ (Units.mk0 _ hne) rfl]

theorem unpack {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : GlobalTheory.TwistChoice.HasReading p b w ψ₀) {i : D.ntw.Tw} {Q : Finset (PlE D.host)} {k : ℕ} (h1 : p.1 = i) (h2 : p.2.1 = Q)
    (h3 : p.2.2.1 = k) : ∃ (ρ : Reading i k b w) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ), ρ.Pulls ψ ψ₀ ∧ twPack D i b Q k ψ = p := by
  obtain ⟨i', Q', k', φ⟩ := p
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, _, hρ, congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) (psiAt_psiAt b φ)⟩

theorem pack_pow {i i' : D.ntw.Tw} {k k' : ℕ} {b b' : Bool} {v v' : D.what₂.places.Pl} (ρ : Reading i k b v) (ρ' : Reading i' k' b' v')
    {Q Q' : Finset (PlE D.host)} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ' : D.ntw.RCG i' Q' →* (D.ntw.Ok i' k')ˣ}
    {ψ₀ ψ₀' : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h1 : i' = i) (h2 : Q' = Q) (h3 : k' = k) (h4 : ψ₀' = ψ₀)
    (hz : ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) (ho : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hp : ρ.Pulls ψ ψ₀)
    (hp' : ρ'.Pulls ψ' ψ₀') :
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ twPack D i' b' Q' k' ψ' = GlobalTheory.HeightCounting.twPackPow D a (twPack D i b Q k ψ) := by
  subst h1 h2 h3 h4
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.T.ringClassGroup_descents_differ_by_power_prime_to_l D _ _ b b' v v' ρ ρ' _ ψ ψ' _ hz ho hp hp'
  refine ⟨if b = b' then a else -a, by split_ifs <;> simpa using ha, ?_⟩
  refine congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) ?_
  cases b <;> cases b'
  · exact (inv_zpow ψ a).symm
  · exact ((inv_zpow' ψ (-a)).trans (congrArg (ψ ^ ·) (neg_neg a))).symm
  · exact (zpow_neg ψ a).symm
  · rfl

theorem exists_data (hG : IsGalois ℚ ↥D.LL0) (s : D.what₂.places.Pl → D.ntw.Tw) (Q : D.what₂.places.Pl → Finset (PlE D.host))
    (k : D.what₂.places.Pl → ℕ) (ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ))
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v) (c2 : ∀ v, Q (D.what₂.places.conj v) = Q v)
    (c3 : ∀ v, k (D.what₂.places.conj v) = k v) (c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v)
    (hex : ∀ v b (ρ : Reading (s v) (k v) b v), ∃ ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ, ρ.Pulls ψ (ψ₀ v)) :
    ∃ (b : D.what₂.places.Pl → Bool) (ρ : ∀ v, Reading (s v) (k v) (b v) v)
      (ψ : ∀ v, D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), (∀ v, ReadsAt (s v) (b v) v) ∧ (∀ v, (ρ v).Pulls (ψ v) (ψ₀ v)) ∧
      (∀ v, D.what₂.places.conj v ≠ v → b (D.what₂.places.conj v) = !b v) ∧
      ∀ v, twPack D (s (D.what₂.places.conj v)) (b (D.what₂.places.conj v)) (Q (D.what₂.places.conj v)) (k (D.what₂.places.conj v))
        (ψ (D.what₂.places.conj v)) = twPack D (s v) (b v) (Q v) (k v) (ψ v) := by
  classical
  choose b₀ hb using hs
  have h0 : ∀ v, ∃ p : TwPack D, GlobalTheory.TwistChoice.HasReading p (b₀ v) v (ψ₀ v) ∧ p.1 = s v ∧ p.2.1 = Q v ∧ p.2.2.1 = k v := fun v => by
    obtain ⟨ρ⟩ := (hb v).nonempty_reading (k v)
    obtain ⟨ψ, hψ⟩ := hex v _ ρ
    refine ⟨twPack D (s v) (b₀ v) (Q v) (k v) ψ, ⟨ρ, ?_⟩, rfl, rfl, rfl⟩
    show ρ.Pulls (BlochKatoReduction.Gen.psiAt (b₀ v) (BlochKatoReduction.Gen.psiAt (b₀ v) ψ)) _
    rwa [psiAt_psiAt]
  choose p hp using h0
  obtain ⟨o, ho⟩ := GlobalTheory.TwistChoice.exists_orbitRep (D := D)
  let b : D.what₂.places.Pl → Bool := fun w => if o w = w then b₀ w else !b₀ (D.what₂.places.conj w)
  have h1 : ∀ v, ReadsAt (s v) (b v) v ∧ ∃ (ρ : Reading (s v) (k v) (b v) v)
      (ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), ρ.Pulls ψ (ψ₀ v) ∧ twPack D (s v) (b v) (Q v) (k v) ψ = p (o v) := fun v => by
    by_cases h2 : o v = v
    · have e : b v = b₀ v := if_pos h2
      rw [e, h2]
      exact ⟨hb v, unpack (hp v).1 (hp v).2.1 (hp v).2.2.1 (hp v).2.2.2⟩
    · have e : b v = !b₀ (D.what₂.places.conj v) := if_neg h2
      have h3 := (hb (D.what₂.places.conj v)).conj hG
      have h4 := (hp (D.what₂.places.conj v)).1.conj hG
      rw [D.what₂.places.conj_conj] at h3 h4
      rw [c1] at h3
      rw [c4] at h4
      rw [e, (ho v).1.resolve_left h2]
      exact ⟨h3, unpack h4 ((hp _).2.1.trans (c1 v)) ((hp _).2.2.1.trans (c2 v)) ((hp _).2.2.2.trans (c3 v))⟩
  choose hr ρ ψ h2 h3 using h1
  refine ⟨b, ρ, ψ, hr, h2, fun w hne => ?_, fun v => by rw [h3, h3, (ho v).2]⟩
  simp only [b, (ho w).2, D.what₂.places.conj_conj]
  rcases (ho w).1 with h | h
  · rw [if_neg (by rw [h]; exact hne.symm), if_pos h]
  · rw [if_pos h, if_neg (by rw [h]; exact hne), Bool.not_not]

abbrev kMap {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) : NX.Kk D i k →+* FractionRing ρ.Oe :=
  IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj

theorem reads_of_pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) {Q : Finset (PlE D.host)}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} {χ : HChar D.host.E} (hp : ρ.Pulls ψ ψ₀)
    (hg : GalOf D χ ψ₀) {ι : FractionRing ρ.Oe →+* ℂ} (hι : ∀ x, ι (ρ.emb x) = D.what₂.embLL x) :
    SideRead i b k (ι.comp (kMap ρ)) ∧ ReadsHecke (ι.comp (kMap ρ)) (ψ.comp (D.ntw.art i Q)) χ := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [RingHom.comp_apply, ← (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D i k b v ρ).2.1 x, hι]
    rfl
  · obtain ⟨-, art, ha, h⟩ := hg
    refine ⟨art, ha, fun x σ e => (h x σ e).trans (Units.ext ?_)⟩
    show D.what₂.embLL (ψ₀ σ : D.what₂.LLˣ) = ι (kMap ρ (algebraMap _ _ ((ψ (D.ntw.art i Q σ) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)))
    rw [← hι, hp σ]
    simp [IsFractionRing.map]

theorem rank_of_levEq {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (h : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ)) (hw : CellWt m X b hA j e) :
    Module.finrank D.what₂.LL (D.what₂.MtL μ j') = Module.finrank (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
  haveI : FiniteDimensional (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
    obtain ⟨S, hS⟩ := D.nexp.MtLat_fg i (j.1 + 1) b k Q ψ
    refine ⟨S, ?_⟩
    rw [← D.nexp.MtLat_span i (j.1 + 1) b k Q ψ, ← hS, Submodule.span_span_of_tower]
  have h1 := GlobalTheory.T.finrank_algebraicModularForms_complexification _ _ _ e _ _ _ _ _ (cell X b hA j).χ hw (cell X b hA j).J_open
    (Module.Finite.equiv (cell X b hA j).real)
  rw [(cell X b hA j).real.finrank_eq, ← h1]
  have h2 : NG.TypeSp m.wt.ρ (cell X b hA j).J (cx e (cell X b hA j).χ) = NG.TypeSp m.wt.ρ m.J m.χ := by
    obtain ⟨h3, h4⟩ := h
    ext f
    refine and_congr_right fun _ => ⟨fun H κ => ?_, fun H κ => ?_⟩
    · rw [h4 κ.1 κ.2 (h3 ▸ κ.2)]
      exact H ⟨κ.1, h3 ▸ κ.2⟩
    · rw [← h4 κ.1 (h3.symm ▸ κ.2) κ.2]
      exact H ⟨κ.1, h3.symm ▸ κ.2⟩
  rw [h2, ← m.real_range, LinearMap.finrank_range_of_inj m.real_inj]
  obtain ⟨h3, h4⟩ := D.what₂.jMt_basis μ j' (Module.Free.chooseBasis _ _)
  rw [Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis _ _),
    Module.finrank_eq_nat_card_basis (Module.Basis.mk h3 h4.ge)]

theorem exists_choice (hP : PrN) (hG : IsGalois ℚ ↥D.LL0) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (M : MtFam D) (X : NExpTied D)
    (F : TwFrameC D) (xi : D.what₂.Tup → HChar D.host.E) (χ : D.what₂.places.Pl → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (k : D.what₂.places.Pl → ℕ) (s : D.what₂.places.Pl → D.ntw.Tw)
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v)
    (htp : ∀ C : NChoice D, C.Q = Q → ∃ tp : TupTied D cf C, tp.xi = xi ∧ tp.psi = χ)
    (h1 : ∀ v, IsPsi (H := D.host) (D.what₂.places.resChar v) (Q v) (χ v))
    (h2 : ∀ v, (χ v).OrderDvd (D.what₂.places.resChar v ^ k v))
    (h3 : ∀ v, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.what₂.places.resChar v ^ k v))
    (h4 : ∀ v, ¬ TwistedAt D v → Q v = ∅) (h5 : ∀ v, Disjoint (Q v) (D.ntw.S0 (s v)))
    (h6 : ∀ v v', (∀ x ∈ D.LL0, 0 ≤ D.what₂.places.val v x ↔ 0 ≤ D.what₂.places.val v' x) → k v = k v' ∧ χ v = χ v')
    (h7 : ∀ v, χ (D.what₂.places.conj v) = χ v ∧ k (D.what₂.places.conj v) = k v)
    (h8 : ∀ v b (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok (s v) (k v))ˣ) (hA : NX.AdmTw D (s v) (k v) (Q v) ψ) (j : Fin D.R.m),
      TwistedAt D v → D.ntw.l (s v) = D.what₂.places.resChar v → IntegralHeckeForms.TwOK (s v) (k v) (Q v) ψ → ∀ e, SideRead (s v) b (k v) e →
      ReadsHecke e ψ (χ v) →
      LevEq (mtAt M v j).J (mtAt M v j).χ (cell X b hA j).J (cx e (cell X b hA j).χ) ∧ CellWt (mtAt M v j) X b hA j e) :
    ∃ (C : NChoice D) (tp : TupTied D cf C), tp.xi = xi ∧ tp.psi = χ ∧ C.Q = Q ∧ C.k' = k ∧ ChoiceSide D cf M X C tp ∧
      (∀ v, IntegralHeckeForms.TwOK (C.twI v) (C.k' v) (C.Q v) ((C.psi' v).comp (D.ntw.art (C.twI v) (C.Q v)))) ∧ C.twI = s := by
  classical
  have hl : ∀ v, D.ntw.l (s v) = D.what₂.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  have hQ : ∀ v v', χ v = χ v' → Q v = Q v' := fun v v' e => Finset.ext fun u =>
    not_iff_not.1 (((h1 v).ram u).symm.trans (e ▸ (h1 v').ram u))
  let g : HChar D.host.E → ℕ → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) := fun c n =>
    @Classical.epsilon _ ⟨1⟩ fun ψ₀ => GalOf D c ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1
  let ψ₀ := fun v => g (χ v) (D.ntw.l (s v) ^ k v)
  have hψ : ∀ v, GalOf D (χ v) (ψ₀ v) ∧ ∀ g, ψ₀ v g ^ (D.ntw.l (s v) ^ k v) = 1 := fun v =>
    Classical.epsilon_spec (GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter hP.what₂.art D (χ v) _ (pow_pos (D.ntw.lPrime _).out.pos _) (hl v ▸ h2 v) (hl v ▸ h3 v))
  have c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v := fun v => by simp only [ψ₀, c1, (h7 v).1, (h7 v).2]
  have hd := fun v b (ρ : Reading (s v) (k v) b v) =>
    let ⟨a1, a2, a3⟩ := GlobalTheory.T.galois_character_anti_ramified_exactly hP D _ (Q v) (χ v) (ψ₀ v) (D.ntw.lPrime (s v)).out (hl v ▸ h1 v) (hψ v).1
    GlobalTheory.T.exists_ringClassGroup_descent_of_coeffFieldTwist D (s v) (k v) b v ρ (Q v) (ψ₀ v) (h1 v).split (h5 v) (hψ v).1.1 a1 (hψ v).2 a2 a3
  obtain ⟨b, ρ, ψ, hr, hp, hb, hc⟩ := exists_data hG s Q k ψ₀ hs c1 (fun v => hQ _ _ (h7 v).1) (fun v => (h7 v).2) c4
    fun v b ρ => (hd v b ρ).1
  have hok := fun v => (hd v _ (ρ v)).2 _ (hp v)
  choose ι hι using fun v => GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField D F (s v) (k v) (b v) v (ρ v)
  have hlev := fun v hA j (hv : TwistedAt D v) =>
    let ⟨a1, a2⟩ := reads_of_pulls (ρ v) (hp v) (hψ v).1 (hι v)
    h8 v (b v) _ hA j hv (hl v) (hok v) _ a1 a2
  have hrk : ∀ v, TwistedAt D v → GlobalTheory.TwistChoice.RankEq (s v) (b v) (Q v) (k v) (ψ v) v := fun v hv j j1 j2 => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨a1, a2⟩ := hlev v (GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v)) ⟨j, j2⟩ hv
    exact rank_of_levEq _ X _ _ ⟨j, j2⟩ _ a1 a2
  let C := GlobalTheory.TwistChoice.choiceOf s b Q k ψ hr ρ hrk
  obtain ⟨tp, t1, t2⟩ := htp C rfl
  refine ⟨C, tp, t1, t2, rfl, rfl, ⟨⟨fun a => hE.elim a, fun a => hE.elim a, fun a => hE.elim a,
    ⟨ψ₀, c4, hp, fun a => hE.elim a⟩, fun v x y z _ hx => (ρ v).emb_side x y z hx⟩,
    ⟨c1, fun v _ => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1, fun v _ x => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).2.2 _ x, fun v _ => hb v,
      fun v v' _ _ e => ?_, fun v _ => hc v⟩, h4, fun v _ => GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v), ?_, ?_⟩, hok, rfl⟩
  · have e' : s v' = s v := e
    have key : k v' = k v ∧ χ v' = χ v := by
      have a1 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1
      have a2 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v')).1
      have a3 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ ((ρ v').conj hG)).1
      rw [e'] at a2 a3
      by_cases hbb : b v' = b v
      · rw [hbb] at a2
        exact h6 _ _ fun x hx => (a2 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
      · have : (!b v') = b v := by revert hbb; cases b v <;> cases b v' <;> simp
        rw [this] at a3
        have a4 := h6 _ _ fun x hx => (a3 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
        exact ⟨(h7 v').2.symm.trans a4.1, (h7 v').1.symm.trans a4.2⟩
    exact pack_pow (ρ v) (ρ v') e' (hQ _ _ key.2) key.1 (by simp only [ψ₀, e', key.1, key.2]) (hl v ▸ h3 v) (hψ v).2 (hp v) (hp v')
  · intro v _ u hu _ A σ hA hσ y hy
    obtain ⟨-, art, ha, h⟩ := (hψ v).1
    have a1 := h.val_eq ha (((h1 v).ram u).2 hu) hA hσ
    have a2 : y = (ψ₀ v σ : D.what₂.LLˣ) := D.what₂.embLL.injective (by rw [hy, t2, a1, inv_inv]; rfl)
    rw [a2]
    exact hp v σ
  · intro v j j1 j2 hv hA
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨⟨a1, a2⟩, -⟩ := hlev v hA ⟨j, j2⟩ hv
    exact ⟨ι v, hι v, a1, fun κ h h' => congrArg Units.val (a2 κ h h')⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem muIsW (x : St P) : V4.MuIsW (w.st x.o.Z) f T P.Wt w.I.xi where
  inj := w.ok.xi_inj
  range := w.xi_range
  mu0 := w.l.xi0
  star := by
    show w.I.xi w.I.muStar = f.del
    rw [w.ok.xi_star, w.C_eq]
  star' := by
    show w.I.xi w.I.muStar' = f.del'
    rw [w.ok.xi_star', w.C_eq]
  tw := P.q.mu.tw
  on := P.q.mu.on
  off := P.q.mu.off
  sub := P.sub
  supp := P.supp

theorem cfOf_eq (x : St P) : cfOf x = Fr.at (w.st x.o.Z) f :=
  congrArg (Fr.at (w.st x.o.Z)) w.C_eq

theorem exists_tp (x : St P) (C : NChoice (Dof x)) (h : C.Q = QOf P) :
    ∃ tp : TupTied (Dof x) (cfOf x) C, tp.xi = w.I.xi ∧ tp.psi = T.psi := by
  rw [cfOf_eq]
  exact (GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW x)).2.2.2 C fun v _ =>
    (congrFun h v).trans (Model.qOf_eq v)

theorem disjoint_conductorPlaces_excludedSet {Q : Finset (PlE D.host)} {i : D.ntw.Tw} (h : OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D)))
    (h1 : ∀ u ∈ Q, u ∉ placesOver D.host.E (D.ntw.l i)) (h2 : ∀ u ∈ Q, ∀ p ∈ lowAll D, u ∉ placesOver D.host.E p) :
    Disjoint Q (D.ntw.S0 i) := Finset.disjoint_left.2 fun u hu hS => by
  obtain ⟨p, hp, h3⟩ := h u hS
  rcases Finset.mem_insert.1 hp with rfl | hp
  exacts [h1 u hu h3, h2 u hu p hp h3]

theorem choices_exist_for : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SCk hL := by
  intro hCo hCW hHM hP hS hL
  refine ((GlobalTheory.T.choice_side_of_twisted hCo hCW hHM hP hS hL).and ((GlobalTheory.T.good_places_all_states hL).and (GlobalTheory.T.twistConductors_avoid_excludedPrimes.and ((GlobalTheory.T.bad_places_sub_of_admissible_twist hP hL).and ((GlobalTheory.T.side_read_hecke_of_admissible_twist hP hL).and ((GlobalTheory.T.split_place_of_admissible_twist hP hL).and
    ((GlobalTheory.T.joint_eta_of_admissible_twist hP hL).and (GlobalTheory.T.cell_weight_of_admissible_twist hP hL)))))))).trans (StepW.of_all ?_)
  rintro K B f T w - - ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ P x l s hs c1
  have hl : ∀ v, (Dof x).ntw.l (s v) = B.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  obtain ⟨C, tp, b1, b2, b3, b4, b5, b6, b7⟩ := exists_choice (D := Dof x) hP B.coeffGaloisSubfield_isGalois l.a.A.bare (cfOf x) l.mt.M l.b.Bs.exp
    l.b.Bs.twF w.I.xi T.psi (QOf P) T.k s hs c1 (exists_tp x) (fun v => Model.qOf_eq (P := P) v ▸ T.psi_is v) T.psi_ord P.coh.roots
    (fun v hv => Model.qOf_off v fun h => hv ((Model.twisted_iff x v).2 h))
    (fun v => disjoint_conductorPlaces_excludedSet (l.b.rootsOfUnityRing_le_wittIntegers (s v)) (fun u hu h => T.Q_l v u (Model.qOf_eq (P := P) v ▸ hu) (hl v ▸ h))
      fun u hu => a2 P x v u (Model.qOf_eq (P := P) v ▸ hu))
    (fun v v' h => (P.coh.same v v' h).2) T.conj fun v b ψ hA j hv hl' hok e he hr => by
      have hg := TupTie.good_set f T (w.xi_range ▸ Set.mem_range_self ((Dof x).what₂.muTw v))
      exact ⟨levEq _ _ b hA j e he (a1 P x l.toLA)
        (fun s' ξ => GlobalTheory.T.exists_local_unit_character_nontrivial (Dof x) (cfOf x) j _ s' ξ hg.2.1 hg.2.2) (l.mt.mt.prod v j) (l.mt.mt.para v j) (l.mt.mt.uni v j)
        (l.mt.mt.hyp v j) (a3 P x l v _ b ψ hA j hv hl' hok) (a4 P x l v _ b ψ hA j hv hl' hok e he hr)
        (a5 P x l v _ b ψ hA j hv hl' hok) (a6 P x l v _ b ψ hA j hv hl' hok), a7 P x l v _ b ψ hA j hv hl' hok e he⟩
  obtain ⟨c, hc⟩ := a0 P x l C tp b1 b2 b3 (fun v _ => congrFun b4 v) b5 fun v _ => b6 v
  exact ⟨c, hc.trans b7⟩

end GlobalTheory.LevCmp

end
