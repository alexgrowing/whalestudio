import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmTypeValuationEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrderValuationCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeExtendScalarsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeStableUnderActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeEigenDecompositionLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeActionToResidueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReduceLatticeCoordsToResidueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldEigenBasisDescendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TiedActionComposeResidueMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasesChangeByBlockMatricesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasisSpansEigenspaceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResidueHodgeLatticeAdaptedBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenbasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiLinearCombinationDetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BasisOfSubmoduleIffUniqueCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpIntegersValuationRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldEmbeddingsIntoCpIntegralStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpEmbeddingFactorsThroughComplexStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmConjugationCompatComplexConjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointEigenFrameReductionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointComponentEigenReductionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmIntegersRegularAtComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationLatticeBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombTangentIffLinearSumStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrSpecializationEigenFrameStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem inc_eq : ∀ (E Ωf : Type) [Field E] [NumberField E] [Field Ωf] (σ σ₂ : E →+* Ωf), (∀ b : 𝓞 E, σ (b : E) = σ₂ (b : E)) → σ = σ₂ := by
  intro E Ωf _ _ _ σ σ₂ h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem eig_eq : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W] (ρ : 𝓞 E →+* Module.End K W) (σ : 𝓞 E →+* K) (σ' : E →+* K), (∀ a : 𝓞 E, σ a = σ' (a : E)) → eigSp ρ σ = HT.eigSp ρ σ' := by
  intro E _ _ K W _ _ _ ρ σ σ' h
  unfold eigSp HT.eigSp
  congr 1
  funext a
  rw [h a]
  rfl

theorem log_end {F : Type} [NormedField F] (M : ℕ) (a : ℤ) (x pp mu : F) (hM : 0 < M) (hx : x ≠ 0) (hp : pp ≠ 0)
    (hmu : ‖mu‖ = 1) (h : x ^ M = pp ^ a * mu) : Real.log ‖x‖ = (a / M) * Real.log ‖pp‖ := by
  have h1 := congrArg norm h
  rw [norm_pow, norm_mul, hmu, _root_.mul_one, norm_zpow] at h1
  have h2 := congrArg Real.log h1
  rw [Real.log_pow, Real.log_zpow] at h2
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  field_simp
  linarith

theorem norm_eq_one_of {F : Type} [NormedField F] (x y : F) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : x * y = 1) : ‖x‖ = 1 := by
  have h4 := congrArg norm h
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg x, norm_nonneg y]

set_option maxHeartbeats 4000000 in

theorem value_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (φ : FrameFn Xo c) (𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q)) (σ : E →+* Z.Ω) (v : Fin D.p → Z.V) (w : Fin D.q → Z.V) (u : Fin (D.p + D.q) → Z.V × Module.Dual Z.Ω Z.V) (α κ' : Z.Ω) (M : ℕ) (a : ℤ), τ (H.rt : E) = H.rt0 → Irreducible ϖ → Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) → LinearIndependent Z.Ω v → Submodule.span Z.Ω (Set.range v) = HT.eigSp Z.ρ σ → LinearIndependent Z.Ω w → Submodule.span Z.Ω (Set.range w) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → IsAdapted 𝓗.ρH σ v w u → 0 < M → (∀ x, OrderAt (detLat (𝓗.quot σ) u) (α / κ') (Z.inc (β ϖ)) M a x) → κ' ≠ 0 → Represents Y U τ Z.M (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w) φ → IsLineFn U τ φ → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ ϖ p κ φ 𝓗 σ v w u α κ' M a hτ hϖ hinj hr hσ hv hvs hw hws had hM hord hκ' hrep hφ
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  haveI : FiniteDimensional Z.Ω Z.V := 𝓗.finiteDimensional
  have hσE : σ = Z.inc.comp (inE c τ) := inc_eq E Z.Ω _ _ hσ
  obtain ⟨f, hf⟩ : ∃ f : (E →+* ℂ_[p]) → (E →+* ℂ), ∀ s, s = κ.comp (inE c (f s)) :=
    ⟨fun s => (GlobalTheory.T.cp_embedding_factors_through_complex E H l c p κ s).choose, fun s => (GlobalTheory.T.cp_embedding_factors_through_complex E H l c p κ s).choose_spec⟩
  obtain ⟨hI, hℓ₀, hnorm⟩ := GlobalTheory.T.cp_integers_valuation_ring p
  obtain ⟨hint, hcard⟩ := GlobalTheory.T.number_field_embeddings_into_cp_integral E p
  have hinv : ∀ a, H.bar (H.bar a) = a := fun a => (GlobalTheory.T.cm_conjugation_compat_complex_conj E H τ a).2
  have hbarF : ∀ a : 𝓞 E, inE c (ComplexEmbedding.conjugate τ) (a : E) = inE c τ (H.bar a : 𝓞 E) := fun a =>
    Subtype.ext (GlobalTheory.T.cm_conjugation_compat_complex_conj E H τ a).1
  obtain ⟨gm, hgm0, hgm⟩ := GlobalTheory.T.cm_type_valuation_embedding E (OCp p) ℂ_[p] H.bar (κ.comp (inE c τ))
    (κ.comp (inE c (ComplexEmbedding.conjugate τ)))
    (fun s => Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c (f s))))) D.p D.q
    (NormedField.valuation (K := ℂ_[p])) hI hℓ₀ hint hcard (fun a => by simp only [RingHom.comp_apply, hbarF]) hinv
  refine ⟨(a / M) * Real.log ‖κ (β ϖ)‖ + Real.log ‖gm‖, ?_⟩
  intro V K _ _ _ _ _ _ j βK y vv ww T tK m m' hj hκ hF hIv hIw

  obtain ⟨z, hz⟩ := GlobalTheory.T.dvr_point_eigen_frame_reduction E H D l Xo c O β Y p κ V K j βK y hr hj hκ hF.1
  obtain ⟨h₁, h₂, ψ, hsp, hle, hval, hval', hVr, hinc⟩ :=
    GlobalTheory.T.dvr_point_component_eigen_reduction E H D l Xo c O β Y U Z p κ V K j βK y z hinj hr hj hκ hF.1 hF.2.1 hz
  haveI : CharZero K := charZero_of_injective_ringHom βK.injective
  obtain ⟨U₁, hU₁, t, ht⟩ := 𝓗.free ⟨_, h₂⟩
  obtain ⟨U₂, hU₂, ℓ, hℓs, hℓ⟩ := 𝓗.vb ⟨_, h₂⟩ trivial
  have hy₁ : centre (y ≫ Y.j) ∈ U₁ := hsp.mem_open U₁.2 hU₁
  have hy₂ : centre (y ≫ Y.j) ∈ U₂ := hsp.mem_open U₂.2 hU₂
  have hH : ∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ U₁ → q.1 ∈ U₂ → HodgeAt 𝓗.ρH (𝓗.HL q) ℓ t := by
    intro q q₁ q₂
    have hfr := hℓ q trivial q₂
    refine ⟨ht q q₁, (congrFun 𝓗.map_fst q).trans hfr.2, fun f => ?_⟩
    have e := congrFun 𝓗.comap_inr q
    have : ((0 : Z.V), f) ∈ 𝓗.HL q ↔ f ∈ (Z.M.lat.dual) q := by
      rw [← e]; exact Iff.rfl
    rw [this, ← hfr.2]
    exact Iff.rfl
  have hHx := hH ⟨_, h₂⟩ hU₁ hU₂
  have hHy := hH ⟨_, h₁⟩ hy₁ hy₂
  have hLI : LinearIndependent Z.Ω ℓ := (hℓ ⟨_, h₂⟩ trivial hU₂).1
  obtain ⟨htmem, hstab, hρst⟩ := GlobalTheory.T.hodge_lattice_stable_under_action E Z.Ω Z.V Z.ρ 𝓗.ρH _ _ _ ℓ t (𝓗.HL ⟨_, h₁⟩) 𝓗.act_fst hHy
  have hmemC : ∀ r : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩, (j.comp ψ) ⟨r, hle r.2⟩ ∈ (algebraMap (OCp p) ℂ_[p]).range := by
    intro r
    obtain ⟨x, hx⟩ := hVr r (hle r.2) r.2
    rw [hnorm, RingHom.comp_apply, ← hx]
    exact (hj _).2 ⟨x, rfl⟩
  have hmemK : ∀ r : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩, ψ ⟨r, hle r.2⟩ ∈ (algebraMap V K).range :=
    fun r => hVr r (hle r.2) r.2
  obtain ⟨ρC, ρHC, ev, HV, hC1, hC2, hTC, hEC, hHV1, hHV2, hFC⟩ :=
    GlobalTheory.T.hodge_lattice_extend_scalars E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar _ _ hle _ _ ℓ t (𝓗.HL ⟨_, h₂⟩) (𝓗.HL ⟨_, h₁⟩) ℂ_[p] (OCp p) (j.comp ψ)
      𝓗.act_fst 𝓗.act_inr hLI hℓs hHx hHy hmemC
  obtain ⟨ρK, -, -, -, -, -, hTK, -, -, -, -⟩ :=
    (GlobalTheory.T.hodge_lattice_extend_scalars E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar _ _ hle _ _ ℓ t (𝓗.HL ⟨_, h₂⟩) (𝓗.HL ⟨_, h₁⟩) K V ψ
      𝓗.act_fst 𝓗.act_inr hLI hℓs hHx hHy hmemK)

  haveI : IsLocalRing (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) := GlobalTheory.T.generic_point_component_local_ring _ _ _ Z.gen _
  have hcarry : ∀ (τ₀ : E →+* ℂ) (e : E), ∃ h : Z.inc.comp (inE c τ₀) e ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩,
      ψ ⟨_, h⟩ = βK.comp (inE c τ₀) e := fun τ₀ e => hinc _
  have hcarryC : ∀ (τ₀ : E →+* ℂ) (e : E), ∃ h : Z.inc.comp (inE c τ₀) e ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩,
      (j.comp ψ) ⟨_, h⟩ = κ.comp (inE c τ₀) e := fun τ₀ e => by
    obtain ⟨h, e'⟩ := hinc (inE c τ₀ e)
    refine ⟨h, ?_⟩
    have e'' : ψ ⟨(Z.inc.comp (inE c τ₀)) e, h⟩ = βK (inE c τ₀ e) := e'
    rw [RingHom.comp_apply, e'', ← hκ]
    rfl
  have hregF : ∀ (τ₀ : E →+* ℂ) (e : E), Z.inc.comp (inE c τ₀) e ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ :=
    fun τ₀ e => (hcarry τ₀ e).1
  subst hσE
  have hws' : Submodule.span Z.Ω (Set.range w) = HT.eigSp Z.ρ (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ))) := by
    rw [hws]; exact eig_eq E Z.Ω Z.V Z.ρ _ _ (fun a => rfl)
  have hrk : Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c τ))) = D.p := by
    rw [← hvs, finrank_span_eq_card hv]; simp
  have hrk' : Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ)))) = D.q := by
    rw [← hws', finrank_span_eq_card hw]; simp
  obtain ⟨b₁, b₂, u', A', hb₁, hs₁, hb₂, hs₂, had', hu'm, hA', hfA⟩ :=
    GlobalTheory.T.hodge_lattice_eigen_decomposition_local E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar _ _ D.p D.q ℓ t (𝓗.HL ⟨_, h₁⟩) (Z.inc.comp (inE c τ))
      (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ))) 𝓗.act_fst 𝓗.act_inr
      (fun a => by simp only [RingHom.comp_apply, hbarF]) hinv (hregF τ) (hregF _) hLI hℓs hHy hrk hrk'
  have hcoord : ∀ {n : ℕ} (b : Fin n → Z.V) (W' : Submodule _ Z.V), W' ≤ Submodule.span (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) (Set.range ℓ) →
      (∀ i, b i ∈ W') → ∃ x : Fin n → Fin _ → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ∀ i, b i = comb ℓ (x i) := by
    intro n b W' hW hb
    choose x hx using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (hW (hb i))
    exact ⟨x, fun i => (hx i).symm⟩
  have hin₁ : ∀ i, b₁ i ∈ HT.eigSub Z.ρ (Z.inc.comp (inE c τ)) (Submodule.span (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) (Set.range ℓ)) :=
    fun i => hs₁ ▸ Submodule.subset_span ⟨i, rfl⟩
  have hin₂ : ∀ i, b₂ i ∈ HT.eigSub Z.ρ (Z.inc.comp (inE c (ComplexEmbedding.conjugate τ))) (Submodule.span (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) (Set.range ℓ)) :=
    fun i => hs₂ ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨x₁, hx₁⟩ := hcoord b₁ _ inf_le_left hin₁
  obtain ⟨x₂, hx₂⟩ := hcoord b₂ _ inf_le_left hin₂
  obtain ⟨hK₁, hK₁s⟩ := GlobalTheory.T.reduce_lattice_coords_to_residue E Z.Ω Z.V K Z.ρ _ _ _ ℓ ψ ρK _ (βK.comp (inE c τ)) b₁ x₁ hLI hℓs hρst hTK
    (hcarry τ) hx₁ hb₁ hs₁ hrk
  obtain ⟨hK₂, hK₂s⟩ := GlobalTheory.T.reduce_lattice_coords_to_residue E Z.Ω Z.V K Z.ρ _ _ _ ℓ ψ ρK _ (βK.comp (inE c (ComplexEmbedding.conjugate τ))) b₂ x₂ hLI hℓs hρst hTK
    (hcarry _) hx₂ hb₂ hs₂ hrk'
  obtain ⟨MU, MY, hSV, hVal, hAU, hAY⟩ := GlobalTheory.T.component_specialization_lattice_basis E H D l Xo c O β Y U Z K y h₁ ψ _ ℓ ρK hval
    (hℓ ⟨_, h₁⟩ trivial hy₂) hTK

  have hfrK : ∀ {n : ℕ} (σ₀ : E →+* K) (σi : 𝓞 E →+* K) (bK : Fin n → Fin _ → K), (∀ a : 𝓞 E, σi a = σ₀ (a : E)) →
      LinearIndependent K bK → Submodule.span K (Set.range bK) = HT.eigSp ρK σ₀ →
      IsEigFrame Xo.univ.t.act (under y) σi (fun i => MU.pt (bK i)) := by
    intro n σ₀ σi bK hi h1 h2
    rw [GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ _ _ _ _ MU _ _ ρK σi n bK hAU, eig_eq E K _ ρK σi σ₀ hi]
    exact (GlobalTheory.T.basis_of_submodule_iff_unique_coords K _ _ n bK).1 ⟨h1, h2⟩
  have hFy : IsFramed U τ βK y (fun i => MU.pt (fun k => ψ (x₁ i k))) (fun i => MU.pt (fun k => ψ (x₂ i k))) :=
    ⟨hF.1, hF.2.1, hfrK (βK.comp (inE c τ)) _ _ (fun a => rfl) hK₁ hK₁s,
      hfrK (βK.comp (inE c (ComplexEmbedding.conjugate τ))) _ _ (fun a => rfl) hK₂ hK₂s⟩
  choose vK hvK using fun i => MU.onto (vv i) (hF.2.2.1.1 i).1
  choose wK hwK using fun i => MU.onto (ww i) (hF.2.2.2.1 i).1
  obtain rfl : vv = fun i => MU.pt (vK i) := funext fun i => (hvK i).symm
  obtain rfl : ww = fun i => MU.pt (wK i) := funext fun i => (hwK i).symm
  have hbasK : ∀ {n : ℕ} (σ₀ : E →+* K) (σi : 𝓞 E →+* K) (bK : Fin n → Fin _ → K), (∀ a : 𝓞 E, σi a = σ₀ (a : E)) →
      IsEigFrame Xo.univ.t.act (under y) σi (fun i => MU.pt (bK i)) →
      LinearIndependent K bK ∧ Submodule.span K (Set.range bK) = HT.eigSp ρK σ₀ := by
    intro n σ₀ σi bK hi h
    rw [GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ _ _ _ _ MU _ _ ρK σi n bK hAU, eig_eq E K _ ρK σi σ₀ hi] at h
    exact (GlobalTheory.T.basis_of_submodule_iff_unique_coords K _ _ n bK).2 h
  obtain ⟨hvLI, hvsp⟩ := hbasK (βK.comp (inE c τ)) _ vK (fun a => rfl) hF.2.2.1
  obtain ⟨hwLI, hwsp⟩ := hbasK (βK.comp (inE c (ComplexEmbedding.conjugate τ))) _ wK (fun a => rfl) hF.2.2.2
  have hfr₁ := hℓ ⟨_, h₁⟩ trivial hy₂
  have hfr₂ := hℓ ⟨_, h₂⟩ trivial hU₂
  have hvV := GlobalTheory.T.dvr_specialization_eigen_frame E H D l Xo c O β Y U Z V K y z h₁ h₂ ψ _ ℓ ρK MU MY T tK m m' _ (βK.comp (inE c τ)) _ vK
    hz hle hVr hfr₂ hfr₁ hSV hVal hAU (fun a => rfl) hIv hvLI
  have hwV := GlobalTheory.T.dvr_specialization_eigen_frame E H D l Xo c O β Y U Z V K y z h₁ h₂ ψ _ ℓ ρK MU MY T tK m m' _
    (βK.comp (inE c (ComplexEmbedding.conjugate τ))) _ wK hz hle hVr hfr₂ hfr₁ hSV hVal hAU (fun a => rfl) hIw hwLI
  have hjmap := GlobalTheory.T.tied_action_compose_residue_map E Z.Ω Z.V K ℂ_[p] Z.ρ _ _ ℓ ψ j ρK ρC hρst hTK hTC
  have hjV : ∀ a : K, a ∈ (algebraMap V K).range → j a ∈ (algebraMap (OCp p) ℂ_[p]).range := fun a ha =>
    (hnorm _).2 ((hj a).2 ha)
  obtain ⟨hvC, hvCs, hvCA⟩ := GlobalTheory.T.fraction_field_eigen_basis_descends E K ℂ_[p] V (OCp p) j _ _ ρK ρC (βK.comp (inE c τ)) vK hjV hjmap hvLI hvV
  obtain ⟨hwC, hwCs, hwCA⟩ := GlobalTheory.T.fraction_field_eigen_basis_descends E K ℂ_[p] V (OCp p) j _ _ ρK ρC (βK.comp (inE c (ComplexEmbedding.conjugate τ))) wK hjV hjmap hwLI hwV
  have hjσ : ∀ τ₀ : E →+* ℂ, j.comp (βK.comp (inE c τ₀)) = κ.comp (inE c τ₀) := fun τ₀ => by
    rw [← RingHom.comp_assoc, hκ]
  rw [hjσ] at hvCs hvCA hwCs hwCA
  choose PK hPK using fun i => (Submodule.mem_span_range_iff_exists_fun K).1
    (show vK i ∈ Submodule.span K (Set.range fun i k => ψ (x₁ i k)) by
      rw [hK₁s, ← hvsp]; exact Submodule.subset_span ⟨i, rfl⟩)
  choose QK hQK using fun i => (Submodule.mem_span_range_iff_exists_fun K).1
    (show wK i ∈ Submodule.span K (Set.range fun i k => ψ (x₂ i k)) by
      rw [hK₂s, ← hwsp]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hchg := hφ.chg K βK y _ _ _ _ (Matrix.of PK) (Matrix.of QK) hFy hF
    (fun i => (GlobalTheory.T.is_comb_tangent_iff_linear_sum _ _ _ _ _ MU _ _ _ _).2 (hPK i).symm)
    (fun i => (GlobalTheory.T.is_comb_tangent_iff_linear_sum _ _ _ _ _ MU _ _ _ _).2 (hQK i).symm)

  have hsp₁ : ∀ i, b₁ i ∈ Submodule.span Z.Ω (Set.range v) := fun i => hvs ▸ (hin₁ i).2
  have hsp₂ : ∀ i, b₂ i ∈ Submodule.span Z.Ω (Set.range w) := fun i => hws' ▸ (hin₂ i).2
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun Z.Ω).1 (hsp₁ i)
  choose Q hQ using fun i => (Submodule.mem_span_range_iff_exists_fun Z.Ω).1 (hsp₂ i)
  have hPb : b₁ = fun i => ∑ k, Matrix.of P i k • v k := funext fun i => (hP i).symm
  have hQb : b₂ = fun i => ∑ k, Matrix.of Q i k • w k := funext fun i => (hQ i).symm
  have hP0 : (Matrix.of P).det ≠ 0 := HodgeDeterminantLattice.det_ne_zero (u := v) (by rw [← hPb]; exact hb₁)
  have hQ0 : (Matrix.of Q).det ≠ 0 := HodgeDeterminantLattice.det_ne_zero (u := w) (by rw [← hQb]; exact hb₂)
  obtain ⟨u₀, hu₀, hu₀s⟩ := 𝓗.exists_basis_eigSp (Z.inc.comp (inE c τ))
  have hdim : Module.finrank Z.Ω (HT.eigSp 𝓗.ρH (Z.inc.comp (inE c τ))) = D.p + D.q := by
    rw [← hu₀s, finrank_span_eq_card hu₀]; simp
  obtain ⟨huLI, huS⟩ := GlobalTheory.T.adapted_basis_spans_eigenspace E Z.Ω Z.V 𝓗.ρH _ D.p D.q v w u had hv hdim inferInstance
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.T.adapted_bases_change_by_block_matrices E Z.Ω Z.V 𝓗.ρH _ D.p D.q v b₁ w b₂ u u' (Matrix.of P) (Matrix.of Q) had had' hv huS
    (fun i => (hP i).symm) (fun i => (hQ i).symm)
  set A'Ω : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Z.Ω := (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩).subtype.mapMatrix A' with hA'Ω
  have hdetA' : A'Ω.det = ((A'.det : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) := by
    rw [hA'Ω, ← RingHom.map_det]; rfl
  have hfu : (fun i => ∑ k, (A'Ω * B) i k • u k) = fun i => HT.eigProj 𝓗.ρH (Z.inc.comp (inE c τ)) (t i) := by
    funext i
    rw [hfA i, ← HodgeDeterminantLattice.sum_smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB k]
    rfl
  have hσx : ∀ a : 𝓞 E, (Z.inc.comp (inE c τ)) (a : E) ∈ (algebraMap (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩) Z.Ω).range := fun a =>
    ⟨⟨_, GlobalTheory.T.cm_integers_regular_at_component E H D l Xo c O β Y U Z τ _ hσ ⟨_, h₂⟩ a⟩, rfl⟩
  have hframe : (𝓗.quot (Z.inc.comp (inE c τ))).IsFrameAt (fun i => ∑ k, (A'Ω * B) i k • u k) ⟨_, h₂⟩ := by
    rw [hfu]
    exact ⟨HodgeDeterminantLattice.linearIndependent_eigProj _ (ht ⟨_, h₂⟩ hU₁), HodgeDeterminantLattice.eigQuot_eq_span _ (ht ⟨_, h₂⟩ hU₁) hσx⟩
  have hgen := HodgeDeterminantLattice.detLat_of_frame huLI hframe
  have hVy := hrep K βK y _ _ b₁ b₂ (α / (Matrix.of P).det) (κ' / (Matrix.of Q).det) hFy
    (by rw [hPb, GlobalTheory.T.iota_multi_linear_combination_det, smul_smul, div_mul_cancel₀ _ hP0]) (by rw [hQb, GlobalTheory.T.iota_multi_linear_combination_det, smul_smul, div_mul_cancel₀ _ hQ0])
    (fun i => ⟨_, by rw [hx₁ i]; exact hVal (x₁ i), hSV _⟩) (fun i => ⟨_, by rw [hx₂ i]; exact hVal (x₂ i), hSV _⟩)
  obtain ⟨hd, hd'⟩ := hval' _ _ hVy
  obtain ⟨ud, hud⟩ := hA'
  set dR : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ := ⟨_, hd⟩ * ((ud⁻¹ : (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)ˣ) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) with hdR
  have hud0 : ((ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) ≠ 0 := fun h0 =>
    ud.ne_zero (Subtype.ext h0)
  have hdv : (α / κ') / (A'Ω * B).det = (dR : Z.Ω) := by
    have hinvc : (((ud⁻¹ : (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)ˣ) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) =
        ((ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have h2 : (((((ud⁻¹ : (regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)ˣ) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) * (ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩)) : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω) = 1 := by
        rw [ud.inv_mul]; rfl
      exact h2
    have hBd : B.det = (Matrix.of P).det / (Matrix.of Q).det := eq_div_of_mul_eq hQ0 hBdet
    have hdRc : (dR : Z.Ω) = (α / (Matrix.of P).det) / (κ' / (Matrix.of Q).det) * ((ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) : Z.Ω)⁻¹ := by
      rw [hdR, ← hinvc]; rfl
    rw [Matrix.det_mul, hdetA', ← hud, hBd, hdRc]
    field_simp
  have hβ0 : βK (β ϖ) ≠ 0 := by
    rw [Ne, map_eq_zero, map_eq_zero_iff β hinj]
    exact hϖ.ne_zero
  obtain ⟨hϖr, hϖv⟩ := hinc (β ϖ)
  have hValϖ := hval ⟨_, hϖr⟩
  rw [hϖv] at hValϖ
  have hValϖ' := hval dR
  rw [← hdv] at hValϖ'
  obtain ⟨uV, huV⟩ := GlobalTheory.T.order_valuation_compare Y.X Z.Ω (Z.ξ₀ ≫ Y.j) _ (α / κ') (Z.inc (β ϖ)) M a V K z h₂ (A'Ω * B).det (ψ dR) (βK (β ϖ))
    Z.gen (hord _) hgen (by rw [hz]; exact hValϖ') (by rw [hz]; exact hValϖ) hβ0

  have hmemu : ∀ i, u' i ∈ 𝓗.HL ⟨_, h₁⟩ := hu'm
  have hσtieC := hcarryC τ
  have hadC := GlobalTheory.T.specialize_hodge_lattice_eigenbasis E Z.Ω Z.V ℂ_[p] _ _ D.p D.q ℓ (j.comp ψ) 𝓗.ρH ρHC (𝓗.HL ⟨_, h₁⟩) ev _ (κ.comp (inE c τ)) b₁ b₂ u' x₁ x₂ hu'm
    hEC hσtieC hstab had' hx₁ hx₂
  have hep : ∀ i, HT.eigProj 𝓗.ρH (Z.inc.comp (inE c τ)) (t i) ∈ 𝓗.HL ⟨_, h₁⟩ := fun i => by
    rw [hfA i]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ (A' i k) (hu'm k)
  have hfC : ∀ i, HT.eigProj ρHC (κ.comp (inE c τ)) (ev ⟨t i, htmem i⟩) =
      ∑ k, ((j.comp ψ).mapMatrix A') i k • ev ⟨u' k, hu'm k⟩ := by
    intro i
    rw [← GlobalTheory.T.hodge_lattice_eval_eigProj_comm E Z.Ω Z.V ℂ_[p] _ _ ℓ (j.comp ψ) 𝓗.ρH ρHC (𝓗.HL ⟨_, h₁⟩) ev _ (κ.comp (inE c τ)) ⟨t i, htmem i⟩ (hep i) hEC hσtieC hstab]
    have : (⟨_, hep i⟩ : 𝓗.HL ⟨_, h₁⟩) = ∑ k, A' i k • (⟨u' k, hu'm k⟩ : 𝓗.HL ⟨_, h₁⟩) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      exact hfA i
    rw [this, map_sum]
    exact Finset.sum_congr rfl fun k _ => (ev.map_smulₛₗ _ _)
  have hrkC : ∀ s, Module.finrank ℂ_[p] (HT.eigSp ρC s) = Module.finrank Z.Ω (HT.eigSp Z.ρ (Z.inc.comp (inE c (f s)))) := by
    intro s
    refine GlobalTheory.T.finrank_eigSp_eq_of_lattice_specialization E Z.Ω Z.V ℂ_[p] Z.ρ _ _ ℓ (j.comp ψ) ρC _ s hLI hℓs hρst hTC ?_
    intro e
    obtain ⟨h, e'⟩ := hcarryC (f s) e
    exact ⟨h, e'.trans (by rw [← hf s])⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.T.residue_hodge_lattice_adapted_basis E ℂ_[p] (OCp p) H.bar (κ.comp (inE c τ)) (κ.comp (inE c (ComplexEmbedding.conjugate τ))) _ D.p D.q
    ρC ρHC HV (fun i => ev ⟨t i, htmem i⟩) (fun i k => (j.comp ψ) (x₁ i k)) (fun i k => j (vK i k))
    (fun i k => (j.comp ψ) (x₂ i k)) (fun i k => j (wK i k)) (fun i => ev ⟨u' i, hu'm i⟩) ((j.comp ψ).mapMatrix A')
    (j.mapMatrix (Matrix.of PK)) (j.mapMatrix (Matrix.of QK)) gm hC1 hC2
    (fun a => by simp only [RingHom.comp_apply, hbarF]) hinv (hint _) (hFC htmem) hadC
    (fun i => by
      funext k
      have := congrFun (hPK i) k
      rw [← this]
      simp [Finset.sum_apply, map_sum])
    (fun i => by
      funext k
      have := congrFun (hQK i) k
      rw [← this]
      simp [Finset.sum_apply, map_sum])
    (GlobalTheory.T.reduce_lattice_coords_to_residue E Z.Ω Z.V ℂ_[p] Z.ρ _ _ _ ℓ (j.comp ψ) ρC _ (κ.comp (inE c τ)) b₁ x₁ hLI hℓs hρst hTC (hcarryC τ) hx₁ hb₁ hs₁ hrk).1 hfC
    (fun v' w' u'' B' h1 h2 h3 h4 h5 h6 h7 => hgm (Fin _ → ℂ_[p]) ρC ρHC HV (stdLat (OCp p) ℂ_[p] _) (fun i => ev ⟨t i, htmem i⟩) v' w' u'' B'
      hC1 hC2 hHV1 hHV2 (hFC htmem) hrkC h1 h2 h3 h4 h5 h6 h7)
    hvC hvCs hvCA hwC hwCs hwCA

  have hPd : (Matrix.of PK).det ≠ 0 := HodgeDeterminantLattice.det_ne_zero (u := fun i k => ψ (x₁ i k)) (by
    have : (fun i => ∑ k, Matrix.of PK i k • (fun k' => ψ (x₁ k k'))) = vK := funext hPK
    rw [this]; exact hvLI)
  have hφ0 := hφ.ne K βK y _ _ hF
  have hψd : ψ dR * ψ (ud : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩) = φ K y (fun i => MU.pt (fun k => ψ (x₁ i k))) (fun i => MU.pt (fun k => ψ (x₂ i k))) := by
    rw [← map_mul, hdR, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact hd'
  rw [← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, ← hud, RingHom.comp_apply] at hε
  have hjφ : j (φ K y (fun i => MU.pt (vK i)) (fun i => MU.pt (wK i))) =
      j (ψ dR) * (algebraMap (OCp p) ℂ_[p] ε * gm) := by
    apply mul_right_cancel₀ ((map_ne_zero j).2 hPd)
    rw [← map_mul, hchg, ← hψd, map_mul, map_mul, _root_.mul_assoc, hε]
    ring
  have hjφ0 : j (φ K y (fun i => MU.pt (vK i)) (fun i => MU.pt (wK i))) ≠ 0 := (map_ne_zero j).2 hφ0
  have hx0 : j (ψ dR) ≠ 0 := fun h0 => hjφ0 (by rw [hjφ, h0, zero_mul])
  have hκπ : j (βK (β ϖ)) = κ (β ϖ) := by rw [← hκ]; rfl
  have hκ0 : κ (β ϖ) ≠ 0 := by rw [← hκπ]; exact (map_ne_zero j).2 hβ0
  have hmu : ‖j (algebraMap V K uV)‖ = 1 := norm_eq_one_of _ (j (algebraMap V K (uV⁻¹ : Vˣ))) ((hj _).2 ⟨_, rfl⟩) ((hj _).2 ⟨_, rfl⟩)
    (by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one])
  have hlog := log_end M a (j (ψ dR)) (κ (β ϖ)) (j (algebraMap V K uV)) hM hx0 hκ0 hmu (by
    rw [← hκπ, ← map_pow, huV, map_mul, map_zpow₀])
  have hε1 : ‖algebraMap (OCp p) ℂ_[p] ε‖ = 1 := norm_eq_one_of _ (algebraMap (OCp p) ℂ_[p] (ε⁻¹ : (OCp p)ˣ)) ((hnorm _).1 ⟨_, rfl⟩) ((hnorm _).1 ⟨_, rfl⟩)
    (by rw [← map_mul, Units.mul_inv, map_one])
  rw [hjφ, norm_mul, norm_mul, hε1, _root_.one_mul, Real.log_mul (norm_ne_zero_iff.2 hx0) (norm_ne_zero_iff.2 hgm0), hlog]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
