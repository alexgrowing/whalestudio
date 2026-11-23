import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegralChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegEqSumLineHeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFlagRankSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIdealFgNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTangentBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeFlagPointLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationEigenframePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointLocalHeightPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaExtensionEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSupNormLocalRescaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBelowPointDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramGradedSquareOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIdealNormSuccessiveMinimumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFormulaFractionalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUltrametricNormStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.LieMet

namespace GlobalTheory.LieSmooth

section Glue

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem full_lieCoordLat {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] [NumberField K]
    {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G)
    (hb : TanBasis t b) : Full (lieCoordLat t hx b) := by
  obtain ⟨m, r, M, hr, hM, hL, -⟩ := GlobalTheory.T.tangent_basis_integral_change t hx b hb
  exact GlobalTheory.CM.LieLattice.fg_and_span_eq_top _ r M hr (fun i => (hM i).2) hL

theorem grNorm_eq {X : Scheme.{0}} [X.IsSeparated] (t : SAB H X) {K : Type} [Field K] [NumberField K]
    {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G)
    (hb : TanBasis t b) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {xC : Sp C ⟶ X}
    (hC : spMap j ≫ xK = xC) {r : ℕ} (s : Fin r → Fin n) (hs : Function.Injective s)
    (u : Fin r → (Sp (DualNumber C) ⟶ t.G.left)) (hu : ∀ k, u k = spMap (dualMap j) ≫ (tv (b (s k))).left) (i : Fin r) :
    0 < (⨆ a : grIdeal (lieCoordLat t hx b) (fun k => Pi.single (s k) (1 : K)) i, ‖j a‖) ∧
      grNorm t xC (latDR t xC) u i = (⨆ a : grIdeal (lieCoordLat t hx b) (fun k => Pi.single (s k) (1 : K)) i, ‖j a‖)⁻¹ := by
  have hv : LinearIndependent K (fun k => (Pi.single (s k) (1 : K) : Fin n → K)) := by
    simpa [Function.comp_def] using (Pi.basisFun K (Fin n)).linearIndependent.comp s hs
  obtain ⟨h0, h1⟩ := GlobalTheory.T.graded_ideal_norm_successive_minimum j _ _ i (full_lieCoordLat t hx b hb) hv
  obtain ⟨hi, hl⟩ := GlobalTheory.T.tangent_basis_ultrametric_norm t hx b hb j hC
  refine ⟨h0, ?_⟩
  have hU : u = fun k => (tv (bcTan j hC (b (s k)))).left := funext fun k => by rw [hu, left_bcTan]
  have e (d : Fin r → C) : ∑ k, d k • bcTan j hC (b (s k)) =
      ∑ m, (∑ k, d k • fun m => j ((Pi.single (s k) (1 : K) : Fin n → K) m)) m • bcTan j hC (b m) := by
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.sum_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single (s k) (fun m _ hm => by simp [hm]) (by simp)]
    simp
  have key (d : Fin r → C) : (∃ w ∈ latDR t xC, IsCombAtG t xC u d w) ↔
      (∑ k, d k • fun m => j ((Pi.single (s k) (1 : K) : Fin n → K) m)) ∈ latC j (lieCoordLat t hx b) := by
    rw [hU]
    constructor
    · rintro ⟨w, hw, hc⟩
      obtain ⟨d', hd', rfl⟩ := (hl w).1 hw
      have := (LieMet.isComb_iff _ _ _).1 hc
      rw [e] at this
      rwa [← Fintype.linearIndependent_iffₛ.1 hi _ _ this |> funext]
    · intro hd
      exact ⟨_, (hl _).2 ⟨_, hd, rfl⟩, (LieMet.isComb_iff _ _ _).2 (e d).symm⟩
  rw [← h1, grNorm]
  simp only [key]

end Glue

section Core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem ht_core (G : ∀ σ : F →+* ℂ, EigMet Z (embOf e σ)) {K : Type} [Field K] [NumberField K] (φ : F →+* K)
    (p : Sp K ⟶ Y.Y.X) (hp : p ≫ Y.Y.str = spMap φ) {fK : c.F →+* K} {xK : Sp K ⟶ Z.X} (g : EigFrame Z fK xK)
    (hc : Y.Carries p g) (hφ : fK = φ.comp e.symm.toRingHom) (hx : xK = p ≫ Y.π ≫ genι Z) (w : Sym E →₀ ℤ)
    (hw : ∀ s ∈ w.support, s.1 = fun _ => false) (𝔞 : ((E →+* ℂ) × ℕ) ⊕ ℕ → Submodule (𝓞 K) K)
    (h𝔞 : ∀ s ∈ w.support, (𝔞 s.2.2).FG ∧ 𝔞 s.2.2 ≠ ⊥)
    (hfin : ∀ s ∈ w.support, ∀ (q : ℕ) [Fact q.Prime] (j : K →+* ℂ_[q]) (xC : Sp ℂ_[q] ⟶ Z.X)
      (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[q]) ⟶ Z.t.G.left)), spMap j ≫ xK = xC →
      (∀ τ i, u τ i = spMap (dualMap j) ≫ g.v τ i) →
      0 < (⨆ a : 𝔞 s.2.2, ‖j a‖) ∧ stepNorm Z.t xC u s.2.2 = (⨆ a : 𝔞 s.2.2, ‖j a‖)⁻¹)
    (q : (K →+* ℂ) → Letter Dw → ℝ)
    (hq : ∀ (σ : K →+* ℂ) (g' : Y.FrameAt (σ := σ.comp φ) (cxPtOf p hp σ)), g.IsMap σ g' →
      ∀ z : Letter Dw, grSq ((G _).gram _ g' z.1) z.2 = q σ z) :
    (adlOf Y (C := cxSt F) (fun _ σ n => Y.met (G σ) n) w).ht (below p) =
      ((w.sum fun s n => (n : ℝ) * idealLog (𝔞 s.2.2)) -
        (1 / 2) * ∑ σ : K →+* ℂ, ∑ z : Letter Dw, (expo Dw w z : ℝ) * Real.log (q σ z)) / Module.finrank ℚ K := by
  obtain ⟨a, ha, hco⟩ := GlobalTheory.T.flag_compactification_eigenframe_point Y p g (expo Dw w) hc
  rw [GlobalTheory.T.height_below_point_decomposition _ φ p hp]
  have hinf (σ : K →+* ℂ) : Real.log ((cxSt F).pn Y.Y (σ.comp φ) (divOf Y (expo Dw w)) (Y.met (G _) (expo Dw w))
      ((cxSt F).cx Y.Y _ ((eqn (divOf Y (expo Dw w)) (below p))⁻¹ : Y.Y.Fnˣ)) (cxPtOf p hp σ)) / 2 =
      Real.log ‖σ a‖ + (1 / 2) * ∑ z : Letter Dw, (expo Dw w z : ℝ) * Real.log (q σ z) := by
    have h1 : embOf e (σ.comp φ) = σ.comp fK := by rw [hφ]; rfl
    have h2 : (Y.down (σ := σ.comp φ) (cxPtOf p hp σ)).1 ≫ genι Z = spMap σ ≫ xK := by
      rw [hx]; simp [FlagCpt.down, cxPtOf]
    obtain ⟨g', hg'⟩ := g.exists_isMap σ h1 h2
    have h3 := FlagCpt.pn_met (G (σ.comp φ)) (expo Dw w) (p := cxPtOf p hp σ) (g := g')
      (GlobalTheory.T.flag_compactification_base_change Y σ p g g' _ _ a h1 h2 hg' hco)
    refine (congrArg (Real.log · / 2) h3).trans ?_
    have h4 : ‖σ a‖ ≠ 0 := by simpa using ha
    rw [Real.log_mul (pow_ne_zero _ h4) (Y.genSq_pos _ _ _).ne', Real.log_pow, FlagCpt.genSq,
      Real.log_prod (fun w _ => (zpow_pos (grSq_pos ((G _).pos _ _ _) _) _).ne')]
    simp only [Real.log_zpow, hq σ g' hg']
    push_cast
    ring
  have hloc (v : HeightOneSpectrum (𝓞 F)) (θ : EmbOver φ) : lgOf Y w v (extOf v) (algPtOf p hp θ) =
      Real.log ((extOf v).w (θ.1 a)) -
        ∑ s ∈ w.support, (w s : ℝ) * Real.log (⨆ a : 𝔞 s.2.2, (extOf v).w (θ.1 a)) := by
    haveI := Fact.mk (residueCharacteristic_prime v)
    obtain ⟨g', hg'⟩ := g.exists_isMap θ.1 (φ' := θ.1.comp fK) (x' := spMap θ.1 ≫ xK) rfl rfl
    have h1 := fun s hs => hfin s hs (resP v) ((ioOf (resP v) (extOf v)).comp θ.1)
      (spMap (ioOf (resP v) (extOf v)) ≫ spMap θ.1 ≫ xK) (fun τ i => spMap (dualMap (ioOf (resP v) (extOf v))) ≫ g'.v τ i)
      (by rw [← Category.assoc, ← Spec.map_comp]; rfl) (fun τ i => by simp only [hg' τ i, GlobalTheory.GradedPieces.dual_comp])
    have h2 : below (algPtOf p hp θ).1 = below p := by
      change p (spMap θ.1 _) = p _
      congr 1
      exact Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [GlobalTheory.T.flag_point_local_height_prime Y w v (extOf v) (algPtOf p hp θ) g' (θ.1 a) (fun s hs => by rw [hw s hs])
      (fun s hs => by rw [(h1 s hs).2]; exact (inv_pos.2 (h1 s hs).1).ne')
      (by rw [h2]; exact GlobalTheory.T.flag_compactification_base_change Y θ.1 p g g' _ _ a rfl rfl hg' hco), Finsupp.sum, Finset.mul_sum, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun s hs => ?_)
    rw [(h1 s hs).2, Real.log_inv, ← GlobalTheory.T.ideal_sup_norm_local_rescale v (extOf v) θ.1 _ (h𝔞 s hs).1 (h𝔞 s hs).2]
    ring
  have hfinsum : ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, lgOf Y w v (extOf v) (algPtOf p hp θ) =
      -(∑ σ : K →+* ℂ, Real.log ‖σ a‖) - w.sum fun s n => (n : ℝ) * idealLog (𝔞 s.2.2) := by
    simp only [hloc, Finset.sum_sub_distrib]
    have h1 := fun s hs => GlobalTheory.T.product_formula_fractional_ideal φ _ (h𝔞 s hs).1 (h𝔞 s hs).2
    have h2 (v : HeightOneSpectrum (𝓞 F)) : ∑ θ : EmbOver φ, ∑ s ∈ w.support,
        (w s : ℝ) * Real.log (⨆ a : 𝔞 s.2.2, (extOf v).w (θ.1 a)) =
        ∑ s ∈ w.support, (w s : ℝ) * ∑ θ : EmbOver φ, Real.log (⨆ a : 𝔞 s.2.2, (extOf v).w (θ.1 a)) := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    have h3 : ∀ s ∈ w.support, (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        (w s : ℝ) * ∑ θ : EmbOver φ, Real.log (⨆ a : 𝔞 s.2.2, (extOf v).w (θ.1 a))).Finite :=
      fun s hs => (h1 s hs).1.subset (Function.support_mul_subset_right _ _)
    simp only [h2]
    rw [finsum_sub_distrib (GlobalTheory.T.product_formula_extension_embeddings φ a ha).1 ((w.support.finite_toSet.biUnion h3).subset
      (Finset.support_sum _ _)), (GlobalTheory.T.product_formula_extension_embeddings φ a ha).2, finsum_sum_comm _ _ h3, Finsupp.sum]
    refine congrArg _ (Finset.sum_congr rfl fun s hs => ?_)
    rw [← mul_finsum' _ _ (h1 s hs).1, (h1 s hs).2]
  change -((∑ σ : K →+* ℂ, (_ - ((1 : ℕ) : ℝ) * 0)) + ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ,
    lgOf Y w v (extOf v) (algPtOf p hp θ)) / (((1 : ℕ) : ℝ) * _) = _
  rw [hfinsum]
  erw [Finset.sum_congr rfl fun σ _ => congrArg (· - ((1 : ℕ) : ℝ) * 0) (hinf σ)]
  simp only [mul_zero, sub_zero, Finset.sum_add_distrib, ← Finset.mul_sum, Nat.cast_one, one_mul]
  ring

end Core

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  (K : Type) [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw)

omit [NumberField K] in

theorem linearIndependent_tauFr (τ : E →+* ℂ) : LinearIndependent K (tauFr K e τ) := by
  have h : tauFr K e τ = Pi.basisFun K (Fin n) ∘ fun j : Fin (Dw.mult τ) => e.symm ⟨τ, j⟩ := by
    funext j; simp [tauFr]
  rw [h]
  exact (Pi.basisFun K (Fin n)).linearIndependent.comp _ (e.symm.injective.comp sigma_mk_injective)

theorem bijective_pos : Function.Bijective fun j => e.symm ((letters Dw).get j) :=
  e.symm.bijective.comp ⟨List.nodup_iff_injective_get.1 (GlobalTheory.Proof.LetterConjugation.nodup_letters Dw), fun x => List.get_of_mem (GlobalTheory.Proof.LetterConjugation.mem_letters Dw x)⟩

omit [NumberField K] in

theorem basis_allFr : LinearIndependent K (allFr K e) ∧ Submodule.span K (Set.range (allFr K e)) = ⊤ := by
  have h : allFr K e = Pi.basisFun K (Fin n) ∘ fun j => e.symm ((letters Dw).get j) := by
    funext j; simp [allFr]
  rw [h, (bijective_pos e).2.range_comp]
  exact ⟨(Pi.basisFun K (Fin n)).linearIndependent.comp _ (bijective_pos e).1, Module.Basis.span_eq _⟩

variable {K} in

theorem bcTan_tauFr {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {fK : c.F →+* K} {xK : Sp K ⟶ Z.X} (g : EigFrame Z fK xK)
    (b : Fin n → TanM xK Z.t.G) (hg : ∀ z : Letter Dw, g.vec z.1 z.2 = b (e.symm z)) {C : Type} [Field C] (σ : K →+* C)
    {σ' : c.F →+* C} {x' : Sp C ⟶ Z.X} (hx : spMap σ ≫ xK = x') (g' : EigFrame Z σ' x') (hg' : g.IsMap σ g')
    (a : Letter Dw) : bcTan σ hx (∑ i, tauFr K e a.1 a.2 i • b i) = g'.vec a.1 a.2 := by
  rw [Finset.sum_eq_single (e.symm a) (fun m _ hm => by simp [tauFr, hm]) (by simp)]
  refine tan_ext ?_
  rw [tauFr, Pi.single_eq_same, one_smul, left_bcTan, ← hg]
  exact (hg' a.1 a.2).symm

variable {K} in

theorem form_tauFr {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z)
    {fK : c.F →+* K} {yK : Sp K ⟶ gen Z} (hov : yK ≫ genStr Z = spMap fK) (g : EigFrame Z fK (yK ≫ genι Z))
    (b : Fin n → TanM (yK ≫ genι Z) Z.t.G) (hg : ∀ z : Letter Dw, g.vec z.1 z.2 = b (e.symm z)) (h : HermFam K (Fin n → K))
    (hh : ∀ (σ : K →+* ℂ) (z : CxPts (genStr Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin n → K),
      h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i))
        (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i))) (σ : K →+* ℂ) :
    (∀ z z' : Letter Dw, z.1 ≠ z'.1 → h.form σ (tauFr K e z.1 z.2) (tauFr K e z'.1 z'.2) = 0) ∧
    ∀ (σ' : c.F →+* ℂ) (z : CxPts (genStr Z) σ') (g' : EigFrame Z σ' (z.1 ≫ genι Z)), σ' = σ.comp fK →
      z.1 = spMap σ ≫ yK → g.IsMap σ g' → ∀ τ, (x.eigMet σ').gram z g' τ = h.gram σ (tauFr K e τ) := by
  have hform (z : CxPts (genStr Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK)
      (g' : EigFrame Z (σ.comp fK) (z.1 ≫ genι Z)) (hg' : g.IsMap σ g') (a a' : Letter Dw) :
      h.form σ (tauFr K e a.1 a.2) (tauFr K e a'.1 a'.2) = x.met _ z (g'.vec a'.1 a'.2) (g'.vec a.1 a.2) := by
    rw [hh σ z hz, bcTan_tauFr e g b hg σ _ g' hg' a', bcTan_tauFr e g b hg σ _ g' hg' a]
  refine ⟨fun z z' hz => ?_, ?_⟩
  · let y : CxPts (genStr Z) (σ.comp fK) := ⟨spMap σ ≫ yK, by rw [Category.assoc, hov, ← Spec.map_comp]; rfl⟩
    obtain ⟨g', hg'⟩ := g.exists_isMap σ (φ' := σ.comp fK) (x' := y.1 ≫ genι Z) rfl (Category.assoc _ _ _)
    exact (hform y rfl g' hg' z z').trans (x.met_vec_eq_zero g' g' hz.symm _ _)
  · rintro _ z g' rfl hz hg' τ
    exact Matrix.ext fun a a' => (hform z hz g' hg' ⟨τ, a⟩ ⟨τ, a'⟩).symm

variable {K} in

theorem stepId_fg {L : Submodule (𝓞 K) (Fin n → K)} (hL : Full L) {s : ((E →+* ℂ) × ℕ) ⊕ ℕ}
    (hs : (letterOf Dw s).isSome) : (stepId e L s).FG ∧ stepId e L s ≠ ⊥ := by
  rcases s with ⟨τ, k⟩ | k
  · have hk : k < Dw.mult τ := by by_contra hk; simp [letterOf, hk] at hs
    simp only [stepId, dif_pos hk]
    exact GlobalTheory.T.graded_ideal_fg_ne_bot K _ _ _ _ _ hL.1 (linearIndependent_tauFr K e τ) (by rw [hL.2]; exact le_top)
  · have hk : k < (letters Dw).length := by simpa [letterOf] using hs
    simp only [stepId, dif_pos hk]
    exact GlobalTheory.T.graded_ideal_fg_ne_bot K _ _ _ _ _ hL.1 (basis_allFr K e).1 (by rw [hL.2]; exact le_top)

variable {K} in

theorem stepNorm_eq {X : Scheme.{0}} [X.IsSeparated] (t : SAB H X)
    {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) (b : Fin n → TanM xK t.G)
    (hb : TanBasis t b) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (j : K →+* C) {xC : Sp C ⟶ X}
    (hC : spMap j ≫ xK = xC) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left))
    (hu : ∀ z : Letter Dw, u z.1 z.2 = spMap (dualMap j) ≫ (tv (b (e.symm z))).left) {s : ((E →+* ℂ) × ℕ) ⊕ ℕ}
    (hs : (letterOf Dw s).isSome) : 0 < (⨆ a : stepId e (lieCoordLat t hx b) s, ‖j a‖) ∧
      stepNorm t xC u s = (⨆ a : stepId e (lieCoordLat t hx b) s, ‖j a‖)⁻¹ := by
  rcases s with ⟨τ, k⟩ | k
  · have hk : k < Dw.mult τ := by by_contra hk; simp [letterOf, hk] at hs
    rw [stepId, stepNorm, dif_pos hk, dif_pos hk]
    exact grNorm_eq t hx b hb j hC (fun i => e.symm ⟨τ, i⟩) (e.symm.injective.comp sigma_mk_injective) (u τ)
      (fun i => hu ⟨τ, i⟩) _
  · have hk : k < (letters Dw).length := by simpa [letterOf] using hs
    rw [stepId, stepNorm, dif_pos hk, dif_pos hk]
    exact grNorm_eq t hx b hb j hC (fun i => e.symm ((letters Dw).get i)) (bijective_pos e).1 _ (fun i => hu _) _

variable {D : D7} (O : Setup D)

theorem ht_lie (y : Pt O.s) (K : Type) [Field K] [NumberField K] (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)) (hL : IsLieAt O y K L h) : Full L ∧
    ∃ e : Fin (D.R.f * O.N) ≃ Letter O.S.Dw,
      (∀ (σ : K →+* ℂ) (z z' : Letter O.S.Dw), z.1 ≠ z'.1 → h.form σ (tauFr K e z.1 z.2) (tauFr K e z'.1 z'.2) = 0) ∧
      ∀ w : Sym D.host.E →₀ ℤ, (∀ s ∈ w.support, (s.1 = fun _ => false) ∧ (letterOf O.S.Dw s.2.2).isSome) →
        (adlOf (O.Φ.C _) (ref0 O _) w).ht (basePt O.Φ y) =
          ((w.sum fun s n => (n : ℝ) * idealLog (stepId e L s.2.2)) - (1 / 2) * ∑ σ : K →+* ℂ, ∑ z : Letter O.S.Dw,
            (expo O.S.Dw w z : ℝ) * Real.log (grSq (h.gram σ (tauFr K e z.1)) z.2)) / Module.finrank ℚ K := by
  obtain ⟨x, P, io, fK, yK, xO, hx, hio, e, b, hc, hov, hb, rfl, hh⟩ := hL
  simp only [left_bcTan] at hb
  obtain ⟨hB, g, hg⟩ := GlobalTheory.T.flag_point_tangent_base_change y io fK yK hio hov e b hb
  have hgv (z : Letter O.S.Dw) : g.v z.1 z.2 = (tv (b (e.symm z))).left := by rw [← hg]; rfl
  obtain ⟨p, hπ, hcar, hbase⟩ := GlobalTheory.T.eigenframe_flag_point_lift O.Φ y io fK yK hio hov g fun τ i => by
    rw [hgv ⟨τ, i⟩, hb, e.apply_symm_apply]; rfl
  have hfull := full_lieCoordLat O.s.T.Z.t hx b hB
  have hform := form_tauFr e x hov g b hg h hh
  refine ⟨hfull, e, fun σ => (hform σ).1, fun w hw => ?_⟩
  haveI := isProper_toroidalModel_structureMap O.s.T.Z
  haveI : O.s.T.Z.X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from O.s.T.Z.s]; infer_instance⟩
  have hp : p ≫ (O.Φ.C (compPt O.s y)).Y.str = spMap (fK.comp O.κ.e.toRingHom) := by
    rw [← (O.Φ.C (compPt O.s y)).π_str, ← Category.assoc, hπ, ← Category.assoc, hov, ← Spec.map_comp]; rfl
  have hφ : fK = (fK.comp O.κ.e.toRingHom).comp O.κ.e.symm.toRingHom := RingHom.ext fun a => by simp
  have h0 : ref0 O (compPt O.s y) = fun _ σ n => (O.Φ.C _).met (x.eigMet (embOf O.κ.e σ)) n := by
    funext _
    exact congrFun hc.h0_eq _
  rw [h0, ← hbase]
  refine ht_core (O.Φ.C _) (fun σ => x.eigMet (embOf O.κ.e σ)) _ p hp g hcar hφ (by rw [← hπ, Category.assoc]) w
    (fun s hs => (hw s hs).1) (stepId e _) (fun s hs => ?_) (fun s hs q _ j xC u hC hu => ?_) _ fun σ g' hg' z => ?_
  · exact stepId_fg e hfull (hw s hs).2
  · exact stepNorm_eq e O.s.T.Z.t hx b hB j hC u (fun z => by rw [hu, hgv]) (hw s hs).2
  · exact congrArg (grSq · z.2) ((hform σ).2 _ _ g' (congrArg σ.comp hφ).symm (by rw [← hπ]; exact Category.assoc _ _ _) hg' z.1)

end Main

section Final

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

open Classical in

theorem sum_expo_single (a : ℕ → Bool) (R : Option ℝ) {s : ((E →+* ℂ) × ℕ) ⊕ ℕ} (m : ℤ) {z : Letter Dw}
    (hz : letterOf Dw s = some z) (f : Letter Dw → ℝ) :
    ∑ x, (expo Dw (Finsupp.single (a, R, s) m) x : ℝ) * f x = m * f z := by
  simp only [expo_single, hz, Option.some.injEq]
  rw [Finset.sum_eq_single z (fun x _ hx => by simp [hx.symm]) (by simp)]
  simp

theorem readsAt_smooth : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∃ C : ℝ, ∀ (y : Pt O.s) (K : Type) [Field K] [NumberField K]
    (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)),
    IsLieAt O y K L h → ReadsAt O (ref0 O) y h L C := by
  intro _ _ D O _ _ _ _ _ _
  refine ⟨0, fun y K _ _ L h hL => ?_⟩
  obtain ⟨hfull, e, horth, hht⟩ := ht_lie O y K L h hL
  have hlen : (letters O.S.Dw).length = D.R.f * O.N := (GlobalTheory.Proof.LetterConjugation.letters_spec D _ _ _ O.S O.κ O.s).1
  have hind : ArIn.ind ∅ = fun _ => false := funext fun q => by simp [ArIn.ind]
  constructor
  · have hk (k : Fin (D.R.f * O.N)) : (k : ℕ) < (letters O.S.Dw).length := k.2.trans_eq hlen.symm
    have hlet (k : Fin (D.R.f * O.N)) : letterOf O.S.Dw (.inr (k : ℕ)) = some ((letters O.S.Dw).get ⟨k, hk k⟩) := by
      simp [letterOf, hk k]
    have hd : detOmSym D.host.E (D.R.f * O.N) = ∑ k : Fin (D.R.f * O.N),
        Finsupp.single ((fun _ => false : ℕ → Bool), (none : Option ℝ), (Sum.inr (k : ℕ) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) (-1) := by
      rw [GlobalTheory.CovolFin.detOmSym_eq, hind, ← Finset.sum_neg_distrib]
      simp only [Finsupp.single_neg]
    rw [omHt, hht _ fun s hs => ?_, GlobalTheory.T.deg_eq_sum_line_heights K _ h L _ _ hfull.1 (basis_allFr K e).1 (hfull.2.trans (basis_allFr K e).2.symm),
      hd, GlobalTheory.CovolFin.expo_sum, ← Finsupp.sum_finset_sum_index (by simp) (by simp [add_mul]),
      ← (finCongr hlen.symm).sum_comp]
    · simp only [Finset.sum_apply, Int.cast_sum, Finset.sum_mul]
      have h1 (σ : K →+* ℂ) := Finset.sum_comm (s := (Finset.univ : Finset (Letter O.S.Dw)))
        (t := (Finset.univ : Finset (Fin (D.R.f * O.N))))
        (f := fun z k => (expo O.S.Dw (Finsupp.single ((fun _ => false : ℕ → Bool), (none : Option ℝ),
          (Sum.inr (k : ℕ) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)) (-1)) z : ℝ) * Real.log (grSq (h.gram σ (tauFr K e z.1)) z.2))
      simp only [h1, sum_expo_single _ _ _ (hlet _), ← GlobalTheory.T.gram_graded_square_orthogonal e h _ (horth _)]
      rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib,
        Finset.sum_eq_zero fun k _ => ?_, abs_zero]
      rw [Finsupp.sum_single_index (by simp), ← Finset.mul_sum]
      simp only [lineHt, stepId, dif_pos (hk k)]
      have : finCongr hlen.symm k = ⟨k, hk k⟩ := rfl
      rw [this]
      push_cast
      ring
    · rw [hd] at hs
      obtain ⟨k, -, hk'⟩ := Finsupp.mem_support_finset_sum _ hs
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hk')]
      exact ⟨rfl, by rw [hlet]; rfl⟩
  · intro τ k hk
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.lattice_flag_rank_saturated K _ h L _ (tauFr K e τ) k hk hfull.1 (linearIndependent_tauFr K e τ)
      (by rw [hfull.2]; exact le_top)
    refine ⟨_, inf_le_left, h1, ?_⟩
    rw [GlobalTheory.T.deg_eq_sum_line_heights K _ h _ _ _ h2 ((linearIndependent_tauFr K e τ).comp _ (Fin.castLE_injective hk)) h3, stepHt,
      Finset.sum_range, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, Finset.sum_eq_zero fun i _ => ?_, abs_zero]
    have hi : (i : ℕ) < O.S.Dw.mult τ := i.2.trans_le hk
    have hlet : letterOf O.S.Dw (.inl (τ, (i : ℕ))) = some ⟨τ, ⟨i, hi⟩⟩ := by simp [letterOf, hi]
    rw [h4, hht _ fun s hs => ?_, Finsupp.sum_single_index (by simp)]
    · simp only [sum_expo_single _ _ _ hlet, lineHt, stepId, dif_pos hi, Int.cast_one, one_mul]
      exact sub_self _
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hs)]
      exact ⟨hind, by rw [hlet]; rfl⟩

end Final

end GlobalTheory.LieSmooth

end
