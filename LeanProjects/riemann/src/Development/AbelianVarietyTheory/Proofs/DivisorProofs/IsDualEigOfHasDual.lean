import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartSectionBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LettersEquivFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatChartTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.ShFam GlobalTheory.VB GlobalTheory.CxPts GlobalTheory.Toroidal Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.Points
open GlobalTheory.LieVB (omega unitSec dUnit)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DRBaseEx

open Matrix GlobalTheory.HermFrame
open GlobalTheory.Twist (resM resM_resM resM_self)
open scoped ComplexOrder ContDiff

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

section Pair

variable {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X}
  {U : Z.X.Opens} {n : ℕ}

def pairMat (u : EigFrame Z φ x) (h : ⊤ ≤ x ⁻¹ᵁ U) (m : Fin n → Γ(omega Z.t.G, U)) (τ : E →+* ℂ) :
    Matrix (Fin (Dw.mult τ)) (Fin n) R := of fun i a => tanEv Z.t (u.tan τ i) h (m a)

theorem pairMat_co (f g : EigFrame Z φ x) (h : ⊤ ≤ x ⁻¹ᵁ U) (m : Fin n → Γ(omega Z.t.G, U)) (τ : E →+* ℂ) :
    pairMat g h m τ = (f.co g τ)ᵀ * pairMat f h m τ := by
  ext i a
  exact tanEv_comb E H Z.X Z.t R x U h _ _ (f.tan τ) _ _ (g.tan τ i) (f.co_spec g τ i) (m a)

theorem pairMat_map {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} {ψ : R →+* R'} (hf : f.IsMap ψ g) (hx : spMap ψ ≫ x = x')
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (m : Fin n → Γ(omega Z.t.G, U)) (τ : E →+* ℂ) :
    pairMat g h' m τ = (pairMat f h m τ).map ψ := by
  ext i a
  have key : ∀ v (hv : IsTanAtG Z.t x' v), v = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i →
      tanEv Z.t hv h' (m a) = ψ (tanEv Z.t (f.tan τ i) h (m a)) := by
    rintro _ hv rfl
    exact TopChart.tanEv_map h (f.tan τ i) ψ hx h' (m a)
  exact key _ _ (hf τ i)

theorem card_eq [Nontrivial R] (u : EigFrame Z φ x) (h : ⊤ ≤ x ⁻¹ᵁ U) {m : Fin n → Γ(omega Z.t.G, U)} (hm : VB.IsFrame m) :
    n = ∑ τ : E →+* ℂ, Dw.mult τ := by
  obtain ⟨Φ, -⟩ := TanPair.exists_tanM_equiv E H Z.X Z.t R x U h n m hm
  simpa using Φ.finrank_eq.symm.trans (Module.finrank_eq_card_basis (eigBasis u))

theorem eq_zero_of_pairMat (u : EigFrame Z φ x) (h : ⊤ ≤ x ⁻¹ᵁ U) {m : Fin n → Γ(omega Z.t.G, U)} (hm : VB.IsFrame m)
    {v : Fin n → R} (hv : ∀ τ, pairMat u h m τ *ᵥ v = 0) : v = 0 := by
  obtain ⟨Φ, hΦ⟩ := TanPair.exists_tanM_equiv E H Z.X Z.t R x U h n m hm
  let L : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Z.t.G →ₗ[R] R := (dotProductBilin R R).flip v ∘ₗ Φ.toLinearMap
  have hL : L = 0 := (eigBasis u).ext fun p => by
    rw [eigBasis_apply]
    refine Eq.trans ?_ (congrFun (hv p.1) p.2)
    change Φ (u.vec p.1 p.2) ⬝ᵥ v = _
    exact congrArg (· ⬝ᵥ v) (funext (hΦ _))
  funext a
  have := LinearMap.congr_fun hL (Φ.symm (Pi.single a 1))
  simpa [L] using this

variable {σ : c.F →+* ℂ} (G : EigMet Z σ) {y : CxPts (genStr Z) σ}

def dualMat (u : EigFrame Z σ (y.1 ≫ genι Z)) (h : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ U) (m : Fin n → Γ(omega Z.t.G, U)) :
    Matrix (Fin n) (Fin n) ℂ := ∑ τ : E →+* ℂ, chg (pairMat u h m τ) (G.gram y u τ)⁻¹

theorem dualMat_eq (f g : EigFrame Z σ (y.1 ≫ genι Z)) (h : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ U) (m : Fin n → Γ(omega Z.t.G, U)) :
    dualMat G g h m = dualMat G f h m := by
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hT := f.isUnit_det_co g τ
  have hT' : IsUnit (f.co g τ)ᴴ.det := by rw [det_conjTranspose]; exact hT.star
  rw [pairMat_co f g, G.change y f g, ← chg_chg]
  congr 1
  rw [chg, transpose_transpose, show (f.co g τ)ᵀᴴᵀ = (f.co g τ)ᴴ from rfl, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    mul_nonsing_inv_cancel_left _ _ hT, nonsing_inv_mul_cancel_right _ _ hT']

theorem form_sum {ι m : Type} [Fintype ι] [Fintype m] (M : ι → Matrix m m ℂ) (v w : m → ℂ) :
    form (∑ i, M i) v w = ∑ i, form (M i) v w := by
  simp only [form_eq_sum, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

theorem posDef_dualMat (u : EigFrame Z σ (y.1 ≫ genι Z)) (h : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ U) {m : Fin n → Γ(omega Z.t.G, U)}
    (hm : VB.IsFrame m) : (dualMat G u h m).PosDef := by
  refine posDef_iff.2 ⟨?_, fun v hv => ?_⟩
  · refine Finset.sum_induction _ IsHermitian (fun _ _ => IsHermitian.add) isHermitian_zero fun τ _ => ?_
    exact isHermitian_mul_mul_conjTranspose (pairMat u h m τ)ᵀ (G.pos y u τ).inv.isHermitian
  · obtain ⟨τ, hτ⟩ := not_forall.1 fun h0 => hv (eq_zero_of_pairMat u h hm h0)
    rw [dualMat, form_sum]
    simp only [form_chg]
    refine Finset.sum_pos' (fun τ _ => ?_) ⟨τ, Finset.mem_univ _, (posDef_iff.1 (G.pos y u τ).inv).2 _ hτ⟩
    by_cases h0 : pairMat u h m τ *ᵥ v = 0
    · simp [h0, form_eq_sum]
    · exact ((posDef_iff.1 (G.pos y u τ).inv).2 _ h0).le

theorem pairMat_mulVec_crd {σ₀ : Oz →+* ℂ} {z : CxPts Z.s σ₀} {x : Sp ℂ ⟶ Z.X} (e : z.1 = x) (u : EigFrame Z σ x)
    (ch : Chart (omega Z.t.G) n) (h : ⊤ ≤ x ⁻¹ᵁ ch.U) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(omega Z.t.G, U)) (τ : E →+* ℂ) :
    pairMat u h ch.e τ *ᵥ ch.crd Z.s σ₀ s z = fun i => tanEv Z.t (u.tan τ i) hU s := by
  subst e
  funext i
  have hW : z ∈ ptsIn Z.s σ₀ (U ⊓ ch.U) := mem_ptsIn_inf.2 ⟨hU, h⟩
  let L : Γ(omega Z.t.G, U ⊓ ch.U) →+ ℂ := AddMonoidHom.mk' (tanEv Z.t (u.tan τ i) hW) (tanEv_add Z.t _ hW)
  refine Eq.trans ?_ (tanEv_resM Z.t (u.tan τ i) hW inf_le_left s)
  rw [← (ch.isFrame.basis inf_le_right).sum_repr (resM _ inf_le_left s)]
  refine Eq.trans ?_ (map_sum L _ _).symm
  rw [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Eq.trans ?_ (tanEv_smul Z.t _ hW _ _).symm
  rw [IsFrame.basis_apply, tanEv_resM Z.t (u.tan τ i) hW inf_le_right, mul_comm, Chart.crd, ev_eq hW]
  rfl

theorem dualMat_chg {σ₀ : Oz →+* ℂ} {z : CxPts Z.s σ₀} (e : z.1 = y.1 ≫ genι Z) (u : EigFrame Z σ (y.1 ≫ genι Z))
    (ch ch' : Chart (omega Z.t.G) n) (h : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ ch.U) (h' : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ ch'.U) :
    dualMat G u h' ch'.e = chg (ch.tr Z.s σ₀ ch' z) (dualMat G u h ch.e) := by
  rw [dualMat, dualMat, chg, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => Eq.trans ?_ (chg_chg _ _ _).symm
  congr 1
  ext i a
  exact (congrFun (pairMat_mulVec_crd e u ch h h' (ch'.e a) τ) i).symm

end Pair

variable {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)}

theorem isPreimmersion_genι (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsPreimmersion (genι Z) :=
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip
    (IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F)))

theorem exists_ext {F : Type} [Field F] [NumberField F] (σ : 𝓞 F →+* ℂ) :
    ∃ σ' : F →+* ℂ, σ = σ'.comp (algebraMap (𝓞 F) F) := by
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  refine ⟨IsFractionRing.lift (K := F) hσ, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

theorem exists_lift {σ : 𝓞 c.F →+* ℂ} (z : CxPts Z.s σ) :
    ∃ (σ' : c.F →+* ℂ) (y : CxPts (genStr Z) σ'), z.1 = y.1 ≫ genι Z := by
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  obtain ⟨σ', rfl⟩ := exists_ext σ
  have e : z.1 ≫ Z.s = spMap σ' ≫ spMap (algebraMap (𝓞 c.F) c.F) :=
    z.2.trans (ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap _ _).symm
  exact ⟨σ', ⟨Limits.pullback.lift _ _ e, Limits.pullback.lift_snd _ _ _⟩, (Limits.pullback.lift_fst _ _ _).symm⟩

variable (G : ∀ σ', EigMet Z σ') {n : ℕ}

theorem dualMat_congr {σ σ' : c.F →+* ℂ} {y : CxPts (genStr Z) σ} {y' : CxPts (genStr Z) σ'}
    (e : y.1 ≫ genι Z = y'.1 ≫ genι Z) (u : EigFrame Z σ (y.1 ≫ genι Z)) (u' : EigFrame Z σ' (y'.1 ≫ genι Z))
    {U : Z.X.Opens} (h : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ U) (h' : ⊤ ≤ (y'.1 ≫ genι Z) ⁻¹ᵁ U) (m : Fin n → Γ(omega Z.t.G, U)) :
    dualMat (G σ) u h m = dualMat (G σ') u' h' m := by
  have := isPreimmersion_genι Z
  have e' := (cancel_mono _).1 e
  obtain rfl : σ = σ' := EigLoc.spMap_inj (y.2.symm.trans (e' ▸ y'.2))
  obtain rfl : y = y' := Subtype.ext e'
  exact dualMat_eq _ _ _ _ _

def HasDual {σ : 𝓞 c.F →+* ℂ} (h : Met Z.s σ (omega Z.t.G) n) : Prop :=
  ∀ (z : CxPts Z.s σ) (σ' : c.F →+* ℂ) (y : CxPts (genStr Z) σ'), z.1 = y.1 ≫ genι Z →
    ∀ (u : EigFrame Z σ' (y.1 ≫ genι Z)) (ch : Chart (omega Z.t.G) n) (hy : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ ch.U),
      h.G ch z = dualMat (G σ') u hy ch.e

theorem exists_hasDual (hV : IsVB (omega Z.t.G) n) (σ : 𝓞 c.F →+* ℂ) : ∃ h : Met Z.s σ (omega Z.t.G) n, HasDual G h := by
  choose σ' y hy using fun z : CxPts Z.s σ => exists_lift z
  have u := fun z => (EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ Z ℂ _ _ (y z).2).some
  have hm : ∀ z, ⊤ ≤ ((y z).1 ≫ genι Z) ⁻¹ᵁ (hV.pick z).U := fun z => hy z ▸ hV.mem_pick z
  refine ⟨.ofPt hV hV.pick hV.mem_pick (fun z => dualMat (G _) (u z) (hm z) (hV.pick z).e)
    fun z => posDef_dualMat _ _ _ (hV.pick z).isFrame, fun z σ'' y' e u' ch h => ?_⟩
  have h' : ⊤ ≤ ((y z).1 ≫ genι Z) ⁻¹ᵁ ch.U := by rw [← hy, e]; exact h
  exact (dualMat_chg _ (hy z) _ _ _ _ h').symm.trans (dualMat_congr G ((hy z).symm.trans e) _ _ _ _ _)

variable {G}

theorem HasDual.isConj (hG : GlobalTheory.ArLieBase.EigConj Z G) {σ σ₁ : 𝓞 c.F →+* ℂ} {h : Met Z.s σ (omega Z.t.G) n}
    {h₁ : Met Z.s σ₁ (omega Z.t.G) n} (k : HasDual G h) (k₁ : HasDual G h₁) : h.IsConj h₁ :=
  Met.isConj_of_exists fun z z₁ e => by
    obtain ⟨σ', y, hy⟩ := exists_lift z
    obtain ⟨u⟩ := EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ Z ℂ _ _ y.2
    let y₁ : CxPts (genStr Z) ((starRingEnd ℂ).comp σ') :=
      ⟨spMap (starRingEnd ℂ) ≫ y.1, by rw [Category.assoc, y.2, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]⟩
    have hx : y₁.1 ≫ genι Z = spMap (starRingEnd ℂ) ≫ y.1 ≫ genι Z := Category.assoc _ _ _
    obtain ⟨u₁, hu⟩ := u.exists_isMap (starRingEnd ℂ) rfl hx
    have hy₁ : z₁.1 = y₁.1 ≫ genι Z := by rw [e, hy, hx]
    have hc := h.isVB.mem_pick z
    have hm : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ (h.isVB.pick z).U := hy ▸ hc
    have hm₁ : ⊤ ≤ (y₁.1 ≫ genι Z) ⁻¹ᵁ (h.isVB.pick z).U := hy₁ ▸ (mem_ptsIn_iff_of_conj e).2 hc
    refine ⟨_, hc, ?_⟩
    rw [k z _ y hy u _ hm, k₁ z₁ _ y₁ hy₁ u₁ _ hm₁, dualMat, dualMat]
    refine Eq.trans (Finset.sum_congr rfl fun τ _ => ?_) (map_sum (starRingEnd ℂ).mapMatrix _ _).symm
    rw [pairMat_map hu hx.symm hm, hG _ _ y y₁ u u₁ τ rfl rfl hu]
    refine Eq.trans ?_ (chg_map_star _ _)
    exact congrArg _ (congrArg transpose (dualGram_map_star _))

theorem isDualEig_of_hasDual {h : VMetric Z.s (omega Z.t.G) n} (k : ∀ σ, HasDual G (h.met σ)) : IsDualEig G h := by
  intro σ' y z e u U W hU f f' hz
  have hc := h.isVB.mem_pick z
  have hm : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ (h.isVB.pick z).U := e ▸ hc
  have hU' : ⊤ ≤ (y.1 ≫ genι Z) ⁻¹ᵁ U := e ▸ hz
  rw [Met.form_eq _ _ hc _ _ hz, k _ z _ y e u _ hm, dualMat, form_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [form_chg, pairMat_mulVec_crd e u _ hm hU', pairMat_mulVec_crd e u _ hm hU']
  simp only [(tanEv_dUnit_eq _ _ _ _).2]

theorem vInfAt_of_re_im {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {g : CxPts p σ → ℂ}
    {y : CxPts p σ} (h₁ : CInfAt (fun z => (g z).re) y) (h₂ : CInfAt (fun z => (g z).im) y) : VInfAt g y := by
  simpa using ((vInfAt_iff_cInfAt.2 h₁).prodMk (vInfAt_iff_cInfAt.2 h₂)).comp_contDiff
    (Ψ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I)
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const))

theorem exists_frame (w : gen Z) (U : (gen Z).Opens) (hw : w ∈ U) : ∃ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1))
    (_ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), w ∈ V.1 ∧ V.1 ≤ U ∧ LogKS.chart V ≫ genStr Z = spMap φ := by
  obtain ⟨V₀, hV₀, φ, F, hw₀, hφ, -⟩ := EigSpread.exists_stable_eigFrame _ _ _ _ _ _ _ _ Z w
  obtain ⟨V, hV, hwV, hle⟩ := exists_isAffineOpen_mem_and_subset (x := w) (U := V₀ ⊓ U) ⟨hw₀, hw⟩
  have h₀ : V ≤ V₀ := fun z hz => (hle hz).1
  have hρ : spMap (resG _ h₀) ≫ affPt hV₀ = LogKS.chart ⟨V, hV⟩ := spMap_affPt hV₀ hV h₀
  obtain ⟨F', -⟩ := F.exists_isMap (resG _ h₀) rfl (x' := LogKS.chart ⟨V, hV⟩ ≫ genι Z)
    (by rw [← hρ]; exact Category.assoc _ _ _)
  refine ⟨⟨V, hV⟩, _, F', hwV, fun z hz => (hle hz).2, ?_⟩
  rw [← hρ, Category.assoc, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  exact congrArg _ hφ

theorem HasDual.isCInf [SmoothOfRelativeDimension Dw.dim (genStr Z)] (hG : ∀ σ', (G σ').SmoothOn (manifold Z σ') Set.univ)
    {σ : 𝓞 c.F →+* ℂ} {h : Met Z.s σ (omega Z.t.G) n} (k : HasDual G h) : h.IsCInf := by
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  intro ch z hz
  obtain ⟨σ', y, hy⟩ := exists_lift z
  have hσ : ∀ w : CxPts (genStr Z) σ', (w.1 ≫ genι Z) ≫ Z.s = spMap σ := fun w => by
    rw [← z.2, hy, Category.assoc, Category.assoc, Limits.pullback.condition, reassoc_of% w.2, reassoc_of% y.2]
  let m : CxPts (genStr Z) σ' → CxPts Z.s σ := fun w => ⟨_, hσ w⟩
  obtain rfl : m y = z := Subtype.ext hy.symm
  obtain ⟨V, φ, F, hyV, hle, hφ⟩ := exists_frame (y.1 (IsLocalRing.closedPoint ℂ)) (genι Z ⁻¹ᵁ ch.U) (mem_ptsIn.1 hz)
  have hyV' : y ∈ ptsIn (genStr Z) σ' V.1 := mem_ptsIn.2 hyV
  have hF : ⊤ ≤ (LogKS.chart V ≫ genι Z) ⁻¹ᵁ ch.U :=
    (le_preimage_affPt V.2).trans ((LogKS.chart V).preimage_mono hle)
  choose g hre him hg using fun τ a b => hG σ' V φ F τ a b hφ
  have ho : IsOpen (Set.univ ∩ ptsIn (genStr Z) σ' V.1) := isOpen_univ.inter (isOpen_ptsIn _)
  have key : ∀ w ∈ ptsIn (genStr Z) σ' V.1, (∀ τ, IsUnit (of (g τ · · w)).det) ∧ h.G ch (m w) =
      ∑ τ : E →+* ℂ, chg (of fun i a => CxPts.ev (genStr Z) σ' V.1 (pairMat F hF ch.e τ i a) w) (of (g τ · · w))⁻¹ := by
    intro w hw
    have hov : σ' = (evHom hw).comp φ := EigLoc.spMap_inj (w.2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ, ← Category.assoc, spMap_evHom hw]))
    have hx : w.1 ≫ genι Z = spMap (evHom hw) ≫ LogKS.chart V ≫ genι Z := by rw [← Category.assoc, spMap_evHom hw]
    obtain ⟨f, hf⟩ := F.exists_isMap (evHom hw) hov hx
    have hgr : ∀ τ, (G σ').gram w f τ = of (g τ · · w) := fun τ => Matrix.ext fun a b => hg τ a b w trivial hw f hf
    have hm : ⊤ ≤ (w.1 ≫ genι Z) ⁻¹ᵁ ch.U := le_trans hw (w.1.preimage_mono hle)
    refine ⟨fun τ => hgr τ ▸ ((G σ').pos w f τ).det_pos.ne'.isUnit, ?_⟩
    rw [k (m w) σ' w rfl f ch hm, dualMat]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hgr, pairMat_map hf hx.symm hF]
    congr 1
    ext i a
    exact (ev_eq hw _).symm
  have hM : MInfAt (fun w => h.G ch (m w)) y := by
    refine MInfAt.congr (fun a b => ?_) (Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds hyV') fun w hw => (key w hw).2)
    simp only [Matrix.sum_apply]
    refine (vInfAt_pi fun τ => ?_).comp_contDiff (Ψ := fun v : (E →+* ℂ) → ℂ => ∑ τ, v τ)
      (ContDiff.sum fun τ _ => contDiff_apply _ _ τ)
    have h₁ : MInfAt (fun w => of (g τ · · w)) y := fun a b => vInfAt_of_re_im
      ((cInfAt_iff_smoothOn _ ho).2 (hre τ a b) y ⟨trivial, hyV'⟩) ((cInfAt_iff_smoothOn _ ho).2 (him τ a b) y ⟨trivial, hyV'⟩)
    exact MInfAt.chg (A := fun w => of fun i a => CxPts.ev (genStr Z) σ' V.1 (pairMat F hF ch.e τ i a) w)
      (H := fun w => (of (g τ · · w))⁻¹) (fun i a => vInfAt_ev _ hyV')
      (fun i j => h₁.dualGram ((key y hyV').1 τ) j i) a b
  intro a b
  have hb := OnModelCInf.baseChange_cInfAt c.F Z.X (gen Z) Z.s (genStr Z) (genι Z) (IsPullback.of_hasPullback _ _) σ' σ m
    fun _ => rfl
  exact vInfAt_of_re_im (hb _ y ((hM a b).comp_contDiff Complex.reCLM.contDiff))
    (hb _ y ((hM a b).comp_contDiff Complex.imCLM.contDiff))

theorem isVB_omega (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsVB (omega Z.t.G) (∑ τ : E →+* ℂ, Dw.mult τ) := by
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := {}
  have := Z.t.semi
  have := Z.t.semi.smooth
  have := Z.flat
  intro x
  obtain ⟨U, n, m, hx, hm⟩ := LieVB.exists_isFrame_omega Z.t.G x
  let η := spMap (algebraMap (𝓞 c.F) c.F) (IsLocalRing.closedPoint c.F)
  have hη : η ⤳ Z.s x := (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => by
    obtain rfl : a = 0 := IsFractionRing.injective (𝓞 c.F) c.F (by
      simpa using (IsLocalRing.maximalIdeal_eq_bot (R := c.F)).le ha)
    exact zero_mem _
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap Z.s hη
  obtain ⟨w, rfl⟩ : x' ∈ Set.range (genι Z) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨_, e.symm⟩
  obtain ⟨K, _, _, p, t, rfl⟩ := GlobalTheory.FlagCptBase.exists_geomPt _ w
  obtain ⟨u⟩ := EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ Z K (Spec.preimage (p ≫ genStr Z)).hom p (Spec.map_preimage _).symm
  have hU : ⊤ ≤ (p ≫ genι Z) ⁻¹ᵁ U := fun t' _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum K) t' t]
    exact hx'.mem_open U.2 hx
  obtain rfl := card_eq u hU hm
  exact ⟨U, m, hx, hm⟩

theorem exists_isDualEig [SmoothOfRelativeDimension Dw.dim (genStr Z)] (hV : IsVB (omega Z.t.G) n)
    (hc : GlobalTheory.ArLieBase.EigConj Z G) (hG : ∀ σ', (G σ').SmoothOn (manifold Z σ') Set.univ) :
    ∃ h : VMetric Z.s (omega Z.t.G) n, h.IsCInf ∧ IsDualEig G h := by
  choose h k using exists_hasDual G hV
  exact ⟨⟨hV, h, fun σ σ' => (k σ).isConj hc (k σ')⟩, fun σ => (k σ).isCInf hG, isDualEig_of_hasDual k⟩

end Free

theorem dim_range {D : D7} (O : Setup D) (c : O.s.Comp) :
    topologicalKrullDim (Set.range (O.Φ.C c).π) = (dimGr D.what₂.Tau O.N O.j : ℕ) := by
  have hsm := O.s.T.smooth
  obtain ⟨X, j, hoi, hj, hr⟩ := GlobalTheory.CompOfVar.exists_var_comp _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e hsm (O.Φ.C c).Y
    (O.Φ.C c).π (O.Φ.C c).π_str
  let f : (O.Φ.C c).Y.X ⟶ X.X := IsOpenImmersion.lift j (O.Φ.C c).π hr
  have hf : f ≫ j = (O.Φ.C c).π := IsOpenImmersion.lift_fac _ _ _
  have hrange : Set.range j = Set.range (O.Φ.C c).π := by
    refine Set.Subset.antisymm ?_ hr
    rintro _ ⟨z, rfl⟩
    obtain ⟨K, _, _, x, t, rfl⟩ := GlobalTheory.FlagCptBase.exists_geomPt _ z
    let χ : O.κ.c.F →+* K := (Spec.preimage (x ≫ j ≫ genStr O.s.T.Z)).hom
    have hχ : x ≫ j ≫ genStr O.s.T.Z = spMap χ := (Spec.map_preimage _).symm
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ O.s.T.Z K χ (x ≫ j) (by rw [Category.assoc, hχ])
    rw [Category.assoc] at g
    obtain ⟨p, ⟨hp, -⟩, -⟩ := GlobalTheory.CarryAll.carries_everywhere _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ _ O.Φ c X j hoi hj f hf
      K χ x hχ g
    refine ⟨p t, ?_⟩
    rw [← hf, ← hp]
    simp only [Scheme.Hom.comp_apply]
  have h : SmoothOfRelativeDimension (0 + O.S.Dw.dim) (j ≫ genStr O.s.T.Z) := inferInstance
  rw [topologicalKrullDim_eq_of_isEmbedding j.isEmbedding hrange, GlobalTheory.HSApp.BigMoving.dim_eq _ X.X _ _ h, zero_add,
    Datum.dim, dimGr, GlobalTheory.ShFam.CmDim.card_tau, O.S.p_eq,
    show O.S.Dw.q = O.N - O.j by have := O.S.rank_eq; have := O.S.p_eq; omega, mul_assoc]

theorem isArithVar_clo {F : Type} [Field F] [NumberField F] {T : Scheme.{0}} (s : T ⟶ Sp (𝓞 F)) (hs : IsProjOver s)
    (w : ↥(Limits.pullback s (spMap (algebraMap (𝓞 F) F)))) {d : ℕ}
    (hd : topologicalKrullDim (closure {w} : Set _) = d) :
    IsArithVar (redι (clo (Limits.pullback.fst s (spMap (algebraMap (𝓞 F) F)) w)) ≫ s) d := by
  set j := Limits.pullback.fst s (spMap (algebraMap (𝓞 F) F)) with hj
  set b := redι (clo (j w)) with hb
  have : IsPreimmersion j := MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip
    (IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F)))
  have hpb : IsPullback (Limits.pullback.fst b j) (Limits.pullback.snd b j ≫ Limits.pullback.snd _ _) (b ≫ s)
      (spMap (algebraMap (𝓞 F) F)) := (IsPullback.of_hasPullback b j).paste_vert (IsPullback.of_hasPullback _ _)
  have hr : Set.range (Limits.pullback.snd b j) = closure {w} := by
    rw [Scheme.Pullback.range_snd, hb, range_redι, j.isEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton]
    rfl
  obtain ⟨v, -⟩ : w ∈ Set.range (Limits.pullback.snd b j) := hr ▸ subset_closure rfl
  have : Nonempty (⊤ : (Limits.pullback b j).Opens) := ⟨⟨v, trivial⟩⟩
  have hc : CharZero Γ(Limits.pullback b j, ⊤) := charZero_of_injective_ringHom
    ((Limits.pullback.snd b j ≫ Limits.pullback.snd _ _).appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom).injective
  have hc' := (Limits.pullback.fst b j).appTop.hom.charZero
  have hproj : IsProjOver (b ≫ s) := by
    obtain ⟨N, i, _, hi⟩ := hs
    exact ⟨N, b ≫ i, inferInstance, by rw [Category.assoc, hi]⟩
  exact ⟨inferInstance, inferInstance, inferInstance, hproj, (flat_int_iff_charZero _).2 hc',
    CurveClosure.dim_eq_of_genFibre F _ _ _ _ _ d hproj hc' hpb
      ((topologicalKrullDim_eq_of_isEmbedding (Limits.pullback.snd b j).isEmbedding hr).symm.trans hd)⟩

theorem redι_genericPoint {T : Scheme.{0}} (z : T) : redι (clo z) (genericPoint _) = z := by
  have h := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme).image (redι (clo z)).continuous
  rw [Set.image_univ, range_redι] at h
  exact h.eq (closure_closure (s := {z})).symm

theorem sum_mult {D : D7} (O : Setup D) : ∑ τ, O.S.Dw.mult τ = D.R.f * O.N := by
  have h := GlobalTheory.LetterCount.two_mul_sum_mult O.S.Dw
  rw [Embeddings.card, O.S.rank_eq, IsTotallyComplex.finrank] at h
  have h₁ := GlobalTheory.ShFam.CmDim.card_tau D
  have h₂ : Fintype.card D.what₂.Tau = D.R.f := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau]
    exact (factCardPsi D.R D.host).1
  rw [IsTotallyComplex.finrank, Nat.mul_div_cancel_left _ two_pos, h₂] at h₁
  rw [← h₁, mul_assoc] at h
  omega

theorem nonempty_drBase {D : D7} (O : Setup D) (h : O.Core) (c : O.s.Comp) : Nonempty (DRBase O c) := by
  obtain ⟨x, P, hc⟩ := h
  have : FiniteDimensional ℚ O.κ.c.F := O.κ.c.fin
  have : NumberField O.κ.c.F := {}
  have hsm := O.s.T.smooth
  let w := (O.Φ.C c).π (genericPoint (O.Φ.C c).Y.X)
  have hw : closure {w} = Set.range (O.Φ.C c).π := by
    have h := (genericPoint_spec (O.Φ.C c).Y.X).image (O.Φ.C c).π.continuous
    rwa [Set.image_univ, (GlobalTheory.FlagCptBase.isClosed_range_π (O.Φ.C c)).closure_eq] at h
  have har := isArithVar_clo O.s.T.Z.s O.s.T.Z.proj w (hw ▸ dim_range O c)
  have hV : IsVB (omega O.s.T.Z.t.G) (D.R.f * O.N) := sum_mult O ▸ isVB_omega O.s.T.Z
  choose h H hd using fun R : ℝ => exists_isDualEig (G := fun σ' => x.eigMetAt σ' (some R)) hV
    (fun σ σ' y y' g g' τ hσ e hg => GlobalTheory.ShFam.ConjMet.eigMetAt_conj x hσ e hg τ _) fun σ' => by
      have e : x.eigMetAt σ' (some R) = x.eigMetAt σ' (some (max R 2)) := by
        have e' : x.wt σ' R = x.wt σ' (max R 2) := funext fun y => by simp only [ToroidalCompactificationData.wt, max_assoc, max_self]
        simp only [ToroidalCompactificationData.eigMetAt, e']
      rw [e]
      exact ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ x σ' _ (le_max_right _ _) (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x σ')
  have := har.isLocallyNoetherian
  obtain ⟨⟨F⟩, -⟩ := GlobalTheory.T.flag_variety_arith_dimension _ _ _ _ har _ _ (hV.pullback (redι (clo (genι O.s.T.Z w))))
  exact ⟨⟨x, P, hc, _, redι (clo (genι O.s.T.Z w)), redι_genericPoint _, har, h, H, hd, F⟩⟩

theorem main : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration →
    OnObj fun _ O _ _ _ _ => ∀ c, Nonempty (DRBase O c) :=
  fun _ _ _ _ _ O h _ _ _ _ _ c => nonempty_drBase O h c

end GlobalTheory.DRBaseEx

end
