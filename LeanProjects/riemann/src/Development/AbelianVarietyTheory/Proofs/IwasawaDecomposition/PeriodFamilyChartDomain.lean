import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RiemSmooth

def stdR (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (hermForm Hm z w).im := rfl

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g) :
    Hm p q = ((imForm Hm (stdR g ⟨p, 1⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) +
      ((imForm Hm (stdR g ⟨p, 0⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [imForm_apply, stdR, hermForm, Pi.basis_apply]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

def coordMat {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) :
    Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ :=
  Matrix.of fun a k => (stdR g).repr (u k) a

theorem std_eq_sum {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) (hM : (coordMat u).det ≠ 0)
    (a : Σ _ : Fin g, Fin 2) :
    stdR g a = ∑ k, ((coordMat u)⁻¹ k a) • u k := by
  apply (stdR g).repr.injective
  ext a'
  have h1 : coordMat u * (coordMat u)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)
  have h2 : ∑ k, coordMat u a' k * (coordMat u)⁻¹ k a = if a = a' then 1 else 0 := by
    rw [← Matrix.mul_apply, h1, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.smul_apply, Finset.sum_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [← h2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem imForm_std {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ))
    (hM : (coordMat u).det ≠ 0) (F : (Σ _ : Fin g, Fin 2) → (Σ _ : Fin g, Fin 2) → ℝ)
    (hF : ∀ k l, (hermForm Hm (u k) (u l)).im = F k l) (a c : Σ _ : Fin g, Fin 2) :
    imForm Hm (stdR g a) (stdR g c) =
      ∑ k, ∑ l, (coordMat u)⁻¹ k a * (coordMat u)⁻¹ l c * F k l := by
  rw [std_eq_sum u hM a, std_eq_sum u hM c]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    imForm_apply, hF]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem contDiffOn_det_real {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s) :
    ContDiffOn ℝ ∞ (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_entry {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s)
    (hdet : ∀ x ∈ s, (M x).det ≠ 0) (k a : ι) :
    ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ k a) s := by
  have hadj : ContDiffOn ℝ ∞ (fun x => (M x).adjugate k a) s := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det_real fun i j => ?_
    by_cases hi : i = a
    · subst hi; simpa [Matrix.updateRow_apply] using contDiffOn_const
    · simpa [Matrix.updateRow_apply, hi] using h i j
  refine ((contDiffOn_det_real h).inv hdet |>.mul hadj).congr fun x hx => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [smul_eq_mul]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

theorem contDiffOn_of_im_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : Type} [AddCommGroup L] {g : ℕ}
    {B : Set X} (hB : IsOpen B) (P : X → (L →+ (Fin g → ℂ))) (F : L → L → ℝ)
    (hP : ∀ v, ContDiffOn ℝ ∞ (fun b => P b v) B)
    (hspan : ∀ b ∈ B, Submodule.span ℝ (Set.range (P b)) = ⊤)
    (Hm : X → Matrix (Fin g) (Fin g) ℂ)
    (hH : ∀ b ∈ B, ∀ x y, (hermForm (Hm b) (P b x) (P b y)).im = F x y) (p q : Fin g) :
    ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  refine contDiffOn_of_locally_contDiffOn fun b₀ hb₀ => ?_
  obtain ⟨t, ht, hts, hli⟩ := exists_linearIndependent ℝ (Set.range (P b₀))
  rw [hspan b₀ hb₀] at hts
  let bt : Module.Basis t ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hts])
  let e := bt.indexEquiv (stdR g)
  have hv : ∀ k, ∃ v, P b₀ v = bt (e.symm k) := fun k => by
    obtain ⟨v, hv⟩ := ht (e.symm k).2
    exact ⟨v, by rw [hv, Module.Basis.mk_apply]⟩
  choose v hv using hv
  let M : X → Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ := fun b => coordMat fun k => P b (v k)
  have hMs : ∀ a k, ContDiffOn ℝ ∞ (fun b => M b a k) B := fun a k => by
    let ℓ : (Fin g → ℂ) →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap ((Finsupp.lapply a).comp (stdR g).repr.toLinearMap)
    exact ℓ.contDiff.comp_contDiffOn (hP (v k))
  have hdet0 : (M b₀).det ≠ 0 := by
    have : M b₀ = (stdR g).toMatrix (bt.reindex e) := by
      ext a k
      simp [M, coordMat, Module.Basis.toMatrix_apply, hv]
    rw [this, ← Module.Basis.det_apply]
    exact ((stdR g).isUnit_det _).ne_zero
  have hcont : ContinuousAt (fun b => (M b).det) b₀ :=
    (contDiffOn_det_real hMs).continuousOn.continuousAt (hB.mem_nhds hb₀)
  obtain ⟨U, hU, hUo, hb₀U⟩ := eventually_nhds_iff.1 (hcont.eventually_ne hdet0)
  refine ⟨U, hUo, hb₀U, ?_⟩
  have hdet : ∀ b ∈ B ∩ U, (M b).det ≠ 0 := fun b hb => hU b hb.2
  have hN := contDiffOn_inv_entry (fun a k => (hMs a k).mono Set.inter_subset_left) hdet
  have hsum : ∀ a c, ContDiffOn ℝ ∞ (fun b => ∑ k, ∑ l, (M b)⁻¹ k a * (M b)⁻¹ l c * F (v k) (v l)) (B ∩ U) :=
    fun a c => ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ =>
      ((hN k a).mul (hN l c)).mul contDiffOn_const
  refine ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 1⟩ ⟨q, 0⟩)).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 0⟩ ⟨q, 0⟩)).mul (contDiffOn_const (c := Complex.I)))).congr
    fun b hb => ?_
  have hF : ∀ k l, (hermForm (Hm b) (P b (v k)) (P b (v l))).im = F (v k) (v l) :=
    fun k l => hH b hb.1 _ _
  have h1 := entry_eq (Hm b) p q
  rw [imForm_std (Hm b) _ (hdet b hb) _ hF, imForm_std (Hm b) _ (hdet b hb) _ hF] at h1
  exact h1

theorem exists_riem_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → ∃ Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ, (∀ b ∈ B, IsRiem Fu i (P b) (Hm b)) ∧ ∀ p q, ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i d B P hB hper hhol
  classical
  let Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ :=
    fun b => if h : b ∈ B then Classical.choose (hper b h).2.2.2.2 else 0
  have hHm : ∀ b (h : b ∈ B), Hm b = Classical.choose (hper b h).2.2.2.2 := fun b h => dif_pos h
  have hR : ∀ b ∈ B, IsRiem Fu i (P b) (Hm b) := fun b h => by
    rw [hHm b h]
    exact Classical.choose_spec (hper b h).2.2.2.2
  refine ⟨Hm, hR, fun p q => ?_⟩
  refine contDiffOn_of_im_eq hB P (fun x y => ((Fu.Di i).EF x y : ℝ)) (fun v => ?_)
    (fun b h => (hper b h).2.2.2.1) Hm (fun b h x y => (hR b h).2.2 x y) p q
  exact contDiffOn_pi.2 fun j =>
    GlobalTheory.ChartGlue.contDiffOn_real hB ((differentiableOn_pi.1 (hhol v)) j)

end GlobalTheory.RiemSmooth
