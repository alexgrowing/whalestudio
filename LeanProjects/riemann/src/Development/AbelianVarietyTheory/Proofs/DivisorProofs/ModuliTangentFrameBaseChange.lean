import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Split

theorem split_eig {K : Type} [CommRing K] {g r : ℕ} {D Nk dk nk : K} (hd : dk * D = 1) (hn : nk * Nk = 1)
    {P : Matrix (Fin g) (Fin g) K} {V : Matrix (Fin g) (Fin r) K} {Hi : Matrix (Fin r) (Fin g) K}
    (S3 : V * Hi * P = Nk • P) {cf : Fin g → K} (hE : P.mulVec cf = D • cf) :
    V.mulVec (nk • Hi.mulVec cf) = cf := by
  have h3 := congrArg (fun M => M.mulVec cf) S3
  simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul] at h3
  have h4 : V.mulVec (Hi.mulVec cf) = Nk • cf := by
    have := congrArg (dk • ·) h3
    simp only [smul_smul, hd, one_smul] at this
    rw [this, show dk * (Nk * D) = Nk by rw [mul_left_comm, hd, mul_one]]
  rw [Matrix.mulVec_smul, h4, smul_smul, hn, one_smul]

theorem split_inj {K : Type} [CommRing K] {g r : ℕ} {Nk nk : K} (hn : nk * Nk = 1)
    {V : Matrix (Fin g) (Fin r) K} {Hi : Matrix (Fin r) (Fin g) K} (S2 : Hi * V = Nk • 1) (a : Fin r → K) :
    nk • Hi.mulVec (V.mulVec a) = a := by
  rw [Matrix.mulVec_mulVec, S2, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, hn, one_smul]

theorem split_form {K : Type} [CommRing K] {g r : ℕ} {D dk : K} (hd : dk * D = 1) {P : Matrix (Fin g) (Fin g) K}
    {cf : Fin g → K} (hE : P.mulVec cf = D • cf) (f : Fin g → K) (fs : Fin r → Fin g → K) (α : Fin r → K)
    (h : Matrix.vecMul f P = ∑ i, α i • Matrix.vecMul (fs i) P) :
    f ⬝ᵥ cf = ∑ i, α i * (fs i ⬝ᵥ cf) := by
  have key : ∀ f' : Fin g → K, Matrix.vecMul f' P ⬝ᵥ cf = D * (f' ⬝ᵥ cf) := fun f' => by
    rw [← Matrix.dotProduct_mulVec, hE, dotProduct_smul, smul_eq_mul]
  have h1 : D * (f ⬝ᵥ cf) = D * ∑ i, α i * (fs i ⬝ᵥ cf) := by
    rw [← key, h, sum_dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_dotProduct, key, smul_eq_mul]
    ring
  have h2 := congrArg (dk * ·) h1
  simpa only [← mul_assoc, hd, one_mul] using h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

theorem split_basis {R : Type} [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) {g r : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis Z.t x e) {D : ℕ}
    {P : Matrix (Fin g) (Fin g) R} (hP : IsEigProj Z x τ e D P) {K : Type} [CommRing K] (ψ₁ : R →+* K)
    (φ : c.F →+* K) (hφ : spMap ψ₁ ≫ x ≫ Z.s = spMap (φ.comp β)) {V : Matrix (Fin g) (Fin r) K}
    {Hi : Matrix (Fin r) (Fin g) K} {Nk dk nk : K} (hd : dk * (D : K) = 1) (hn : nk * Nk = 1)
    (S1 : P.map ψ₁ * V = (D : K) • V) (S2 : Hi * V = Nk • 1) (S3 : V * Hi * P.map ψ₁ = Nk • P.map ψ₁)
    {v : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)}
    (hv : ∀ i, IsCombAtG Z.t (spMap ψ₁ ≫ x) (fun k => spMap (dualMap ψ₁) ≫ e k) (fun k => V k i) (v i)) :
    (∀ i, IsEigTan Z φ (spMap ψ₁ ≫ x) τ (v i)) ∧
    ∀ w, IsEigTan Z φ (spMap ψ₁ ≫ x) τ w → ∃ cf : Fin g → K,
      IsCombAtG Z.t (spMap ψ₁ ≫ x) (fun k => spMap (dualMap ψ₁) ≫ e k) cf w ∧
      (P.map ψ₁).mulVec cf = (D : K) • cf ∧
      ∀ a, IsCombAtG Z.t (spMap ψ₁ ≫ x) v a w ↔ a = nk • Hi.mulVec cf := by
  have he₁ := GlobalTheory.HTPres.isTanBasis_map Z.t he ψ₁
  have hvt : ∀ i, IsTanAtG Z.t (spMap ψ₁ ≫ x) (v i) := fun i => GlobalTheory.ShFam.Pad.Guard.comb_tan he₁.1 (hv i)
  refine ⟨fun i => (hP.2 K ψ₁ φ hφ _ _ (hv i)).2 ?_, fun w hw => ?_⟩
  · funext k
    have := congrFun (congrFun S1 k) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  obtain ⟨cf, hcf, huq⟩ := he.2 K ψ₁ w hw.1
  have hE := (hP.2 K ψ₁ φ hφ cf w hcf).1 hw
  refine ⟨cf, hcf, hE, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · have h1 := Formalism.L2.Pj.tanLinG _ he₁.1 v V a w hv ha
    rw [← huq _ h1, split_inj hn S2]
  · obtain ⟨w', -, hw'⟩ := GlobalTheory.ShFam.Pad.Guard.exists_comb hvt a
    have h1 := Formalism.L2.Pj.tanLinG _ he₁.1 v V a w' hv hw'
    rw [ha, split_eig hd hn S3 hE] at h1
    rwa [GlobalTheory.ShFam.Pad.Guard.comb_unique he₁.1 hcf h1]

end Split

theorem ringBasis_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (kind : ℕ → Bool) (sc : ℕ → ℝ) (g M r D N : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)) (h : Fin M → Fin g → R) (P : Matrix (Fin g) (Fin g) R) (U : Matrix (Fin g) (Fin r) R') (I : Fin r → Fin M), D ≠ 0 → N ≠ 0 → GlobalTheory.LineNorm.IsTanBasis Z.t x e → IsEigProj Z x τ e D P → LatPres Z.t x kind sc e h → IsSplitting D (P.map ψ) (fun j i => ψ (h j i)) N U I → RingBasis Z (spMap ψ ≫ x) τ r kind sc := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z R R' _ _ ψ x τ kind sc g M r D N e h P U I hD hN he hP hL hS
  have hunit : ∀ {K : Type} [CommRing K] (_ : c.F →+* K) (n : ℕ), n ≠ 0 → ∃ k : K, k * (n : K) = 1 := by
    intro K _ φ n hn
    have hu : IsUnit ((n : ℕ) : K) := by
      simpa using ((Nat.cast_ne_zero.2 hn : ((n : ℕ) : c.F) ≠ 0).isUnit).map φ
    obtain ⟨k, hk⟩ := hu.exists_left_inv
    exact ⟨k, hk⟩
  have hv0 : ∀ k, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e k) :=
    fun k => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 k)
  choose u hu using fun i => GlobalTheory.ShFam.Pad.Guard.exists_comb hv0 (fun k => U k i)
  have hbc : ∀ {K : Type} [CommRing K] (ψ₂ : R' →+* K),
      spMap ψ₂ ≫ spMap ψ ≫ x = spMap (ψ₂.comp ψ) ≫ x ∧
      (∀ i, IsCombAtG Z.t (spMap (ψ₂.comp ψ) ≫ x) (fun k => spMap (dualMap (ψ₂.comp ψ)) ≫ e k)
        (fun k => (U.map ψ₂) k i) (spMap (dualMap ψ₂) ≫ u i)) ∧
      P.map (ψ₂.comp ψ) * U.map ψ₂ = (D : K) • U.map ψ₂ ∧
      (Matrix.of fun i k => ψ₂ (ψ (h (I i) k))) * U.map ψ₂ = (N : K) • 1 ∧
      U.map ψ₂ * (Matrix.of fun i k => ψ₂ (ψ (h (I i) k))) * P.map (ψ₂.comp ψ) =
        (N : K) • P.map (ψ₂.comp ψ) := by
    intro K _ ψ₂
    have hx1 : spMap ψ₂ ≫ spMap ψ ≫ x = spMap (ψ₂.comp ψ) ≫ x := by
      rw [← Category.assoc, GlobalTheory.ShFam.Pad.Guard.sp_comp]
    have hPm : P.map (ψ₂.comp ψ) = (P.map ψ).map ψ₂ := by ext; simp
    have hHm : (Matrix.of fun i k => ψ₂ (ψ (h (I i) k))) =
        (Matrix.of fun i k => ψ (h (I i) k)).map ψ₂ := by ext; simp
    refine ⟨hx1, fun i => ?_, ?_, ?_, ?_⟩
    · have := GlobalTheory.LatDRFree.comb_map Z.t ψ₂ (hu i).2
      simp only [GlobalTheory.HTPres.bc_bc] at this
      rw [hx1] at this
      exact this
    · rw [hPm, ← Matrix.map_mul, hS.1]; ext; simp
    · rw [hHm, ← Matrix.map_mul, hS.2.1]; ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
    · rw [hHm, hPm, ← Matrix.map_mul, ← Matrix.map_mul, hS.2.2.1]; ext; simp
  refine ⟨N, u, hN, fun K _ ψ₂ φ hφ => ?_, fun p _ ψ₃ φ hφ => ?_⟩
  · obtain ⟨hx1, hc, S1, S2, S3⟩ := hbc ψ₂
    have hφ' : spMap (ψ₂.comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) := by
      rw [← Category.assoc, ← hx1]; simpa only [Category.assoc] using hφ
    obtain ⟨dk, hd⟩ := hunit φ D hD
    obtain ⟨nk, hn⟩ := hunit φ N hN
    rw [hx1]
    obtain ⟨h1, h2⟩ := split_basis Z x τ he hP (ψ₂.comp ψ) φ hφ' hd hn S1 S2 S3 hc
    refine ⟨h1, fun w hw => ?_⟩
    obtain ⟨cf, -, -, hA⟩ := h2 w hw
    exact ⟨_, (hA _).2 rfl, fun a ha => (hA a).1 ha⟩
  · obtain ⟨hx1, hc, S1, S2, S3⟩ := hbc ((intO ℂ_[p]).subtype.comp ψ₃)
    have hφ' : spMap (((intO ℂ_[p]).subtype.comp ψ₃).comp ψ) ≫ x ≫ Z.s = spMap (φ.comp β) := by
      rw [← Category.assoc, ← hx1]; simpa only [Category.assoc] using hφ
    obtain ⟨dk, hd⟩ := hunit φ D hD
    obtain ⟨nk, hn⟩ := hunit φ N hN
    obtain ⟨δ, hδ, hlat⟩ := hL.2 p (ψ₃.comp ψ)
    refine ⟨δ, hδ, fun w hw => ?_⟩
    rw [hx1] at hw ⊢
    obtain ⟨-, h2⟩ := split_basis Z x τ he hP _ φ hφ' hd hn S1 S2 S3 hc
    obtain ⟨cf, hcf, hE, hA⟩ := h2 w hw
    refine Iff.trans ?_ (hlat cf w hcf).symm
    have hNa : ∀ i, (N : ℂ_[p]) * (nk • Matrix.mulVec (Matrix.of fun i k => ((intO ℂ_[p]).subtype.comp ψ₃) (ψ (h (I i) k))) cf) i = (fun k => ((intO ℂ_[p]).subtype.comp ψ₃) (ψ (h (I i) k))) ⬝ᵥ cf := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (N : ℂ_[p]) nk, hn, one_mul]
      rfl
    constructor
    · rintro ⟨a, ha, hca⟩ j
      rw [(hA a).1 hca] at ha
      obtain ⟨α, hα⟩ := hS.2.2.2 j
      have hα' : Matrix.vecMul (fun k => ((intO ℂ_[p]).subtype.comp ψ₃) (ψ (h j k)))
          (P.map (((intO ℂ_[p]).subtype.comp ψ₃).comp ψ)) =
          ∑ i, ((intO ℂ_[p]).subtype.comp ψ₃) (α i) •
            Matrix.vecMul (fun k => ((intO ℂ_[p]).subtype.comp ψ₃) (ψ (h (I i) k)))
              (P.map (((intO ℂ_[p]).subtype.comp ψ₃).comp ψ)) := by
        funext k
        have := congrArg (fun v => ((intO ℂ_[p]).subtype.comp ψ₃) (v k)) hα
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, RingHom.map_vecMul] at this
        simpa [Finset.sum_apply, Matrix.map_map, Function.comp_def] using this
      show (fun k => ((intO ℂ_[p]).subtype.comp ψ₃) (ψ (h j k))) ⬝ᵥ cf ∈ intO ℂ_[p]
      rw [split_form hd hE _ _ _ hα']
      refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ (ψ₃ (α i)).2 ?_
      show ‖_‖ ≤ 1
      rw [← hNa]
      exact ha i
    · intro hj
      refine ⟨_, fun i => ?_, (hA _).2 rfl⟩
      rw [hNa]
      exact hj (I i)

end GlobalTheory.ArLieBase
