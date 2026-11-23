import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelTrivializingBlowupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkFlagPairIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalCommonRefinementModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDegreeMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullbackCompositeStatement

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CkPairWd

open GlobalTheory.Vert.Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
  [CharZero O] [CharP (ResidueField O) p]

theorem hom_eq {Z₁ Z : Vert.Model O} (a b : Hom Z₁ Z) (h : a.f = b.f) : a = b := by
  cases a; cases b; cases h; rfl

theorem picSymPull_comp {X Y W : Scheme.{0}} (g : W ⟶ Y) (f : Y ⟶ X) (y : PicSym X) :
    picSymPull (g ≫ f) y = picSymPull g (picSymPull f y) := by
  have : (picSymPull (g ≫ f)).toLinearMap = (picSymPull g).toLinearMap ∘ₗ (picSymPull f).toLinearMap :=
    picSym_linearMap_ext fun n c => by
      simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, map_prod, picSymPull_c1Pic, pull_comp]
  exact LinearMap.congr_fun this y

def ckLin {Z : ITh} {r : ℕ} (P : FPair Z r) (k : ℕ) : Z.Ch →ₗ[ℚ] ℚ :=
  ∑ i, (Z.capDeg (P.Dv i)) ∘ₗ LinearMap.mulLeft ℚ (Gk Z k (Z.c1 (P.x i)) (Z.c1 (P.x' i)))

theorem ckLin_apply {Z : ITh} {r : ℕ} (P : FPair Z r) (k : ℕ) (Q : Z.Ch) : ckLin P k Q = ck P k Q := by
  simp [ckLin, ck, LinearMap.sum_apply]

theorem ck_pull {B B₁ : Vert.Model O} (hB : IsNormalScheme B.X) (h : Hom B₁ B) (h0 : h.relDim = 0)
    {E E' : B.X.Modules} {φ : B.GenIso E E'} {F F' : B₁.X.Modules} {ψ : B₁.GenIso F F'} {r : ℕ}
    (P : FlagPair φ r) (P₁ : FlagPair ψ r)
    (hx : ∀ i, (P₁.toFPair p).x i = smallPull h.f ((P.toFPair p).x i))
    (hx' : ∀ i, (P₁.toFPair p).x' i = smallPull h.f ((P.toFPair p).x' i))
    (hD : ∀ i, (P₁.toFPair p).Dv i = vPullQ h.comp_str ((P.toFPair p).Dv i)) (k : ℕ) (y : PicSym B.X) :
    ck (P₁.toFPair p) k (picSymPull h.f y) = h.fibreDeg 1 * ck (P.toFPair p) k y := by
  have hp := (GlobalTheory.T.cap_degree_finite_pullback O p B hB B₁ h h0).2
  have hc : ∀ a : SmallPic B.X, (symOf (smallPull h.f a) : PicSym B₁.X) = picSymPull h.f (symOf a) :=
    fun a => (symMap_symOf _ a).symm
  have hG : ∀ (a b : PicSym B.X), Gk (B₁.toITh p) k (picSymPull h.f a) (picSymPull h.f b) =
      picSymPull h.f (Gk (B.toITh p) k a b) := fun a b => by
    simp [Gk, map_sum, map_mul, map_pow]
  simp only [ck, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hx, hx', hD, hc, hc, hG, ← map_mul]
  exact hp _ _

theorem exists_pull_comp {B B₁ B₂ : Vert.Model O} {f : B₁.X ⟶ B.X} (hf : f ≫ B.str = B₁.str) (h : Hom B₂ B₁)
    {c : B₂.X ⟶ B.X} (hc : c ≫ B.str = B₂.str) (e : h.f ≫ f = c) {E E' : B.X.Modules} {φ : B.GenIso E E'} {r : ℕ}
    (P : FlagPair (φ.pull hf) r) : ∃ P₂ : FlagPair (φ.pull hc) r, ∀ i,
      (P₂.toFPair p).x i = smallPull h.f ((P.toFPair p).x i) ∧
      (P₂.toFPair p).x' i = smallPull h.f ((P.toFPair p).x' i) ∧
      (P₂.toFPair p).Dv i = vPullQ h.comp_str ((P.toFPair p).Dv i) := by
  obtain ⟨P₁, h₁⟩ := GlobalTheory.T.flag_pair_pullback O p B₁ B₂ h.f h.comp_str _ _ (φ.pull hf) r P
  obtain ⟨P₂, h₂⟩ := GlobalTheory.T.flag_pair_pullback_composite O p B B₁ B₂ f hf h.f h.comp_str c hc e E E' φ r P₁
  exact ⟨P₂, fun i => ⟨(h₂ i).1.trans (h₁ i).1, (h₂ i).2.1.trans (h₁ i).2.1, (h₂ i).2.2.trans (h₁ i).2.2⟩⟩

theorem ckP_spec : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X →
    ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r k : ℕ), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r →
    IsCk p φ r k (ckP p φ r k) ∧ (∀ f, IsCk p φ r k f → f = ckP p φ r k) ∧
    ∀ (P : GlobalTheory.Vert.Model.FlagPair φ r) (Q : PicSym B.X), ckP p φ r k Q = ck (P.toFPair p) k Q := by
  intro O _ _ _ p _ _ _ B hB E E' φ r k hE hE'

  obtain ⟨B', π', hB', hπ', hP'⟩ := GlobalTheory.T.normal_model_trivializing_blowup O p B hB 1 (fun _ => r) (fun _ => E) (fun _ => E')
    (fun _ => φ) (fun _ => ⟨hE, hE'⟩)
  obtain ⟨P'⟩ := hP' 0
  have hdeg' := (GlobalTheory.T.cap_degree_finite_pullback O p B hB B' π' hπ').1
  let f₀ : PicSym B.X →ₗ[ℚ] ℚ :=
    (π'.fibreDeg 1)⁻¹ • ((ckLin (P'.toFPair p) k) ∘ₗ (picSymPull π'.f).toLinearMap)
  have hf₀ : ∀ Q, f₀ Q = (π'.fibreDeg 1)⁻¹ * ck (P'.toFPair p) k (picSymPull π'.f Q) := fun Q => by
    rw [← ckLin_apply]; rfl
  have hex : IsCk p φ r k f₀ := by
    intro M hM hM0 Q
    obtain ⟨B₃, h₁, h₂, hB₃, h₁0, h₂0, e⟩ := GlobalTheory.T.normal_common_refinement_models O p B M.B B' M.π π' hM0 hπ'
    have hc : (h₁.f ≫ M.π.f) ≫ B.str = B₃.str := (h₁.comp M.π).comp_str
    obtain ⟨Pa, ha⟩ := exists_pull_comp p M.π.comp_str h₁ hc rfl M.pair
    obtain ⟨Pb, hb⟩ := exists_pull_comp p π'.comp_str h₂ hc e.symm P'
    have hab := GlobalTheory.T.ck_flag_pair_independent O p B₃ hB₃ _ _ (φ.pull hc) r k Pa Pb (picSymPull (h₁.f ≫ M.π.f) Q)
    have ea := ck_pull p hM h₁ h₁0 M.pair Pa (fun i => (ha i).1) (fun i => (ha i).2.1) (fun i => (ha i).2.2) k
      (picSymPull M.π.f Q)
    have eb := ck_pull p hB' h₂ h₂0 P' Pb (fun i => (hb i).1) (fun i => (hb i).2.1) (fun i => (hb i).2.2) k
      (picSymPull π'.f Q)
    rw [← picSymPull_comp] at ea eb
    rw [← e] at eb
    have d₁ := GlobalTheory.T.fibre_degree_multiplicative O B M.B B₃ h₁ M.π h₁0 hM0
    have d₂ := GlobalTheory.T.fibre_degree_multiplicative O B B' B₃ h₂ π' h₂0 hπ'
    rw [hom_eq (h₁.comp M.π) (h₂.comp π') e] at d₁
    have hpos := (GlobalTheory.T.cap_degree_finite_pullback O p M.B hM B₃ h₁ h₁0).1
    rw [hf₀]
    change ck (M.pair.toFPair p) k _ = _
    have hh : h₁.fibreDeg 1 * M.π.fibreDeg 1 = h₂.fibreDeg 1 * π'.fibreDeg 1 := d₁.symm.trans d₂
    have key := ea.symm.trans (hab.trans eb)
    refine mul_left_cancel₀ hpos.ne' (key.trans ?_)
    rw [← mul_assoc, hh, mul_assoc, mul_inv_cancel_left₀ hdeg'.ne']
  have hck : IsCk p φ r k (ckP p φ r k) := Classical.epsilon_spec ⟨f₀, hex⟩
  let M' : FlagModel φ r := ⟨B', π', P'⟩
  refine ⟨hck, fun f hf => ?_, fun P Q => ?_⟩
  · refine LinearMap.ext fun Q => ?_
    have h1 := hf M' hB' hπ' Q
    have h2 := hck M' hB' hπ' Q
    exact mul_left_cancel₀ hdeg'.ne' (h1.symm.trans h2)
  · obtain ⟨P₀, h₀⟩ := GlobalTheory.T.flag_pair_pullback O p B B (𝟙 B.X) (Hom.id B).comp_str E E' φ r P
    let M₀ : FlagModel φ r := ⟨B, Hom.id B, P₀⟩
    have hM₀ : (Hom.id B).relDim = 0 := by simp [Hom.relDim]
    have h1 := hck M₀ hB hM₀ Q
    have h2 := ck_pull p hB (Hom.id B) hM₀ P P₀ (fun i => (h₀ i).1) (fun i => (h₀ i).2.1)
      (fun i => (h₀ i).2.2) k Q
    have hpos := (GlobalTheory.T.cap_degree_finite_pullback O p B hB B (Hom.id B) hM₀).1
    exact mul_left_cancel₀ hpos.ne' (h1.symm.trans h2)

end GlobalTheory.CkPairWd

end
