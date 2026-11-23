import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAgree
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

section Bundle

def Adapted {Y : Scheme.{0}} {N : Y.Modules} {r : ℕ} (fl : Vert.Flag N r) {W : Y.Opens} (s : Fin r → Γ(N, W)) : Prop :=
  IsFrame s ∧ ∀ k : Fin (r + 1), ∃ t : Fin k → Γ(fl.F k, W), IsFrame t ∧
    ∀ i : Fin k, (fl.ι k).app W (t i) = s (Fin.castLE (Nat.lt_succ_iff.1 k.2) i)

variable {B Y : Scheme.{0}} {M : B.Modules} {r : ℕ} (hM : IsVB M r) (π : Y ⟶ B)

def coordAt {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f) {K : Type} [CommRing K] (y : Sp K ⟶ Y) {W : Y.Opens}
    (hWV : W ≤ π ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W) (s : Γ((Scheme.Modules.pullback π).obj M, W)) : Fin r → K :=
  haveI := hM.isQuasicoherent
  fun b => TangentOrigin.evalPt y W hy (((hf.pullback π).basis hWV).repr s b)

def FlagMat (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f)
    {K : Type} [CommRing K] (y : Sp K ⟶ Y) (A : Matrix (Fin r) (Fin r) K) : Prop :=
  IsUnit A.det ∧ ∀ (k : Fin (r + 1)) (W : Y.Opens) (hWV : W ≤ π ⁻¹ᵁ V) (t : Γ(fl.F k, W)) (hy : ⊤ ≤ y ⁻¹ᵁ W),
    ∃ cf : Fin r → K, (∀ l : Fin r, (k : ℕ) ≤ l → cf l = 0) ∧
      coordAt hM π hf y hWV hy ((fl.ι k).app W t) = Matrix.vecMul cf A

def StepIso (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {T : Scheme.{0}} {x : T ⟶ B}
    (fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r) (y : T ⟶ Y) (w : y ≫ π = x) : Prop :=
  ∀ i, ∃ e : (Scheme.Modules.pullback y).obj (fl.F i) ≅ fl'.F i,
    e.hom ≫ fl'.ι i = (Scheme.Modules.pullback y).map (fl.ι i) ≫
      (Scheme.Modules.pullbackComp y π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M

variable {hM π}

theorem FlagMat.mul {fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r} {V : B.Opens} {f : Fin r → Γ(M, V)}
    {hf : IsFrame f} {K : Type} [CommRing K] {y : Sp K ⟶ Y} {A T : Matrix (Fin r) (Fin r) K}
    (h : FlagMat hM π fl hf y A) (hT : IsUnit T.det) (hT' : ∀ i j, i < j → T i j = 0) :
    FlagMat hM π fl hf y (T * A) := by
  refine ⟨by rw [Matrix.det_mul]; exact hT.mul h.1, fun k W hWV t hy => ?_⟩
  obtain ⟨cf, h1, h2⟩ := h.2 k W hWV t hy
  have := T.invertibleOfIsUnitDet hT
  have hb : T.BlockTriangular OrderDual.toDual := fun a b hab => hT' a b hab
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨Matrix.vecMul cf T⁻¹, fun l hl => ?_, ?_⟩
  · rw [Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m l with hm | hm
    · rw [show T⁻¹ m l = 0 from hi hm, mul_zero]
    · rw [h1 m (hl.trans hm), zero_mul]
  · rw [h2, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]

end Bundle

def lieMat (dual : Bool) {r : ℕ} {K : Type} [CommRing K] (d : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  cond dual ((Matrix.transpose d⁻¹).submatrix Fin.rev id) d

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def AgreeAt {Bs Bg Y : Scheme.{0}} {M : Bs.Modules} {r : ℕ} (hM : IsVB M r) (jB : Bg ⟶ Bs) (u : FrAssign Z M r jB)
    (π : Y ⟶ Bs) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (dual : Bool) {K : Type} [CommRing K]
    (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (x : Sp K ⟶ Z.X) (v : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)) : Prop :=
  ∀ (V : Bs.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin r) (Fin r) K),
    (∀ i, IsCombAtG Z.t x (u V f hf K xb hx) (d i) (v i)) → FlagMat hM π fl hf y (lieMat dual d)

def Bears {ι : Type} {rk : ι → ℕ} (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a))
    {Bs Bg Y : Scheme.{0}} {M : ι → Bs.Modules} (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z)
    (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)) {K : Type} [CommRing K]
    (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) {χ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z χ x) : Prop :=
  y ≫ π = xb ≫ jB ∧ x = xb ≫ πB ≫ genι Z ∧ xb ≫ πB ≫ genStr Z = spMap χ ∧
    ∀ a, AgreeAt Z (hM a) jB (u a) π (fl a) (dual a) y xb x fun i => g.v (emb a) (Fin.cast (hr a) i)

end Lie

end GlobalTheory.FlagCls

end
