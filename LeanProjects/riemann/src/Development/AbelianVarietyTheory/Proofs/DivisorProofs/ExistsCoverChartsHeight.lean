import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartResult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogValsOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtLetter

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open GlobalTheory.HalfGeo GlobalTheory.ConstLat
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.EqHalf.Frame

attribute [local instance] Over.cartesianMonoidalCategory

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F}
  (C : GlobalTheory.ShFam.FlagCpt Z ε)

omit [NumberField F] in

theorem isFlagFrame_cast {g : ℕ} (hg : (letters Dw).length = g) :
    IsFlagFrame Z.t (C.π ≫ GlobalTheory.Toroidal.genι Z)
      (fun i : Fin g => C.f0.v ((letters Dw).get (Fin.cast hg.symm i)).1 ((letters Dw).get (Fin.cast hg.symm i)).2)
      (fun y i => (fr C y).v ((letters Dw).get (Fin.cast hg.symm i)).1 ((letters Dw).get (Fin.cast hg.symm i)).2)
      (fun y i => dg C y ((letters Dw).get (Fin.cast hg.symm i)).1 ((letters Dw).get (Fin.cast hg.symm i)).2) := by
  subst hg
  exact isFlagFrame_concat C

theorem exists_open (V : Cover C.Y) (ρ' : V.X ⟶ Z.X) (e₄ : V.j ≫ ρ' = V.π ≫ C.π ≫ GlobalTheory.Toroidal.genι Z) :
    ∃ W : C.Y.X.Opens, genericPoint C.Y.X ∈ W ∧ (∀ x : V.G, V.π x ∈ W → ρ' (V.j x) ∈ Set.range Z.j) ∧
      ρ' (genericPoint V.X) ∈ Set.range Z.j := by
  haveI := Z.jQ_open
  let W : C.Y.X.Opens := C.π ⁻¹ᵁ Z.jQ.opensRange
  have hW : genericPoint C.Y.X ∈ W := by
    letI := (GlobalTheory.ShFam.constF ε C.Y).toAlgebra
    refine ⟨GlobalTheory.AllWt.ptF C.y0 (IsLocalRing.closedPoint _), ?_⟩
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun q : Sp C.Y.Fn ⟶ _ => q (IsLocalRing.closedPoint _)) C.y0_x).trans ?_)
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg C.π Scheme.fromSpecStalk_closedPoint)
  have hrange (x : V.G) (hx : V.π x ∈ W) : ρ' (V.j x) ∈ Set.range Z.j := by
    obtain ⟨q, hq⟩ := hx
    refine ⟨q, ?_⟩
    rw [← Scheme.Hom.comp_apply, e₄, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hq]
    rfl
  refine ⟨W, hW, hrange, ?_⟩
  have h₁ : V.j (genericPoint V.G) = genericPoint V.X :=
    ((GlobalTheory.HtGen.SplitCover.j_gen_specializes V).antisymm (genericPoint_specializes _)).eq
  have h₂ : V.π (genericPoint V.G) = genericPoint C.Y.X := (V.φ_eq_fnMap.1.antisymm (genericPoint_specializes _)).eq
  rw [← h₁]
  exact hrange _ (h₂ ▸ hW)

end Flags

theorem exists_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    {t : SAB H X} {F : Type} [Field F] [NumberField F] {Y : Var F} {g N : ℕ} (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X)
    (hρ : V.j ≫ ρ' = V.π ≫ ρ) {u₀ : Fin g → (Sp (DualNumber Y.Fn) ⟶ t.G.left)}
    {f : ∀ y : Y.X, Fin g → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)} {d : Y.X → Fin g → Y.Fnˣ}
    (hf : IsFlagFrame t ρ u₀ f d)
    (P : ∀ (U : V.X.Opens) (_ : IsAffineOpen U) (k : ℕ), (Fin k → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) →
      (Fin N → Fin k → Γ(V.X, U)) → Prop)
    (hD : ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (k : ℕ) (e : Fin k → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)),
      IsTanBasis t (R := Γ(V.X, U)) (hU.fromSpec ≫ ρ') e → ∃ h : Fin N → Fin k → Γ(V.X, U), P U hU k e h) :
    ∃ (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (U : V.X → V.X.Opens) (hU : ∀ x, IsAffineOpen (U x)) (k : V.X → ℕ)
      (e : ∀ x, Fin (k x) → (Sp (DualNumber Γ(V.X, U x)) ⟶ t.G.left)) (h : ∀ x, Fin N → Fin (k x) → Γ(V.X, U x))
      (M : V.X → Matrix (Fin N) (Fin g) V.G.functionField),
      (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) ∧ (∀ x, x ∈ U x) ∧
      (∀ x, IsTanBasis t ((hU x).fromSpec ≫ ρ') (e x)) ∧ (∀ x, P (U x) (hU x) (k x) (e x) (h x)) ∧
      ∀ x, ChartVal V ρ' f T (hU x) (e x) (h x) (M x) := by
  classical
  choose cf hc₁ hc₂ hc₃ using hf.tri
  let T : Y.X → Matrix (Fin g) (Fin g) Y.Fn := fun y => Matrix.of fun k i => cf y i k
  have hT (y : Y.X) : (T y).BlockTriangular id := fun k i h => hc₂ y i k h
  have hTu (y : Y.X) : IsUnit (T y).det := by
    rw [Matrix.det_of_isUpperTriangular (hT y), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ h => (d y i).ne_zero ((hc₁ y i).symm.trans h)
  have hch : ∀ x : V.X, ∃ (U : V.X.Opens) (hU : IsAffineOpen U) (n : ℕ)
      (e : Fin n → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (h : Fin N → Fin n → Γ(V.X, U))
      (M : Matrix (Fin N) (Fin g) V.G.functionField),
      x ∈ U ∧ IsTanBasis t (hU.fromSpec ≫ ρ') e ∧ P U hU n e h ∧ ChartVal V ρ' f T hU e h M := by
    intro x
    obtain ⟨⟨U, hU⟩, n, e, hx, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H X t V.X ρ' x
    obtain ⟨h, hh⟩ := hD U hU n e he
    obtain ⟨M, hM⟩ := chartSt_holds E H X t F Y V ρ' ρ hρ g u₀ f T hf.tan hTu hc₃ U hU n e he _ h
    exact ⟨U, hU, n, e, h, M, hx, he, hh, hM⟩
  choose U hU n e h M hx he hd hM using hch
  exact ⟨T, U, hU, n, e, h, M, fun y => ⟨hT y, hc₁ y⟩, hx, he, hd, hM⟩

section Setup

variable {D : D7} (O : Setup D) (c : O.s.Comp)

theorem isFlagFrame_frAt : IsFlagFrame O.s.T.Z.t ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z)
    (fun i => (O.Φ.C c).f0.v (letterAt O i).1 (letterAt O i).2)
    (fun y i => (frAt O c y).v (letterAt O i).1 (letterAt O i).2) (dgOf O c) :=
  isFlagFrame_cast (O.Φ.C c) (length_letters O)

variable {v : HeightOneSpectrum (𝓞 D.what₂.LL)} [hp : Fact (resP v).Prime] (e : GlobalTheory.TrueGeo.Ext v) (y : AlgPt (O.Φ.C c).Y)

theorem uAt_eq : uAt O c e y =
    fun l => spMap (dualMap (psiAt O c e y)) ≫ (frAt O c (below y.1)).v (letterAt O l).1 (letterAt O l).2 :=
  funext fun l => uAt.eq_1 O c e y l

theorem ptData_intro (hp' : (resP v).Prime) (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ)
    {Ch : Type} (inC : Ch → Prop)
    (M : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) (AlgebraicClosure D.what₂.LL))
    (xO : Sp ↥(intO ℂ_[resP v]) ⟶ O.s.T.Z.X)
    (χ : Fin (D.R.f * O.N + D.R.f * O.N) → TorsChar O.s.T.Z.t xO (resP v ^ n))
    (h₁ : spMap (intO ℂ_[resP v]).subtype ≫ xO = ptAt O c e y) (h₂ : Gens χ) (h₃ : WeilData O xO χ (gram O.S.Dw b))
    (h₄ : Equivar O.s.T.Z.t χ (chiAct O.S.Dw b))
    (h₅ : ∀ a, inC a → DlogVals O.s.T.Z.t xO χ (uAt O c e y) ((M a).map (ioOf (resP v) e))) :
    PtData O c b n hp' e y inC M := by
  have e₀ : hp = PtData._proof_1 hp' := rfl
  subst e₀
  rw [PtData.eq_1]
  exact ⟨xO, χ, h₁, h₂, h₃, h₄, h₅⟩

end Setup

open GlobalTheory.Mean4 GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published in

theorem exists_frame : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ (c : O.s.Comp)
    (b : Module.Basis (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ O.S.Dw.La) (n : ℕ), 3 ≤ n →
    ∃ (V : Cover (O.Φ.C c).Y) (W : (O.Φ.C c).Y.X.Opens) (Ch : Type) (U : Ch → V.X.Opens)
      (H : Ch → Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N)) V.G.functionField)
      (T' : (O.Φ.C c).Y.X → Matrix (Fin (D.R.f * O.N)) (Fin (D.R.f * O.N)) (O.Φ.C c).Y.Fn),
      genericPoint (O.Φ.C c).Y.X ∈ W ∧ (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
      (∀ y, (T' y).BlockTriangular id ∧ ∀ i, T' y i i = (dgOf O c y i : (O.Φ.C c).Y.Fn)) ∧
      LineBase V (dgOf O c) (wholeA O c T R) p ∧ LineBase V (dgOf O c) (eigA O c T R) p ∧
      (∀ a, ChartReg V (U a) (H a) T') ∧
      AtTest V W p fun v e y z yt => ∀ hp : (resP v).Prime,
        PtData O c b n hp e y (fun a => ⊤ ≤ yt ⁻¹ᵁ U a) (fun a => GlobalTheory.WholeFlag.valMat V (H a) (T' (below y.1)) z) := by
  intro _ _ _ _ _ D O _ T R _ p hp _ c b n _
  classical
  haveI := Fact.mk hp
  obtain ⟨hX, hN, M₀, ρ₀, hM, hρ⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e)
    O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hj := O.indef
  obtain ⟨V₀, hV₀⟩ := GlobalTheory.EqHalf.LineCover.exists_cover D O T R p c
  obtain ⟨V, a, a', ρ', e₀, e₁, e₂, e₃, e₄, hz, hζ, hs⟩ :=
    GlobalTheory.T.cover_refinement_exists _ _ _ O.s.T.Z.t _ _ M₀ ρ₀ V₀ (p ^ n) (pow_ne_zero _ hp.ne_zero)
  rw [hρ] at e₄
  obtain ⟨hL₁, hL₂⟩ := hV₀ V a a' e₀ e₁ e₂ e₃
  obtain ⟨W, hW, hrange, hgp⟩ := exists_open (O.Φ.C c) V ρ' e₄
  obtain ⟨ch, hG, hE, hD, hI⟩ := GlobalTheory.EqFamily.exists_family _ _ _ _ _ _ O.s.T.Z (by omega) V.X ρ' p n V.normal hz hζ hs hgp _ b
  have hf := isFlagFrame_frAt O c
  obtain ⟨T', U, hU, k, e, h, M, hT, hx, he, hd, hM⟩ := exists_charts V ρ' _ e₄ hf
    (fun U hU k e h => ∀ (x : Γ(V.X, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ V.X), spMap x ≫ hU.fromSpec = y →
      ∀ j, DlogIs O.s.T.Z.t p n (ch j y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) hD
  refine ⟨V, W, V.X, U, M, T', hW, fun x _ => ⟨x, hx x⟩, hT, hL₁, hL₂, fun a z hz k l => ?_,
    fun v hv ε y hy z yt hz hyt hp' => ?_⟩
  · obtain ⟨α, b, -, -, hb⟩ := hM a z hz
    exact ⟨_, (hb k l).symm⟩
  subst hv
  obtain ⟨yO, h₁, h₂, h₃⟩ := GlobalTheory.HalfGeo.DlogFrame.dlogVals_valMat _ _ _ O.s.T.Z.t _ _ V ρ' _ e₄ _
    (fun y i => (frAt O c y).v (letterAt O i).1 (letterAt O i).2) T' v n ε y z yt hz hyt (psiAt O c ε y) (psiAt.eq_1 O c ε y)
  refine ptData_intro O c ε y hp' b n _ _ (yO ≫ ρ') (fun m => ch m yO) (h₂.trans (ptAt.eq_1 O c ε y).symm) (hG yO) ?_
    (hE yO) fun a ha => ?_
  swap
  · rw [uAt_eq]
    exact h₃ _ (U a) (hU a) _ (e a) (h a) (M a) (he a) (hM a) ha fun x hx => hd a x yO hx
  rw [WeilData.eq_1]
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.DetHT.exists_lift_int O.s.T.Z (z ≫ V.j ≫ ρ') (by
    rintro _ ⟨q, rfl⟩
    obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure D.what₂.LL)) _ _
    refine hrange (below z) ?_
    rw [← hz] at hy
    exact hy)
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure D.what₂.LL) := Algebra.IsAlgebraic.trans ℚ D.what₂.LL _
  refine hI yO _ (ioOf (resP v) ε) z₀
    (fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic x)) ?_
  rw [← Category.assoc, h₁, hz₀, Category.assoc, Category.assoc]

end GlobalTheory.EqHalf.Frame

end
