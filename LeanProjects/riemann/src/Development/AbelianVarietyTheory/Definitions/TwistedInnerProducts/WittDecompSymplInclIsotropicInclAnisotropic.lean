import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel

variable {D : D7}

def pairS (T : HSp D) {ρ : ℕ} (x x' : Mx D T.rank ρ) : AE D := (adj x' ⬝ (gA T ⬝ x)).trace

def pairT (S : HSp D) {ρ : ℕ} (ξ η : Mx D ρ S.rank) : AE D := (giA S ⬝ (adj η ⬝ ξ)).trace

theorem pairT_adj (S : HSp D) {ρ : ℕ} (c : AE D) (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) :
    pairT S ξ (c • (adj y ⬝ gA S)) = (cA D c • (y ⬝ ξ)).trace := by
  rw [pairT, adj_smul, adj_mul, adj_adj, adj_gA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, giA_gA_cancel]

namespace HypDec

section Source

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)

def extX : Mx D T.rank ρ →+ WO S T where
  toFun x := x ⬝ d.pX
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

def extY : Mx D T.rank ρ →+ WO S T where
  toFun x := x ⬝ d.pY
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

def ext0 : WO S₀ T →+ WO S T where
  toFun w := w ⬝ d.p0
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

theorem extX_apply (x : Mx D T.rank ρ) : d.extX T x = x ⬝ d.pX := rfl

theorem extY_apply (x : Mx D T.rank ρ) : d.extY T x = x ⬝ d.pY := rfl

theorem matrixExtendByZero_apply (w : WO S₀ T) : d.ext0 T w = w ⬝ d.p0 := rfl

def coordS : WO S T ≃+ Mx D T.rank ρ × WO S₀ T × Mx D T.rank ρ where
  toFun w := (w ⬝ d.jX, w ⬝ d.j0, w ⬝ d.jY)
  invFun p := d.extX T p.1 + d.ext0 T p.2.1 + d.extY T p.2.2
  left_inv w := by
    simp only [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.mul_assoc]
    rw [← Matrix.mul_add, ← Matrix.mul_add, sum_eq_one, Matrix.mul_one]
  right_inv p := by
    simp only [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
      pY_jY, p0_jX, p0_j0, p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  map_add' x y := Prod.ext (Matrix.add_mul _ _ _) (Prod.ext (Matrix.add_mul _ _ _) (Matrix.add_mul _ _ _))

theorem hO_coordS (w w' : WO S T) : hO S T w w' =
    pairS T (w ⬝ d.jX) (w' ⬝ d.jY) + hO S₀ T (w ⬝ d.j0) (w' ⬝ d.j0) + pairS T (w ⬝ d.jY) (w' ⬝ d.jX) := by
  simp only [hO_eq_trace, pairS, adj_mul]
  rw [d.giA_eq, Matrix.add_mul, Matrix.add_mul, trace_add, trace_add, Matrix.mul_assoc, trace_mul_comm,
    Matrix.mul_assoc d.j0, trace_mul_comm d.j0, Matrix.mul_assoc d.jY, trace_mul_comm d.jY]
  simp only [Matrix.mul_assoc]

theorem hO_ext (x x' y y' : Mx D T.rank ρ) (w w' : WO S₀ T) :
    hO S T (d.extX T x + d.ext0 T w + d.extY T y) (d.extX T x' + d.ext0 T w' + d.extY T y') =
      pairS T x y' + hO S₀ T w w' + pairS T y x' := by
  rw [d.hO_coordS]
  simp only [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
    pY_jY, p0_jX, p0_j0, p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]

theorem symplOH_extY_extY (y y' : Mx D T.rank ρ) : symplOH S T (d.extY T y) (d.extY T y') = 0 := by
  have h := d.hO_ext T 0 0 y y' 0 0
  simp only [map_zero, zero_add, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem symplOH_extX_extX (x x' : Mx D T.rank ρ) : symplOH S T (d.extX T x) (d.extX T x') = 0 := by
  have h := d.hO_ext T x x' 0 0 0 0
  simp only [map_zero, add_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_extDual_extAnisotropic (y : Mx D T.rank ρ) (w : WO S₀ T) : symplOH S T (d.extY T y) (d.ext0 T w) = 0 := by
  have h := d.hO_ext T 0 0 y 0 0 w
  simp only [map_zero, zero_add, add_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_extIsotropic_extAnisotropic (x : Mx D T.rank ρ) (w : WO S₀ T) : symplOH S T (d.extX T x) (d.ext0 T w) = 0 := by
  have h := d.hO_ext T x 0 0 0 0 w
  simp only [map_zero, zero_add, add_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_extAnisotropic_extAnisotropic (w w' : WO S₀ T) : symplOH S T (d.ext0 T w) (d.ext0 T w') = symplOH S₀ T w w' := by
  have h := d.hO_ext T 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  rw [symplOH_eq, h, symplOH_eq]

theorem symplOH_extX_extY (x y : Mx D T.rank ρ) : symplOH S T (d.extX T x) (d.extY T y) = trHalf D (pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplOH_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

def qS (c : skewA D ρ) (x : Mx D T.rank ρ) : AF D.host.F := symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1))

theorem extX_levi (a : GL (Fin ρ) (AE D)) (x : Mx D T.rank ρ) : d.extX T x ⬝ mt S (d.levi a) = d.extX T (x ⬝ a.1) := by
  rw [extX_apply, extX_apply, Matrix.mul_assoc, pX_levi, Matrix.mul_assoc]

theorem extX_nC (c : skewA D ρ) (x : Mx D T.rank ρ) :
    d.extX T x ⬝ mt S (d.nC c) = d.extX T x + d.extY T (x ⬝ c.1) := by
  rw [extX_apply, extY_apply, Matrix.mul_assoc, pX_nC, Matrix.mul_add, Matrix.mul_assoc]

theorem extX_nB (b : Mx D ρ S₀.rank) (x : Mx D T.rank ρ) :
    d.extX T x ⬝ mt S (d.nB b) =
      d.extX T x + d.ext0 T (x ⬝ b) - d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b))) := by
  rw [extX_apply, extY_apply, matrixExtendByZero_apply, Matrix.mul_assoc, pX_nB, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc,
    Matrix.mul_assoc]

theorem wittDecomp_homAction_extAnisotropic_equivariant (g : GA D S₀) (h : GA D T) (w : WO S₀ T) :
    actO S T (d.emb0 g) h (d.ext0 T w) = d.ext0 T (actO S₀ T g h w) := by
  simp only [actO_eq, matrixExtendByZero_apply, ← map_inv, Matrix.mul_assoc, wittDecomp_projAnisotropic_anisotropicEmbedding]

def mixS (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ)
    (x : Mx D T.rank ρ) : WO S₀ T → ℂ := fun w₀ =>
  ∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 ∂μ

variable {T} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrandS_eq (f : WO S T → ℂ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 =
      ψ (symplOH S T (d.extY T a) (d.extX T x)) * f (d.extY T a + d.extX T x + d.ext0 T w₀) := by
  simp only [heisO, zero_add, symplOH_zero_left, GlobalTheory.OrientedHeis.symplOH_add_left, wittDecomp_sympl_extDual_extAnisotropic,
    wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrandS_periodic {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) (w₀ : WO S₀ T)
    (γ : Mx D T.rank ρ) (hγ : γ ∈ ratMx D T.rank ρ) (a : Mx D T.rank ρ) :
    heisO ψ S T (d.extY T (γ + a)) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 =
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 := by
  obtain ⟨δ, hδ⟩ : d.extY T γ ∈ ratMx D _ _ := ratMx_mul hγ (rat_mem _)
  have h := hf.quasi δ (d.extY T a + d.extX T x + d.ext0 T w₀)
  rw [show ratW T S δ = d.extY T γ from hδ] at h
  rw [integrandS_eq, integrandS_eq, map_add (d.extY T), add_assoc (d.extY T γ), add_assoc (d.extY T γ), h, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, symplOH_extY_extY,
    wittDecomp_sympl_extDual_extAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.extY T γ) _), add_neg_cancel_right]

theorem integrableOn_mixS (hψ : Continuous ψ) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ)
    (w₀ : WO S₀ T) : IntegrableOn
      (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0) 𝓕 μ := by
  refine covolOne_integrableOn hμ _ ?_ (d.integrandS_periodic hf x w₀)
  have hc : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  simp only [integrandS_eq]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH hc continuous_const)).mul
    (hf.cont.comp ((hc.add continuous_const).add continuous_const))

theorem mixS_indep {μ μ' : Measure (Mx D T.rank ρ)} {𝓕 𝓕' : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) (hμ' : IsCovolOne (ratMx D T.rank ρ) μ' 𝓕') {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : d.mixS T ψ μ' 𝓕' f = d.mixS T ψ μ 𝓕 f := by
  funext x w₀
  exact covolOne_integral_eq hμ hμ' _ (d.integrandS_periodic hf x w₀)

end Source

section Target

variable {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)

def incX : Mx D ρ S.rank →+ WO S T where
  toFun ξ := d.jX ⬝ ξ
  map_zero' := Matrix.mul_zero _
  map_add' _ _ := Matrix.mul_add _ _ _

def incY : Mx D ρ S.rank →+ WO S T where
  toFun η := d.jY ⬝ η
  map_zero' := Matrix.mul_zero _
  map_add' _ _ := Matrix.mul_add _ _ _

def inc0 : WO S T₀ →+ WO S T where
  toFun w := d.j0 ⬝ w
  map_zero' := Matrix.mul_zero _
  map_add' _ _ := Matrix.mul_add _ _ _

def incAdj : Mx D S.rank ρ →+ WO S T where
  toFun y := d.incY S (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S))
  map_zero' := by rw [adj_zero, Matrix.zero_mul, smul_zero, map_zero]
  map_add' _ _ := by rw [adj_add, Matrix.add_mul, smul_add, map_add]

theorem incX_apply (ξ : Mx D ρ S.rank) : d.incX S ξ = d.jX ⬝ ξ := rfl

theorem incY_apply (η : Mx D ρ S.rank) : d.incY S η = d.jY ⬝ η := rfl

theorem wittDecomp_inclAnisotropicHom_apply (w : WO S T₀) : d.inc0 S w = d.j0 ⬝ w := rfl

theorem incAdj_apply (y : Mx D S.rank ρ) :
    d.incAdj S y = d.incY S (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)) := rfl

theorem wittDecomp_trace0Unit_mul_conj_neg_inv : incA D D.host.xi0 * cA D (incA D (-D.host.xi0⁻¹)) = 1 := by
  rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]

def coordT : WO S T ≃+ Mx D ρ S.rank × WO S T₀ × Mx D ρ S.rank where
  toFun w := (d.pX ⬝ w, d.p0 ⬝ w, d.pY ⬝ w)
  invFun p := d.incX S p.1 + d.inc0 S p.2.1 + d.incY S p.2.2
  left_inv w := by
    simp only [incX_apply, incY_apply, wittDecomp_inclAnisotropicHom_apply, ← Matrix.mul_assoc]
    rw [← Matrix.add_mul, ← Matrix.add_mul, sum_eq_one, Matrix.one_mul]
  right_inv p := by
    simp only [incX_apply, incY_apply, wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
      pY_jY, p0_jX, p0_j0, p0_jY, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  map_add' x y := Prod.ext (Matrix.mul_add _ _ _) (Prod.ext (Matrix.mul_add _ _ _) (Matrix.mul_add _ _ _))

theorem hO_coordT (w w' : WO S T) : hO S T w w' =
    pairT S (d.pX ⬝ w) (d.pY ⬝ w') + hO S T₀ (d.p0 ⬝ w) (d.p0 ⬝ w') + pairT S (d.pY ⬝ w) (d.pX ⬝ w') := by
  simp only [hO_eq_trace, pairT, adj_mul]
  rw [d.gA_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add, Matrix.mul_assoc]

theorem hO_inc (ξ ξ' η η' : Mx D ρ S.rank) (w w' : WO S T₀) :
    hO S T (d.incX S ξ + d.inc0 S w + d.incY S η) (d.incX S ξ' + d.inc0 S w' + d.incY S η') =
      pairT S ξ η' + hO S T₀ w w' + pairT S η ξ' := by
  rw [d.hO_coordT]
  simp only [incX_apply, incY_apply, wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc, pX_jX, pX_j0, pX_jY, pY_jX, pY_j0,
    pY_jY, p0_jX, p0_j0, p0_jY, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]

theorem symplOH_incX_incX (ξ ξ' : Mx D ρ S.rank) : symplOH S T (d.incX S ξ) (d.incX S ξ') = 0 := by
  have h := d.hO_inc S ξ ξ' 0 0 0 0
  simp only [map_zero, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem symplOH_incY_incY (η η' : Mx D ρ S.rank) : symplOH S T (d.incY S η) (d.incY S η') = 0 := by
  have h := d.hO_inc S 0 0 η η' 0 0
  simp only [map_zero, zero_add, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul, trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_inclIsotropic_inclAnisotropic (ξ : Mx D ρ S.rank) (w : WO S T₀) : symplOH S T (d.incX S ξ) (d.inc0 S w) = 0 := by
  have h := d.hO_inc S ξ 0 0 0 0 w
  simp only [map_zero, zero_add, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_inclDual_inclAnisotropic (η : Mx D ρ S.rank) (w : WO S T₀) : symplOH S T (d.incY S η) (d.inc0 S w) = 0 := by
  have h := d.hO_inc S 0 0 η 0 0 w
  simp only [map_zero, zero_add, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]

theorem wittDecomp_sympl_inclAnisotropic_inclAnisotropic (w w' : WO S T₀) : symplOH S T (d.inc0 S w) (d.inc0 S w') = symplOH S T₀ w w' := by
  have h := d.hO_inc S 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairT, Matrix.mul_zero, trace_zero] at h
  rw [symplOH_eq, h, symplOH_eq]

theorem hO_incX_incY (ξ η : Mx D ρ S.rank) : hO S T (d.incX S ξ) (d.incY S η) = pairT S ξ η := by
  have h := d.hO_inc S ξ 0 0 η 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S T₀, Matrix.mul_zero, trace_zero] at h
  rw [h, show pairT S (0 : Mx D ρ S.rank) 0 = 0 by simp [pairT], add_zero]

theorem symplO_incX_incAdj (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) :
    symplO S T (d.incX S ξ) (d.incAdj S y) = Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace := by
  rw [symplO_eq, incAdj_apply, hO_incX_incY, pairT_adj]
  exact congrArg _ (mul_trace_smul wittDecomp_trace0Unit_mul_conj_neg_inv _)

def qT (c : skewA D ρ) (y : Mx D S.rank ρ) : AF D.host.F :=
  symplOH S T (d.incAdj S y) (mt T (d.nC c)⁻¹ ⬝ d.incAdj S y - d.incAdj S y)

theorem actO_incAdj (g : GA D S) (a : GL (Fin ρ) (AE D)) (y : Mx D S.rank ρ) :
    actO S T g (d.levi a)⁻¹ (d.incAdj S y) = d.incAdj S (mt S g ⬝ y ⬝ a.1) := by
  simp only [actO_eq, incAdj_apply, incY_apply, ← map_inv, cancel₂ (d.levi_jY _), inv_inv, adj_mul, mt_inv S g,
    Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul, gA_giA_cancel]

def mixT (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ)
    (y : Mx D S.rank ρ) : WO S T₀ → ℂ := fun w₀ =>
  ∫ ξ in 𝓕, heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 ∂μ

variable {S} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrandT_eq (f : WO S T → ℂ) (y : Mx D S.rank ρ) (ξ : Mx D ρ S.rank) (w₀ : WO S T₀) :
    heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 =
      ψ (symplOH S T (d.incX S ξ) (d.incAdj S y)) * f (d.incX S ξ + d.incAdj S y + d.inc0 S w₀) := by
  have h : symplOH S T (d.incAdj S y) (d.inc0 S w₀) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ w₀
  simp only [heisO, zero_add, symplOH_zero_left, GlobalTheory.OrientedHeis.symplOH_add_left, h,
    wittDecomp_sympl_inclIsotropic_inclAnisotropic, add_zero, AddChar.map_zero_eq_one, one_mul]

theorem integrandT_periodic {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (y : Mx D S.rank ρ) (w₀ : WO S T₀)
    (γ : Mx D ρ S.rank) (hγ : γ ∈ ratMx D ρ S.rank) (ξ : Mx D ρ S.rank) :
    heisO ψ S T (d.incX S (γ + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 =
      heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 := by
  obtain ⟨δ, hδ⟩ : d.incX S γ ∈ ratMx D _ _ := ratMx_mul (rat_mem _) hγ
  have h := hf.quasi δ (d.incX S ξ + d.incAdj S y + d.inc0 S w₀)
  rw [show ratW T S δ = d.incX S γ from hδ] at h
  rw [integrandT_eq, integrandT_eq, map_add (d.incX S), add_assoc (d.incX S γ), add_assoc (d.incX S γ), h, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, symplOH_incX_incX,
    wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.incX S γ) _), add_neg_cancel_right]

theorem integrableOn_mixT (hψ : Continuous ψ) {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (y : Mx D S.rank ρ)
    (w₀ : WO S T₀) : IntegrableOn
      (fun ξ => heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0) 𝓕 μ := by
  refine covolOne_integrableOn hμ _ ?_ (d.integrandT_periodic hf y w₀)
  have hc : Continuous (d.incX S) := continuous_const.matrix_mul continuous_id
  simp only [integrandT_eq]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH hc continuous_const)).mul
    (hf.cont.comp ((hc.add continuous_const).add continuous_const))

end Target

end HypDec

section Examples

abbrev diagSp (D : D7) (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) : HSp D :=
  Examples₂.stdSpace Examples₂.star_isIntegral N neg p q

theorem diagSp_gram (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) :
    (diagSp D N neg p q).gram = (Matrix.diagonal fun i => Examples₂.sgn (neg i) : Matrix (Fin N) (Fin N) D.host.E) := by
  funext i j
  exact Examples₂.stdSpace_gram_apply _ N neg p q i j

theorem gram_check {N k l : ℕ} {neg : Fin N → Bool} {p q : ℕ} (a : Matrix (Fin N) (Fin k) D.host.E)
    (b : Matrix (Fin N) (Fin l) D.host.E) (c : Matrix (Fin k) (Fin l) D.host.E)
    (h : aᴴ * (Matrix.diagonal fun i => Examples₂.sgn (neg i) : Matrix (Fin N) (Fin N) D.host.E) * b = c) :
    aᴴ ⬝ (show Matrix (Fin N) (Fin N) D.host.E from (diagSp D N neg p q).gram) ⬝ b = c := by
  rw [← h]; congr 2; exact diagSp_gram N neg p q

section Field

variable (E : Type) [Field E] [CharZero E] [StarRing E]

abbrev sgnM {N : ℕ} (neg : Fin N → Bool) : Matrix (Fin N) (Fin N) E := Matrix.diagonal fun i => Examples₂.sgn (neg i)

omit [CharZero E] in
theorem col_gram {N : ℕ} (neg : Fin N → Bool) (a b : Matrix (Fin N) (Fin 1) E) (c : Matrix (Fin 1) (Fin 1) E)
    (h : ∑ k, star (a k 0) * Examples₂.sgn (neg k) * b k 0 = c 0 0) : aᴴ * sgnM E neg * b = c := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, ← h, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

omit [CharZero E] in
theorem plane_gram (a b : Matrix (Fin 2) (Fin 1) E) (ha : a = !![1; 0]) (hb : b = !![0; 1]) :
    aᴴ * sgnM E ![false, true] * a = sgnM E ![false] ∧ bᴴ * sgnM E ![false, true] * b = sgnM E ![true] ∧
    bᴴ * sgnM E ![false, true] * a = 0 := by
  subst ha hb
  refine ⟨col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_⟩ <;> simp [Fin.sum_univ_two, Examples₂.sgn]

theorem three_gram (e e' i : Matrix (Fin 3) (Fin 1) E) (he : e = !![0; 1; 1]) (he' : e' = !![0; 1 / 2; -(1 / 2)])
    (hi : i = !![1; 0; 0]) :
    eᴴ * sgnM E ![false, false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, false, true] * e = 1 ∧ iᴴ * sgnM E ![false, false, true] * i = sgnM E ![false] ∧
    iᴴ * sgnM E ![false, false, true] * e = 0 ∧ iᴴ * sgnM E ![false, false, true] * e' = 0 := by
  subst he he' hi
  refine ⟨col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_,
    col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_⟩ <;> simp [Fin.sum_univ_three, Examples₂.sgn]
  norm_num

end Field

def orthDecPlane (D : D7) :
    OrthDec (diagSp D 2 ![false, true] 1 1) (diagSp D 1 ![false] 1 0) (diagSp D 1 ![true] 0 1) where
  iA := (!![1; 0] : Matrix (Fin 2) (Fin 1) D.host.E)
  iB := (!![0; 1] : Matrix (Fin 2) (Fin 1) D.host.E)
  isoA := (gram_check _ _ _ (plane_gram D.host.E _ _ rfl rfl).1).trans (diagSp_gram 1 _ 1 0).symm
  isoB := (gram_check _ _ _ (plane_gram D.host.E _ _ rfl rfl).2.1).trans (diagSp_gram 1 _ 0 1).symm
  orth := gram_check _ _ _ (plane_gram D.host.E _ _ rfl rfl).2.2
  rank_add := rfl

def hypDecThree (D : D7) : HypDec (diagSp D 3 ![false, false, true] 2 1) (diagSp D 1 ![false] 1 0) 1 where
  e := (!![0; 1; 1] : Matrix (Fin 3) (Fin 1) D.host.E)
  e' := (!![0; 1 / 2; -(1 / 2)] : Matrix (Fin 3) (Fin 1) D.host.E)
  i₀ := (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) D.host.E)
  ee := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).1
  e'e' := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.1
  e'e := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.1
  iso := (gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.1).trans (diagSp_gram 1 _ 1 0).symm
  i₀e := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.1
  i₀e' := gram_check _ _ _ (three_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.2
  rank_add := rfl

theorem pairS_plus (S₀ T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (b b' : Mx D ρ S₀.rank) :
    pairS T x (x ⬝ (b' ⬝ plus S₀ b)) = hO S₀ T (x ⬝ b) (x ⬝ b') := by
  rw [pairS, hO_eq_trace, adj_mul, adj_mul_plus, plus, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trHalf_half (z : AE D) : trHalf D (half D * z) + trHalf D (half D * z) = trHalf D z := by
  rw [← map_add, ← add_mul, half_add_half, one_mul]

example {S S₀ T : HSp D} (d : HypDec S S₀ 0) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) (x a : Mx D T.rank 0)
    (w₀ : WO S₀ T) :
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 = f (d.ext0 T w₀) := by
  rw [d.integrandS_eq, Subsingleton.elim a 0, Subsingleton.elim x 0, map_zero, map_zero, symplOH_zero_left,
    AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]

end Examples

end GlobalTheory.MixModel

end
