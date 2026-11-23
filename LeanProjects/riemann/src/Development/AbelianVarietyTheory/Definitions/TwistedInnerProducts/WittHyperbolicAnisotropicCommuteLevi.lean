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

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel

variable {D : D7}

namespace HypDec

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

section Unip

variable (b : Mx D ρ S₀.rank) (c : skewA D ρ)

theorem nB_mem_GQ {b : Mx D ρ S₀.rank} (h : b ∈ ratMx D ρ S₀.rank) : d.nB b ∈ GQ S := by
  have h' : plus S₀ b ∈ ratMx D _ _ := ratMx_mul (rat_mem _) (ratMx_adj h)
  exact d.ofImages_mem_GQ (d.images_nB b) (rat_mem _) (add_mem (rat_mem _) (ratMx_mul (rat_mem _) h))
    (sub_mem (sub_mem (rat_mem _) (ratMx_mul (rat_mem _) h')) (ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul h h'))))

theorem nC_mem_GQ {c : skewA D ρ} (h : c.1 ∈ ratMx D ρ ρ) : d.nC c ∈ GQ S :=
  d.ofImages_mem_GQ (d.images_nC c) (rat_mem _) (rat_mem _) (add_mem (rat_mem _) (ratMx_mul (rat_mem _) h))

theorem continuous_nB : Continuous d.nB := by
  have := (lattice_Mx D S.rank ρ).1
  have : ContinuousSub (Mx D S.rank ρ) := IsTopologicalAddGroup.to_continuousSub
  have h : Continuous (plus S₀ : Mx D ρ S₀.rank → _) := continuous_const.matrix_mul continuous_adj
  have h1 : Continuous fun b : Mx D ρ S₀.rank => b ⬝ plus S₀ b := continuous_id.matrix_mul h
  have h2 : Continuous fun b : Mx D ρ S₀.rank => half D • (b ⬝ plus S₀ b) := h1.const_smul (half D)
  have h3 : Continuous fun b : Mx D ρ S₀.rank => d.jX ⬝ b := continuous_const.matrix_mul continuous_id
  refine continuous_of_mt S ?_
  simp only [nB, mt_ofImages]
  refine Continuous.add (Continuous.add continuous_const (Continuous.matrix_mul ?_ continuous_const))
    (Continuous.matrix_mul ?_ continuous_const)
  · exact Continuous.add continuous_const h3
  · exact Continuous.sub (Continuous.sub continuous_const (continuous_const.matrix_mul h))
      (continuous_const.matrix_mul h2)

theorem continuous_nC : Continuous d.nC := by
  have h3 : Continuous fun c : skewA D ρ => d.jX ⬝ c.1 := continuous_const.matrix_mul continuous_subtype_val
  refine continuous_of_mt S ?_
  simp only [nC, mt_ofImages]
  exact Continuous.add continuous_const (Continuous.matrix_mul (Continuous.add continuous_const h3) continuous_const)

theorem nB_zero : d.nB 0 = 1 :=
  d.ga_ext (by rw [nB_jX, mt_one, Matrix.one_mul]) (by rw [nB_j0, mt_one, Matrix.one_mul, Matrix.mul_zero, add_zero])
    (by rw [nB_jY, mt_one, Matrix.one_mul, plus_zero, Matrix.mul_zero, Matrix.mul_zero, smul_zero, Matrix.mul_zero,
      sub_zero, sub_zero])

theorem nC_zero : d.nC 0 = 1 :=
  d.ga_ext (by rw [nC_jX, mt_one, Matrix.one_mul]) (by rw [nC_j0, mt_one, Matrix.one_mul])
    (by rw [nC_jY, mt_one, Matrix.one_mul, AddSubgroup.coe_zero, Matrix.mul_zero, add_zero])

theorem nC_add (c c' : skewA D ρ) : d.nC (c + c') = d.nC c * d.nC c' :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nC_jX]) (by simp only [mt_mul, Matrix.mul_assoc, nC_j0])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_jY, Matrix.mul_add, cancel₂ (d.nC_jX _), AddSubgroup.coe_add, add_assoc])

theorem nB_mul_nB (b₁ b₂ : Mx D ρ S₀.rank) : d.nB b₁ * d.nB b₂ = d.nB (b₁ + b₂) * d.nC (cComm S₀ b₁ b₂) := by
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, nC_jX])
    (by simp only [mt_mul, Matrix.mul_assoc, nB_j0, nC_j0, Matrix.mul_add, cancel₂ (d.nB_jX _), add_assoc]) ?_
  have h := half_smul_add (b₁ ⬝ plus S₀ b₂)
  simp only [mt_mul, Matrix.mul_assoc, nB_jY, nC_jY, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul,
    cancel₂ (d.nB_jX _), cancel₂ (d.nB_j0 _), cComm, plus_add, smul_add, smul_sub]
  generalize half D • (b₁ ⬝ plus S₀ b₂) = u at h ⊢
  rw [← h, Matrix.mul_add]
  abel

theorem nB_inv : (d.nB b)⁻¹ = d.nB (-b) := by
  have h : cComm S₀ b (-b) = 0 := Subtype.ext (by
    simp only [cComm, plus_neg, Matrix.neg_mul, Matrix.mul_neg, sub_self, smul_zero, AddSubgroup.coe_zero])
  rw [inv_eq_iff_mul_eq_one, nB_mul_nB, add_neg_cancel, h, nB_zero, nC_zero, one_mul]

theorem nC_inv : (d.nC c)⁻¹ = d.nC (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← nC_add, add_neg_cancel, nC_zero]

theorem nC_mul_nB : d.nC c * d.nB b = d.nB b * d.nC c :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, nC_jX])
    (by simp only [mt_mul, Matrix.mul_assoc, nB_j0, nC_j0, Matrix.mul_add, cancel₂ (d.nC_jX _)])
    (by
      simp only [mt_mul, Matrix.mul_assoc, nB_jY, nC_jY, Matrix.mul_add, Matrix.mul_sub, cancel₂ (d.nB_jX _),
        cancel₂ (d.nC_jX _), cancel₂ (d.nC_j0 _)]
      abel)

theorem levi_mul_nB (a : GL (Fin ρ) (AE D)) : d.levi a * d.nB b = d.nB (a.1 ⬝ b) * d.levi a := by
  have h : adj a.1 ⬝ adj (a⁻¹).1 = 1 := by rw [← adj_mul, Units.inv_mul, adj_one]
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, levi_jX, cancel₂ (d.nB_jX _)])
    (by simp only [mt_mul, Matrix.mul_assoc, nB_j0, wittDecomp_levi_inclAnisotropic, Matrix.mul_add, cancel₂ (d.levi_jX _)]) ?_
  simp only [mt_mul, Matrix.mul_assoc, nB_jY, levi_jY, Matrix.mul_sub, Matrix.sub_mul, cancel₂ (d.levi_jX _),
    cancel₂ (d.wittDecomp_levi_inclAnisotropic _), cancel₂ (d.nB_jY _), plus_mul_left, Matrix.mul_smul, Matrix.smul_mul, h, Matrix.mul_one]

theorem levi_mul_nC (a : GL (Fin ρ) (AE D)) : d.levi a * d.nC c = d.nC (skewConj a.1 c) * d.levi a := by
  have h : adj a.1 ⬝ adj (a⁻¹).1 = 1 := by rw [← adj_mul, Units.inv_mul, adj_one]
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nC_jX, levi_jX, cancel₂ (d.nC_jX _)])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_j0, wittDecomp_levi_inclAnisotropic]) ?_
  simp only [mt_mul, Matrix.mul_assoc, nC_jY, levi_jY, Matrix.mul_add, Matrix.add_mul, cancel₂ (d.levi_jX _),
    cancel₂ (d.nC_jY _), skewConj, h, Matrix.mul_one]

theorem wittHyperbolic_anisotropic_conj_nB (g : GA D S₀) : d.emb0 g * d.nB b = d.nB (b ⬝ mt S₀ g⁻¹) * d.emb0 g := by
  refine d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nB_jX, wittDecomp_anisotropicEmbedding_inclX]) ?_ ?_
  · simp only [mt_mul, Matrix.mul_assoc, nB_j0, wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_add, Matrix.add_mul, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _),
      cancel₂ (d.nB_j0 _), mt_inv_mul, Matrix.mul_one]
  · simp only [mt_mul, Matrix.mul_assoc, nB_jY, wittDecomp_anisotropicEmbedding_inclY, Matrix.mul_sub, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _), cancel₂ (d.wittDecomp_anisotropicEmbedding_inclAnisotropic _),
      plus_mul_inv, cancel₂ (mt_inv_mul S₀ g), Matrix.one_mul]

theorem wittHyperbolic_anisotropic_commute_nC (g : GA D S₀) : d.emb0 g * d.nC c = d.nC c * d.emb0 g :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, nC_jX, wittDecomp_anisotropicEmbedding_inclX])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_j0, wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ (d.nC_j0 _)])
    (by simp only [mt_mul, Matrix.mul_assoc, nC_jY, wittDecomp_anisotropicEmbedding_inclY, Matrix.mul_add, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _)])

theorem wittHyperbolic_anisotropic_commute_levi (g : GA D S₀) (a : GL (Fin ρ) (AE D)) : d.emb0 g * d.levi a = d.levi a * d.emb0 g :=
  d.ga_ext (by simp only [mt_mul, Matrix.mul_assoc, levi_jX, wittDecomp_anisotropicEmbedding_inclX, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclX _)])
    (by simp only [mt_mul, Matrix.mul_assoc, wittDecomp_levi_inclAnisotropic, wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ (d.wittDecomp_levi_inclAnisotropic _)])
    (by simp only [mt_mul, Matrix.mul_assoc, levi_jY, wittDecomp_anisotropicEmbedding_inclY, cancel₂ (d.wittDecomp_anisotropicEmbedding_inclY _)])

end Unip

theorem mulVec_perp {M : Mx D S.rank S.rank} {U : Mx D ρ ρ} {b : Mx D ρ S₀.rank} (h1 : M ⬝ d.jX = d.jX ⬝ U)
    (h2 : M ⬝ d.j0 = d.jX ⬝ b) (v : Fin S.rank → AE D) (h3 : d.pY *ᵥ v = 0) :
    M *ᵥ v = d.jX *ᵥ ((U ⬝ d.pX + b ⬝ d.p0) *ᵥ v) := by
  have h4 : M = d.jX ⬝ (U ⬝ d.pX + b ⬝ d.p0) + (M ⬝ d.jY) ⬝ d.pY :=
    d.mat_ext (by simp only [h1, Matrix.add_mul, Matrix.mul_assoc, pX_jX, p0_jX, pY_jX, Matrix.mul_one,
        Matrix.mul_zero, add_zero])
      (by simp only [h2, Matrix.add_mul, Matrix.mul_assoc, pX_j0, p0_j0, pY_j0, Matrix.mul_one, Matrix.mul_zero,
        add_zero, zero_add])
      (by simp only [Matrix.add_mul, Matrix.mul_assoc, pX_jY, p0_jY, pY_jY, Matrix.mul_one, Matrix.mul_zero,
        add_zero, zero_add])
  exact (congrArg (· *ᵥ v) h4).trans (mulVec_of_kill _ _ _ _ _ h3)

theorem pY_ratV {x : Fin S.rank → D.host.E} (hx : d.qY *ᵥ x = 0) : d.pY *ᵥ ratV x = 0 := by
  funext i
  have := RingHom.map_mulVec (incA D) d.qY x i
  rw [hx, Pi.zero_apply, map_zero] at this
  exact this.symm

theorem subOne_mul {k : ℕ} (g : GA D S) (y : Mx D S.rank k) : subOne S g ⬝ y = mt S g ⬝ y - y :=
  (Matrix.sub_mul _ _ _).trans (by rw [Matrix.one_mul]; rfl)

theorem mem_NFlag {g : GA D S} {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D)) {b : Mx D ρ S₀.rank}
    (hX : mt S g ⬝ d.jX = d.jX ⬝ u.1) (h0 : mt S g ⬝ d.j0 = d.j0 + d.jX ⬝ b) : g ∈ NFlag S d.e := by
  have h1 : subOne S g ⬝ d.jX = d.jX ⬝ (u.1 - 1) := by rw [subOne_mul, hX, Matrix.mul_sub, Matrix.mul_one]
  have h2 : subOne S g ⬝ d.j0 = d.jX ⬝ b := by rw [subOne_mul, h0, add_sub_cancel_left]
  refine Subgroup.subset_closure ⟨fun i => ⟨fun j => (u.1 - 1) j i, fun j hj => ?_, ?_⟩,
    fun x hx => ⟨_, d.mulVec_perp h1 h2 _ (d.pY_ratV hx)⟩⟩
  · beta_reduce
    rcases hj.eq_or_lt with rfl | hj
    · rw [Matrix.sub_apply, (hu i i).2, Matrix.one_apply_eq, sub_self]
    · rw [Matrix.sub_apply, (hu j i).1 hj, Matrix.one_apply_ne hj.ne', sub_self]
  · funext k
    exact congrFun (congrFun h1 k) i

theorem one_mem_upperUni : (1 : GL (Fin ρ) (AE D)) ∈ upperUni ρ (AE D) :=
  fun i j => by
    rw [Units.val_one]
    exact ⟨fun h => Matrix.one_apply_ne h.ne', Matrix.one_apply_eq i⟩

theorem levi_mem_NFlag {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D)) : d.levi u ∈ NFlag S d.e :=
  d.mem_NFlag hu (b := 0) (d.levi_jX u) (by rw [wittDecomp_levi_inclAnisotropic, Matrix.mul_zero, add_zero])

theorem nB_mem_NFlag (b : Mx D ρ S₀.rank) : d.nB b ∈ NFlag S d.e :=
  d.mem_NFlag one_mem_upperUni (by rw [nB_jX, Units.val_one, Matrix.mul_one]) (d.nB_j0 b)

theorem nC_mem_NFlag (c : skewA D ρ) : d.nC c ∈ NFlag S d.e :=
  d.mem_NFlag one_mem_upperUni (b := 0) (by rw [nC_jX, Units.val_one, Matrix.mul_one])
    (by rw [nC_j0, Matrix.mul_zero, add_zero])

end HypDec

end GlobalTheory.MixModel

end
