import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.UnfZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.FixRep
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open GlobalTheory.CuspRep UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

attribute [local instance 100000] MeasurableSpace.pi

variable {K : Type} [Field K] [NumberField K]

private theorem sfin {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] : SFinite ν := inferInstance

private theorem out_mk {n : ℕ} (h : G1 K n → ℂ) (hh : ∀ γ ∈ Gam K n, ∀ m, h (γ * m) = h m) (g : G1 K n) :
    h (Quotient.out (mk (Gam K n) g)) = h g := by
  obtain ⟨γ, e⟩ := RightCosetSpace.mk_eq_mk_iff.1 (show mk (Gam K n) (Quotient.out (mk (Gam K n) g)) = mk (Gam K n) g from Quotient.out_eq _)
  rw [← e]
  exact hh _ γ.2 _

private theorem int_out {n : ℕ} (μ : Measure (G1 K n)) (h : G1 K n → ℂ) (hh : ∀ γ ∈ Gam K n, ∀ m, h (γ * m) = h m) :
    ∫ y, h (Quotient.out y) ∂quotientMeasure (Gam K n) μ = ∫ g, h g ∂fd μ := by
  rw [integral_quotientMeasure]
  simp only [out_mk h hh]

private theorem left_gam {n : ℕ} {φ : AdelicGLn.AdelicGL K n → ℂ} (h : IsLeftInvariant φ) :
    ∀ γ ∈ Gam K n, ∀ m : G1 K n, φ ((γ * m : G1 K n) : AdelicGLn.AdelicGL K n) = φ m := by
  rintro γ ⟨δ, hδ⟩ m
  have : (γ : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n δ := hδ.symm
  rw [Subgroup.coe_mul, this, h]

private theorem lev_blk {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := Units.ext (GlobalTheory.SmGL.val_emb₂ R _ _)

private theorem lev_zero {R : Type} [CommRing R] (x : GL (Fin 2) R) : GlobalTheory.CompanionTheory.CTFin.lev R 2 0 (x, 1) = x := by
  rw [lev_blk]
  ext i j
  have e : ∀ i : Fin 2, (finSumFinEquiv (m := 2) (n := 0)).symm i = Sum.inl i := fun i => finSumFinEquiv_symm_apply_castAdd i
  simp [blk, e]

private theorem ct_top (φ : AdelicGLn.AdelicGL K 2 → ℂ) (g : AdelicGLn.AdelicGL K 2) : constantTerm 2 φ g = φ g := by
  haveI : IsEmpty (UPos 2 2) := ⟨fun p => by have := p.1.2.2; have := p.2.2; omega⟩
  have e : ∀ X : UPos 2 2 → 𝔸[K], unipGL X = 1 := fun X => by rw [Subsingleton.elim X 0, unipGL_zero]
  have e2 : unipFundamentalDomain K 2 2 = univ := eq_univ_of_forall fun X p => isEmptyElim p
  simp [constantTerm, e, e2, Measure.real, Measure.pi_empty_univ]

private theorem zt_blk (a : ℝ) : blk (InvariantSubmoduleMonicPolynomial.zt K a) (InvariantSubmoduleMonicPolynomial.zt K a) = UpperTheory.ConvolutionTheory.BW.zt K (2 + 2) (a + a) := by
  have h1 : ∀ u, blk (scalarUnits K 2 u) (scalarUnits K 2 u) = scalarUnits K (2 + 2) u := by
    intro u
    refine Units.ext ?_
    simp only [blk, scalarUnits_apply, coe_diagUnits, Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    simp only [Function.comp]
    cases finSumFinEquiv.symm i <;> rfl
  simp only [InvariantSubmoduleMonicPolynomial.zt, UpperTheory.ConvolutionTheory.BW.zt, centralSection, MonoidHom.comp_apply, h1]
  congr 2
  refine Subtype.ext ?_
  show Real.exp a ^ _ = Real.exp (a + a) ^ _
  have : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [← Real.exp_mul, ← Real.exp_mul]
  congr 1
  push_cast
  field_simp
  ring

private theorem zt_add (a b : ℝ) : InvariantSubmoduleMonicPolynomial.zt K (a + b) = InvariantSubmoduleMonicPolynomial.zt K a * InvariantSubmoduleMonicPolynomial.zt K b := by
  rw [InvariantSubmoduleMonicPolynomial.zt, InvariantSubmoduleMonicPolynomial.zt, InvariantSubmoduleMonicPolynomial.zt, ← map_mul]
  congr 1
  exact Subtype.ext (Real.exp_add a b)

private theorem lev_lv (a b : G1 K 2) (s t : ℝ) :
    blk (InvariantSubmoduleMonicPolynomial.zt K s * (a : AdelicGLn.AdelicGL K 2)) (InvariantSubmoduleMonicPolynomial.zt K t * (b : AdelicGLn.AdelicGL K 2)) =
      UpperTheory.ConvolutionTheory.BW.zt K (2 + 2) ((s + t) / 2 + (s + t) / 2) * ((lv a b ((s - t) / 2) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := by
  have hc : ∀ (x : ℝ) (g : AdelicGLn.AdelicGL K 2), g * InvariantSubmoduleMonicPolynomial.zt K x = InvariantSubmoduleMonicPolynomial.zt K x * g := fun x g => (centralSection_mul_comm _ g).symm
  rw [blkLaws.1, ← zt_blk, blkLaws.2.2.2.2.2.1, hc, hc, ← mul_assoc, ← mul_assoc, ← zt_add, ← zt_add]
  congr 3 <;> ring

variable [IsTotallyComplex K]

private theorem blo_rd {S : Set (Pl K)} (b : Blo S 2) (τ : Submodule ℂ (L2 (mu1 K 2)))
    (h : ((cuspToL2 (mu1 K 2) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 K 2)) : L2 (mu1 K 2)) ∈ τ) :
    Rd τ fun m : G1 K 2 => b.f.1 (m : AdelicGLn.AdelicGL K 2) := by
  obtain ⟨hu, hc⟩ := cuspUmg K 2 b.f b.cusp
  refine ⟨((umgOps K 2).2 _ hu).1.comp continuous_subtype_val, ⟨_, h, ?_⟩, left_gam hu.left, fun m => ?_, ?_⟩
  · filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) (mu1 K 2)).ae (coeFn_cuspToL2 (mu1 K 2) ⟨b.f.1, b.cusp⟩)] with y hy
    rw [hy]
    rfl
  · have := hc 1 one_pos one_lt_two (m : AdelicGLn.AdelicGL K 2)
    unfold constantTerm at this
    exact this
  · exact rapidDecay K 2 b.f hu hc

theorem compZero (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 (mu1 K 2))) (D : TypeDat K (2 + 2)) {d : ℕ}
    (A : Line μ τ₁ τ₂ D d) (h₁ : CuspIrr (mu1 K 2) τ₁) (h₂ : CuspIrr (mu1 K 2) τ₂) (a : CC K (2 + 2)) (ha : D.Hecke a) (y : L2 μ)
    (w : Sm K (2 + 2)) (hw : Rep μ (Rop μ a y) w) (hJ : ∀ u, ⟪A.J u, Rop μ a y⟫_ℂ = 0) {S : Set (Pl K)} (b₁ b₂ : Blo S 2)
    (m₁ : ((cuspToL2 (mu1 K 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 K 2)) : L2 (mu1 K 2)) ∈ τ₁)
    (m₂ : ((cuspToL2 (mu1 K 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 K 2)) : L2 (mu1 K 2)) ∈ τ₂) (k : KA K (2 + 2)) :
    (Dat.cons b₁ (Dat.cons b₂ Dat.nil)).comp (rt K (2 + 2) k w).1 = 0 := by
  funext t
  have r₁ := blo_rd b₁ τ₁ m₁
  have r₂ := blo_rd b₂ τ₂ m₂
  have hc : Continuous fun g : G1 K (2 + 2) => w.1 (g : AdelicGLn.AdelicGL K (2 + 2)) :=
    ((umgOps K _).2 _ hw.umg).1.comp continuous_subtype_val
  have hΓ := left_gam hw.umg.left
  have hrep : Reps μ (Rop μ a y) fun g : G1 K (2 + 2) => w.1 (g : AdelicGLn.AdelicGL K (2 + 2)) :=
    ((quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae hw.ae).mono fun g hg => hg.trans (out_mk (fun g : G1 K (2 + 2) => w.1 (g : AdelicGLn.AdelicGL K (2 + 2))) hΓ g)
  obtain ⟨F, hF, hFu, hFr, -⟩ := ctOps K 2 2 w hw.umg
  have hrat : ∀ γ₁ ∈ Gam K 2, ∀ γ₂ ∈ Gam K 2, ∀ g : G1 K (2 + 2),
      constantTerm 2 w.1 ((lv γ₁ γ₂ 0 * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = constantTerm 2 w.1 (g : AdelicGLn.AdelicGL K (2 + 2)) := by
    rintro γ₁ ⟨δ₁, e₁⟩ γ₂ ⟨δ₂, e₂⟩ g
    have e₁' : (γ₁ : AdelicGLn.AdelicGL K 2) = ratGL K 2 δ₁ := e₁.symm
    have e₂' : (γ₂ : AdelicGLn.AdelicGL K 2) = ratGL K 2 δ₂ := e₂.symm
    have z0 : InvariantSubmoduleMonicPolynomial.zt K 0 = 1 := by
      have := zt_add (K := K) 0 0
      rwa [add_zero, left_eq_mul] at this
    rw [Subgroup.coe_mul, blkLaws.1, neg_zero, z0, mul_one, mul_one, e₁', e₂', ← lev_blk, ← hF]
    exact hFr (δ₁, δ₂) _
  let k' : G1 K (2 + 2) := ⟨k, (blkLaws.2.2.2.2.2.2.2.2.2.2.2 _).2 _ k.2⟩
  obtain ⟨hi, h0⟩ := unfZero μ (mu1 K 2) τ₁ τ₂ D A h₁ h₂ _ _ (fun g => constantTerm 2 w.1 (g : AdelicGLn.AdelicGL K (2 + 2))) _ _ hc hΓ hrep
    (by
      obtain ⟨N, hN⟩ := hw.umg.growth
      obtain ⟨B, hB⟩ := hN 1
      rw [map_one, Module.End.one_apply] at hB
      exact ⟨N, B, fun g => hB g⟩)
    (fixRep μ D a ha y _ hc hrep) hJ (fun g => rfl) hrat (fun X g => by
      have e : GlobalTheory.CuspRep.unip X = unipGL X := Units.ext rfl
      rw [← hF, Subgroup.coe_mul, ← hFu X g, e]
      rfl) r₁ r₂
    ((t (0 : Fin 2) - t (1 : Fin 2)) / 2) k' k.2
  haveI := finFd (mu1 K 2)
  haveI := sfin (fd (mu1 K 2))
  rw [integral_prod_symm _ hi] at h0
  have e : ∀ a b : G1 K 2, constantTerm 2 (rt K (2 + 2) k w).1 (GlobalTheory.CompanionTheory.CTFin.lev (Ad K) 2 2
      (UpperTheory.ConvolutionTheory.BW.zt K 2 (t (0 : Fin 2)) * a, UpperTheory.ConvolutionTheory.BW.zt K 2 (t (1 : Fin 2)) * b)) =
      constantTerm 2 w.1 ((lv a b ((t (0 : Fin 2) - t (1 : Fin 2)) / 2) * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := by
    intro a b
    rw [lev_blk]
    erw [lev_lv]
    refine integral_congr_ae (ae_of_all _ fun X => ?_)
    show w.1 (unipGL X * (_ * _) * _) = w.1 (unipGL X * (_ * _))
    rw [← mul_assoc, UpperTheory.ConvolutionTheory.BW.zt, ← centralSection_mul_comm, mul_assoc, mul_assoc]
    exact hw.cen _ _
  have hmul := (blkLaws (K := K)).2.1
  have hl : ∀ γ₁ ∈ Gam K 2, ∀ γ₂ ∈ Gam K 2, ∀ (a b : G1 K 2) s,
      constantTerm 2 w.1 ((lv (γ₁ * a) (γ₂ * b) s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        constantTerm 2 w.1 ((lv a b s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := fun γ₁ h1 γ₂ h2 a b s => by
    rw [← hrat γ₁ h1 γ₂ h2 (lv a b s * k'), ← mul_assoc, hmul, zero_add]
  show slice (r := 2) (s := 0) b₂.f.1 (t (1 : Fin 2)) (slice (r := 2) (s := 2) b₁.f.1 (t (0 : Fin 2)) (rt K (2 + 2) k w).1) 1 = 0
  rw [← h0, ← int_out (mu1 K 2) _ fun γ hγ b => by
    simp only [r₂.rat γ hγ b, fun a s => (by simpa only [one_mul] using hl 1 (one_mem _) γ hγ a b s :
      constantTerm 2 w.1 ((lv a (γ * b) s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = _)]]
  refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
  simp only
  rw [← int_out (mu1 K 2) _ fun γ hγ a => by
    simp only [r₁.rat γ hγ a, fun b s => (by simpa only [one_mul] using hl γ hγ 1 (one_mem _) a b s :
      constantTerm 2 w.1 ((lv (γ * a) b s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = _)]]
  erw [lev_zero, ct_top]
  rw [slice, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y₁ => ?_)
  simp only
  erw [e]
  rw [map_mul]
  ring

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX
