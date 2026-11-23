import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleApply
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZAux
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import GroundTheory.PAdicHodge.ACrisGalois

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth.GrothendieckPhiBijection

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL k) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    obtain ⟨h, Γ, hΓ⟩ := exists_enum u
    have hm : MvPolynomial.monomial u a = MvPolynomial.C a * ∏ i : Fin h, MvPolynomial.X (Γ i) := by
      rw [prod_X_of_map u Γ hΓ, MvPolynomial.C_mul_monomial, mul_one]
    have hC : phiOf Lseg (MvPolynomial.C a) = (a : R k) := by simp [phiOf]
    rw [hm, map_mul, hC, hprod h _ Γ rfl, ← zsmul_eq_mul, map_zsmul, AddEquiv.symm_apply_apply, map_zsmul,
      ell_prod hA hj hJ hAlt Lseg hL Δ Γ rfl, hΓ, MvPolynomial.coeff_C_mul, prod_X_of_map u Γ hΓ,
      MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd ((toMultiset_eq_single_iff u Δ).mp h1) h2
    · exact absurd ((toMultiset_eq_single_iff u Δ).mpr h2) h1
    · simp
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq, MvPolynomial.coeff_add, add_mul]

end PositivityTheory.Groth.GrothendieckPhiBijection

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

open GrothendieckPhiBijection in

theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
  obtain ⟨Lseg, hL, hbij, hrep, hprod⟩ := phiL_main hk h2
  obtain ⟨hC, -, -, -, -, -, -, -, hJ, hJS, hAlt⟩ := hk
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hx : ∀ Δ : Segment k, ∃ p : MvPolynomial (Segment k) ℤ,
      phiOf Lseg p = toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) ∧
        ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = Δ.ms := by
    intro Δ
    obtain ⟨n, hn⟩ := hC.exh ⟨Δ.len * Δ.d, Z Δ⟩
    obtain ⟨p, hp1, hp2⟩ := hrep n _ hn
    exact ⟨p, hp1, fun s hs => (hp2 s hs).trans (msupp_seg hA hC.jac Z hZ hJS Δ hn)⟩
  choose p hp1 hp2 using hx
  let ψ : MvPolynomial (Segment k) ℤ →+* MvPolynomial (Segment k) ℤ := (MvPolynomial.aeval p).toRingHom
  have hψX : ∀ Δ, ψ (MvPolynomial.X Δ) = p Δ := fun Δ => MvPolynomial.aeval_X p Δ
  have hcomp : (phiOf Lseg).comp ψ = phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, phiOf]
    · intro Δ
      rw [RingHom.comp_apply, hψX, hp1, phiOf_X]
  have hψ : Function.Bijective ψ := by
    apply h1 (Segment k) (fun Δ => Δ.len) ψ
    intro Δ
    have hell := ell_phiOf hA hC.jac hJ hAlt Lseg hL hprod Δ (p Δ)
    rw [hp1, AddEquiv.symm_apply_apply, ell_sg (hJS Z hZ Δ).1 (hJS Z hZ Δ).2] at hell
    have hc : (p Δ).coeff (Finsupp.single Δ 1) = (-1) ^ (Δ.len - 1) := by
      have h' : ((-1 : ℤ) ^ (Δ.len - 1)) * ((-1) ^ (Δ.len - 1)) = 1 := by
        rw [← mul_pow]
        simp
      calc (p Δ).coeff (Finsupp.single Δ 1)
          = (p Δ).coeff (Finsupp.single Δ 1) * ((-1) ^ (Δ.len - 1) * (-1) ^ (Δ.len - 1)) := by
            rw [h', mul_one]
        _ = (-1) ^ (Δ.len - 1) := by rw [← mul_assoc, ← hell, one_mul]
    refine ⟨(-1) ^ (Δ.len - 1), _, vars_lt hA (p Δ) (hp2 Δ), ?_⟩
    rw [hψX, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    push_cast
    rw [← hc, add_sub_cancel]
  rw [← hcomp]
  exact hbij.comp hψ

end PositivityTheory.Groth

end
