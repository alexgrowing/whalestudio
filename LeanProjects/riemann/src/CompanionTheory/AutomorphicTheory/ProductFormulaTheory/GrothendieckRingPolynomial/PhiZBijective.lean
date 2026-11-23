import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleApply
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZAux
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.GrothendieckPhiBijection

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL k) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  have hm : ∀ s : Segment k →₀ ℕ, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial s 1))) =
      if s = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0 := by
    intro s
    obtain ⟨h, Γ, hΓ⟩ := exists_enum s
    rw [← prod_X_of_map s Γ hΓ, hprod h _ Γ rfl, AddEquiv.symm_apply_apply, ell_prod hA hj hJ hAlt Lseg hL, hΓ]
    by_cases hs : s = Finsupp.single Δ 1
    · rw [if_pos ((toMultiset_eq_single_iff s Δ).2 hs), if_pos hs]
    · rw [if_neg (fun h => hs ((toMultiset_eq_single_iff s Δ).1 h)), if_neg hs]
  have hm' : ∀ v, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial v (p.coeff v)))) =
      p.coeff v * (if v = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0) := by
    intro v
    have : MvPolynomial.monomial v (p.coeff v) = p.coeff v • MvPolynomial.monomial v (1 : ℤ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_zsmul, map_zsmul, map_zsmul, hm, smul_eq_mul]
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, hm']
  rw [Finset.sum_eq_single (Finsupp.single Δ 1)]
  · simp
  · intro b _ hb; simp [hb]
  · intro hn; rw [MvPolynomial.notMem_support_iff.1 hn]; simp

end CompanionTheory.Groth.GrothendieckPhiBijection

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

open GrothendieckPhiBijection in

theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨Lseg, hL, hbij, hpre, hprod⟩ := phiL_main hk h2
  obtain ⟨hcls, -, -, -, -, -, -, -, hJ, hS, hAlt⟩ := hk
  have key : ∀ Δ : Segment k, ∃ p : MvPolynomial (Segment k) ℤ,
      phiOf Lseg p = toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) ∧
      ∃ (ε : ℤˣ) (q : MvPolynomial (Segment k) ℤ), (∀ t ∈ q.vars, t.len < Δ.len) ∧
        p = (ε : ℤ) • MvPolynomial.X Δ + q := by
    intro Δ
    obtain ⟨𝔫, h𝔫⟩ := hcls.exh ⟨Δ.len * Δ.d, Z Δ⟩
    obtain ⟨p, hp, hsupp⟩ := hpre 𝔫 _ h𝔫
    have hms := msupp_seg hA hcls.jac Z hZ hS Δ h𝔫
    have hce : p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) = 1 := by
      rw [← ell_phiOf hA hcls.jac hJ hAlt Lseg hL hprod Δ p, hp, AddEquiv.symm_apply_apply,
        ell_sg (hS Z hZ Δ).1 (hS Z hZ Δ).2]
    have hc : p.coeff (Finsupp.single Δ 1) = (-1) ^ (Δ.len - 1) := by
      have hsq : ((-1 : ℤ) ^ (Δ.len - 1)) * (-1) ^ (Δ.len - 1) = 1 := by
        rw [← mul_pow]; norm_num
      calc p.coeff (Finsupp.single Δ 1)
          = p.coeff (Finsupp.single Δ 1) * ((-1) ^ (Δ.len - 1) * (-1) ^ (Δ.len - 1)) := by rw [hsq, mul_one]
        _ = (-1) ^ (Δ.len - 1) := by rw [← mul_assoc, hce, one_mul]
    refine ⟨p, hp, (-1) ^ (Δ.len - 1),
      p - MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)),
      vars_lt hA p (fun s hs => (hsupp s hs).trans hms), ?_⟩
    have hX : (((-1 : ℤˣ) ^ (Δ.len - 1) : ℤˣ) : ℤ) • (MvPolynomial.X Δ : MvPolynomial (Segment k) ℤ) =
        MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)) := by
      rw [hc, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      push_cast
      rfl
    rw [hX]
    ring
  choose p hp ε q hq hpq using key
  have hψ : Function.Bijective (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) :=
    h1 (Segment k) Segment.len _ fun Δ => ⟨ε Δ, q Δ, hq Δ, by rw [MvPolynomial.eval₂Hom_X']; exact hpq Δ⟩
  have heq : phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) =
      (phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int ((phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩)).comp MvPolynomial.C)
        (((phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p)).comp
          MvPolynomial.C)) r
    · intro Δ
      rw [phiOf_X, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', hp Δ]
  rw [heq]
  exact hbij.comp hψ

end CompanionTheory.Groth

end
