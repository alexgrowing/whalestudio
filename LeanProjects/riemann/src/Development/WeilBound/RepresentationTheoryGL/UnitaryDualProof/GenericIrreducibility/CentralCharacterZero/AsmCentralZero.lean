import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.RgUd.Exp.Asm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem asmGeneric {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (h : IsGeneric π) (φ : π.Equiv σ) : IsGeneric σ := by
  obtain ⟨ψ, hc, hne, hg⟩ := h
  exact ⟨ψ, hc, hne, hg.of_equiv φ⟩

theorem asmUnitComp {G H X : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (f : H →* G) (h : IsUnitarisable ρ) : IsUnitarisable (ρ.comp f) := by
  obtain ⟨B, h1, h2, h3⟩ := h
  exact ⟨B, h1, h2, fun g v w => h3 (f g) v w⟩

theorem asmInd {r t N : ℕ} (e : r + t = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {A : Representation ℂ (GL (Fin r) k) V} {B : Representation ℂ (GL (Fin t) k) W}
    (hG : IsGeneric (ind₂ (stdSum e) (extTensor A B))) (hU : IsUnitarisable (ind₂ (stdSum e) (extTensor A B))) :
    IsGeneric (prod₂ A B) ∧ IsUnitarisable (prod₂ A B) := by
  subst e
  exact ⟨hG, hU⟩

theorem asmScalar {n : ℕ} (hn : n = 0) (z : kˣ) : GeneralLinearGroup.scalar (Fin n) z = 1 :=
  Units.ext (Matrix.ext fun i _ => absurd i.2 (by omega))

theorem asmCentralZero {n : ℕ} (hn : n = 0) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) k) V) : HasCentralChar ρ 1 := fun z v => by
  rw [asmScalar hn z, map_one]
  simp

theorem asmNormInv (ω : kˣ →* ℂˣ) (m s : ℝ) (hn : ∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ (m * s)) :
    ∀ z, ‖((ω⁻¹ : kˣ →* ℂˣ) z : ℂ)‖ = nabs k z ^ (m * -s) := by
  intro z
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hn, ← Real.rpow_neg (nabs_pos' k z).le, mul_neg]

theorem asmZero (ω : kˣ →* ℂˣ) (m : ℕ) (hm : 0 < m) (s : ℝ)
    (hn : ∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ ((m : ℝ) * s)) (h1 : ∀ z, ‖(ω z : ℂ)‖ = 1) : s = 0 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have hne : nabs k ϖ ≠ 1 := fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hpos := nabs_pos' k ϖ
  have h2 : nabs k ϖ ^ ((m : ℝ) * s) = 1 := (hn ϖ).symm.trans (h1 ϖ)
  have h3 : (m : ℝ) * s * Real.log (nabs k ϖ) = 0 := by
    have := congrArg Real.log h2
    rwa [Real.log_rpow hpos, Real.log_one] at this
  have hL0 : Real.log (nabs k ϖ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hne
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  rcases mul_eq_zero.1 h3 with h | h
  · exact (mul_eq_zero.1 h).resolve_left hm'
  · exact absurd h hL0

theorem asmLower (hL : ExpLow k) (y z : IrrGL k) {N : ℕ} (hd2 : ∑ a, (![y, z] a).1 = N)
    (hG : IsGeneric (prodIrr ![y, z] hd2)) (hU : IsUnitarisable (prodIrr ![y, z] hd2)) (hy : 1 ≤ y.1)
    (ω : kˣ →* ℂˣ) (s : ℝ) (hm : 0 < z.1) (hω : HasCentralChar z.rep ω)
    (hn : ∀ w, ‖(ω w : ℂ)‖ = nabs k w ^ ((z.1 : ℝ) * s)) : -1 / 2 < s := by
  have h : y.1 + z.1 = N := (Fin.sum_univ_two _).symm.trans hd2
  have E : Nonempty ((ind₂ (stdSum h) (extTensor y.rep z.rep)).Equiv (prodIrr ![y, z] hd2)) :=
    GlobalTheory.CompanionTheory.BZSegComm.nonempty_ind₂_equiv_multiProd (d := fun a => (![y, z] a).1) hd2 h
      (fun a => (![y, z] a).rep)
  obtain ⟨E⟩ := E
  have hgu := asmInd h (asmGeneric hG E.symm) (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E.symm hU)
  exact hL y.1 z.1 _ _ y.rep z.rep ω s hy hm y.2.rep.smooth z.2.rep.smooth hgu.1 hgu.2 hω hn

theorem asmThetaGU (hT : ThetaProd k) (hF : ThetaFacts k) {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hA : IsSmooth A) (hB : IsSmooth B) (hG : IsGeneric (prod₂ A B)) (hU : IsUnitarisable (prod₂ A B)) :
    IsGeneric (prod₂ (B.comp (Zc.Cos.thetaW k t)) (A.comp (Zc.Cos.thetaW k r))) ∧
      IsUnitarisable (prod₂ (B.comp (Zc.Cos.thetaW k t)) (A.comp (Zc.Cos.thetaW k r))) := by
  obtain ⟨Θ⟩ := hT r t V W A B hA hB
  have hG2 : IsGeneric ((prod₂ A B).comp (Zc.Cos.thetaW k (r + t))) := hF.1 _ _ _ hG
  have hU2 : IsUnitarisable ((prod₂ A B).comp (Zc.Cos.thetaW k (r + t))) := asmUnitComp _ _ hU
  exact asmInd (add_comm t r) (asmGeneric hG2 Θ) (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv Θ hU2)

theorem asmSmoothTheta {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    (h : IsSmooth ρ) : IsSmooth (ρ.comp (Zc.Cos.thetaW k n)) :=
  GlobalTheory.SmGL.isSmooth_comp h _ (GlobalTheory.CompanionTheory.ThetaProd.continuous_thetaW n)

theorem asmPair (z y : IrrGL k) {N : ℕ} (hd3 : ∑ a, (![z, y] a).1 = N) (hG : IsGeneric (prodIrr ![z, y] hd3))
    (hU : IsUnitarisable (prodIrr ![z, y] hd3)) :
    IsGeneric (prod₂ z.rep y.rep) ∧ IsUnitarisable (prod₂ z.rep y.rep) := by
  have h : z.1 + y.1 = N := (Fin.sum_univ_two _).symm.trans hd3
  have E : Nonempty ((ind₂ (stdSum h) (extTensor z.rep y.rep)).Equiv (prodIrr ![z, y] hd3)) :=
    GlobalTheory.CompanionTheory.BZSegComm.nonempty_ind₂_equiv_multiProd (d := fun a => (![z, y] a).1) hd3 h
      (fun a => (![z, y] a).rep)
  obtain ⟨E⟩ := E
  exact asmInd h (asmGeneric hG E.symm) (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E.symm hU)

theorem asmUpper (hL : ExpLow k) (hT : ThetaProd k) (hF : ThetaFacts k) (z y : IrrGL k) {N : ℕ}
    (hd3 : ∑ a, (![z, y] a).1 = N) (hG : IsGeneric (prodIrr ![z, y] hd3))
    (hU : IsUnitarisable (prodIrr ![z, y] hd3)) (hy : 1 ≤ y.1) (ω : kˣ →* ℂˣ) (s : ℝ) (hm : 0 < z.1)
    (hω : HasCentralChar z.rep ω) (hn : ∀ w, ‖(ω w : ℂ)‖ = nabs k w ^ ((z.1 : ℝ) * s)) : -1 / 2 < -s := by
  have hgu := asmPair z y hd3 hG hU
  have hgu2 := asmThetaGU hT hF z.rep y.rep z.2.rep.smooth y.2.rep.smooth hgu.1 hgu.2
  have hc : HasCentralChar (z.rep.comp (Zc.Cos.thetaW k z.1)) ω⁻¹ := hF.2 _ _ _ _ hω
  have hn2 : ∀ w, ‖((ω⁻¹ : kˣ →* ℂˣ) w : ℂ)‖ = nabs k w ^ ((z.1 : ℝ) * -s) := asmNormInv ω _ _ hn
  exact hL y.1 z.1 _ _ (y.rep.comp (Zc.Cos.thetaW k y.1)) (z.rep.comp (Zc.Cos.thetaW k z.1)) ω⁻¹ (-s) hy hm
    (asmSmoothTheta _ y.2.rep.smooth) (asmSmoothTheta _ z.2.rep.smooth) hgu2.1 hgu2.2 hc hn2

end PositivityTheory.RgUd.Exp.Asm

namespace PositivityTheory.RgUd.Exp

open PositivityTheory.RgUd.Exp.Asm

theorem expBound_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    MoveLast k → MoveFirst k → ThetaProd k → ThetaFacts k → CentralProd2 k → ExpLow k → ExpBound k := by
  intro hML hMF hT hF hC hL
  unfold ExpBound
  intro h N x hd hirr hU hG j ω s hm hω hn
  obtain ⟨y, hd2, ⟨E⟩⟩ := hML h N x hd hirr j
  have hy2 : y.1 + (x j).1 = N := (Fin.sum_univ_two _).symm.trans hd2
  rcases Nat.eq_zero_or_pos y.1 with hy0 | hy0
  · have hcy : HasCentralChar y.rep 1 := asmCentralZero hy0 y.rep
    have hcπ : HasCentralChar (prodIrr ![y, x j] hd2) (1 * ω) := hC y (x j) N hd2 1 ω hcy hω
    have hcπ' : HasCentralChar (prodIrr x hd) (1 * ω) := hasCentralChar_of_equiv E.symm hcπ
    have := Model.nontrivial_of_isIrreducible hirr
    have h1 : ∀ z, ‖(((1 * ω) z : ℂˣ) : ℂ)‖ = 1 := fun z =>
      GlobalTheory.LocGL.UnitaryOrder.norm_eq_one_of_isUnitarisable hU (hcπ' z)
    have hs : s = 0 := asmZero ω (x j).1 hm s hn (fun z => by simpa using h1 z)
    rw [hs, abs_zero]
    norm_num
  · have hlow := asmLower hL y (x j) hd2 (asmGeneric hG E)
      (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E hU) hy0 ω s hm hω hn
    obtain ⟨y', hd3, ⟨E'⟩⟩ := hMF h N x hd hirr j
    have hy3 : (x j).1 + y'.1 = N := (Fin.sum_univ_two _).symm.trans hd3
    have hy' : 1 ≤ y'.1 := by omega
    have hup := asmUpper hL hT hF (x j) y' hd3 (asmGeneric hG E')
      (GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E' hU) hy' ω s hm hω hn
    rw [abs_lt]
    constructor <;> linarith

end PositivityTheory.RgUd.Exp
