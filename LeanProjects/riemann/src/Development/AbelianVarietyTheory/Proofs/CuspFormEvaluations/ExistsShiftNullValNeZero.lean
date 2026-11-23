import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsorStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaBase

open GlobalTheory.ThetaCoord GlobalTheory.VVRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mk_eq_zero_iff (k : ℕ) (m : Dw.La) :
    (Submodule.Quotient.mk m : LatMod Dw k) = 0 ↔ ∃ m' : Dw.La, k • m' = m := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

theorem exists_shift {R : ℕ} (hR : R ≠ 0) (q : LatMod Dw (R ^ 4)) (hq : R • q = 0) :
    ∃ u : LatMod Dw R, (Submodule.Quotient.mk (R ^ 3 • qRep u) : LatMod Dw (R ^ 4)) = q := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨m', hm⟩ := (mk_eq_zero_iff (R ^ 4) (R • m)).1 hq
  have e : R ^ 3 • m' = m := by
    have h : R • R ^ 3 • m' = R • m := by rw [← hm, ← mul_nsmul', ← pow_succ']
    refine Dw.unimod.1 (LinearMap.ext fun v => nsmul_right_injective hR ?_)
    have := congrArg (fun t => Dw.EF t v) h
    simpa only [map_nsmul, LinearMap.smul_apply] using this
  refine ⟨Submodule.Quotient.mk m', ?_⟩
  have h : (Submodule.Quotient.mk (qRep (Submodule.Quotient.mk m' : LatMod Dw R)) : LatMod Dw R) =
      Submodule.Quotient.mk m' := Classical.choose_spec (Submodule.Quotient.mk_surjective _ _)
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub] at h ⊢
  obtain ⟨d, hd⟩ := (mk_eq_zero_iff R _).1 h
  refine (mk_eq_zero_iff _ _).2 ⟨d, ?_⟩
  rw [← e, ← smul_sub, ← hd, ← mul_nsmul', ← pow_succ]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem gen_ne_zero {K : Type} [CommRing K] [Nontrivial K] [Algebra c.F K] (y : FrPt Xo c K) :
    (SecM.ofSec Xo.univ.t.G y.s : SecM Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk y.x)) ≠ 0 := fun h => by
  have h₀ : ∀ i, y.s.f i = 0 := fun i => congrFun (congrArg Subtype.val h) i
  exact zero_ne_one ((y.gen y.s).unique (y₁ := 0) (y₂ := 1) (fun i => by rw [h₀, MulZeroClass.mul_zero])
    (fun i => by rw [h₀, MulZeroClass.mul_zero]))

theorem exists_nullVal_ne_zero (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K)
    (N : ℕ) {n : ℕ} (hn : 2 ≤ n) (a : ptO Xo y.x ⟶ Xo.univ.t.G) :
    ∃ z : ptO Xo y.x ⟶ Xo.univ.t.G, z ^ n = 1 ∧
      ∀ p w, IsNullVal Xo c N y p w → p ^ N = a * z → w ≠ 0 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange (UnivPol.pol Xo) y.x hn hK y.s
    (gen_ne_zero Xo c y) a
  refine ⟨z, hz, ?_⟩
  rintro p w ⟨F, ⟨t', α₀, α, s₁, U, -, rfl, -, -, -, hs₁, hU, hF⟩, hw⟩ hp h₀
  let o : (Over.mk y.x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk y.x).left ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ o)
  replace hJ : Good Xo.univ.t.PP.L o J := hJ
  have b₁ := sv_act hU.pt_eq hF (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ t'
  have b₃ := sv_of_isValueAt hw (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [b₃, b₂, hp, h₀, map_zero, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu o J hJ))).ne_zero b₁.symm

end GlobalTheory.EtaBase

namespace GlobalTheory

open GlobalTheory.EtaBase

theorem exists_shift_nullVal_ne_zero : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → 1 < R → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → K), IsFullLev Xo (R ^ 4) y.x ev → (∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) → ∀ (n : ℕ) (x₀ : Fin n → Dw.La) (g : LevGrp Dw (R ^ 4)), ∃ u : Fin n → LatMod Dw R, ∀ b, w (g (shiftFam R x₀ u b)) ≠ 0 := by
  intro hL E _ _ _ H Dw l Xo c R _ hR K _ _ _ y ev w hev hw n x₀ g
  have hR₀ : R ≠ 0 := by omega
  have e₀ : ev 0 = 1 := by
    have := hev.1 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have es : ∀ (m : ℕ) q, ev (m • q) = ev q ^ m := fun m q => by
    induction m with
    | zero => rw [zero_smul, e₀, pow_zero]
    | succ m ih => rw [succ_nsmul, hev.1, ih, pow_succ]
  have sur := ((T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (by positivity)).2.2.1 K y.x ev hev).1
  have key : ∀ x : Dw.La, ∃ u : LatMod Dw R,
      w (g (Submodule.Quotient.mk (x + R • qRep u))) ≠ 0 := fun x => by
    obtain ⟨z, hz, h⟩ := exists_nullVal_ne_zero Xo c hL y (R ^ 2) hR (ev (g (Submodule.Quotient.mk x)) ^ R ^ 2)
    obtain ⟨q, rfl⟩ := sur z (by rw [pow_succ', pow_mul, hz, one_pow])
    have hq : R • q = 0 := hev.2.2 K (RingHom.id K) _ _ (by rw [es, hz, e₀])
    obtain ⟨u, hu⟩ := exists_shift hR₀ (g.symm q) (by rw [← map_nsmul, hq, map_zero])
    refine ⟨u, h _ _ (hw _) ?_⟩
    rw [← es, ← es, ← hev.1, ← g.apply_symm_apply q, ← hu, ← map_nsmul, ← map_nsmul, ← map_add]
    congr 2
    show (Submodule.Quotient.mk (R ^ 2 • (x + R • qRep u)) : LatMod Dw (R ^ 4)) =
      Submodule.Quotient.mk (R ^ 2 • x + R ^ 3 • qRep u)
    rw [smul_add, ← mul_nsmul', ← pow_succ]
  choose u hu using key
  exact ⟨fun b => u (x₀ b), fun b => hu (x₀ b)⟩

end GlobalTheory
