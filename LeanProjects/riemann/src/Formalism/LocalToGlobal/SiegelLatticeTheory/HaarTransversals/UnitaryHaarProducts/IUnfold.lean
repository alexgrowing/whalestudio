import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.ReductionTau
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ExistsMulMulConjTransposeEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.FreeQuotientRank

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal NNReal
open Matrix

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH

section MultAbs

variable {G : Type*} [Group G]

theorem mult_mono (Γ : Subgroup G) {Ω Ω' : Set G} (h : Ω ⊆ Ω') (x : G) :
    FoldBound.mult Γ Ω x ≤ FoldBound.mult Γ Ω' x := by
  unfold FoldBound.mult
  refine iSup_mono fun y => ?_
  exact ENat.toENNReal_le.2 (Set.encard_le_encard fun γ hγ => h hγ)

theorem mult_union (Γ : Subgroup G) (Ω Ω' : Set G) (x : G) :
    FoldBound.mult Γ (Ω ∪ Ω') x ≤ FoldBound.mult Γ Ω x + FoldBound.mult Γ Ω' x := by
  unfold FoldBound.mult
  refine iSup_le fun y => ?_
  have e : ({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω ∪ Ω'} : Set Γ) =
      {γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω} ∪ {γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω'} := by
    ext γ; simp
  rw [e]
  refine le_trans (ENat.toENNReal_le.2 (Set.encard_union_le _ _)) ?_
  rw [ENat.toENNReal_add]
  exact add_le_add (le_iSup (fun y => ((({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞)) y)
    (le_iSup (fun y => ((({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω'} : Set Γ).encard : ℕ∞) : ℝ≥0∞)) y)

theorem mult_biUnion {ι : Type*} (Γ : Subgroup G) (A : Finset ι) (Ω : ι → Set G) (x : G) :
    FoldBound.mult Γ (⋃ i ∈ A, Ω i) x ≤ ∑ i ∈ A, FoldBound.mult Γ (Ω i) x := by
  induction A using Finset.induction_on with
  | empty =>
    unfold FoldBound.mult
    simp
  | insert a A ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (mult_union Γ _ _ x).trans (add_le_add le_rfl ih)

theorem mult_rtrans (Γ : Subgroup G) (Ω : Set G) (a x : G) :
    FoldBound.mult Γ ((fun w => w * a) ⁻¹' Ω) x = FoldBound.mult Γ Ω x := by
  unfold FoldBound.mult
  have e : ∀ y : G, ({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ (fun w => w * a) ⁻¹' Ω} : Set Γ) =
      {γ : Γ | x⁻¹ * ((γ : G) * (y * a)) ∈ Ω} := by
    intro y; ext γ; simp [mul_assoc]
  simp only [e]
  exact (Equiv.mulRight a).iSup_comp (g := fun y => ((({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞))

theorem mult_left (Γ : Subgroup G) (Ω : Set G) (γ : G) (hγ : γ ∈ Γ) (x : G) :
    FoldBound.mult Γ Ω (γ * x) = FoldBound.mult Γ Ω x := by
  unfold FoldBound.mult
  refine iSup_congr fun y => ?_
  have : ({δ : Γ | (γ * x)⁻¹ * ((δ : G) * y) ∈ Ω} : Set Γ) =
      (fun δ : Γ => (⟨γ, hγ⟩ : Γ) * δ) '' {δ : Γ | x⁻¹ * ((δ : G) * y) ∈ Ω} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨(⟨γ, hγ⟩ : Γ)⁻¹ * δ, ?_, by simp⟩
      simpa [mul_assoc] using h
    · rintro ⟨δ', h, rfl⟩
      simpa [mul_assoc] using h
  rw [this, (mul_right_injective (⟨γ, hγ⟩ : Γ)).encard_image]

end MultAbs

section Inst

variable (I : AutInst)

def normI (g : I.Ginf) : ℝ := ∏ v, WuDecay.opn (uMat (g v))

def nilradicalExponent : ℝ := 4 * (I.n : ℝ) ^ 2 * Real.sqrt (2 * ((Finset.univ.sup fun v => I.qAt v : ℕ) : ℝ))

theorem normI_nonneg (g : I.Ginf) : 0 ≤ normI I g :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem exponentN1_nonneg : 0 ≤ nilradicalExponent I := by unfold nilradicalExponent; positivity

def TauTrans : Prop :=
  1 ≤ I.n → ∀ (x : I.GA) (g : I.Ginf),
    LitS.Size.tau1 I x ≤ LitS.Size.tau1 I (x * ((g, 1) : I.GA)) * normI I g ^ ((1 : ℝ) / (I.f : ℝ))

def NormPow : Prop :=
  1 ≤ I.n → ∀ g : I.Ginf, normI I g ^ ((4 * I.n ^ 2 : ℕ) : ℝ) ≤ normI I g ^ nilradicalExponent I

def NormGeOne : Prop := 1 ≤ I.n → ∀ g : I.Ginf, 1 ≤ normI I g

def OmCover : Prop :=
  ∀ Ω : Set I.GA, IsCompact Ω → ∃ (r : InfinitePlace I.F → ℝ) (K' : Subgroup I.Gf) (A : Finset I.Gf),
    (∀ v, 0 ≤ r v) ∧ (K' : Set I.Gf) ⊆ I.Kset ∧
      Ω ⊆ ⋃ a ∈ A, (fun w => w * ((1, a) : I.GA)⁻¹) ⁻¹' Count.Om I r (K' : Set I.Gf)

end Inst

theorem normInf_eq {D : D7} (X : HidaSetting D) (g : X.B.I.Ginf) : WuDecay.normInf X g = normI X.B.I g := rfl

theorem N1_eq_exponentN1 {D : D7} (X : HidaSetting D) : WuDecay.N1 X = nilradicalExponent X.B.I := rfl

theorem n_pos {D : D7} (X : HidaSetting D) : 1 ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := Formalism.BasicNotions.Ranks.r_eq (R := D.R)
  have h3 := D.R.two_le_m
  omega

theorem f_pos (I : AutInst) : 0 < (I.f : ℝ) := by
  have : 0 < I.f := Module.finrank_pos
  exact_mod_cast this

theorem multPoly_of {D : D7} (X : HidaSetting D) (hL : Count.LatCount X.B.I) (hT : Formalism.MainNotions.LeviCoordinates.DistTri)
    (hR : LitS.ReductionTau) (hTT : TauTrans X.B.I) (hNP : NormPow X.B.I) (hO : OmCover X.B.I) :
    Cut.MultPoly X := by
  intro Ω CC hΩ hCC
  have hn := n_pos X
  obtain ⟨hcont, hpos⟩ := hR X.B.I hn
  have hMB := Count.multBound_of_latCount X.B.I hL hT
  obtain ⟨r, K', A, hr, hK', hcov⟩ := hO Ω hΩ
  rcases CC.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, fun c hc => by simp [hE] at hc⟩
  obtain ⟨c0, hc0, hmin⟩ := hCC.exists_isMinOn hne hcont.continuousOn
  set k : ℕ := 4 * X.B.I.n ^ 2 * X.B.I.f with hk
  set m := LitS.Size.tau1 X.B.I c0 with hm_def
  have hm : 0 < m := (hpos c0).1
  have hCOm : 0 ≤ Count.COm X.B.I r := by unfold Count.COm; positivity
  refine ⟨(A.card : ℝ) * Count.COm X.B.I r / m ^ k, fun c hc g => ?_⟩
  set x := c * ((g, 1) : X.B.I.GA) with hx_def
  have hx : 0 < LitS.Size.tau1 X.B.I x := (hpos x).1
  have hmult : FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω x ≤
      (A.card : ℝ≥0∞) * ENNReal.ofReal (Count.COm X.B.I r / LitS.Size.tau1 X.B.I x ^ k) := by
    refine (mult_mono _ hcov x).trans ((mult_biUnion _ A _ x).trans ?_)
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul A _ _ fun a _ => ?_
    rw [mult_rtrans]
    exact hMB r hr K' hK' x hx
  refine hmult.trans ?_

  set N := normI X.B.I g with hN
  have hN0 : 0 ≤ N := normI_nonneg _ g
  set P := N ^ ((1 : ℝ) / (X.B.I.f : ℝ)) with hP
  have hτ : m ≤ LitS.Size.tau1 X.B.I x * P := (hmin hc).trans (hTT hn c g)
  have hPk : P ^ k = N ^ ((4 * X.B.I.n ^ 2 : ℕ) : ℝ) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    have hf := f_pos X.B.I
    rw [hk]; push_cast
    field_simp
  have hkey : 1 / LitS.Size.tau1 X.B.I x ^ k ≤ P ^ k / m ^ k := by
    rw [div_le_div_iff₀ (pow_pos hx k) (pow_pos hm k), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm.le (by rw [mul_comm]; exact hτ) k
  have hreal : (A.card : ℝ) * (Count.COm X.B.I r / LitS.Size.tau1 X.B.I x ^ k) ≤
      (A.card : ℝ) * Count.COm X.B.I r / m ^ k * WuDecay.normInf X g ^ WuDecay.N1 X := by
    rw [normInf_eq, N1_eq_exponentN1, ← hN]
    have h1 : Count.COm X.B.I r / LitS.Size.tau1 X.B.I x ^ k ≤ Count.COm X.B.I r * (P ^ k / m ^ k) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hkey hCOm
    have h2 : P ^ k ≤ N ^ nilradicalExponent X.B.I := hPk ▸ hNP hn g
    calc (A.card : ℝ) * (Count.COm X.B.I r / LitS.Size.tau1 X.B.I x ^ k)
        ≤ (A.card : ℝ) * (Count.COm X.B.I r * (P ^ k / m ^ k)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = (A.card : ℝ) * Count.COm X.B.I r / m ^ k * P ^ k := by ring
      _ ≤ (A.card : ℝ) * Count.COm X.B.I r / m ^ k * N ^ nilradicalExponent X.B.I :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hreal

section Steps

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def SCompact : Prop :=
  ∃ CS : Set X.B.I.GA, IsCompact CS ∧ ∀ y : X.B.I.GA, y.1 ∈ X.SinfU u → y.2 ∈ SfinU X u →
    ∃ σ ∈ Srat X u, ∃ c ∈ CS, y = σ * c

def LevelSubgroupCompactOpen : Prop := IsOpen X.K2 ∧ IsCompact X.K2

def PsiUnit : Prop := ∀ n ∈ X.NfinU u, ‖X.psiFinU u n‖ ≤ 1

def ColBound (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ T : Cu X u hK, ∃ M : ℝ, ∀ (h : Hfin X u) (ξ : X.Vpi u),
    ‖(T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (1, h)‖ ≤ M * ‖ξ‖

def WuNormInv : Prop := ∀ s ∈ X.SinfU u, ∀ x, ‖X.Wu u (s * x)‖ = ‖X.Wu u x‖

def WeightMeas : Prop := Measurable (WuDecay.nuInf X u) ∧ Measurable fun x => ‖X.Wu u x‖

def SinfSection : Prop :=
  ∀ C : Set X.B.I.Ginf, IsCompact C → ∃ (a : X.B.I.Ginf → ℝ≥0∞) (B : ℝ≥0∞), Measurable a ∧ (∀ x, a x ≤ 1) ∧
    B < ⊤ ∧ (∀ x, ∫⁻ p, a (p.1 * p.2 * x) ∂((X.muN u).prod (X.muH u)) ≤ B) ∧
    ∀ x, ∃ t ∈ X.SinfU u, ∀ c ∈ C, c ∈ X.SinfU u → a (c * t * x) = 1

end Steps

section SGrp

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem one_mem_sinf : (1 : X.B.I.Ginf) ∈ X.SinfU u := by
  intro v
  have e : uMat ((1 : X.B.I.Ginf) v) = 1 := by simp [uMat]
  rw [e]
  refine ⟨fun a => ?_, ?_⟩ <;> simp [Submodule.zero_mem]

theorem one_mem_sfin : (1 : X.B.I.Gf) ∈ SfinU X u := by
  have e : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
  refine ⟨fun a => ?_, ?_⟩ <;> simp [e, Submodule.zero_mem]

theorem mem_sset_of_closure (hS : SGroup X u) {y : X.B.I.GA}
    (hy : y ∈ Subgroup.closure {y : X.B.I.GA | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u}) :
    y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u := by
  have : y ∈ ((Subgroup.closure {y : X.B.I.GA | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u} : Subgroup X.B.I.GA) :
      Set X.B.I.GA) := hy
  rw [hS] at this
  exact this

theorem sinf_mul (hS : SGroup X u) {s t : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (ht : t ∈ X.SinfU u) :
    s * t ∈ X.SinfU u := by
  have h := mem_sset_of_closure X u hS (Subgroup.mul_mem _
    (Subgroup.subset_closure (show ((s, 1) : X.B.I.GA).1 ∈ X.SinfU u ∧ ((s, 1) : X.B.I.GA).2 ∈ SfinU X u from
      ⟨hs, one_mem_sfin X u⟩))
    (Subgroup.subset_closure (show ((t, 1) : X.B.I.GA).1 ∈ X.SinfU u ∧ ((t, 1) : X.B.I.GA).2 ∈ SfinU X u from
      ⟨ht, one_mem_sfin X u⟩)))
  simpa using h.1

theorem sinf_inv (hS : SGroup X u) {s : X.B.I.Ginf} (hs : s ∈ X.SinfU u) : s⁻¹ ∈ X.SinfU u := by
  have h := mem_sset_of_closure X u hS (Subgroup.inv_mem _
    (Subgroup.subset_closure (show ((s, 1) : X.B.I.GA).1 ∈ X.SinfU u ∧ ((s, 1) : X.B.I.GA).2 ∈ SfinU X u from
      ⟨hs, one_mem_sfin X u⟩)))
  simpa using h.1

theorem sfin_mul (hS : SGroup X u) {s t : X.B.I.Gf} (hs : s ∈ SfinU X u) (ht : t ∈ SfinU X u) :
    s * t ∈ SfinU X u := by
  have h := mem_sset_of_closure X u hS (Subgroup.mul_mem _
    (Subgroup.subset_closure (show ((1, s) : X.B.I.GA).1 ∈ X.SinfU u ∧ ((1, s) : X.B.I.GA).2 ∈ SfinU X u from
      ⟨one_mem_sinf X u, hs⟩))
    (Subgroup.subset_closure (show ((1, t) : X.B.I.GA).1 ∈ X.SinfU u ∧ ((1, t) : X.B.I.GA).2 ∈ SfinU X u from
      ⟨one_mem_sinf X u, ht⟩)))
  simpa using h.2

theorem srat_mem (hS : SGroup X u) {σ : X.B.I.GA} (hσ : σ ∈ Srat X u) :
    σ.1 ∈ X.SinfU u ∧ σ.2 ∈ SfinU X u :=
  mem_sset_of_closure X u hS (Subgroup.mem_inf.1 hσ).2

theorem nfin_sfin {n : X.B.I.Gf} (hn : n ∈ X.NfinU u) : n ∈ SfinU X u := ⟨hn.1, hn.2.1⟩

theorem hfin_sfin (h : Hfin X u) : (h : X.B.I.Gf) ∈ SfinU X u := by
  have hfix : ∀ y ∈ fixSet X u, X.B.I.fmat (h : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := h.2
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (Or.inl (Or.inl ⟨a, rfl⟩)), sub_self]
    exact Submodule.zero_mem _
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (Or.inr rfl), sub_self]
    exact Submodule.zero_mem _

theorem ninf_sinf {s : X.B.I.Ginf} (hs : s ∈ X.NinfU u) : s ∈ X.SinfU u := fun v => (hs v).1

theorem nuInf_left (hS : SGroup X u) {s : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (x : X.B.I.Ginf) :
    WuDecay.nuInf X u (s * x) = WuDecay.nuInf X u x := by
  unfold WuDecay.nuInf
  let e : X.SinfU u ≃ X.SinfU u :=
    { toFun := fun t => ⟨(t : X.B.I.Ginf) * s, sinf_mul X u hS t.2 hs⟩
      invFun := fun t => ⟨(t : X.B.I.Ginf) * s⁻¹, sinf_mul X u hS t.2 (sinf_inv X u hS hs)⟩
      left_inv := fun t => by ext; simp
      right_inv := fun t => by ext; simp }
  conv_rhs => rw [← e.iInf_comp]
  refine iInf_congr fun t => ?_
  simp [e, mul_assoc]

end SGrp

theorem setLIntegral_le_of_cover {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {s : Set G} (h : IsFundamentalDomain Γ s μ)
    (Φ Ψ : G → ℝ≥0∞) (hΨ : Measurable Ψ) (hc : ∀ x, Φ x ≤ ∑' g : Γ, Ψ ((g : G) * x)) :
    ∫⁻ x in s, Φ x ∂μ ≤ ∫⁻ x, Ψ x ∂μ := by
  haveI : MeasurableConstSMul Γ G := ⟨fun c => measurable_const_mul (c : G)⟩
  rw [h.lintegral_eq_tsum'' Ψ]
  calc ∫⁻ x in s, Φ x ∂μ ≤ ∫⁻ x in s, ∑' g : Γ, Ψ ((g : G) * x) ∂μ := lintegral_mono hc
    _ = ∑' g : Γ, ∫⁻ x in s, Ψ (g • x) ∂μ :=
        lintegral_tsum fun g => ((hΨ.comp (measurable_const_mul (g : G))).aemeasurable)

section Weight

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def wt (x : X.B.I.Ginf) : ℝ≥0∞ := ENNReal.ofReal (WuDecay.nuInf X u x ^ WuDecay.N1 X) * ‖X.Wu u x‖ₑ

theorem wt_ne_top (x : X.B.I.Ginf) : wt X u x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top

theorem wt_left (hSG : SGroup X u) (hWI : WuNormInv X u) {s : X.B.I.Ginf} (hs : s ∈ X.SinfU u)
    (x : X.B.I.Ginf) : wt X u (s * x) = wt X u x := by
  unfold wt
  rw [nuInf_left X u hSG hs, ← ofReal_norm, ← ofReal_norm, hWI _ hs]

theorem wt_meas (hWM : WeightMeas X u) : Measurable (wt X u) := by
  refine Measurable.mul (ENNReal.measurable_ofReal.comp (hWM.1.pow_const _)) ?_
  have e : (fun x => ‖X.Wu u x‖ₑ) = fun x => ENNReal.ofReal ‖X.Wu u x‖ := by
    funext x; exact (ofReal_norm _).symm
  rw [e]; exact ENNReal.measurable_ofReal.comp hWM.2

theorem wt_int (hWD : WuDecay.WuDecay X) : ∫⁻ x, wt X u x ∂(X.nuQ u) < ⊤ := by
  have h := (hWD u).2
  unfold WuDecay.WuWeighted at h
  calc ∫⁻ x, wt X u x ∂(X.nuQ u)
      = ∫⁻ x, ‖X.Wu u x‖ₑ * ENNReal.ofReal (WuDecay.nuInf X u x ^ WuDecay.N1 X) ∂(X.nuQ u) :=
        lintegral_congr fun x => mul_comm _ _
    _ < ⊤ := h

theorem ae_NH : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u ∧ p.2 ∈ (Hinf X u : Set X.B.I.Ginf) := by
  haveI := (X.muN_haar u).1
  haveI := (X.muH_haar u).1
  rw [ae_iff]
  refine measure_mono_null (t := (X.NinfU u)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ ((Hinf X u : Set X.B.I.Ginf))ᶜ) ?_ ?_
  · intro p hp
    simp only [Set.mem_ofPred_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨hp, trivial⟩
    · exact Or.inr ⟨trivial, hp⟩
  · refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, show (X.muN u) (X.NinfU u)ᶜ = 0 from (X.muN_haar u).2.2.1, zero_mul]
    · rw [Measure.prod_prod, show (X.muH u) ((Hinf X u : Set X.B.I.Ginf))ᶜ = 0 from (X.muH_haar u).2.2.1,
        mul_zero]

theorem weil_bound (hSG : SGroup X u) (hWI : WuNormInv X u) (hWM : WeightMeas X u)
    (a : X.B.I.Ginf → ℝ≥0∞) (ha : Measurable a) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hBint : ∀ x, ∫⁻ p, a (p.1 * p.2 * x) ∂((X.muN u).prod (X.muH u)) ≤ B) :
    ∫⁻ x, wt X u x * a x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) ≤ (∫⁻ x, wt X u x ∂(X.nuQ u)) * B := by
  have hweil := X.nuQ_weil u (fun x => wt X u x * a x) ((wt_meas X u hWM).mul ha)
  rw [hweil, ← lintegral_mul_const' _ _ hB]
  refine lintegral_mono fun x => ?_
  refine (lintegral_map_le (fun s => wt X u (s * x) * a (s * x)) (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)).trans ?_
  have hae2 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)),
      wt X u (p.1 * p.2 * x) * a (p.1 * p.2 * x) = wt X u x * a (p.1 * p.2 * x) := by
    filter_upwards [ae_NH X u] with p hp
    have hs : p.1 * p.2 ∈ X.SinfU u := sinf_mul X u hSG (ninf_sinf X u hp.1) (hinf_le_sinf X u p.2 hp.2)
    rw [wt_left X u hSG hWI hs]
  rw [lintegral_congr_ae hae2, lintegral_const_mul' _ _ (wt_ne_top X u x)]
  exact mul_le_mul' le_rfl (hBint x)

end Weight

theorem prod_bound {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (K0 : ℝ≥0∞) (hK0 : K0 ≠ ⊤)
    (a : X.B.I.Ginf → ℝ≥0∞) (ha1 : ∀ x, a x ≤ 1) (Cf : Set X.B.I.Gf) (hμf : X.B.μf Cf ≠ ⊤) :
    ∫⁻ y, K0 * (wt X u y.1 * a y.1) * Cf.indicator 1 y.2 ∂(X.B.I.muA X.B.μf) ≤
      K0 * (∫⁻ x, wt X u x * a x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)) * X.B.μf Cf := by
  have hfin : ∀ x, K0 * (wt X u x * a x) ≠ ⊤ := fun x =>
    ENNReal.mul_ne_top hK0 (ENNReal.mul_ne_top (wt_ne_top X u x) (ne_top_of_le_ne_top ENNReal.one_ne_top (ha1 x)))
  unfold AutInst.muA
  calc ∫⁻ y, K0 * (wt X u y.1 * a y.1) * Cf.indicator 1 y.2 ∂((Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)).prod X.B.μf)
      ≤ ∫⁻ x, ∫⁻ z, K0 * (wt X u x * a x) * Cf.indicator 1 z ∂X.B.μf ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) :=
        lintegral_prod_le _
    _ ≤ ∫⁻ x, K0 * (wt X u x * a x) * X.B.μf Cf ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
        refine lintegral_mono fun x => ?_
        rw [lintegral_const_mul' _ _ (hfin x)]
        exact mul_le_mul' le_rfl (lintegral_indicator_one_le Cf)
    _ = K0 * (∫⁻ x, wt X u x * a x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)) * X.B.μf Cf := by
        rw [lintegral_mul_const' _ _ hμf, lintegral_const_mul' _ _ hK0]

theorem iUnfold_of {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)
    (hSG : SGroup X u) (hSC : SCompact X u) (hKT : LevelSubgroupCompactOpen X) (hPU : PsiUnit X u) (hCB : ColBound X u hK)
    (hWI : WuNormInv X u) (hWM : WeightMeas X u) (hSec : SinfSection X u) (hNG : NormGeOne X.B.I) :
    Cut.IUnfold X u hK := by
  intro hMP hWD hPW T Ω hΩ Fs hFs
  have hn := n_pos X
  obtain ⟨CS, hCS, hdec⟩ := hSC

  obtain ⟨CC, hCCd⟩ : ∃ CC : Set X.B.I.GA,
      CC = (fun p : X.B.I.GA × X.B.I.Gf => p.1 * ((1, X.xu u * p.2) : X.B.I.GA)) '' (CS ×ˢ X.K2) := ⟨_, rfl⟩
  have hCC : IsCompact CC := hCCd ▸ (hCS.prod hKT.2).image (by fun_prop)
  obtain ⟨C, hC⟩ := hMP Ω CC hΩ hCC
  obtain ⟨M, hM⟩ := hCB T
  obtain ⟨N1, hN1d⟩ : ∃ N1 : ℝ, N1 = WuDecay.N1 X := ⟨_, rfl⟩
  have hN1 : 0 ≤ N1 := hN1d ▸ exponentN1_nonneg X.B.I

  obtain ⟨a, B, ha, ha1, hB, hBint, hsec⟩ := hSec (Prod.fst '' CS) (hCS.image continuous_fst)

  obtain ⟨Cf, hCfd⟩ : ∃ Cf : Set X.B.I.Gf,
      Cf = (fun p : X.B.I.GA × X.B.I.Gf => p.1.2 * X.xu u * p.2) '' (CS ×ˢ X.K2) := ⟨_, rfl⟩
  have hCfc : IsCompact Cf := hCfd ▸ (hCS.prod hKT.2).image (by fun_prop)
  have hCfo : IsOpen Cf := by
    have e : Cf = ⋃ c ∈ CS, (fun z => (c.2 * X.xu u)⁻¹ * z) ⁻¹' X.K2 := by
      rw [hCfd]
      ext z
      constructor
      · rintro ⟨⟨c, k⟩, ⟨hc, hk⟩, rfl⟩
        refine Set.mem_iUnion₂.2 ⟨c, hc, ?_⟩
        show (c.2 * X.xu u)⁻¹ * (c.2 * X.xu u * k) ∈ X.K2
        rwa [← mul_assoc, inv_mul_cancel, one_mul]
      · intro hz
        obtain ⟨c, hc, hk⟩ := Set.mem_iUnion₂.1 hz
        refine ⟨(c, (c.2 * X.xu u)⁻¹ * z), ⟨hc, hk⟩, ?_⟩
        show c.2 * X.xu u * ((c.2 * X.xu u)⁻¹ * z) = z
        rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [e]
    exact isOpen_biUnion fun c _ => hKT.1.preimage (continuous_const_mul _)
  have hμf : X.B.μf Cf < ⊤ := hCfc.measure_lt_top

  obtain ⟨K0, hK0d⟩ : ∃ K0 : ℝ≥0∞, K0 = ENNReal.ofReal (max C 0 * 2 ^ N1 * max M 0) := ⟨_, rfl⟩
  have hΨm : Measurable fun y : X.B.I.GA => K0 * (wt X u y.1 * a y.1) * Cf.indicator 1 y.2 :=
    Measurable.mul (Measurable.const_mul (((wt_meas X u hWM).mul ha).comp measurable_fst) _)
      ((measurable_one.indicator hCfo.measurableSet).comp measurable_snd)

  have hA : ∀ y : X.B.I.GA, FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω y * ‖Ph X u hK T y‖ₑ ≤
      ∑' γ : Srat X u, K0 * (wt X u ((γ : X.B.I.GA) * y).1 * a ((γ : X.B.I.GA) * y).1) *
        Cf.indicator 1 ((γ : X.B.I.GA) * y).2 := by
    intro y
    by_cases hex : ∃ n h k, IsDec X u y.2 n h k
    swap
    · rw [Cut.ph_eq_zero X u hK T y hex]; simp
    obtain ⟨n, h, k, hnN, hkK, hy2⟩ := hex
    have hsf : n * (h : X.B.I.Gf) ∈ SfinU X u := sfin_mul X u hSG (nfin_sfin X u hnN) (hfin_sfin X u h)
    have hdecomp : ∀ (t : X.B.I.Ginf) (σ c : X.B.I.GA), σ * c = ((t⁻¹, n * (h : X.B.I.Gf)) : X.B.I.GA) →
        y = σ * (c * ((1, X.xu u * k) : X.B.I.GA) * ((t * y.1, 1) : X.B.I.GA)) := by
      intro t σ c hσc
      rw [← mul_assoc, ← mul_assoc, hσc]
      refine Prod.ext ?_ ?_
      · show y.1 = t⁻¹ * 1 * (t * y.1)
        rw [mul_one, inv_mul_cancel_left]
      · show y.2 = n * (h : X.B.I.Gf) * (X.xu u * k) * 1
        rw [hy2, mul_one, mul_assoc (n * (h : X.B.I.Gf))]

    have hPh : ‖Ph X u hK T y‖ ≤ max M 0 * ‖X.Wu u y.1‖ := by
      rw [Cut.ph_eq X u hK hPW T y n h k ⟨hnN, hkK, hy2⟩]
      unfold phVal
      rw [norm_mul, norm_mul, hK.2.2.2.2 k hkK, mul_one]
      calc ‖X.psiFinU u n‖ * ‖(T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y.1) (1, h)‖
          ≤ 1 * (M * ‖X.Wu u y.1‖) := mul_le_mul (hPU n hnN) (hM h _) (norm_nonneg _) zero_le_one
        _ ≤ max M 0 * ‖X.Wu u y.1‖ := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

    obtain ⟨ν0, hν0⟩ : ∃ ν0 : ℝ, ν0 = WuDecay.nuInf X u y.1 := ⟨_, rfl⟩
    haveI : Nonempty (X.SinfU u) := ⟨⟨1, one_mem_sinf X u⟩⟩
    have hν1 : 1 ≤ ν0 := hν0 ▸ le_ciInf fun t => hNG hn _
    obtain ⟨t, ht⟩ : ∃ t : X.SinfU u, WuDecay.normInf X ((t : X.B.I.Ginf) * y.1) < ν0 + 1 :=
      exists_lt_of_ciInf_lt (by
        have h' : WuDecay.nuInf X u y.1 < ν0 + 1 := by rw [← hν0]; linarith
        exact h')
    obtain ⟨σ, hσ, c, hc, hdc⟩ := hdec (((t : X.B.I.Ginf)⁻¹, n * (h : X.B.I.Gf)) : X.B.I.GA)
      (sinf_inv X u hSG t.2) hsf
    have hmy : FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω y ≤
        ENNReal.ofReal (max C 0 * 2 ^ N1 * ν0 ^ N1) := by
      rw [hdecomp t σ c hdc.symm, mult_left _ Ω σ (Subgroup.mem_inf.1 hσ).1]
      have hcc : c * ((1, X.xu u * k) : X.B.I.GA) ∈ CC := hCCd ▸ ⟨(c, k), ⟨hc, hkK⟩, rfl⟩
      refine (hC _ hcc _).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hN1d]
      have h0 : 0 ≤ WuDecay.normInf X ((t : X.B.I.Ginf) * y.1) := normI_nonneg _ _
      have h1 : WuDecay.normInf X ((t : X.B.I.Ginf) * y.1) ^ N1 ≤ (2 * ν0) ^ N1 :=
        Real.rpow_le_rpow h0 (by linarith) hN1
      rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
      calc C * WuDecay.normInf X ((t : X.B.I.Ginf) * y.1) ^ N1
          ≤ max C 0 * WuDecay.normInf X ((t : X.B.I.Ginf) * y.1) ^ N1 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg h0 _)
        _ ≤ max C 0 * (2 ^ N1 * ν0 ^ N1) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
        _ = max C 0 * 2 ^ N1 * ν0 ^ N1 := by ring
    have hmain : FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω y * ‖Ph X u hK T y‖ₑ ≤ K0 * wt X u y.1 := by
      have hPe : ‖Ph X u hK T y‖ₑ ≤ ENNReal.ofReal (max M 0) * ‖X.Wu u y.1‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (le_max_right _ _)]
        exact ENNReal.ofReal_le_ofReal hPh
      have hC2 : 0 ≤ max C 0 * 2 ^ N1 := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _)
      calc FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω y * ‖Ph X u hK T y‖ₑ
          ≤ ENNReal.ofReal (max C 0 * 2 ^ N1 * ν0 ^ N1) * (ENNReal.ofReal (max M 0) * ‖X.Wu u y.1‖ₑ) :=
            mul_le_mul' hmy hPe
        _ = K0 * wt X u y.1 := by
            rw [hK0d, wt, ← hN1d, ← hν0, ENNReal.ofReal_mul hC2, ENNReal.ofReal_mul hC2]
            ring

    obtain ⟨t', ht', hat⟩ := hsec y.1
    obtain ⟨σ', hσ', c', hc', hdc'⟩ := hdec ((t'⁻¹, n * (h : X.B.I.Gf)) : X.B.I.GA) (sinf_inv X u hSG ht') hsf
    have hc'1 : c'.1 ∈ X.SinfU u := by
      have e1 : c' = σ'⁻¹ * ((t'⁻¹, n * (h : X.B.I.Gf)) : X.B.I.GA) := by
        rw [hdc', ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e1]
      exact sinf_mul X u hSG (sinf_inv X u hSG (srat_mem X u hSG hσ').1) (sinf_inv X u hSG ht')
    have hz : σ'⁻¹ * y = c' * ((1, X.xu u * k) : X.B.I.GA) * ((t' * y.1, 1) : X.B.I.GA) := by
      have e := hdecomp t' σ' c' hdc'.symm
      calc σ'⁻¹ * y = σ'⁻¹ * (σ' * (c' * ((1, X.xu u * k) : X.B.I.GA) * ((t' * y.1, 1) : X.B.I.GA))) := by
            rw [← e]
        _ = _ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    have hS1 : c'.1 * t' ∈ X.SinfU u := sinf_mul X u hSG hc'1 ht'
    have hz1 : (σ'⁻¹ * y).1 = c'.1 * t' * y.1 := by
      rw [hz]; show c'.1 * 1 * (t' * y.1) = c'.1 * t' * y.1; rw [mul_one, mul_assoc]
    have hz2 : (σ'⁻¹ * y).2 ∈ Cf := by
      rw [hz, hCfd]
      refine ⟨(c', k), ⟨hc', hkK⟩, ?_⟩
      show c'.2 * X.xu u * k = c'.2 * (X.xu u * k) * 1
      rw [mul_one, mul_assoc]
    have hterm : K0 * (wt X u (σ'⁻¹ * y).1 * a (σ'⁻¹ * y).1) * Cf.indicator 1 (σ'⁻¹ * y).2 = K0 * wt X u y.1 := by
      rw [hz1, wt_left X u hSG hWI hS1, hat c'.1 ⟨c', hc', rfl⟩ hc'1, Set.indicator_of_mem hz2, mul_one,
        Pi.one_apply, mul_one]
    calc FoldBound.mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω y * ‖Ph X u hK T y‖ₑ ≤ K0 * wt X u y.1 := hmain
      _ = K0 * (wt X u (σ'⁻¹ * y).1 * a (σ'⁻¹ * y).1) * Cf.indicator 1 (σ'⁻¹ * y).2 := hterm.symm
      _ ≤ ∑' γ : Srat X u, K0 * (wt X u ((γ : X.B.I.GA) * y).1 * a ((γ : X.B.I.GA) * y).1) *
            Cf.indicator 1 ((γ : X.B.I.GA) * y).2 :=
          ENNReal.le_tsum (f := fun γ : Srat X u => K0 * (wt X u ((γ : X.B.I.GA) * y).1 *
            a ((γ : X.B.I.GA) * y).1) * Cf.indicator 1 ((γ : X.B.I.GA) * y).2)
            ⟨σ'⁻¹, (Srat X u).inv_mem hσ'⟩

  haveI : (X.B.I.muA X.B.μf).IsMulLeftInvariant := (Cut.muA_isHaar' X.B.I X.B.μf).toIsMulLeftInvariant
  haveI : Countable (Srat X u) := by
    have h1 : ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I : Subgroup X.B.I.GA) : Set X.B.I.GA).Countable :=
      Set.countable_coe_iff.1 (Formalism.MainNotions.LeviCoordinates.rr_GF_countable X.B.I)
    exact (h1.mono fun x hx => (Subgroup.mem_inf.1 hx).1).to_subtype
  unfold PoincareSeriesSquareIntegrable.multiplicityLIntegral
  refine lt_of_le_of_lt (setLIntegral_le_of_cover (Srat X u) hFs _ _ hΨm hA) ?_
  have hK0 : K0 ≠ ⊤ := hK0d ▸ ENNReal.ofReal_ne_top
  refine lt_of_le_of_lt (prod_bound X u K0 hK0 a ha1 Cf hμf.ne) ?_
  refine lt_of_le_of_lt (mul_le_mul' (mul_le_mul' le_rfl
    (weil_bound X u hSG hWI hWM a ha B hB.ne hBint)) le_rfl) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hK0.lt_top (ENNReal.mul_lt_top (wt_int X u hWD) hB)) hμf

section Close

theorem psiR_norm {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by
  unfold psiR
  rw [Complex.norm_exp]
  have him : ((∑ a, (rootCoord ε e f z g a + star (rootCoord ε e f z g a))) / (gg : ℂ)).im = 0 := by
    simp [Complex.div_im, Complex.im_sum, Complex.star_def]
  have hre : (2 * (Real.pi : ℂ) * Complex.I *
      ((∑ a, (rootCoord ε e f z g a + star (rootCoord ε e f z g a))) / (gg : ℂ))).re = 0 := by
    rw [Complex.mul_re, him]
    simp
  rw [hre, Real.exp_zero]

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem wuNormInv_holds : WuNormInv X u := by
  intro s hs x
  have h1 := (X.Wu_spec u).1 s hs x
  rw [h1, norm_smul]
  have hp : ‖psiInf X.B.I X.B.g (fun a => crdOf X.B.I X.ιE X.bas (X.eX a))
      (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) s‖ = 1 := by
    unfold psiInf
    rw [norm_prod]
    exact Finset.prod_eq_one fun v _ => psiR_norm _ _ _ _ _ _
  rw [hp, one_mul]
  have hu := (X.piU_rep u).2.2.1 s hs (X.Wu u x) (X.Wu u x)
  have h2 : ‖X.piU u s (X.Wu u x)‖ ^ 2 = ‖X.Wu u x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, hu]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

theorem normInf_continuous : Continuous (WuDecay.normInf X) := by
  unfold WuDecay.normInf
  refine continuous_finset_prod _ fun v _ => ?_
  unfold WuDecay.opn
  have hlin : Continuous fun M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) M :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin X.B.I.n)).toAlgEquiv.toLinearMap)
  exact continuous_norm.comp (hlin.comp ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)))

theorem weightMeas_holds : WeightMeas X u := by
  refine ⟨?_, (X.Wu_spec u).2.2.1.norm.measurable⟩
  refine UpperSemicontinuous.measurable ?_
  unfold WuDecay.nuInf
  refine upperSemicontinuous_ciInf (fun x => ⟨0, ?_⟩) fun t =>
    ((normInf_continuous X).comp (continuous_const.mul continuous_id)).upperSemicontinuous
  rintro _ ⟨t, rfl⟩
  exact normI_nonneg _ _

theorem level_subgroup_compact_open : LevelSubgroupCompactOpen X := by
  have hc := Cut.level_subgroup_isClopen X (Formalism.L2.SG.Closed.level_subgroup_is_group X) (Formalism.L2.SG.Closed.level_subgroup_properties X)
  exact ⟨hc.isOpen, (Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).of_isClosed_subset hc.isClosed
    (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1⟩

theorem multPoly_holds_of (hTT : TauTrans X.B.I) (hNP : NormPow X.B.I) (hO : OmCover X.B.I) : Cut.MultPoly X :=
  multPoly_of X (Formalism.L2.SG.Closed.LatCount_holds X.B.I) Formalism.L2.SG.Closed.DistTri_holds reduction_theory hTT hNP hO

theorem iUnfold_holds_of (hK : X.LevelSubgroupCharacter) (hSC : SCompact X u) (hPU : PsiUnit X u) (hCB : ColBound X u hK)
    (hSec : SinfSection X u) (hNG : NormGeOne X.B.I) : Cut.IUnfold X u hK :=
  iUnfold_of X u hK (Cut.sGroup_holds X u) hSC (level_subgroup_compact_open X) hPU hCB (wuNormInv_holds X u)
    (weightMeas_holds X u) hSec hNG

end Close

section Norms

theorem opn_ge_one {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    1 ≤ WuDecay.opn (uMat g) := by
  have hA : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨T, hT⟩ : ∃ T, T = Matrix.toEuclideanCLM (𝕜 := ℂ) (uMat g) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = Matrix.toEuclideanCLM (𝕜 := ℂ) (Formalism.REAL.Jm ε) := ⟨_, rfl⟩
  have hTJ : star T * J * T = J := by
    rw [hT, hJ, ← map_star, ← map_mul, ← map_mul, Matrix.star_eq_conjTranspose, hA]
  have hJJ : star J * J = 1 := by
    rw [hJ, ← map_star, ← map_mul, Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose,
      Formalism.REAL.Jm_mul_self, map_one]
  have hJs : star J = J := by
    rw [hJ, ← map_star, Matrix.star_eq_conjTranspose, Formalism.REAL.Jm_conjTranspose]
  have hJn : ‖J‖ = 1 := by
    have h := CStarRing.norm_star_mul_self (x := J)
    rw [hJJ, norm_one] at h
    nlinarith [norm_nonneg J]
  have hL : J * star T * J * T = 1 := by
    calc J * star T * J * T = J * (star T * J * T) := by simp only [mul_assoc]
      _ = 1 := by rw [hTJ, ← hJJ, hJs]
  have h1 : (1 : ℝ) ≤ ‖T‖ * ‖T‖ := by
    calc (1 : ℝ) = ‖J * star T * J * T‖ := by rw [hL, norm_one]
      _ ≤ ‖J * star T * J‖ * ‖T‖ := norm_mul_le _ _
      _ ≤ ‖J * star T‖ * ‖J‖ * ‖T‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖J‖ * ‖star T‖ * ‖J‖ * ‖T‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖T‖ * ‖T‖ := by rw [hJn, norm_star]; ring
  unfold WuDecay.opn
  rw [← hT]
  nlinarith [norm_nonneg T]

theorem opn_eq_one_of_definite {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (hε : ∀ a, ε a = true)
    (g : Formalism.REAL.UJ ε) : WuDecay.opn (uMat g) = 1 := by
  have hJ1 : Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    simp [hε a]
  have hA : (uMat g)ᴴ * uMat g = 1 := by
    have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
    rwa [hJ1, Matrix.mul_one] at h
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨T, hT⟩ : ∃ T, T = Matrix.toEuclideanCLM (𝕜 := ℂ) (uMat g) := ⟨_, rfl⟩
  have hTT : star T * T = 1 := by
    rw [hT, ← map_star, ← map_mul, Matrix.star_eq_conjTranspose, hA, map_one]
  have h := CStarRing.norm_star_mul_self (x := T)
  rw [hTT, norm_one] at h
  unfold WuDecay.opn
  rw [← hT]
  nlinarith [norm_nonneg T]

theorem normGeOne_holds (I : AutInst) : NormGeOne I := by
  intro hn g
  unfold normI
  calc (1 : ℝ) = ∏ _v : InfinitePlace I.F, (1 : ℝ) := Finset.prod_const_one.symm
    _ ≤ ∏ v, WuDecay.opn (uMat (g v)) :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) fun v _ => opn_ge_one hn (I.ε v) (g v)

theorem normPow_holds (I : AutInst) : NormPow I := by
  intro hn g
  by_cases hq : ∃ v, 1 ≤ I.qAt v
  · obtain ⟨v, hv⟩ := hq
    refine Real.rpow_le_rpow_of_exponent_le (normGeOne_holds I hn g) ?_
    have hq0 : (1 : ℝ) ≤ ((Finset.univ.sup fun v => I.qAt v : ℕ) : ℝ) := by
      exact_mod_cast hv.trans (Finset.le_sup (f := fun v => I.qAt v) (Finset.mem_univ v))
    have hs : (1 : ℝ) ≤ Real.sqrt (2 * ((Finset.univ.sup fun v => I.qAt v : ℕ) : ℝ)) := by
      rw [Real.one_le_sqrt]; linarith
    unfold nilradicalExponent
    push_cast
    have h4 : (0 : ℝ) ≤ 4 * (I.n : ℝ) ^ 2 := by positivity
    nlinarith
  · push_neg at hq
    have h1 : normI I g = 1 := by
      unfold normI
      refine Finset.prod_eq_one fun v _ => opn_eq_one_of_definite hn (I.ε v) (fun a => ?_) (g v)
      have h0 : I.qAt v = 0 := by have := hq v; omega
      unfold AutInst.qAt at h0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
      have := h0 (Finset.mem_univ a)
      simpa using this
    rw [h1, Real.one_rpow, Real.one_rpow]

end Norms

section Close2

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem multPoly_holds_of' (hTT : TauTrans X.B.I) (hO : OmCover X.B.I) : Cut.MultPoly X :=
  multPoly_holds_of X hTT (normPow_holds X.B.I) hO

theorem iUnfold_holds_of' (hK : X.LevelSubgroupCharacter) (hSC : SCompact X u) (hPU : PsiUnit X u) (hCB : ColBound X u hK)
    (hSec : SinfSection X u) : Cut.IUnfold X u hK :=
  iUnfold_holds_of X u hK hSC hPU hCB hSec (normGeOne_holds X.B.I)

end Close2

section TauT

open LitS.Size

theorem sum_sq_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ WuDecay.opn M ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) M).le_opNorm (WithLp.toLp 2 w)
  rw [Matrix.toEuclideanCLM_toLp] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [WuDecay.opn] using h2

variable (I : AutInst)

theorem size_subOfEq_le_pl {x x' : I.GA} (hlat : latSet I x' = latSet I x)
    (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (hY : ∀ v u, coordV I x' v u = Y v *ᵥ coordV I x v u) (c : InfinitePlace I.F → ℝ) (hc : ∀ v, 1 ≤ c v)
    (hb : ∀ v (w : Fin I.n → ℂ), ∑ i, ‖(Y v *ᵥ w) i‖ ^ 2 ≤ c v * ∑ i, ‖w i‖ ^ 2) (s : Sub I x) :
    size I (Tau.subOfEq I hlat s) ≤ (∏ v, c v) ^ ((1 : ℝ) / (2 * (I.f : ℝ))) * size I s := by
  have h5 := Tau.t5
  have hcm : ∀ v, Tau.cmat I x' v s.b = Y v * Tau.cmat I x v s.b := by
    intro v
    ext i a
    simp [Tau.cmat, hY, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hdet : ∀ v, (gramV I x' v s.b).det.re ≤ c v ^ s.j * (gramV I x v s.b).det.re := by
    intro v
    have h := (h5 I.n s.j (Y v) (Tau.cmat I x v s.b) 0 (c v) le_rfl fun w =>
      ⟨by rw [zero_mul]; positivity, hb v w⟩).2
    rw [Tau.gramV_eq, Tau.gramV_eq, hcm]
    exact h
  have hP0 : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => le_trans zero_le_one (hc v)
  have hprod : (∏ v, (gramV I x' v s.b).det.re) ≤ (∏ v, c v) ^ s.j * ∏ v, (gramV I x v s.b).det.re := by
    calc (∏ v, (gramV I x' v s.b).det.re) ≤ ∏ v, (c v ^ s.j * (gramV I x v s.b).det.re) :=
          Finset.prod_le_prod (fun v _ => Tau.det_gram_nonneg I h5 x' v s.j_pos s.b) fun v _ => hdet v
      _ = (∏ v, c v) ^ s.j * ∏ v, (gramV I x v s.b).det.re := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow]
  have hht : ht I (Tau.subOfEq I hlat s) ≤ (∏ v, c v) ^ s.j * ht I s := by
    unfold ht
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hprod (Nat.cast_nonneg _)
  have hf : 0 < (I.f : ℝ) := f_pos I
  have hj : 0 < (s.j : ℝ) := by exact_mod_cast s.j_pos
  have he : 0 ≤ (1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)) := by positivity
  have hje : (s.j : ℝ) * ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ))) = (1 : ℝ) / (2 * (I.f : ℝ)) := by
    field_simp
  unfold size
  change ht I (Tau.subOfEq I hlat s) ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ))) ≤ _
  calc ht I (Tau.subOfEq I hlat s) ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ ((∏ v, c v) ^ s.j * ht I s) ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.rpow_le_rpow (Tau.ht_nonneg I h5 _) hht he
    _ = ((∏ v, c v) ^ (s.j : ℝ)) ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ))) *
          ht I s ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ))) := by
        rw [Real.mul_rpow (pow_nonneg hP0 _) (Tau.ht_nonneg I h5 s), Real.rpow_natCast]
    _ = (∏ v, c v) ^ ((1 : ℝ) / (2 * (I.f : ℝ))) * ht I s ^ ((1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ))) := by
        rw [← Real.rpow_mul hP0, hje]

theorem tauTrans_holds : TauTrans I := by
  intro hn x g
  set x' := x * ((g, 1) : I.GA) with hx'
  have hlat : latSet I x = latSet I x' := by
    have h2 : x'.2 = x.2 := by rw [hx']; exact mul_one x.2
    unfold latSet
    rw [h2]
  have hY : ∀ v u, coordV I x v u = uMat (g v) *ᵥ coordV I x' v u := fun v u => Tau.coordV_mul' I x g 1 v u
  have hc : ∀ v, 1 ≤ WuDecay.opn (uMat (g v)) ^ 2 := fun v => one_le_pow₀ (opn_ge_one hn (I.ε v) (g v))
  have hb : ∀ v (w : Fin I.n → ℂ), ∑ i, ‖(uMat (g v) *ᵥ w) i‖ ^ 2 ≤
      WuDecay.opn (uMat (g v)) ^ 2 * ∑ i, ‖w i‖ ^ 2 := fun v w => sum_sq_mulVec_le _ w
  have hN1 := normGeOne_holds I hn g
  have hN0 : 0 ≤ normI I g := le_trans zero_le_one hN1
  set P := normI I g ^ ((1 : ℝ) / (I.f : ℝ)) with hP
  have hf : 0 < (I.f : ℝ) := f_pos I
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 (by positivity)
  have hprodc : (∏ v, WuDecay.opn (uMat (g v)) ^ 2) ^ ((1 : ℝ) / (2 * (I.f : ℝ))) = P := by
    rw [Finset.prod_pow, hP]
    change (normI I g ^ 2) ^ ((1 : ℝ) / (2 * (I.f : ℝ))) = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    push_cast
    field_simp

  have hsz : ∀ s' : Sub I x', size I (Tau.subOfEq I hlat s') ≤ P * size I s' := fun s' => by
    have := size_subOfEq_le_pl I hlat (fun v => uMat (g v)) hY _ hc hb s'
    rwa [hprodc] at this

  have hne' : Nonempty (Sub I x') := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    have hpos := ((reduction_theory I hn).2 x').1
    unfold LitS.Size.tau1 at hpos
    rw [Real.iInf_of_isEmpty] at hpos
    norm_num at hpos
  have hbdd : BddBelow (Set.range fun s : Sub I x => size I s) :=
    ⟨0, by rintro _ ⟨s, rfl⟩; exact Tau.size_nonneg I Tau.t5 s⟩
  have hinf : (⨅ s : Sub I x, size I s) ≤ P * ⨅ s' : Sub I x', size I s' := by
    have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
    rw [← div_le_iff₀' hPpos]
    refine le_ciInf fun s' => ?_
    rw [div_le_iff₀' hPpos]
    exact (ciInf_le hbdd _).trans (hsz s')
  unfold LitS.Size.tau1
  set a := ⨅ s' : Sub I x', size I s'
  calc min (1 / 2) (⨅ s : Sub I x, size I s) ≤ min (1 / 2) (P * a) := min_le_min le_rfl hinf
    _ ≤ min (1 / 2) a * P := by
        rcases le_total a (1 / 2) with h | h
        · rw [min_eq_right h, mul_comm]; exact min_le_right _ _
        · rw [min_eq_left h]
          exact (min_le_left _ _).trans (by nlinarith)

end TauT

theorem multPoly_holds_of'' {D : D7} (X : HidaSetting D) (hO : OmCover X.B.I) : Cut.MultPoly X :=
  multPoly_holds_of' X (tauTrans_holds X.B.I) hO

end Formalism.L2.SG.Pf
