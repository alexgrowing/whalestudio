import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrbitLocallyConstant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentSubgroupSuccDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralWhittakerTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergSubgroupFourierJacobiCommutatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPowerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumnStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntriStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevelsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeHeisenbergVariableSignStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeOperatorWeilRowUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicQuotientStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotIntFJUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumSmulOfLocallyConstantCompactSupportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalFStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.FourierJacobi
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem heisenberg : Heisenberg k := by
  intro n _ _ c ρ h1 hc
  have h2 : ρ < c := by omega
  refine ⟨(GlobalTheory.T.fourierJacobiUnipotent_eq_prod_rootExchange k n c ρ h1 h2).1, (GlobalTheory.T.exists_heisenbergSubgroup_fourierJacobi_commutator k n c ρ h1 h2).1, (GlobalTheory.T.exists_heisenbergSubgroup_fourierJacobi_commutator k n c ρ h1 h2).2, ?_⟩
  intro ψ hψ _ u β₀ Φ₀
  refine ⟨⟨Φ₀.2.1.comp_continuous (continuous_add_const β₀),
    Φ₀.2.2.comp_homeomorph (Homeomorph.addRight β₀)⟩,
    ⟨(((GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).2 ψ hψ).comp_continuous (f := fun β : n → k => u ⬝ᵥ β) (by fun_prop)).mul Φ₀.2.1,
      Φ₀.2.2.mul_left⟩, ?_⟩
  funext β
  simp only [schM, schT, Pi.smul_apply, smul_eq_mul, dotProduct_add, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul]
  congr 3
  ring

section Bessel
variable {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} {ψ : AddChar k Circle} {ν : Measure k}
  {P A : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
  {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
  {fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ} {b b₀ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ}

omit [DecidableEq n] in
theorem sb_int [ν.IsAddHaarMeasure] {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    Integrable f (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2

def stab (ρ : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (v : A) : Set (n → k) :=
  {β | σ (colE c (ρ + 1) β) v = v}

omit [MeasurableSpace k] [BorelSpace k] in
theorem stab_nhds (hσ : IsSmoothRep σ) (v : A) : stab ρ σ v ∈ 𝓝 (0 : n → k) :=
  ((hσ v).preimage ExchangeSupport.continuous_colE).mem_nhds (by simp [ExchangeSupport.colE_zero])

theorem fj_conv [ν.IsAddHaarMeasure] (hfj : IsFJ ψ ρ σ fj) (Φ Ψ : SB (n → k)) :
    ∃ w : SB (n → k), (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧
      (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧
      ∀ φ v, fj φ v w = ∫ y, Φ.1 y * fj φ (σ (colE c (ρ + 1) y) v) Ψ ∂(Measure.pi fun _ => ν) := by
  obtain ⟨T, w, hT, h1, h2, h3⟩ := GlobalTheory.T.exists_schwartzBruhat_convolution_localFieldPower k n ν Φ Ψ
  refine ⟨w, h1, h2, fun φ v => ?_⟩
  rw [h3]
  congr 1; funext y
  rw [hfj.1 φ v y (T y) Ψ (by funext β; simp [schT, hT])]

omit [DecidableEq n] [BorelSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [Field k] in
theorem integral_mul_of_support {U : Set (n → k)} {Ψ f : (n → k) → ℂ} {z : ℂ} (h0 : ∀ y, y ∉ U → Ψ y = 0)
    (h1 : ∀ y ∈ U, f y = z) :
    ∫ y, Ψ y * f y ∂(Measure.pi fun _ => ν) = (∫ y, Ψ y ∂(Measure.pi fun _ => ν)) * z := by
  rw [← integral_mul_const]
  congr 1; funext y
  by_cases hy : y ∈ U
  · rw [h1 y hy]
  · simp [h0 y hy]

theorem fj_indep [ν.IsAddHaarMeasure] (hfj : IsFJ ψ ρ σ fj) (φ : P) (v : A) (Φ Ψ : SB (n → k))
    (hΦ : ∀ y, y ∉ stab ρ σ v → Φ.1 y = 0) (hΦ1 : ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = 1)
    (hΨ : ∀ y, y ∉ stab ρ σ v → Ψ.1 y = 0) (hΨ1 : ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1) :
    fj φ v Φ = fj φ v Ψ := by
  obtain ⟨w, h1, -, h3⟩ := fj_conv (ν := ν) hfj Φ Ψ
  obtain ⟨w', -, h2', h3'⟩ := fj_conv (ν := ν) hfj Ψ Φ
  have e : w = w' := Subtype.ext (funext fun x => (h1 x).trans (h2' x).symm)
  have a := h3 φ v
  have a' := h3' φ v
  rw [integral_mul_of_support (z := fj φ v Ψ) hΦ (fun y hy => by rw [show σ _ v = v from hy]), hΦ1, one_mul] at a
  rw [integral_mul_of_support (z := fj φ v Φ) hΨ (fun y hy => by rw [show σ _ v = v from hy]), hΨ1, one_mul] at a'
  rw [← a, ← a', e]

theorem exists_represents [ν.IsAddHaarMeasure] (h1 : 1 ≤ ρ) (h2 : ρ < c) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hσ : IsSmoothRep σ) (hfj : IsFJ ψ ρ σ fj) : ∃ b, Represents ψ ν ρ σ fj b := by
  choose Ψ hΨ hΨ1 using fun v : A => GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
  have key : ∀ U ∈ 𝓝 (0 : n → k), ∃ Φ : SB (n → k), (∀ y, y ∉ U → Φ.1 y = 0) ∧
      ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = 1 ∧ ∀ φ v, U ⊆ stab ρ σ v → fj φ v (Ψ v) = fj φ v Φ := by
    intro U hU
    obtain ⟨Φ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν U hU
    exact ⟨Φ, a, a1, fun φ v hv => fj_indep hfj φ v _ _ (hΨ v) (hΨ1 v) (fun y hy => a y fun h => hy (hv h)) a1⟩
  let b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun φ v => fj φ v (Ψ v)) (by intros; simp) (by intros; simp)
    (by
      intro φ v w
      obtain ⟨Φ, -, -, h⟩ := key _ (inter_mem (stab_nhds (ρ := ρ) hσ v) (stab_nhds (ρ := ρ) hσ w))
      rw [h φ v Set.inter_subset_left, h φ w Set.inter_subset_right, h φ (v + w)]
      · simp
      · intro y hy
        change σ _ _ = _
        rw [map_add, show σ _ v = v from hy.1, show σ _ w = w from hy.2])
    (by
      intro z φ v
      obtain ⟨Φ, -, -, h⟩ := key _ (stab_nhds (ρ := ρ) hσ v)
      rw [h φ v subset_rfl, h φ (z • v)]
      · simp
      · intro y hy
        change σ _ _ = _
        rw [map_smul, show σ _ v = v from hy])
  have hb : ∀ φ v, b φ v = fj φ v (Ψ v) := fun _ _ => rfl
  have hN : ∀ φ, IsNEquiv ψ (ρ + 1) σ (b φ) := by
    intro φ g hg v
    obtain ⟨g₁, hg₁, u, rfl⟩ := RadicalDecomp.succ_decomp k n c ρ g hg
    obtain ⟨-, hs, -, -, -, -, hr, -⟩ := Radical.unipotent_radical_basic k n c (ρ + 1)
    have hu : {β : n → k | (ψ ((-u) ⬝ᵥ β) : ℂ) = 1} ∈ 𝓝 (0 : n → k) :=
      ((((GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).2 ψ hψ).comp_continuous (f := fun β : n → k => (-u) ⬝ᵥ β)
        (by fun_prop)).isOpen_fiber 1).mem_nhds (by simp)
    obtain ⟨Φ, a, -, h⟩ := key _ (inter_mem (inter_mem (stab_nhds (ρ := ρ) hσ v)
      (stab_nhds (ρ := ρ) hσ (σ (g₁ * rowE c ρ u) v))) hu)
    rw [hb, hb, h φ v fun y hy => hy.1.1, h φ _ fun y hy => hy.1.2, map_mul, Module.End.mul_apply,
      hfj.2.2 φ _ Φ g₁ hg₁, hs _ hg₁.2 _ (hr ρ u (by omega)).1, (hr ρ u (by omega)).2, add_zero,
      hfj.2.1 φ v u Φ Φ]
    funext β
    by_cases hβ : (ψ ((-u) ⬝ᵥ β) : ℂ) = 1
    · rw [schM, hβ, one_mul]
    · rw [schM, a β fun h => hβ h.2, mul_zero]
  refine ⟨b, hN, fun φ v Φ₀ => ⟨?_, ?_⟩⟩
  · have := ((ExchangeSupport.exchange_support k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ (b φ) v).2 (hN φ)).1
    exact sb_int ⟨Φ₀.2.1.mul this.1, Φ₀.2.2.mul_right⟩
  · obtain ⟨K, hK, hKi⟩ := GlobalTheory.QuotInt.exists_open_stab (G := Multiplicative (n → k))
      (F := fun x => Φ₀.1 x.toAdd) Φ₀.2
    have hK' : {y : n → k | Multiplicative.ofAdd y ∈ K} ∈ 𝓝 (0 : n → k) := hK.mem_nhds K.one_mem
    obtain ⟨Φ, a, a1, h⟩ := key _ (inter_mem (stab_nhds (ρ := ρ) hσ v) hK')
    obtain ⟨w, -, e2, e3⟩ := fj_conv (ν := ν) hfj Φ₀ Φ
    have e : w = Φ₀ := by
      refine Subtype.ext (funext fun x => ?_)
      rw [e2, integral_mul_of_support (z := Φ₀.1 x) a, a1, one_mul]
      intro y hy
      rw [sub_eq_add_neg]
      exact hKi (Multiplicative.ofAdd x) _ (K.inv_mem hy.2)
    rw [← e, e3, e]
    congr 1; funext y
    rw [hb, h]
    intro β hβ
    change σ _ _ = _
    rw [← Module.End.mul_apply, ← map_mul, ← ExchangeSupport.colE_add, add_comm β y, ExchangeSupport.colE_add,
      map_mul, Module.End.mul_apply, show σ _ v = v from hβ.1]

theorem represents_eval (hb : Represents ψ ν ρ σ fj b) (φ : P) (v : A) (Ψ : SB (n → k))
    (hΨ : ∀ y, y ∉ stab ρ σ v → Ψ.1 y = 0) :
    fj φ v Ψ = (∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν)) * b φ v := by
  rw [(hb.2 φ v Ψ).2, integral_mul_of_support hΨ (fun y hy => by rw [show σ _ v = v from hy])]

theorem exchanges_eq (h1 : 1 ≤ ρ) (h2 : ρ < c) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hν : IsSelfDual ψ ν)
    (hσ : IsSmoothRep σ) (h : ExchangesTo ψ ν ρ σ b₀ b) (φ : P) (v : A) : b₀ φ v = exDown ν ρ σ (b φ) v := by
  rw [← (exDown_exUp_and_exUp_exDown k n c ρ h1 h2 ψ hψ hψ1 ν hν A σ hσ (b₀ φ) v).1 (h.1 φ)]
  congr 1
  funext w
  exact (h.2 φ w).2.symm

theorem uniqueBessel : UniqueBessel k := by
  intro n _ _ c ρ h1 hc ψ ν hψ hψ1 hν P A _ _ _ _ σ hσ fj hfj
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hS := ExchangeSupport.exchange_support k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ
  refine ⟨existsUnique_of_exists_of_unique (exists_represents h1 h2 hψ hψ1 hσ hfj) fun b b' hb hb' => ?_,
    fun b hb => ⟨existsUnique_of_exists_of_unique ?_ fun b₀ b₁ h h' => ?_, fun b₀ h φ v Φ₀ => ?_⟩⟩
  · ext φ v
    obtain ⟨Ψ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
    have e := represents_eval hb φ v Ψ a
    rw [represents_eval hb' φ v Ψ a, a1, one_mul, one_mul] at e
    exact e.symm
  · choose L hL hL' using fun φ =>
      (Exchange.exchange_isPos k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ).2.1 (b φ) (hb.1 φ)
    refine ⟨⟨⟨L, fun φ φ' => ?_⟩, fun z φ => ?_⟩, hL', fun φ v => ⟨sb_int ((hS _ v).1 (hL' φ)).1, ?_⟩⟩
    · ext v
      simp only [hL, exDown, map_add, LinearMap.add_apply]
      exact integral_add (sb_int ((hS _ v).2 (hb.1 φ)).1) (sb_int ((hS _ v).2 (hb.1 φ')).1)
    · ext v
      simp only [hL, exDown, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, integral_const_mul]
    · rw [← (exDown_exUp_and_exUp_exDown k n c ρ h1 h2 ψ hψ hψ1 ν hν A σ hσ (b φ) v).2 (hb.1 φ)]
      congr 1
      funext w
      exact (hL φ w).symm
  · ext φ v
    rw [exchanges_eq h1 h2 hψ hψ1 hν hσ h, exchanges_eq h1 h2 hψ hψ1 hν hσ h']
  · obtain ⟨s1, -, s3⟩ := (hS (b₀ φ) v).1 (h.1 φ)
    have hh := (GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n ψ hψ hψ1 ν hν).1 Φ₀
    refine ⟨sb_int ⟨hh.1.mul s1.1, hh.2.mul_right⟩, ?_⟩
    rw [(hb.2 φ v Φ₀).2]
    simp only [(h.2 φ _).2, s3, hat, ← integral_const_mul, ← integral_mul_const]
    rw [integral_integral_swap]
    · congr 1; funext u; congr 1; funext β; ring
    · have := ((sb_int (ν := ν) Φ₀.2).mul_prod (sb_int (ν := ν) s1)).bdd_mul (c := 1)
        (f := fun z : (n → k) × (n → k) => (ψ (z.2 ⬝ᵥ z.1) : ℂ))
        (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => (Circle.norm_coe _).le)
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry]
      ring

theorem exponents : Exponents k := by
  intro n _ _ c ρ h1 hc ψ ν hψ hψ1 hν P A _ _ _ _ π σ _ hσ η _ _ fj b _ hb
  have h2 : ρ < c := by omega
  have := hν.1
  have main : ∀ s e : ℝ, s + e + 1 = 0 → IsFJInv η s π σ fj → ∀ (g : GL n k) φ v,
      b (twist η π g φ) (σ (embX c g) v) =
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ e : ℝ) : ℂ) * b φ v := by
    intro s e hse hinv g φ v
    obtain ⟨Ψ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
    let T : (n → k) ≃ₜ (n → k) :=
      { toFun := fun β => (g⁻¹ : GL n k).val *ᵥ β
        invFun := fun β => g.val *ᵥ β
        left_inv := fun β => by simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
        right_inv := fun β => by simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let Φ : SB (n → k) := ((η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ)) •
        ⟨fun β => Ψ.1 (T β), Ψ.2.1.comp_continuous T.continuous, Ψ.2.2.comp_homeomorph T⟩
    have e1 := hinv g φ v Ψ Φ rfl
    have hpos : 0 < nabs k (Matrix.GeneralLinearGroup.det g) := by
      simp only [nabs]; exact_mod_cast distribHaarChar_pos
    have hinv' : (nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det g) := by
      simp [nabs]
    have e2 : ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (s + 1) : ℝ) : ℂ) := by
      have := (linear_change_of_variables k n n ν).1 g⁻¹ Ψ.1
      rw [a1, hinv'] at this
      change ∫ y, _ * Ψ.1 ((g⁻¹ : GL n k).val *ᵥ y) ∂_ = _
      rw [integral_const_mul, this, Real.rpow_add hpos]
      simp [mul_assoc]
    rw [represents_eval hb φ v Ψ a, a1, one_mul, represents_eval hb _ _ Φ, e2] at e1
    · change b ((η (Matrix.GeneralLinearGroup.det g) : ℂ) • π g φ) _ = _
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← e1]
      have : ((nabs k (Matrix.GeneralLinearGroup.det g) ^ e : ℝ) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (s + 1) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add hpos, show e + (s + 1) = 0 by linarith]
        simp
      linear_combination (-(η (Matrix.GeneralLinearGroup.det g) : ℂ) * b (π g φ) (σ (embX c g) v)) * this
    · intro y hy
      change _ * Ψ.1 ((g⁻¹ : GL n k).val *ᵥ y) = 0
      rw [a _ fun h => hy ?_, mul_zero]
      have h' : σ _ v = v := h
      rw [← QuotStep.conj_colE, map_inv, inv_inv] at h'
      change σ _ _ = _
      conv_rhs => rw [← h']
      simp only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨main, fun hinv => ?_⟩
  have hp : IsPos ψ (ρ + 1) (twist η π) σ b :=
    ⟨hb.1, main _ _ (by rw [hc]; push_cast; ring) hinv⟩
  refine ⟨hp, fun b₀ h => ?_⟩
  obtain ⟨b', e, hb'⟩ := ((Exchange.exchange_isPos k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ).2.2 P _ b).2 hp
  have : b₀ = b' := by
    ext φ v
    rw [e, exchanges_eq h1 h2 hψ hψ1 hν hσ h]
  exact this ▸ hb'

end Bessel

theorem localSign : LocalSign k := by
  intro n n' _ _ _ _ c ρ h1 hc
  have h2 : ρ < c := by omega
  refine ⟨(GlobalTheory.T.mem_fourierJacobiSubgroup_iff_parabolic_mul_column k n c ρ h1 h2).1,
    GlobalTheory.T.isUnimodular_blockUpperTriangular_symmetricLevels k n c _ _ (fun i => ?_) _ ((GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries k n c ρ).2 h1 h2),
    (GlobalTheory.T.rootExchange_heisenbergVariable_sign k n n' c ρ h1 h2).1, fun ψ ν hψ _ hν => ?_⟩
  · have := i.2
    simp only [Fin.val_rev]
    omega
  · have := hν.1
    exact ⟨fun μ _ => (GlobalTheory.T.rootExchange_heisenbergVariable_sign k n n' c ρ h1 h2).2 ψ ν hψ μ,
      fun μX μG _ _ => GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient k n c ρ h1 h2 ν μX μG⟩

theorem target : Target k := by
  intro n n' _ _ _ _ c ρ h1 hc ψ ν hψ hψ1 hν μ hμ μX μG hX hG P A P' A' _ _ _ _ _ _ _ _ π σ π' σ' _ hσ _ _
    ϑ θ _ hθ fj b b' _ hb hp _ φ F
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hμ' := (GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).1 μ hμ
  have main : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ h, Integrable (fun β : n → k => b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β)
          (σ (colE c (ρ + 1) β) (σ h F))) (Measure.pi fun _ => ν)) ∧
      ∀ z : ℂ,
        (IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
            b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
              ∂(Measure.pi fun _ => ν)) z) ∧
        (IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsFJInt ψ ν μX μG μ ρ σ θ fj φ F Φ.1 z) := by
    intro Φ
    have e : ∀ h β, b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F)) =
        rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1 (colE c (ρ + 1) β * h) := by
      intro h β
      have := om_mul μ 1 1 (colE c (ρ + 1) β) h Φ.1
      rw [one_mul] at this
      rw [rInt, this, map_mul]
      rfl
    obtain ⟨z₀, hz₀⟩ := exists_isQuotInt_unfolding k n n' c (ρ + 1) (by omega) h2 ψ hψ hψ1 ν μ hμ' μX μG A σ hσ
      P P' π π' θ hθ b hp φ F Φ (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) fun h Ψ hΨ => by rw [rInt, ← hΨ, app_coe]
    have W := GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient k n c ρ h1 h2 ν μX μG (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1)
    have val : ∀ h w, HasTensorVal (fun Ψ Φ₀ => fj (θ φ Ψ) (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w ↔
        w = ∫ β : n → k, b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
          ∂(Measure.pi fun _ => ν) := by
      intro h
      have v1 : ∀ w, HasTensorVal (fun Ψ Φ₀ => fj (θ φ Ψ) (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w →
          w = ∫ β : n → k, b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
            ∂(Measure.pi fun _ => ν) := by
        rintro w ⟨m, Ψ, Φ₀, hd, rfl⟩
        simp only [(hb.2 _ _ _).2]
        rw [← integral_finset_sum _ fun i _ => (hb.2 _ _ _).1]
        congr 1; funext β
        have : (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) = (∑ i, (Φ₀ i).1 β • Ψ i : SB (Matrix n n' k)).1 := by
          funext x₀
          simp [hd, mul_comm]
        rw [this, app_coe]
        simp
      let T : (n → k) → SB (Matrix n n' k) := fun β =>
        opL hψ ν (ρ + 1) (omR μ (1, colE c (ρ + 1) β) (omR μ (1, h) Φ))
      have hT : IsLocallyConstant T :=
        ((orbit_locallyConstant (omR_smooth hμ') (omR μ (1, h) Φ)).comp_continuous
          (continuous_const.prodMk ExchangeSupport.continuous_colE)).comp fun Ψ => opL hψ ν (ρ + 1) Ψ
      obtain ⟨K, hK, HK⟩ := ColumnSupport.opE_colE_eq_zero k n n' c ρ h2 ψ ν μ _ (omR μ (1, h) Φ).2
      obtain ⟨m, Ψ, Φ₀, hd⟩ := GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport (n → k) _ T hT K hK fun β hβ => Subtype.ext (by
        have := HK β hβ fun _ => 1
        simp only [one_mul] at this
        exact this)
      have v2 : HasTensorVal (fun Ψ Φ₀ => fj (θ φ Ψ) (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) _ :=
        ⟨m, Ψ, Φ₀, fun x y => by
          have := congrArg (fun t : SB (Matrix n n' k) => t.1 x) (hd y)
          refine Eq.trans this ?_
          simp [mul_comm], rfl⟩
      exact fun w => ⟨v1 w, fun hw => by rw [hw, ← v1 _ v2]; exact v2⟩
    have i1 : ∀ z, IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
            b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
              ∂(Measure.pi fun _ => ν)) z := by
      intro z
      simp only [e]
      exact ⟨fun hz => (W z hz).2, fun hz => GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ k n c ρ h1 h2 ν μX μG _ _ _ (W z₀ hz₀).2 hz ▸ hz₀⟩
    refine ⟨fun h => ?_, fun z => ⟨i1 z, (i1 z).trans ⟨fun hz => ⟨_, fun h => (val h _).2 rfl, hz⟩, ?_⟩⟩⟩
    · simp only [e]
      exact (W z₀ hz₀).1 h
    · rintro ⟨f, hf, hz⟩
      rwa [show f = _ from funext fun h => (val h _).1 (hf h)] at hz
  refine ⟨fun Φ => ⟨fun h => (opL hψ ν (ρ + 1) (omR μ (1, h) Φ)).2,
    fun h β => (opL hψ ν (ρ + 1) (omR μ (1, colE c (ρ + 1) β) (omR μ (1, h) Φ))).2, main Φ⟩,
    forall_congr' fun Φ => ((main Φ).2 _).2⟩

theorem source : Source k := by
  intro n n' _ _ _ _ c ρ hc ψ ν hψ hψ1 hν μ hμ μX μG hX hG P A P' A' _ _ _ _ _ _ _ _ π σ π' σ' _ _ _ _
    ϑ θ hϑ _ fj' b b' _ _ hfj φ F
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hμ' := (GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).1 μ hμ
  have hF := GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n' ψ hψ hψ1 ν hν
  have main : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Φ₀ : SB (n' → k)),
      ∃ w : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), avg ψ ν μ ρ Φ₀ Φ.1 = w.1 ∧
      (∀ h, opE ψ ν ρ (om μ 1 h w.1) = opEFJ ψ ν ρ Φ₀ (om μ 1 h Φ.1)) ∧ fj' φ (ϑ F Φ) Φ₀ = b' φ (ϑ F w) := by
    intro Φ Φ₀
    have hh := hF.1 Φ₀
    let T : (n' → k) → SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := fun u =>
      hat ψ ν Φ₀.1 u • omR μ (rowE (c + 1) ρ u, 1) Φ
    have hT : IsLocallyConstant T :=
      (hh.1.prodMk ((orbit_locallyConstant (omR_smooth hμ') Φ).comp_continuous
        (ExchangeSupport.continuous_rowE.prodMk continuous_const))).comp fun z => z.1 • z.2
    obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
      (Measure.pi fun _ => ν) _ T hT _ hh.2 fun u hu => by
        simp only [T, image_eq_zero_of_notMem_tsupport hu, zero_smul]
    refine ⟨w, funext fun x => (hw (ev x)).symm, fun h => funext fun x₀ => ?_, ?_⟩
    · refine (hw ((ev x₀).comp ((opL hψ ν ρ).comp (omR μ (1, h))))).trans ?_
      rw [opEFJ]
      congr 1; funext u
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul]
      congr 1
      have := GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent k n n' c ρ (by omega) (by omega) ψ hψ ν μ (omR μ (1, h) Φ) u x₀
      rw [← omR_val, omR_mul, one_mul, mul_one] at this
      rw [omR_mul, one_mul, mul_one]
      exact this
    · rw [hfj]
      refine Eq.trans ?_ (hw ((b' φ).comp (ϑ F))).symm
      congr 1; funext u
      have := hϑ (rowE (c + 1) ρ u) 1 F Φ (omR μ (rowE (c + 1) ρ u, 1) Φ) rfl
      rw [map_one, Module.End.one_apply] at this
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul, this]
  refine ⟨GlobalTheory.T.isUnimodular_blockUpperTriangular_symmetricLevels k n c _ _ (fun i => ?_) _ (GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries k n c ρ).1, fun Φ Φ₀ => ?_, fun H Φ => ?_,
    fun H Φ Φ₀ => ?_⟩
  · have := i.2
    simp only [Fin.val_rev]
    omega
  · obtain ⟨w, e1, e2, e3⟩ := main Φ Φ₀
    rw [e1, app_coe]
    exact ⟨w.2, fun h => (opL hψ ν ρ (omR μ (1, h) Φ)).2, fun h => e2 h ▸ (opL hψ ν ρ (omR μ (1, h) w)).2, e2, e3⟩
  · have hU : {u : n' → k | omR μ (rowE (c + 1) ρ u, 1) Φ = Φ} ∈ 𝓝 (0 : n' → k) :=
      ((omR_smooth hμ' Φ).preimage (ExchangeSupport.continuous_rowE.prodMk continuous_const)).mem_nhds (by
        change omR μ (rowE (c + 1) ρ 0, 1) Φ = Φ
        rw [ExchangeSupport.rowE_zero, ← Prod.one_eq_mk, map_one, Module.End.one_apply])
    obtain ⟨g, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n' ν _ hU
    obtain ⟨Φ₀, h0⟩ := hF.2 g
    obtain ⟨w, e1, e2, e3⟩ := main Φ Φ₀
    have e : w = Φ := by
      refine Subtype.ext (e1.symm.trans (funext fun x => ?_))
      rw [avg, h0, integral_mul_of_support (z := Φ.1 x) a, a1, one_mul]
      intro u hu
      exact congrArg (fun t : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) => t.1 x) hu
    have := H Φ Φ₀
    simp only [← e2, e3, e] at this
    exact this
  · obtain ⟨w, -, e2, e3⟩ := main Φ Φ₀
    simp only [← e2, e3]
    exact H w

theorem fourierJacobiBessel : FourierJacobiBessel :=
  fun _ _ _ _ _ _ _ => ⟨heisenberg, uniqueBessel, exponents, localSign, target, source⟩

end GlobalTheory.RootEx.FourierJacobi
