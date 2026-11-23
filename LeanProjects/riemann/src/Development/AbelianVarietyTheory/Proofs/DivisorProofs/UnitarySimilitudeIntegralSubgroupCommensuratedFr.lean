import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableConjRangeGLSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicIntegersQuotPrimePowOfFiniteDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicTensorUnramifiedIntegersQuotPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicPowMulMemTensorUnramifiedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableMapConjProdPiStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HeckeP

theorem mem_range_map_subtype {B : Type} [CommRing B] (R : Subring B) {n : ℕ} (g : GL (Fin n) B) :
    g ∈ (GeneralLinearGroup.map R.subtype).range ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) B) i j ∈ R) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((h : Matrix (Fin n) (Fin n) R) i j).2
    · rw [← map_inv]; exact ((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (fun X : Matrix (Fin n) (Fin n) R => X.map R.subtype) :=
      fun X Y e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
    have hM : M.map R.subtype = (g : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have hM' : M'.map R.subtype = ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
    have e1 : M * M' = 1 := hinj (by
      show (M * M').map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv)
    have e2 : M' * M = 1 := hinj (by
      show (M' * M).map R.subtype = (1 : Matrix (Fin n) (Fin n) R).map R.subtype
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul)
    exact ⟨⟨M, M', e1, e2⟩, Units.ext hM⟩

variable (p : ℕ) [Fact p.Prime]

theorem inclK_mem_intKQ_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (a : K) :
    inclK p K r a ∈ intKQ p K r ↔ a ∈ GlobalTheory.LKLoc.intK p K := by
  constructor
  · intro h
    have h1 := GlobalTheory.LKRes.Model.mulMap_intKQ p K r _ h
    have h2 : GlobalTheory.LKRes.Model.mulMap p K r (inclK p K r a) = (a : PadicAlgCl p) := by
      show (a : PadicAlgCl p) * 1 = _
      rw [mul_one]
    rw [h2] at h1
    exact (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 h1
  · intro h
    exact Subring.subset_closure (Or.inl ⟨⟨a, h⟩, rfl⟩)

theorem map_inclK_mem_Kres_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (g : GL (Fin n) K) :
    GeneralLinearGroup.map (inclK p K r).toRingHom g ∈ Kres p K n r ↔ g ∈ GlobalTheory.LKLoc.KintK p K n := by
  unfold Kres GlobalTheory.LKLoc.KintK
  rw [mem_range_map_subtype, mem_range_map_subtype, ← map_inv]
  simp only [GeneralLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, RingHom.mapMatrix_apply]
  simp [Matrix.map_apply, inclK_mem_intKQ_iff]

theorem scalar_mem_Kint_iff (r : ℕ) (s : ℚ_[p]ˣ) :
    (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom s) ∈
        GlobalTheory.LKLoc.Kint p (Q0 p) 1 r ↔ ‖(s : ℚ_[p])‖ ≤ 1 ∧ ‖((s⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1 := by
  unfold GlobalTheory.LKLoc.Kint
  rw [mem_range_map_subtype, ← map_inv, ← map_inv]
  have key : ∀ t : ℚ_[p], algebraMap ℚ_[p] (Qr p r) t ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖ ≤ 1 := by
    intro t
    rw [GlobalTheory.LKLoc.intR, Subring.mem_comap, ValuationSubring.mem_toSubring, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff,
      ← IsScalarTower.algebraMap_apply, PadicAlgCl.norm_extends]
  have key' : ∀ t : ℚ_[p], (algebraMap ℚ_[p] (Qr p r) t)⁻¹ ∈ GlobalTheory.LKLoc.intR p (Q0 p) r ↔ ‖t‖⁻¹ ≤ 1 := by
    intro t; rw [← map_inv₀, key, norm_inv]
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, key, key']

theorem inclG_mem_KHT_iff (G : HTGroup p) (r : ℕ) (x : Gp G) :
    inclG G r x ∈ KHT p G.m G.n r G.Fw ↔
      (‖(x.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((x.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ∧
        ∀ w, x.2 w ∈ GlobalTheory.LKLoc.KintK p (G.Fw w) G.n := by
  unfold KHT
  rw [Subgroup.mem_prod, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]
  have h1 : (inclG G r x).1 =
      (GeneralLinearGroup.scalar (Fin 1)) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom x.1) := rfl
  have h2 : ∀ w, (inclG G r x).2 w = GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom (x.2 w) :=
    fun w => rfl
  rw [h1, scalar_mem_Kint_iff]
  simp only [h2, map_inclK_mem_Kres_iff]

theorem gl_one_map_conj {R : Type} [CommRing R] (H : Subgroup (GL (Fin 1) R)) (g : GL (Fin 1) R) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have hc : ∀ a b : GL (Fin 1) R, a * b = b * a := fun a b => by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have : (MulAut.conj g).toMonoidHom = MonoidHom.id _ := MonoidHom.ext fun x => by
    show g * x * g⁻¹ = x
    rw [hc g x, mul_inv_cancel_right]
  rw [this, Subgroup.map_id]

theorem Kres_commensurable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    Subgroup.Commensurable ((Kres p K n r).map (MulAut.conj g).toMonoidHom) (Kres p K n r) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  have mono : ∀ (x : KQ p K r) (k l : ℕ), k ≤ l → (p : KQ p K r) ^ k * x ∈ intKQ p K r →
      (p : KQ p K r) ^ l * x ∈ intKQ p K r := by
    intro x k l hkl h
    rw [← Nat.add_sub_cancel' hkl, pow_add, mul_comm ((p : KQ p K r) ^ k), mul_assoc]
    exact mul_mem (pow_mem (natCast_mem _ p) _) h
  choose f hf using GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers p K r
  let k : ℕ := (Finset.univ.sup fun ij : Fin n × Fin n => f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) ⊔
    Finset.univ.sup fun ij : Fin n × Fin n => f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)
  have hk1 : ∀ i j, (p : KQ p K r) ^ k * (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_left.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f ((g : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  have hk2 : ∀ i j, (p : KQ p K r) ^ k *
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r :=
    fun i j => mono _ _ _ (le_sup_right.trans' (Finset.le_sup (f := fun ij : Fin n × Fin n =>
      f (((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) ij.1 ij.2)) (Finset.mem_univ (i, j)))) (hf _)
  let c : intKQ p K r := (p : intKQ p K r) ^ k
  have hc : (c : KQ p K r) = (p : KQ p K r) ^ k := by simp [c]
  have hfin : Finite (intKQ p K r ⧸ Ideal.span {c * c}) := by
    have h := GlobalTheory.T.finite_padicTensorUnramifiedIntegers_quot_primePow p K r (2 * k) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p K (2 * k)) (GlobalTheory.T.finite_padicIntegers_quot_primePow_of_finiteDim p (Qr p r) (2 * k))
    have e : c * c = (p : intKQ p K r) ^ (2 * k) := by simp only [c]; ring
    rw [e]; exact h
  exact GlobalTheory.T.commensurable_conj_range_gl_map_subtype (intKQ p K r) n c hfin g (fun i j => by rw [hc]; exact hk1 i j)
    (fun i j => by rw [hc]; exact hk2 i j)

end GlobalTheory.HeckeP

open GlobalTheory.HeckeP in

theorem GlobalTheory.heckeOperator_integral :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
      (∀ g : Gr G r, Subgroup.Commensurable ((KHT p G.m G.n r G.Fw).map (MulAut.conj g).toMonoidHom)
        (KHT p G.m G.n r G.Fw)) ∧
      (KHT p G.m G.n r G.Fw).comap (inclG G r) = Kp0 G ∧
      (KHT p G.m G.n r G.Fw).map (sigG G r) ≤ KHT p G.m G.n r G.Fw := by
  intro p _ G r hr
  refine ⟨fun g => ?_, ?_, ?_⟩
  · unfold KHT
    exact GlobalTheory.T.commensurable_map_conj_prod_pi' _ _ g (by rw [gl_one_map_conj])
      (fun i => Kres_commensurable p (G.Fw i) G.n r hr (g.2 i))
  · ext x
    rw [Subgroup.mem_comap, Kp0, Subgroup.mem_comap, inclG_mem_KHT_iff, inclG_mem_KHT_iff]
  · rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.LKRes.Model.sigHT_KHT p _ _ _ _ x hx
