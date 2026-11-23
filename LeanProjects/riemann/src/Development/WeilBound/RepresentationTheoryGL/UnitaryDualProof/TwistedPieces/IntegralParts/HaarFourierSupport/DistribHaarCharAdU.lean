import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceNilpotentConeProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoxInvariantSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharConductorIntegersContinuousNeOneStatement

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

structure Hyp : Prop where
  symm : ∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)
  nondeg : ∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0
  nil : ∀ x ∈ NB Z, τ x = 0

abbrev dd : ℕ := Module.finrank k (PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z)

def bas : Module.Basis (Fin (dd Z)) k (PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z) := Module.finBasis k _

def ee (j : Fin (dd Z)) : Matrix (Fin n) (Fin n) k := (bas Z j : PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z)

def E (u : Fin (dd Z) → k) : Matrix (Fin n) (Fin n) k := ((bas Z).equivFun.symm u : PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z)

def D (x : Matrix (Fin n) (Fin n) k) : Fin (dd Z) → k := fun j => τ (ee Z j * x)

def G : Matrix (Fin (dd Z)) (Fin (dd Z)) k := Matrix.of fun i j => τ (ee Z i * ee Z j)

theorem dd_eq : dd Z = dB Z := by
  have e : PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL Z =
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    ext x
    simp only [PositivityTheory.RgUd.T.Nil.Four.Phi2.BzL, Bz, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff,
      SetLike.mem_coe]
  unfold dd dB
  rw [e, Subalgebra.finrank_toSubmodule]

theorem E_apply (u : Fin (dd Z) → k) : E Z u = ∑ j, u j • ee Z j := by
  simp [E, ee, Module.Basis.equivFun_symm_apply]

theorem E_mem (u : Fin (dd Z) → k) : E Z u ∈ Bz Z := ((bas Z).equivFun.symm u).2

theorem ee_mem (j : Fin (dd Z)) : ee Z j ∈ Bz Z := (bas Z j).2

theorem E_add (u u' : Fin (dd Z) → k) : E Z (u + u') = E Z u + E Z u' := by
  simp only [E, map_add, Submodule.coe_add]

theorem E_smul (c : k) (u : Fin (dd Z) → k) : E Z (c • u) = c • E Z u := by
  simp only [E, map_smul, Submodule.coe_smul]

theorem E_neg (u : Fin (dd Z) → k) : E Z (-u) = -E Z u := by
  simp only [E, map_neg, Submodule.coe_neg]

theorem E_injective : Function.Injective (E Z) := fun u u' h =>
  (bas Z).equivFun.symm.injective (Subtype.ext h)

theorem E_zero : E Z 0 = 0 := by simp [E]

theorem exists_E {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ Bz Z) : ∃ u, E Z u = w :=
  ⟨(bas Z).equivFun ⟨w, hw⟩, by simp [E]⟩

theorem dot_D (u : Fin (dd Z) → k) (x : Matrix (Fin n) (Fin n) k) : u ⬝ᵥ D τ Z x = τ (E Z u * x) := by
  simp [E_apply, D, dotProduct, Finset.sum_mul, map_sum, smul_mul_assoc]

theorem D_E (u : Fin (dd Z) → k) : D τ Z (E Z u) = G τ Z *ᵥ u := by
  funext i
  simp [D, G, E_apply, mulVec, dotProduct, Finset.mul_sum, map_sum, mul_smul_comm, mul_comm]

theorem D_add (x y : Matrix (Fin n) (Fin n) k) : D τ Z (x + y) = D τ Z x + D τ Z y := by
  funext j; simp [D, mul_add]

theorem D_sub (x y : Matrix (Fin n) (Fin n) k) : D τ Z (x - y) = D τ Z x - D τ Z y := by
  funext j; simp [D, mul_sub]

theorem D_smul (c : k) (x : Matrix (Fin n) (Fin n) k) : D τ Z (c • x) = c • D τ Z x := by
  funext j; simp [D]

theorem mul_mem_Bz {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) (hy : y ∈ Bz Z) : x * y ∈ Bz Z := by
  intro a ha
  rw [← mul_assoc, hx a ha, mul_assoc, hy a ha, mul_assoc]

theorem val_mem_Bz {g : GL (Fin n) k} (hg : g ∈ Gz Z) : g.val ∈ Bz Z := fun a ha => hg a ha

variable {τ Z}

theorem G_symm (h : Hyp τ Z) : (G τ Z)ᵀ = G τ Z := by
  ext i j
  simp only [G, transpose_apply, of_apply]
  exact h.symm _ (ee_mem Z j) _ (ee_mem Z i)

theorem G_inj (h : Hyp τ Z) {u : Fin (dd Z) → k} (hu : G τ Z *ᵥ u = 0) : u = 0 := by
  have hw : E Z u = 0 := by
    refine h.nondeg _ (E_mem Z u) fun y hy => ?_
    obtain ⟨u', rfl⟩ := exists_E Z hy
    rw [h.symm _ (E_mem Z u) _ (E_mem Z u'), ← dot_D, D_E, hu, dotProduct_zero]
  exact E_injective Z (by rw [hw, E_zero])

theorem G_det (h : Hyp τ Z) : (G τ Z).det ≠ 0 := by
  intro h0
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  exact hu0 (G_inj h hu)

variable (τ Z)

def Pr (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin n) (Fin n) k := E Z ((G τ Z)⁻¹ *ᵥ D τ Z x)

variable {τ Z}

theorem D_Pr (h : Hyp τ Z) (x : Matrix (Fin n) (Fin n) k) : D τ Z (Pr τ Z x) = D τ Z x := by
  rw [Pr, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det h)), one_mulVec]

theorem Pr_E (h : Hyp τ Z) (u : Fin (dd Z) → k) : Pr τ Z (E Z u) = E Z u := by
  rw [Pr, D_E, mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det h)), one_mulVec]

theorem D_sub_Pr (h : Hyp τ Z) (x : Matrix (Fin n) (Fin n) k) : D τ Z (x - Pr τ Z x) = 0 := by
  rw [D_sub, D_Pr h, sub_self]

theorem Pr_add (x y : Matrix (Fin n) (Fin n) k) : Pr τ Z (x + y) = Pr τ Z x + Pr τ Z y := by
  simp [Pr, D_add, mulVec_add, E_add]

theorem Pr_smul (c : k) (x : Matrix (Fin n) (Fin n) k) : Pr τ Z (c • x) = c • Pr τ Z x := by
  simp [Pr, D_smul, mulVec_smul, E_smul]

theorem Pr_of_D {x : Matrix (Fin n) (Fin n) k} (hx : D τ Z x = 0) : Pr τ Z x = 0 := by
  simp [Pr, hx, E]

theorem Pr_of_mem (h : Hyp τ Z) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) : Pr τ Z x = x := by
  obtain ⟨u, rfl⟩ := exists_E Z hx
  exact Pr_E h u

theorem tau_conj (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) {y : Matrix (Fin n) (Fin n) k} (hy : y ∈ Bz Z) :
    τ (g.val * y * g⁻¹.val) = τ y := by
  have hgi : g⁻¹.val ∈ Bz Z := val_mem_Bz Z (PositivityTheory.RgUd.T.Nil.Four.Phi2.inv_mem_Gz hg)
  rw [h.symm _ (mul_mem_Bz Z (val_mem_Bz Z hg) hy) _ hgi, ← mul_assoc, Units.inv_mul, one_mul]

def adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (Fin (dd Z) → k) →ₗ[k] (Fin (dd Z) → k) where
  toFun u := (bas Z).equivFun ⟨g.val * E Z u * g⁻¹.val, PositivityTheory.RgUd.T.Nil.Four.Phi2.conj_mem_Bz hg (E_mem Z u)⟩
  map_add' u u' := by
    rw [← map_add]
    congr 1
    ext1
    simp [E_add, mul_add, add_mul]
  map_smul' c u := by
    rw [← map_smul]
    congr 1
    ext1
    simp [E_smul]

theorem E_adL {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (dd Z) → k) :
    E Z (adL hg u) = g.val * E Z u * g⁻¹.val := by
  simp [adL, E]

theorem conj_mul (g : GL (Fin n) k) (A B : Matrix (Fin n) (Fin n) k) :
    g.val * A * g⁻¹.val * (g.val * B * g⁻¹.val) = g.val * (A * B) * g⁻¹.val := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem dot_conj (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (dd Z) → k)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) :
    adL hg u ⬝ᵥ D τ Z (g.val * x * g⁻¹.val) = u ⬝ᵥ D τ Z x := by
  rw [dot_D, dot_D, E_adL, conj_mul, tau_conj h hg (mul_mem_Bz Z (E_mem Z u) hx)]

def adM {g : GL (Fin n) k} (hg : g ∈ Gz Z) : Matrix (Fin (dd Z)) (Fin (dd Z)) k := LinearMap.toMatrix' (adL hg)

theorem adM_mulVec {g : GL (Fin n) k} (hg : g ∈ Gz Z) (u : Fin (dd Z) → k) : adM hg *ᵥ u = adL hg u :=
  LinearMap.toMatrix'_mulVec _ _

theorem dot_G (u u' : Fin (dd Z) → k) : u ⬝ᵥ (G τ Z *ᵥ u') = τ (E Z u * E Z u') := by
  rw [← D_E, dot_D]

theorem gram_adM (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg)ᵀ * G τ Z * adM hg = G τ Z := by
  have key : ∀ u u', u ⬝ᵥ (((adM hg)ᵀ * G τ Z * adM hg) *ᵥ u') = u ⬝ᵥ (G τ Z *ᵥ u') := by
    intro u u'
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, adM_mulVec, adM_mulVec, dot_G,
      dot_G, E_adL, E_adL, conj_mul, tau_conj h hg (mul_mem_Bz Z (E_mem Z u) (E_mem Z u'))]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single_one] using this

theorem det_adM_sq (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : (adM hg).det ^ 2 = 1 := by
  have h1 := congrArg Matrix.det (gram_adM h hg)
  rw [det_mul, det_mul, det_transpose] at h1
  have h2 : ((adM hg).det ^ 2 - 1) * (G τ Z).det = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linear_combination h3
  · exact absurd h3 (G_det h)

def adU (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) : GL (Fin (dd Z)) k :=
  Matrix.nonsingInvUnit (adM hg) (Ne.isUnit fun h0 => by
    have := det_adM_sq h hg
    rw [h0] at this
    norm_num at this)

theorem distribHaarChar_adU (h : Hyp τ Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) :
    (distribHaarChar k (Matrix.GeneralLinearGroup.det (adU h hg)) : NNReal) = 1 := by
  set u := Matrix.GeneralLinearGroup.det (adU h hg)
  have hu : u ^ 2 = 1 := Units.ext (by
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_adM_sq h hg)
  have h2 : (distribHaarChar k u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end PositivityTheory.RgUd.TP.Nil.Four
