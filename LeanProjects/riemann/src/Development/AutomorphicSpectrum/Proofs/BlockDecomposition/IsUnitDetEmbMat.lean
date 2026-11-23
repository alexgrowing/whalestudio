import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6

noncomputable section

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module TensorProduct Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps
open scoped Classical

section Coord

variable {Qp Om LL BdR : Type} [Field Qp] [Field Om] [Field LL] [CommRing BdR]
  [Algebra Qp Om] [Algebra Qp LL] [Algebra Qp BdR] [Algebra Om BdR] [IsScalarTower Qp Om BdR]

def ev (σ : LL →ₐ[Qp] Om) : (Fin 1 → LL) ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift
    ((LinearMap.mul Qp BdR).comp
      (((IsScalarTower.toAlgHom Qp Om BdR).toLinearMap.comp σ.toLinearMap).comp
        (LinearMap.proj 0 : (Fin 1 → LL) →ₗ[Qp] LL)))

@[simp] theorem ev_tmul (σ : LL →ₐ[Qp] Om) (v : Fin 1 → LL) (b : BdR) :
    ev σ (v ⊗ₜ[Qp] b) = algebraMap Om BdR (σ (v 0)) * b := by
  simp [ev]

theorem ev_smul (σ : LL →ₐ[Qp] Om) (c : LL) (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    ev σ (c • z) = algebraMap Om BdR (σ c) * ev σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [TensorProduct.smul_tmul', mul_assoc]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]

variable [FiniteDimensional Qp LL] [Algebra.IsSeparable Qp LL] [IsAlgClosed Om]

variable (Qp Om LL) in

def embBasis : Basis (LL →ₐ[Qp] Om) Qp LL :=
  (finBasis Qp LL).reindex (Fintype.equivFinOfCardEq (AlgHom.card Qp LL Om)).symm

variable (Qp Om LL) in

def embMat : Matrix (LL →ₐ[Qp] Om) (LL →ₐ[Qp] Om) Om :=
  Algebra.embeddingsMatrixReindex Qp Om (embBasis Qp Om LL) (Equiv.refl _)

theorem embMat_apply (i j : LL →ₐ[Qp] Om) : embMat Qp Om LL i j = j (embBasis Qp Om LL i) := rfl

theorem isUnit_det_embMat : IsUnit (embMat Qp Om LL).det := by
  refine isUnit_iff_ne_zero.2 fun h => ?_
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two Qp Om (embBasis Qp Om LL) (Equiv.refl _)
  have h2 : algebraMap Qp Om (Algebra.discr Qp (embBasis Qp Om LL)) = 0 := by
    rw [h1]; change (embMat Qp Om LL).det ^ 2 = 0; rw [h]; simp
  exact Algebra.discr_not_zero_of_basis Qp (embBasis Qp Om LL)
    ((map_eq_zero_iff _ (algebraMap Qp Om).injective).1 h2)

def coordInv (f : (LL →ₐ[Qp] Om) → BdR) : (Fin 1 → LL) ⊗[Qp] BdR :=
  ∑ i, (fun _ => embBasis Qp Om LL i) ⊗ₜ[Qp]
    ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j

theorem ev_coordInv (f : (LL →ₐ[Qp] Om) → BdR) (k : LL →ₐ[Qp] Om) :
    ev k (coordInv f) = f k := by
  have hN : (embMat Qp Om LL)⁻¹ * embMat Qp Om LL = 1 := Matrix.nonsing_inv_mul _ isUnit_det_embMat
  have h1 : ∀ j, ∑ i, embMat Qp Om LL i k * (embMat Qp Om LL)⁻¹ j i = if j = k then 1 else 0 := fun j => by
    have := congrFun (congrFun hN j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [coordInv, map_sum, ev_tmul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ i, algebraMap Om BdR (k (embBasis Qp Om LL i)) *
      (algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j) =
      algebraMap Om BdR (if j = k then 1 else 0) * f j := fun j => by
    rw [← h1 j, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, embMat_apply, mul_assoc]
  simp only [h2]
  simp

theorem coordInv_add (f g : (LL →ₐ[Qp] Om) → BdR) : coordInv (f + g) = coordInv f + coordInv g := by
  simp only [coordInv, Pi.add_apply, mul_add, Finset.sum_add_distrib, tmul_add]

theorem coordInv_ev (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    coordInv (fun σ : LL →ₐ[Qp] Om => ev σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add x y hx hy =>
    nth_rw 2 [← hx]
    nth_rw 2 [← hy]
    rw [← coordInv_add]
    congr 1
    funext σ
    simp
  | tmul v b =>
    have hM : embMat Qp Om LL * (embMat Qp Om LL)⁻¹ = 1 := Matrix.mul_nonsing_inv _ isUnit_det_embMat
    set a := (embBasis Qp Om LL).repr (v 0) with ha
    have hv : v 0 = ∑ k, a k • embBasis Qp Om LL k := ((embBasis Qp Om LL).sum_repr (v 0)).symm
    have h1 : ∀ i, ∑ j, (embMat Qp Om LL)⁻¹ j i * j (v 0) = algebraMap Qp Om (a i) := fun i => by
      have h2 : ∀ j : LL →ₐ[Qp] Om, j (v 0) = ∑ k, algebraMap Qp Om (a k) * embMat Qp Om LL k j := fun j => by
        rw [hv, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, Algebra.smul_def, embMat_apply]
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h3 : ∀ k, ∑ j, (embMat Qp Om LL)⁻¹ j i * (algebraMap Qp Om (a k) * embMat Qp Om LL k j) =
          algebraMap Qp Om (a k) * (if k = i then 1 else 0) := fun k => by
        have := congrFun (congrFun hM k) i
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp only [h3]
      simp
    have h4 : ∀ i, ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) *
        (algebraMap Om BdR (j (v 0)) * b) = a i • b := fun i => by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply Qp Om BdR, ← h1, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    simp only [coordInv, ev_tmul, h4, tmul_smul]
    have h5 : v = ∑ i, a i • (fun _ : Fin 1 => embBasis Qp Om LL i) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact hv
    conv_rhs => rw [h5, sum_tmul]
    exact Finset.sum_congr rfl fun i _ => rfl

theorem ev_injective {z w : (Fin 1 → LL) ⊗[Qp] BdR} (h : ∀ σ : LL →ₐ[Qp] Om, ev σ z = ev σ w) : z = w := by
  rw [← coordInv_ev (Om := Om) z, ← coordInv_ev (Om := Om) w]
  exact congrArg _ (funext h)

end Coord

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR_iff (ρ : Representation LL G V) (z : V ⊗[Qp] BdR) :
    z ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g z = z := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_DdRE_iff (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (z : V ⊗[Qp] BdR) :
    z ∈ DdRE PD ρ τ ↔ z ∈ DdR PD ρ ∧
      ∀ c, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c z = τ c • z := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem exists_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ)
    (h : ∀ a, multV PD ρ τ a = if a = J then 1 else 0) :
    ∃ z ∈ DdRE PD ρ τ, (∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z) ∧
      z ∈ FilV PD (LL := LL) (V := V) J ∧ z ∉ FilV PD (LL := LL) (V := V) (J + 1) := by
  haveI : FiniteDimensional LL (DdRE PD ρ τ) :=
    finite_ddRE_of_multV PD ρ τ {J} (by simp) fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl
  have hanti : ∀ a, FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := fun a =>
    inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1))
  have h1 : finrank LL (DdRE PD ρ τ) = 1 :=
    finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left) hanti
      (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩)
      (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) J h
  have hJ := h J
  rw [if_pos rfl] at hJ
  unfold multV at hJ
  have hle : finrank LL (FildR PD ρ τ J) ≤ 1 := by
    rw [← h1]; exact Submodule.finrank_mono inf_le_left
  have h2 : finrank LL (FildR PD ρ τ J) = 1 := by omega
  have h3 : finrank LL (FildR PD ρ τ (J + 1)) = 0 := by omega
  have h4 : FildR PD ρ τ J = DdRE PD ρ τ :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, h2])
  haveI : FiniteDimensional LL (FildR PD ρ τ (J + 1)) := Submodule.finiteDimensional_of_le inf_le_left
  have h5 : FildR PD ρ τ (J + 1) = ⊥ := Submodule.finrank_eq_zero.1 h3
  obtain ⟨z, hz0, hz⟩ := finrank_eq_one_iff'.1 h1
  have hz1 : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ J := by rw [h4]; exact z.2
  refine ⟨z, z.2, fun w hw => ?_, hz1.2, fun hz2 => ?_⟩
  · obtain ⟨c, hc⟩ := hz ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · have : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ (J + 1) := ⟨z.2, hz2⟩
    rw [h5, Submodule.mem_bot] at this
    exact hz0 (Subtype.ext this)

theorem multV_of_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ DdRE PD ρ τ) (hgen : ∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z)
    (h1 : z ∈ FilV PD (LL := LL) (V := V) J) (h2 : z ∉ FilV PD (LL := LL) (V := V) (J + 1)) (a : ℤ) :
    multV PD ρ τ a = if a = J then 1 else 0 := by
  have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  have hlo : ∀ a ≤ J, FildR PD ρ τ a = LL ∙ z := fun a ha => by
    refine le_antisymm (fun w hw => ?_) ?_
    · obtain ⟨c, rfl⟩ := hgen w hw.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hz, filV_anti PD ha h1⟩
  have hhi : ∀ a, J < a → FildR PD ρ τ a = ⊥ := fun a ha => by
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨c, rfl⟩ := hgen w hw.1
    by_cases hc : c = 0
    · simp [hc]
    · refine absurd ?_ h2
      have := filV_anti PD (by omega : J + 1 ≤ a) hw.2
      simpa [hc] using (Submodule.smul_mem_iff _ hc).1 this
  have hone : finrank LL (LL ∙ z) = 1 := finrank_span_singleton hz0
  unfold multV
  rcases lt_trichotomy a J with ha | ha | ha
  · rw [hlo a ha.le, hlo (a + 1) (by omega), if_neg ha.ne]; simp
  · subst ha
    rw [hlo a le_rfl, hhi (a + 1) (by omega), if_pos rfl, hone]; simp
  · rw [hhi a ha, hhi (a + 1) (by omega), if_neg ha.ne']; simp

end Period

end GlobalTheory.CompanionTheory.DeRhamChar
