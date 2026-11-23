import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerAlgO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderFaithfulLattice
import GroundTheory.Brauer.DoubleCentralizer

open scoped TensorProduct
namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

theorem Datum.tmul_one_injective : Function.Injective (fun x : D.La => (1 : ℚ) ⊗ₜ[ℤ] x) := by
  haveI := D.freeLa
  have hinj : Function.Injective (LinearMap.rTensor D.La (Algebra.linearMap ℤ ℚ)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => by
      simp only [Algebra.linearMap_apply, algebraMap_int_eq, eq_intCast] at h; exact_mod_cast h)
  intro x y h
  apply (TensorProduct.lid ℤ D.La).symm.injective
  apply hinj
  simpa using h

theorem Datum.actQ_injective : Function.Injective D.actQ := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  apply GlobalTheory.HTFaith.faithful p D b
  intro y
  apply D.tmul_one_injective
  have := congrArg (fun f : Module.End ℚ D.VQ => f (1 ⊗ₜ y)) hb
  simpa [D.actQ_tmul] using this

theorem Datum.exists_of_mem_algO {g : Module.End ℚ D.VQ} (hg : g ∈ D.algO) :
    ∃ (q : ℚ) (x : D.O), g = q • D.actQ x := by
  induction hg using Algebra.adjoin_induction with
  | mem g hg => obtain ⟨x, rfl⟩ := hg; exact ⟨1, x, by rw [one_smul]⟩
  | algebraMap r => exact ⟨r, 1, by rw [map_one, Algebra.algebraMap_eq_smul_one]⟩
  | add g h _ _ hg hh =>
    obtain ⟨q, x, rfl⟩ := hg
    obtain ⟨q', x', rfl⟩ := hh
    refine ⟨1 / (q.den * q'.den), (q.num * q'.den : ℤ) • x + (q'.num * q.den : ℤ) • x', ?_⟩
    rw [map_add, map_zsmul, map_zsmul, smul_add, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
      smul_smul, smul_smul]
    congr 2
    · push_cast; conv_lhs => rw [← Rat.num_div_den q]
      field_simp
    · push_cast; conv_lhs => rw [← Rat.num_div_den q']
      field_simp
  | mul g h _ _ hg hh =>
    obtain ⟨q, x, rfl⟩ := hg
    obtain ⟨q', x', rfl⟩ := hh
    exact ⟨q * q', x * x', by rw [smul_mul_smul_comm, map_mul]⟩
end GlobalTheory.UPel.HT

open NumberField
namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]
theorem Datum.center_algO (D : Datum p) (g : Module.End ℚ D.VQ) (hg : g ∈ D.algO)
    (hc : ∀ h ∈ D.algO, h * g = g * h) : ∃ c : D.F, g = ((D.actF c : D.endO) : Module.End ℚ D.VQ) := by
  obtain ⟨q, x, rfl⟩ := D.exists_of_mem_algO hg
  rcases eq_or_ne q 0 with hq | hq
  · exact ⟨0, by rw [hq, zero_smul, map_zero]; rfl⟩
  have hx : ∀ y, x * y = y * x := by
    intro y
    have h := hc (D.actQ y) (D.actQ_mem_algO y)
    rw [mul_smul_comm, smul_mul_assoc] at h
    have h' := smul_right_injective _ hq h
    apply D.actQ_injective
    rw [map_mul, map_mul]; exact h'.symm
  obtain ⟨c, e, he, hce⟩ := D.central x hx
  refine ⟨(q / e) • ((c : 𝓞 D.F) : D.F), ?_⟩
  rw [map_smul, D.actF_coe, Subalgebra.coe_smul, D.coe_actInt, ← hce, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  congr 1
  field_simp
end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]
theorem Datum.finrank_algO (D : Datum p) : Module.finrank ℚ D.algO = D.m ^ 2 * Module.finrank ℚ D.F := by
  haveI := D.freeO; haveI := D.finO
  let b := Module.Free.chooseBasis ℤ D.O
  let v : Module.Free.ChooseBasisIndex ℤ D.O → Module.End ℚ D.VQ := fun i => D.actQ (b i)
  let f : D.O →ₗ[ℤ] Module.End ℚ D.VQ := D.actQ.toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := D.actQ_injective
  have hZ : LinearIndependent ℤ v := b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)
  have hQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hZ
  have hspan : Submodule.span ℚ (Set.range v) = Subalgebra.toSubmodule D.algO := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact D.actQ_mem_algO _
    · intro g hg
      obtain ⟨q, x, rfl⟩ := D.exists_of_mem_algO hg
      refine Submodule.smul_mem _ q ?_
      have hx : D.actQ x = f x := rfl
      rw [hx, ← b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← Subalgebra.finrank_toSubmodule, ← hspan, finrank_span_eq_card hQ, ← Module.finrank_eq_card_chooseBasisIndex,
    D.rankO]
end GlobalTheory.UPel.HT

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

def Datum.toReal (D : Datum p) : D.VQ →ₗ[ℤ] ℝ ⊗[ℤ] D.La :=
  ((Algebra.linearMap ℚ ℝ).restrictScalars ℤ).rTensor D.La

theorem Datum.toReal_tmul (D : Datum p) (q : ℚ) (x : D.La) : D.toReal (q ⊗ₜ x) = (q : ℝ) ⊗ₜ x := rfl

theorem Datum.toReal_smul (D : Datum p) (q : ℚ) (t : D.VQ) : D.toReal (q • t) = (q : ℝ) • D.toReal t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul q' x =>
    rw [TensorProduct.smul_tmul', D.toReal_tmul, D.toReal_tmul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
      Rat.cast_mul]

theorem Datum.toReal_injective (D : Datum p) : Function.Injective D.toReal := by
  haveI := D.freeLa
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => by
    simpa using h)

def Datum.actReal (D : Datum p) (x : D.O) : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
  LinearMap.baseChange ℝ (DistribMulAction.toLinearMap ℤ D.La x)

theorem Datum.actReal_tmul (D : Datum p) (x : D.O) (r : ℝ) (y : D.La) : D.actReal x (r ⊗ₜ y) = r ⊗ₜ (x • y) := rfl

theorem Datum.toReal_actQ (D : Datum p) (x : D.O) (t : D.VQ) : D.toReal (D.actQ x t) = D.actReal x (D.toReal t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul q y => rw [D.actQ_tmul, D.toReal_tmul, D.toReal_tmul, D.actReal_tmul]

theorem Datum.ER_actReal (D : Datum p) (x : D.O) (a c : ℝ ⊗[ℤ] D.La) :
    D.EF.baseChange ℝ (D.actReal x a) c = D.EF.baseChange ℝ a (D.actReal (D.star x).unop c) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | tmul r y =>
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c c' h h' => simp only [map_add, h, h']
    | tmul r' z => rw [D.actReal_tmul, D.actReal_tmul, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, D.adj]

theorem Datum.exists_form (D : Datum p) : ∃ φ : D.VQ → D.VQ → ℝ,
  (∀ u, u ≠ 0 → 0 < φ u u) ∧
  (∀ (x : D.O) (u w : D.VQ), φ (D.actQ x u) w = φ u (D.actQ (D.star x).unop w)) ∧
  (∀ (q : ℚ) (u w : D.VQ), φ (q • u) w = q * φ u w) ∧
  (∀ (q : ℚ) (u w : D.VQ), φ u (q • w) = q * φ u w) := by
  obtain ⟨J, -, -, hJpos, hJO, -⟩ := D.dom
  refine ⟨fun u w => D.EF.baseChange ℝ (J (D.toReal u)) (D.toReal w), fun u hu => ?_, fun x u w => ?_,
    fun q u w => ?_, fun q u w => ?_⟩
  · refine hJpos _ fun h => hu (D.toReal_injective ?_)
    rw [h, map_zero]
  · have hc : J ∘ₗ D.actReal x = D.actReal x ∘ₗ J := hJO x (D.actReal x) fun y => rfl
    simp only
    rw [D.toReal_actQ, D.toReal_actQ, ← LinearMap.comp_apply J, hc, LinearMap.comp_apply, D.ER_actReal]
  · simp only
    rw [D.toReal_smul, map_smul, LinearMap.map_smul₂, smul_eq_mul]
  · simp only
    rw [D.toReal_smul, map_smul, smul_eq_mul]
end GlobalTheory.UPel.HT

end

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

theorem Datum.isSemisimpleRing_algO_of_form (D : Datum p) (φ : D.VQ → D.VQ → ℝ)
    (hpos : ∀ u, u ≠ 0 → 0 < φ u u)
    (hadj : ∀ (x : D.O) (u w : D.VQ), φ (D.actQ x u) w = φ u (D.actQ (D.star x).unop w))
    (hl : ∀ (q : ℚ) (u w : D.VQ), φ (q • u) w = q * φ u w)
    (hr : ∀ (q : ℚ) (u w : D.VQ), φ u (q • w) = q * φ u w) : IsSemisimpleRing D.algO := by

  have hB : ∀ h ∈ D.algO, D.adjE h ∈ D.algO ∧ ∀ u w, φ (h u) w = φ u (D.adjE h w) := by
    intro h hh
    obtain ⟨q, x, rfl⟩ := D.exists_of_mem_algO hh
    rw [D.adjE_smul, D.adjE_actQ]
    refine ⟨Subalgebra.smul_mem _ (D.actQ_mem_algO _) q, fun u w => ?_⟩
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hl, hr, hadj]
  have h0 : ∀ u, φ u 0 = 0 := fun u => by
    have := hr 0 u 0
    rwa [zero_smul, Rat.cast_zero, zero_mul] at this
  have hzero : ∀ z : Module.End ℚ D.VQ, (∀ u, φ (z u) (z u) = 0) → z = 0 := by
    intro z hz
    refine LinearMap.ext fun u => ?_
    by_contra hne
    exact (hpos _ hne).ne' (hz u)

  have hsq : ∀ z ∈ D.algO, D.adjE z = z → z * z = 0 → z = 0 := by
    intro z hz hs hzz
    apply hzero
    intro u
    rw [(hB z hz).2, hs, ← Module.End.mul_apply, hzz, LinearMap.zero_apply, h0]

  have hnil : ∀ y ∈ D.algO, D.adjE y = y → ∀ j : ℕ, y ^ (2 ^ j) = 0 → y = 0 := by
    intro y hy hs j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      apply ih
      have hpow : ∀ k : ℕ, D.adjE (y ^ k) = y ^ k := by
        intro k
        induction k with
        | zero => rw [pow_zero, D.adjE_one]
        | succ k ihk => rw [pow_succ, D.adjE_mul, ihk, hs]; exact (pow_mul_comm' y k).symm
      refine hsq _ (Subalgebra.pow_mem _ hy _) (hpow _) ?_
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hj
  haveI : IsArtinianRing D.algO := IsArtinianRing.of_finite ℚ D.algO
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro g hg
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := D.algO)
  rw [Ideal.jacobson_bot] at hn
  rw [Ideal.mem_bot]
  obtain ⟨hgB, hgadj⟩ := hB g g.2
  let y : D.algO := ⟨D.adjE g, hgB⟩ * g
  have hyJ : y ∈ Ring.jacobson D.algO := Ideal.mul_mem_left _ _ hg
  have hp := Ideal.pow_mem_pow hyJ n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
  have hys : D.adjE (y : Module.End ℚ D.VQ) = y := by
    show D.adjE (D.adjE g * g) = D.adjE g * g
    rw [D.adjE_mul, D.adjE_adjE]
  have hy0 : (y : Module.End ℚ D.VQ) = 0 := by
    refine hnil _ y.2 hys n ?_
    have h2 : (y : Module.End ℚ D.VQ) ^ n = 0 := by
      have := congrArg Subtype.val hp
      simpa using this
    exact pow_eq_zero_of_le (Nat.lt_two_pow_self).le h2
  apply Subtype.ext
  show (g : Module.End ℚ D.VQ) = 0
  apply hzero
  intro u
  rw [hgadj, ← Module.End.mul_apply]
  have : D.adjE g * g = (y : Module.End ℚ D.VQ) := rfl
  rw [this, hy0, LinearMap.zero_apply, h0]
end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

theorem Datum.isSemisimpleRing_algO (D : Datum p) : IsSemisimpleRing D.algO := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := D.exists_form
  exact D.isSemisimpleRing_algO_of_form φ h1 h2 h3 h4
end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

theorem isSimpleRing_of_isSemisimpleRing {R : Type} [Ring R] [Nontrivial R] [IsSemisimpleRing R]
    (h : ∀ e : R, (∀ x : R, e * x = x * e) → e * e = e → e = 0 ∨ e = 1) : IsSimpleRing R := by
  classical
  obtain ⟨n, K, d, _, hd, ⟨φ⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact absurd (φ.injective (Subsingleton.elim _ _) : (0 : R) = 1) zero_ne_one
    · exact IsSimpleRing.of_ringEquiv (φ.trans (RingEquiv.piUnique _)).symm inferInstance
  · let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    let e : (Π i, Matrix (Fin (d i)) (Fin (d i)) (K i)) := Pi.single i0 1
    have hcen : ∀ x : R, φ.symm e * x = x * φ.symm e := by
      intro x
      apply φ.injective
      rw [map_mul, map_mul, RingEquiv.apply_symm_apply]
      funext i
      by_cases hi : i = i0
      · subst hi; simp [e]
      · simp [e, Pi.single_apply, hi]
    have hid : φ.symm e * φ.symm e = φ.symm e := by
      rw [← map_mul]; congr 1; funext i
      by_cases hi : i = i0
      · subst hi; simp [e]
      · simp [e, Pi.single_apply, hi]
    rcases h _ hcen hid with h0 | h1
    · have := congrFun (congrArg φ h0) i0
      simp [e] at this
    · have := congrFun (congrArg φ h1) i1
      simp [e, Pi.single_apply, h01.symm] at this

theorem Datum.actF_injective (D : Datum p) : Function.Injective D.actF := by
  haveI : Nontrivial D.endO := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg Subtype.val h
    exact zero_ne_one this
  exact D.actF.toRingHom.injective

theorem Datum.algO_simple (D : Datum p) : IsSimpleRing D.algO := by
  haveI := D.isSemisimpleRing_algO
  apply isSimpleRing_of_isSemisimpleRing
  intro e he hid
  obtain ⟨c, hc⟩ := D.center_algO e e.2 fun h hh => (congrArg Subtype.val (he ⟨h, hh⟩)).symm
  have hcc : c * c = c := by
    apply D.actF_injective
    apply Subtype.ext
    rw [map_mul, Subalgebra.coe_mul, ← hc]
    exact congrArg Subtype.val hid
  have hc01 : c = 0 ∨ c = 1 := by
    rcases eq_or_ne c 0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (hcc.trans (mul_one c).symm))
  rcases hc01 with h0 | h1
  · left; apply Subtype.ext; rw [hc, h0, map_zero]; rfl
  · right; apply Subtype.ext; rw [hc, h1, map_one]; rfl

theorem endO_centralSimple : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
    Algebra.IsCentral D.F D.endO ∧ IsSimpleRing D.endO ∧ Module.finrank D.F D.endO = D.n ^ 2 := by
  intro p _ D
  haveI : IsSimpleRing D.algO := D.algO_simple
  haveI : IsSimpleRing (Module.End ℚ D.VQ) := GroundTheory.Brauer.isSimpleRing_end ℚ ℚ D.VQ
  have hs := GroundTheory.Brauer.isSimpleRing_centralizer D.algO
  have hdim := GroundTheory.Brauer.finrank_mul_finrank_centralizer D.algO
  have hcc := GroundTheory.Brauer.centralizer_centralizer D.algO
  rw [D.centralizer_algO] at hs hdim hcc
  haveI := D.freeLa; haveI := D.finLa
  have hV : Module.finrank ℚ D.VQ = D.m * D.n * Module.finrank ℚ D.F := by
    rw [Module.finrank_baseChange, D.rankLa]
  rw [Module.finrank_linearMap, hV, D.finrank_algO] at hdim
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hm := D.m_pos
  have hC : Module.finrank ℚ D.endO = D.n ^ 2 * Module.finrank ℚ D.F := by
    have h2 : D.m ^ 2 * Module.finrank ℚ D.F * Module.finrank ℚ D.endO =
        D.m ^ 2 * Module.finrank ℚ D.F * (D.n ^ 2 * Module.finrank ℚ D.F) := by rw [hdim]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have htow := Module.finrank_mul_finrank ℚ D.F D.endO
  refine ⟨⟨fun z hz => ?_⟩, hs, ?_⟩
  · have hz' : (z : Module.End ℚ D.VQ) ∈ D.algO := by
      rw [← hcc, Subalgebra.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subalgebra.mem_center_iff.1 hz ⟨y, hy⟩)
    have hz2 : (z : Module.End ℚ D.VQ) ∈ Subalgebra.centralizer ℚ (D.algO : Set (Module.End ℚ D.VQ)) := by
      rw [D.centralizer_algO]; exact z.2
    obtain ⟨c, hc⟩ := D.center_algO z hz' fun h hh => (Subalgebra.mem_centralizer_iff ℚ).1 hz2 h hh
    exact ⟨c, Subtype.ext hc.symm⟩
  · rw [hC] at htow
    exact Nat.eq_of_mul_eq_mul_left hd (by rw [htow, mul_comm])

end GlobalTheory.UPel.HT
