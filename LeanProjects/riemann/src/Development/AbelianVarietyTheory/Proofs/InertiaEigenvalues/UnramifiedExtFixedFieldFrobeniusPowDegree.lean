import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.UnrDeg

theorem det_pow_ne_zero {k F : Type} [Field k] [Field F] [Algebra k F] (τ : F ≃ₐ[k] F) {n : ℕ}
    (hord : orderOf τ = n) (bas : Module.Basis (Fin n) k F) :
    (Matrix.of fun i j : Fin n => (τ ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : F →ₗ[k] F :=
    { toFun := fun x => ∑ j : Fin n, u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin n → (F →* F) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : F ≃+* F).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom F F).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

variable {l : ℕ} [Fact l.Prime]

def sig (l : ℕ) [Fact l.Prime] : ↥(MaximalUnramifiedExtension l) ≃ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  AlgEquiv.ofBijective (frobUr l) frobUr_bijective

theorem fr_apply (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l k c = (frobUr l ^ k) c := rfl

theorem sig_pow (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : (sig l ^ k) c = fr l k c := by
  rw [fr_apply]
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgHom.mul_apply, ih]; rfl

end GlobalTheory.PMon.UnrDeg

namespace GlobalTheory.PMon.UnrDeg

theorem exists_moved (l : ℕ) [hl : Fact l.Prime] {r k : ℕ} (hk0 : 0 < k) (hkr : k < r) :
    ∃ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ∧ fr l k c ≠ c := by
  have h2 := hl.out.two_le
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hls : l ^ k ≤ l ^ s := Nat.pow_le_pow_right (by omega) (by omega)
  have hl1 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) hk0
  rw [pow_one] at hl1
  have h5 : l ^ s * 2 ≤ l ^ s * l := Nat.mul_le_mul_left _ h2
  have hps : l ^ (s + 1) = l ^ s * l := pow_succ _ _
  have hN0 : 0 < l ^ (s + 1) - 1 := by omega
  have hkN : l ^ k < l ^ (s + 1) - 1 := by omega
  have h1N : 1 < l ^ (s + 1) - 1 := by omega
  have hd : ¬ l ∣ l ^ (s + 1) - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ (s + 1) - 1) := ⟨hN0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ (s + 1) - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, hN0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ (s + 1) - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun h => ?_⟩
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1, show l ^ (s + 1) = (l ^ (s + 1) - 1) + 1 by omega, pow_succ, h1,
      one_mul]
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1] at h
    have h6 : z ^ l ^ k = z ^ 1 := by rw [pow_one]; exact congrArg Subtype.val h
    have := hz.pow_inj hkN h1N h6
    omega

theorem fixed_field_deg : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧
    (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧
    (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧
    (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0 := by
  intro l _ r hr
  let σ := sig l
  let F : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) := IntermediateField.fixedField (Subgroup.zpowers (σ ^ r))
  have hF : ∀ c, c ∈ F ↔ fr l r c = c := fun c => by
    rw [IntermediateField.mem_fixedField_iff, ← sig_pow]
    refine ⟨fun h => h _ (Subgroup.mem_zpowers _), fun h f hf => ?_⟩
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer _ c)).2 h hf
  have hst : ∀ c ∈ F, σ c ∈ F := fun c hc => by
    rw [hF, ← sig_pow] at hc ⊢
    rw [← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hc]
  let τ₀ : ↥F →ₐ[ℚ_[l]] ↥F := ((σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)).comp F.val).codRestrict F.toSubalgebra
    fun c => hst c c.2
  let τ : ↥F ≃ₐ[ℚ_[l]] ↥F := AlgEquiv.ofBijective τ₀ (Algebra.IsAlgebraic.algHom_bijective _)
  have hτ : ∀ (k : ℕ) (c : ↥F), (((τ ^ k) c : ↥F) : ↥(MaximalUnramifiedExtension l)) = fr l k c := fun k c => by
    rw [← sig_pow]
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← ih]; rfl
  have hrτ : τ ^ r = 1 := AlgEquiv.ext fun c => Subtype.ext ((hτ r c).trans ((hF c).1 c.2))
  have hord : orderOf τ = r := by
    rw [orderOf_eq_iff hr]
    refine ⟨hrτ, fun k hkr hk0 hk => ?_⟩
    obtain ⟨c, hc, hm⟩ := exists_moved l hk0 hkr
    have := hτ k ⟨c, (hF c).2 hc⟩
    rw [hk, AlgEquiv.one_apply] at this
    exact hm this.symm
  have hfin : IsOfFinOrder τ := isOfFinOrder_iff_pow_eq_one.2 ⟨r, hr, hrτ⟩
  haveI : Finite ↥(Subgroup.zpowers τ) := hfin.finite_zpowers
  have hbot : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [IntermediateField.mem_fixedField_iff] at hc
    have h1 := congrArg Subtype.val (hc τ (Subgroup.mem_zpowers _))
    have h2 := hτ 1 c
    rw [pow_one] at h2
    obtain ⟨x, hx⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c (h2.symm.trans h1)
    exact ⟨x, Subtype.ext hx⟩
  haveI h1 : FiniteDimensional ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F :=
    inferInstanceAs (FiniteDimensional ↥(FixedPoints.subfield (Subgroup.zpowers τ) ↥F) ↥F)
  haveI h2 : FiniteDimensional ℚ_[l] ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) := by
    rw [hbot]; infer_instance
  haveI h3 : FiniteDimensional ℚ_[l] ↥F := Module.Finite.trans ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F
  have hdeg : Module.finrank ℚ_[l] ↥F = r := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers τ)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.trans hord
  let bas : Module.Basis (Fin r) ℚ_[l] ↥F := Module.finBasisOfFinrankEq ℚ_[l] ↥F hdeg
  refine ⟨⟨F.map (MaximalUnramifiedExtension l).val, (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finiteDimensional⟩, fun k => (bas k : ↥(MaximalUnramifiedExtension l)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact y.2
  · show Module.finrank ℚ_[l] ↥(F.map (MaximalUnramifiedExtension l).val) = r
    rw [← (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finrank_eq]
    exact hdeg
  · intro c
    show _ ↔ (c : Om l) ∈ F.map (MaximalUnramifiedExtension l).val
    rw [IntermediateField.mem_map, ← hF]
    refine ⟨fun h => ⟨c, h, rfl⟩, ?_⟩
    rintro ⟨y, hy, hyc⟩
    rwa [← Subtype.ext hyc]
  · intro k
    exact (hF _).1 (bas k).2
  · exact bas.linearIndependent.map' F.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · intro c hc
    refine ⟨bas.repr ⟨c, (hF c).2 hc⟩, ?_⟩
    have e := congrArg (F.val.toLinearMap) (bas.sum_repr ⟨c, (hF c).2 hc⟩)
    rw [map_sum] at e
    simpa using e.symm
  · intro h0
    let M : Matrix (Fin r) (Fin r) ↥F := Matrix.of fun i j : Fin r => (τ ^ (j : ℕ)) (bas i)
    have e : (Matrix.of fun m k : Fin r => fr l m (bas k : ↥(MaximalUnramifiedExtension l))) = (F.val.mapMatrix M).transpose := by
      refine Matrix.ext fun m k => ?_
      simp only [M, Matrix.of_apply, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
      exact (hτ m (bas k)).symm
    rw [e, Matrix.det_transpose, ← AlgHom.map_det] at h0
    exact det_pow_ne_zero τ hord bas (Subtype.ext h0)

end GlobalTheory.PMon.UnrDeg
