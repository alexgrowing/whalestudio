import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Matrix
open scoped TensorProduct NNReal ENNReal Pointwise Kronecker

namespace GlobalTheory.GaugeEx.ModDet

theorem induction_pi {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] {K : ι → Type}
    [∀ k, Field (K k)] (e : S ≃+* ∀ k, K k) {κ : Type} [Fintype κ] [DecidableEq κ]
    (P : Matrix κ κ S → Prop) (hd : ∀ d : κ → S, (∀ i, IsUnit (d i)) → P (diagonal d))
    (ht : ∀ (i j : κ) (c : S), i ≠ j → P (transvection i j c))
    (hm : ∀ A B, P A → P B → P (A * B)) (g : Matrix κ κ S) (hg : IsUnit g.det) : P g := by
  let E : Matrix κ κ S ≃+* ∀ k, Matrix κ κ (K k) := e.mapMatrix.trans Matrix.piRingEquiv
  have hE : ∀ A k i j, E A k i j = e (A i j) k := fun _ _ _ _ => rfl
  have h1 : ∀ k (A : Matrix κ κ (K k)), A.det ≠ 0 → P (E.symm (Pi.mulSingle k A)) := by
    intro k A hA
    apply diagonal_transvection_induction_of_det_ne_zero
      (fun A => P (E.symm (Pi.mulSingle k A))) A hA
    · intro D hD
      rw [det_diagonal] at hD
      have : E.symm (Pi.mulSingle k (diagonal D)) =
          diagonal fun i => e.symm (Pi.mulSingle k (D i)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        · by_cases hij : i = j
          · subst hij; simp [hk]
          · simp [hij, hk]
      rw [this]
      refine hd _ fun i => ?_
      have : IsUnit (D i) := (Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)).isUnit
      exact (this.map (MonoidHom.mulSingle K k)).map e.symm
    · intro t
      obtain ⟨a, b, hab, c⟩ := t
      have : E.symm (Pi.mulSingle k (transvection a b c)) =
          transvection a b (e.symm (Pi.single k c)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply]
        · simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply, hk]
      rw [TransvectionStruct.toMatrix_mk, this]
      exact ht _ _ _ hab
    · intro A B _ _ hA hB
      rw [Pi.mulSingle_mul, map_mul]
      exact hm _ _ hA hB
  have hdet : ∀ k, (E g k).det ≠ 0 := by
    intro k
    have : E g k = ((Pi.evalRingHom K k).comp e.toRingHom).mapMatrix g := rfl
    rw [this, ← RingHom.map_det]
    exact (hg.map _).ne_zero
  have h2 : ∀ s : Finset ι, P (E.symm fun k => if k ∈ s then E g k else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun k => if k ∈ (∅ : Finset ι) then E g k else 1) = 1 := by funext k; simp
      rw [this, map_one, ← diagonal_one]
      exact hd _ fun _ => isUnit_one
    | insert a s ha ih =>
      have : (fun k => if k ∈ insert a s then E g k else 1) =
          Pi.mulSingle a (E g a) * fun k => if k ∈ s then E g k else 1 := by
        funext k
        by_cases hk : k = a
        · subst hk; simp [ha]
        · simp [hk]
      rw [this, map_mul]
      exact hm _ _ (h1 a _ (hdet a)) ih
  simpa using h2 Finset.univ

section

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]

theorem modu_coe (u : Sˣ) : modu S u = distribHaarChar S u := by
  simp [modu]

theorem modu_mul {a b : S} (ha : IsUnit a) (hb : IsUnit b) : modu S (a * b) = modu S a * modu S b := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  rw [← Units.val_mul, modu_coe, modu_coe, modu_coe, map_mul]

theorem modu_pow {a : S} (ha : IsUnit a) (n : ℕ) : modu S (a ^ n) = modu S a ^ n := by
  obtain ⟨a, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, modu_coe, modu_coe, map_pow]

variable [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]

theorem smul_map_mulVec_pi [IsArtinianRing S] [IsReduced S] (ν : Measure S) [ν.IsAddHaarMeasure]
    {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ S) (hM : IsUnit M.det) :
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν := by
  classical
  have hm : ∀ A : Matrix κ κ S, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  letI := Fintype.ofFinite (MaximalSpectrum S)
  letI : ∀ m : MaximalSpectrum S, Field (S ⧸ m.asIdeal) := fun m =>
    haveI := m.isMaximal
    Ideal.Quotient.field m.asIdeal
  refine (induction_pi (IsArtinianRing.equivPi S).toRingEquiv (fun M : Matrix κ κ S => IsUnit M.det ∧
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν) ?_ ?_ ?_ M hM).2
  · intro D A
    have hu' : (diagonal D).det = ((∏ i, (A i).unit : Sˣ) : S) := by simp
    refine ⟨hu' ▸ Units.isUnit _, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => ((A i).unit)⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := (A i).unit)).symm
    rw [this, Measure.pi_pi, hu', modu_coe, map_prod, ENNReal.coe_finset_prod, smul_eq_mul,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro a b c hab
    rw [det_transvection_of_ne _ _ hab]
    refine ⟨isUnit_one, ?_⟩
    rw [← Units.val_one, modu_coe, map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    simp [transvection, add_mulVec, single_mulVec, hab.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x a xᵢ)]
  · rintro A B ⟨hA, IHA⟩ ⟨hB, IHB⟩
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [det_mul]
    refine ⟨hA.mul hB, ?_⟩
    rw [modu_mul hA hB, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _),
      ← Measure.map_smul, IHB, IHA]

end

theorem tupMeas_eq_map {S : Type} [MeasurableSpace S] (lam : Measure S) [SigmaFinite lam] (n M : ℕ) :
    tupMeas lam n M = (Measure.pi fun _ : Fin n × Fin M => lam).map Function.curry := by
  have hu : Measurable (Function.uncurry : (Fin n → Fin M → S) → Fin n × Fin M → S) :=
    measurable_pi_lambda _ fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hc : Measurable (Function.curry : (Fin n × Fin M → S) → Fin n → Fin M → S) :=
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i => measurable_pi_apply (a, i)
  have : (Measure.pi fun _ : Fin n × Fin M => lam) = (tupMeas lam n M).map Function.uncurry := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hu (MeasurableSet.univ_pi hs)]
    have : (Function.uncurry ⁻¹' Set.pi Set.univ s : Set (Fin n → Fin M → S)) =
        Set.pi Set.univ fun a => Set.pi Set.univ fun i => s (a, i) := by
      ext X
      simp [Function.uncurry]
    rw [this, tupMeas, Measure.pi_pi, Fintype.prod_prod_type]
    simp_rw [Measure.pi_pi]
  rw [this, Measure.map_map hc hu]
  exact Measure.map_id.symm

theorem tupMeas_lrAct : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], IsArtinianRing S → IsReduced S → ∀ (lam : Measure S), lam.IsAddHaarMeasure → ∀ (n M : ℕ) (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S), IsUnit g.det → IsUnit γ.det → tupMeas lam n M = (modu S g.det ^ n * modu S γ.det ^ M) • (tupMeas lam n M).map (lrAct g γ) := by
  intro S _ _ _ _ _ _ _ _ _ _ lam _ n M g γ hg hγ
  have hc : Measurable (Function.curry : (Fin n × Fin M → S) → Fin n → Fin M → S) :=
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i => measurable_pi_apply (a, i)
  have hl : Measurable (lrAct g γ) := by
    refine Continuous.measurable (continuous_pi fun a => continuous_const.matrix_mulVec ?_)
    fun_prop
  have hdet : (γᵀ ⊗ₖ g).det = γ.det ^ M * g.det ^ n := by simp [det_kronecker]
  have key := smul_map_mulVec_pi lam (γᵀ ⊗ₖ g) (hdet ▸ (hγ.pow M).mul (hg.pow n))
  rw [hdet, modu_mul (hγ.pow M) (hg.pow n), modu_pow hγ, modu_pow hg, mul_comm] at key
  have hcomm : lrAct g γ ∘ Function.curry = Function.curry ∘ (γᵀ ⊗ₖ g).mulVec := by
    funext X a i
    simp only [Function.comp, lrAct, Function.curry, mulVec, dotProduct, Fintype.sum_prod_type,
      kroneckerMap_apply, transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hm : Measurable (γᵀ ⊗ₖ g).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [tupMeas_eq_map, Measure.map_map hl hc, hcomm, ← Measure.map_map hc hm, ← Measure.map_smul]
  exact congrArg _ key.symm

end GlobalTheory.GaugeEx.ModDet

end
