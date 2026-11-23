import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaB
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

namespace UpperTheory.LocIdx

open GroundTheory.Heights₂.Heights.LatticeLemmas

section
variable {E V : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} [AddCommGroup V]
  [Module (P.adicCompletion E) V] [Module (P.adicCompletionIntegers E) V]
  [IsScalarTower (P.adicCompletionIntegers E) (P.adicCompletion E) V]

private theorem one_lt_norm (P : HeightOneSpectrum (𝓞 E)) : 1 < Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

private theorem norm_eq_zpow {x : P.adicCompletion E} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm P.asIdeal : ℝ) ^ (Valued.v x).log := by
  rw [← GroundTheory.Global.normalizedAbv_apply]
  exact GroundTheory.Global.normalizedAbv_eq_zpow P hx

private theorem exists_basis (A : Submodule (P.adicCompletionIntegers E) V) (hfg : A.FG)
    (hsp : Submodule.span (P.adicCompletion E) (A : Set V) = ⊤) :
    ∃ (m : ℕ) (c : Module.Basis (Fin m) (P.adicCompletion E) V),
      Submodule.span (P.adicCompletionIntegers E) (Set.range c) = A := by
  haveI : Module.Finite (P.adicCompletionIntegers E) A := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree (P.adicCompletionIntegers E) A := LocalLatticeIndex.isTorsionFree A
  haveI : Module.Free (P.adicCompletionIntegers E) A := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis (P.adicCompletionIntegers E) A
  have hli : LinearIndependent (P.adicCompletionIntegers E) (A.subtype ∘ b) :=
    b.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hliK : LinearIndependent (P.adicCompletion E) (A.subtype ∘ b) :=
    hli.localization (P.adicCompletion E) (nonZeroDivisors (P.adicCompletionIntegers E))
  have hspO : Submodule.span (P.adicCompletionIntegers E) (Set.range (A.subtype ∘ b)) = A := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span (P.adicCompletion E) (Set.range (A.subtype ∘ b)) := by
    rw [← hsp]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← hspO] at hx
    exact Submodule.span_le_restrictScalars (P.adicCompletionIntegers E) (P.adicCompletion E) _ hx
  refine ⟨_, Module.Basis.mk hliK hspK, ?_⟩
  rw [Module.Basis.coe_mk]
  exact hspO

private theorem relIndex_eq_inv_norm_det_basis_change {m : ℕ} (a c : Module.Basis (Fin m) (P.adicCompletion E) V)
    (A B : Submodule (P.adicCompletionIntegers E) V)
    (ha : Submodule.span (P.adicCompletionIntegers E) (Set.range a) = A)
    (hc : Submodule.span (P.adicCompletionIntegers E) (Set.range c) = B) (hBA : B ≤ A) :
    (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ‖LinearMap.det ((a.equiv c (Equiv.refl _)).toLinearMap)‖⁻¹ := by
  have hAfg : A.FG := ha ▸ Submodule.fg_span (Set.finite_range a)
  have hAsp : Submodule.span (P.adicCompletion E) (A : Set V) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← a.span_eq]
    apply Submodule.span_mono
    rw [← ha]
    exact Submodule.subset_span
  have himg : (B : Set V) = (a.equiv c (Equiv.refl _)) '' (A : Set V) := by
    have key : (Submodule.span (P.adicCompletionIntegers E) (Set.range a)).map
        ((a.equiv c (Equiv.refl _)).toLinearMap.restrictScalars (P.adicCompletionIntegers E)) = B := by
      rw [← Submodule.span_image, ← Set.range_comp, ← hc]
      congr 2
      funext i
      simp
    rw [← key, ha, Submodule.map_coe]
    rfl
  exact LocalLatticeIndex.index_eq_det A B _ hAfg hAsp himg hBA

private theorem exists_nat_pow_eq_of_real_eq_zpow_absNorm (r : ℕ) (k : ℤ) (h : (r : ℝ) = (Ideal.absNorm P.asIdeal : ℝ) ^ k) :
    ∃ n : ℕ, r = Ideal.absNorm P.asIdeal ^ n := by
  have hN : (1 : ℝ) < Ideal.absNorm P.asIdeal := by exact_mod_cast one_lt_norm P
  have hpos : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℝ) ^ k := zpow_pos (by linarith) k
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, Nat.cast_zero] at h
      linarith
    · exact h0
  have hk : 0 ≤ k := by
    have h1 : (1 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ k := by
      rw [← h]
      exact_mod_cast hr
    exact (one_le_zpow_iff_right₀ hN).mp h1
  refine ⟨k.toNat, ?_⟩
  have h2 : (r : ℝ) = ((Ideal.absNorm P.asIdeal ^ k.toNat : ℕ) : ℝ) := by
    rw [h, Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg hk]
  exact_mod_cast h2

private theorem relIndex_pow (A B : Submodule (P.adicCompletionIntegers E) V) (hA : A.FG)
    (hsA : Submodule.span (P.adicCompletion E) (A : Set V) = ⊤) (hB : B.FG)
    (hsB : Submodule.span (P.adicCompletion E) (B : Set V) = ⊤) (hBA : B ≤ A) :
    ∃ n : ℕ, B.toAddSubgroup.relIndex A.toAddSubgroup = Ideal.absNorm P.asIdeal ^ n := by
  obtain ⟨m, a, ha⟩ := exists_basis A hA hsA
  obtain ⟨m', c, hc⟩ := exists_basis B hB hsB
  have hm : m' = m := by
    have h1 := Module.finrank_eq_card_basis a
    have h2 := Module.finrank_eq_card_basis c
    simp only [Fintype.card_fin] at h1 h2
    omega
  subst hm
  have h := relIndex_eq_inv_norm_det_basis_change a c A B ha hc hBA
  have hdet : LinearMap.det ((a.equiv c (Equiv.refl _)).toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  rw [norm_eq_zpow hdet, ← _root_.zpow_neg] at h
  exact exists_nat_pow_eq_of_real_eq_zpow_absNorm _ _ h

private theorem main (L : Submodule (P.adicCompletionIntegers E) V)
    (T : V →ₗ[P.adicCompletion E] V) (hfg : L.FG)
    (hsp : Submodule.span (P.adicCompletion E) (L : Set V) = ⊤) (hinj : Function.Injective T) :
    ∃ i j : ℕ, idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) =
        Ideal.absNorm P.asIdeal ^ i ∧
      idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L =
        Ideal.absNorm P.asIdeal ^ j ∧
      Valued.v (LinearMap.det T) = WithZero.exp ((i : ℤ) - j) := by
  obtain ⟨m, a, ha⟩ := exists_basis L hfg hsp
  haveI : FiniteDimensional (P.adicCompletion E) V := Module.Finite.of_basis a
  let Te : V ≃ₗ[(P.adicCompletion E)] V := LinearEquiv.ofInjectiveEndo T hinj
  have hTe : (Te : V →ₗ[(P.adicCompletion E)] V) = T := LinearMap.ext fun x => rfl
  let t := a.map Te
  set TL := L.map (T.restrictScalars (P.adicCompletionIntegers E)) with hTLdef
  have ht : Submodule.span (P.adicCompletionIntegers E) (Set.range t) = TL := by
    rw [hTLdef, ← ha, Submodule.map_span, ← Set.range_comp]
    congr 2
  have hTLfg : TL.FG := hfg.map _
  have hTLsp : Submodule.span (P.adicCompletion E) (TL : Set V) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← t.span_eq]
    apply Submodule.span_mono
    rw [← ht]
    exact Submodule.subset_span
  set M := L ⊓ TL with hMdef
  have hMle1 : M ≤ L := inf_le_left
  have hMle2 : M ≤ TL := inf_le_right
  have hMfg : M.FG := by
    haveI : IsNoetherian (P.adicCompletionIntegers E) L := isNoetherian_of_fg_of_noetherian L hfg
    have hM : M = (TL.comap L.subtype).map L.subtype := by
      rw [Submodule.map_comap_subtype]
    rw [hM]
    exact (IsNoetherian.noetherian _).map _
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (P.adicCompletionIntegers E))
    (Finset.univ : Finset (Fin m × Fin m)) (fun ij => t.repr (a ij.1) ij.2)
  have hai : ∀ i, a i ∈ L := by
    intro i
    rw [← ha]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbai : ∀ i, (b : (P.adicCompletionIntegers E)) • a i ∈ TL := by
    intro i
    rw [← ht]
    rw [← t.sum_repr (a i), Finset.smul_sum]
    apply Submodule.sum_mem
    intro j _
    obtain ⟨y, hy⟩ := hb (i, j) (Finset.mem_univ _)
    rw [← smul_assoc]
    simp only at hy
    rw [← hy, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hbM : ∀ i, (b : (P.adicCompletionIntegers E)) • a i ∈ M := fun i => ⟨L.smul_mem _ (hai i), hbai i⟩
  have hbne : algebraMap (P.adicCompletionIntegers E) (P.adicCompletion E) (b : (P.adicCompletionIntegers E)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hMsp : Submodule.span (P.adicCompletion E) (M : Set V) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← a.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have e : a i = (algebraMap (P.adicCompletionIntegers E) (P.adicCompletion E) (b : (P.adicCompletionIntegers E)))⁻¹ • ((b : (P.adicCompletionIntegers E)) • a i) := by
      rw [← algebraMap_smul (P.adicCompletion E) (b : (P.adicCompletionIntegers E)) (a i), smul_smul, inv_mul_cancel₀ hbne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hbM i))
  obtain ⟨m', c, hc⟩ := exists_basis M hMfg hMsp
  have hm : m' = m := by
    have h1 := Module.finrank_eq_card_basis a
    have h2 := Module.finrank_eq_card_basis c
    simp only [Fintype.card_fin] at h1 h2
    omega
  subst hm
  have h1 := relIndex_eq_inv_norm_det_basis_change a c L M ha hc hMle1
  have h2 := relIndex_eq_inv_norm_det_basis_change t c TL M ht hc hMle2
  have e1 : idx L TL = M.toAddSubgroup.relIndex TL.toAddSubgroup := by
    unfold idx
    rw [hMdef]
    exact (AddSubgroup.inf_relIndex_right L.toAddSubgroup TL.toAddSubgroup).symm
  have e2 : idx TL L = M.toAddSubgroup.relIndex L.toAddSubgroup := by
    unfold idx
    rw [hMdef]
    exact (AddSubgroup.inf_relIndex_left L.toAddSubgroup TL.toAddSubgroup).symm
  obtain ⟨i, hi⟩ := relIndex_pow TL M hTLfg hTLsp hMfg hMsp hMle2
  obtain ⟨j, hj⟩ := relIndex_pow L M hfg hsp hMfg hMsp hMle1
  refine ⟨i, j, by rw [e1]; exact hi, by rw [e2]; exact hj, ?_⟩
  have hcomp : ((t.equiv c (Equiv.refl _)).toLinearMap).comp T =
      (a.equiv c (Equiv.refl _)).toLinearMap := by
    apply a.ext
    intro k
    have hk : T (a k) = t k := by
      show T (a k) = (a.map Te) k
      rw [Module.Basis.map_apply]
      rfl
    show (t.equiv c (Equiv.refl _)) (T (a k)) = (a.equiv c (Equiv.refl _)) (a k)
    rw [hk]
    simp
  have hdT : LinearMap.det T ≠ 0 := by
    rw [← hTe]
    exact (LinearEquiv.isUnit_det' Te).ne_zero
  have hd2 : LinearMap.det ((t.equiv c (Equiv.refl _)).toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have hN : (1 : ℝ) < Ideal.absNorm P.asIdeal := by exact_mod_cast one_lt_norm P
  have hnorm : ‖LinearMap.det T‖ = (Ideal.absNorm P.asIdeal : ℝ) ^ ((i : ℤ) - j) := by
    have n1 : ‖LinearMap.det ((a.equiv c (Equiv.refl _)).toLinearMap)‖ =
        ‖LinearMap.det ((t.equiv c (Equiv.refl _)).toLinearMap)‖ * ‖LinearMap.det T‖ := by
      rw [← hcomp, LinearMap.det_comp, norm_mul]
    rw [hj] at h1
    rw [hi] at h2
    push_cast at h1 h2
    have p2 : ‖LinearMap.det ((t.equiv c (Equiv.refl _)).toLinearMap)‖ ≠ 0 := norm_ne_zero_iff.mpr hd2
    rw [zpow_sub₀ (by positivity), zpow_natCast, zpow_natCast, h1, h2, n1]
    field_simp
  rw [norm_eq_zpow hdT] at hnorm
  have hlog := zpow_right_injective₀ (by linarith : (0 : ℝ) < Ideal.absNorm P.asIdeal) (ne_of_gt hN) hnorm
  rw [← hlog, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hdT)]

end
end UpperTheory.LocIdx

theorem UpperTheory.exists_lattice_index_of_injective_endomorphism :
    ∀ {E V : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) [AddCommGroup V]
        [Module (P.adicCompletion E) V] [Module (P.adicCompletionIntegers E) V]
        [IsScalarTower (P.adicCompletionIntegers E) (P.adicCompletion E) V]
        (L : Submodule (P.adicCompletionIntegers E) V) (T : V →ₗ[P.adicCompletion E] V),
        L.FG → Submodule.span (P.adicCompletion E) (L : Set V) = ⊤ → Function.Injective T →
        ∃ i j : ℕ, idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) = Ideal.absNorm P.asIdeal ^ i ∧
          idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L = Ideal.absNorm P.asIdeal ^ j ∧
          Valued.v (LinearMap.det T) = WithZero.exp ((i : ℤ) - j) := by
  intro E V _ _ P _ _ _ _ L T hfg hsp hinj
  exact UpperTheory.LocIdx.main L T hfg hsp hinj
