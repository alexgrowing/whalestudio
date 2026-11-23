import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighDecomp
import GroundTheory.ProfiniteCohomology.RestrictedRamification.HighProcyclic
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.LocalField
  GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)
  (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})

section Hom

variable {ℓ : ℕ} (hℓ : ℓ.Prime) (hS : ∀ w : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ w.asIdeal → w ∈ S)

theorem val_intCast_nsmul_eq_zsmul {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n] {c : A} (hc : n • c = 0)
    (k : ℤ) : ((k : ZMod n).val) • c = k • c := by
  have h1 : (((k : ZMod n).val : ℕ) : ℤ) = k % n := ZMod.val_intCast k
  rw [← natCast_zsmul, h1]
  conv_rhs => rw [← Int.emod_add_mul_ediv k n]
  rw [add_smul, mul_comm, mul_smul, natCast_zsmul, hc, smul_zero, add_zero]

theorem dvd_of_nsmul_mk_one_div_eq_zero {N m : ℕ} (hN : N ≠ 0) (h : m • QZ.mk (1 / (N : ℚ)) = 0) : N ∣ m := by
  have h2 : QZ.mk ((m : ℚ) * (1 / (N : ℚ))) = 0 := by
    have e := map_nsmul QZ.mkHom m (1 / (N : ℚ))
    rw [nsmul_eq_mul] at e
    exact e.trans h
  obtain ⟨n, hn⟩ := (QZ.mk_eq_zero_iff _).1 h2
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have e1 : (n : ℚ) * (N : ℚ) = m := by rw [hn]; field_simp
  have e2 : n * (N : ℤ) = m := by exact_mod_cast e1
  exact Int.natCast_dvd_natCast.1 ⟨n, by rw [← e2, mul_comm]⟩

theorem exists_localGaloisCohomology_order {ℓ : ℕ} (hℓ : ℓ.Prime) (w : HeightOneSpectrum (𝓞 K.1)) (b : ℕ) :
    ∃ t : localGaloisCohomology K 2 (.inr w), ℓ ^ b • t = 0 ∧ ∀ m : ℕ, m • t = 0 → ℓ ^ b ∣ m := by
  have hN : ℓ ^ b ≠ 0 := pow_ne_zero b hℓ.ne_zero
  obtain ⟨t, ht⟩ := (placeInv_bijective_inr (K := K) w).2 (QZ.mk (1 / ((ℓ ^ b : ℕ) : ℚ)))
  refine ⟨t, ?_, fun m hm => ?_⟩
  · apply (placeInv_bijective_inr (K := K) w).1
    rw [AddMonoidHom.map_nsmul, ht, AddMonoidHom.map_zero]
    exact QZ.nsmul_mk_one_div (ℓ ^ b)
  · refine dvd_of_nsmul_mk_one_div_eq_zero hN ?_
    rw [← ht, ← AddMonoidHom.map_nsmul, hm, AddMonoidHom.map_zero]

set_option maxHeartbeats 8000000 in
include hℓ hS in

theorem exists_char_order_gsDecomp (b : ℕ) :
    ∃ χ : Additive Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →ₜ+ QZ,
      ℓ ^ b • χ = 0 ∧ (∀ m : ℕ, m • χ = 0 → ℓ ^ b ∣ m) ∧
        ∀ h, gsDecomp K S ιs v h = 1 → χ (Additive.ofMul h) = 0 := by
  obtain ⟨t, htk, htm⟩ := exists_localGaloisCohomology_order K hℓ v.1 b
  obtain ⟨x, hxk, hxt, -⟩ := exists_gsLocalRes_eq_single K S ℓ hℓ hS ιs v.1 v.2 t b htk
  obtain ⟨x', hx'⟩ : ∃ x', cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2 x' = x :=
    ⟨_, AddEquiv.apply_symm_apply _ x⟩
  have hloc : gsLoc K S ιs v.1 x' = t := by
    change (gsLocalRes S (ιs.fin v.1) 2).hom
      ((cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) x') = t
    rw [hx']
    exact hxt
  refine ⟨gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) (gsVal K S ιs v.1 v.2 x'), ?_, fun m hm => ?_, fun h hh =>
    gvChar_decompHomS_eq_zero S (ιs.fin v.1) x' (ordEmbMor S (ιs.fin v.1) v.2) h hh⟩
  · have hx'k : ℓ ^ b • x' = 0 := by
      refine (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).injective ?_
      refine ((cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).toAddMonoidHom.map_nsmul
        _ _).trans ?_
      refine (congrArg (ℓ ^ b • ·) hx').trans ?_
      exact hxk.trans (AddEquiv.map_zero _).symm
    refine ((gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)).toAddMonoidHom.map_nsmul _ _).symm.trans ?_
    refine (congrArg (gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)) ((AddMonoidHom.map_nsmul _ _ _).symm.trans
      ((congrArg (gsVal K S ιs v.1 v.2) hx'k).trans (AddMonoidHom.map_zero _)))).trans ?_
    exact AddEquiv.map_zero _
  · apply htm m
    have h1 : gsVal K S ιs v.1 v.2 (m • x') = 0 := by
      refine (gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)).injective ?_
      refine (congrArg (gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)) (AddMonoidHom.map_nsmul _ _ _)).trans ?_
      refine ((gvChar Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)).toAddMonoidHom.map_nsmul _ _).trans ?_
      exact hm.trans (AddEquiv.map_zero _).symm
    have h2 := (gsLoc_eq_zero_iff K S ιs v.1 v.2 (m • x')).2 h1
    exact ((congrArg (m • ·) hloc).symm.trans (AddMonoidHom.map_nsmul (gsLoc K S ιs v.1) m x').symm).trans h2

set_option maxHeartbeats 4000000 in

theorem char_eq_proj_nsmul_of_gsDecomp {ℓ : ℕ} (hℓ : ℓ.Prime) (b : ℕ)
    (χ : Additive Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →ₜ+ QZ)
    (hχk : ℓ ^ b • χ = 0) (hB : ∀ h, gsDecomp K S ιs v h = 1 → χ (Additive.ofMul h) = 0)
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hσ : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (g : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1)) :
    χ (Additive.ofMul g) = (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) : ZMod (ℓ ^ b)).val •
          χ (Additive.ofMul σ) := by
  have hN : ℓ ^ b ≠ 0 := pow_ne_zero b hℓ.ne_zero
  have : NeZero (ℓ ^ b) := ⟨hN⟩
  obtain ⟨c, hcdef⟩ : ∃ c, χ (Additive.ofMul σ) = c := ⟨_, rfl⟩
  have hc : ℓ ^ b • c = 0 := by
    rw [← hcdef, ← ContinuousAddMonoidHom.nsmul_apply, hχk]
    rfl
  rw [hcdef]
  have hE := eq_univ_of_unramifiedDegree v.1 σ hσ
    {g | χ (Additive.ofMul g) = (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) : ZMod (ℓ ^ b)).val • c}
    (isClosed_eq (χ.continuous.comp continuous_ofMul)
      ((continuous_of_discreteTopology (f := fun z : ZMod (ℓ ^ b) => z.val • c)).comp
        ((ProfiniteInteger.continuous_proj _).comp (continuous_toAdd.comp continuous_unramifiedDegree))))
    (fun k => by
      show χ (Additive.ofMul (σ ^ k)) = _
      rw [ofMul_zpow, map_zsmul, hcdef, map_zpow, hσ, ← ofAdd_zsmul, toAdd_ofAdd, zsmul_one, map_intCast]
      exact (val_intCast_nsmul_eq_zsmul (n := ℓ ^ b) hc k).symm)
    (fun g hg h hh => by
      show χ (Additive.ofMul (g * h)) = _
      rw [ofMul_mul, map_add, hB h (gsDecomp_eq_one_of_unramifiedDegree_eq_one K S ιs v h hh), add_zero,
        map_mul, hh, mul_one]
      exact hg)
  have hg : g ∈ {g | χ (Additive.ofMul g) = (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) : ZMod (ℓ ^ b)).val • c} := by
    rw [hE]
    exact Set.mem_univ _
  exact hg

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem proj_unramifiedDegree_eq_zero_of_gsDecomp_eq_one (b : ℕ)
    (g : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hg : gsDecomp K S ιs v g = 1) :
    ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (unramifiedDegree
      (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_unramifiedDegree_eq_one (K := K) (v := v.1)
  obtain ⟨χ, hχk, hA, hB⟩ := exists_char_order_gsDecomp K S ιs v hℓ hS b
  have hC := char_eq_proj_nsmul_of_gsDecomp K S ιs v hℓ b χ hχk hB σ hσ
  obtain ⟨z, hz⟩ : ∃ z : ZMod (ℓ ^ b), ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩
      (Multiplicative.toAdd (unramifiedDegree
        (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) g)) = z := ⟨_, rfl⟩
  have hzc : z.val • χ (Additive.ofMul σ) = 0 := by
    have e := hC g
    rw [hz] at e
    exact e.symm.trans (hB g hg)
  have hzχ : z.val • χ = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    rw [ContinuousAddMonoidHom.nsmul_apply, ← ofMul_toMul y, hC, smul_comm, hzc, smul_zero]
    rfl
  have hdvd := hA z.val hzχ
  have : NeZero (ℓ ^ b) := ⟨pow_ne_zero b hℓ.ne_zero⟩
  have hlt : z.val < ℓ ^ b := ZMod.val_lt z
  have h0 : z.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  rw [hz]
  exact (ZMod.val_eq_zero z).1 h0

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem exists_hom_zmod_pow_rangeRestrict_gsDecomp
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1))
    (hσ : unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1) (b : ℕ) :
    ∃ φ : (gsDecomp K S ιs v).range →* Multiplicative (ZMod (ℓ ^ b)),
      IsOpen (φ.ker : Set (gsDecomp K S ιs v).range) ∧
        φ ((gsDecomp K S ιs v).rangeRestrict σ) = Multiplicative.ofAdd 1 := by
  set deg := unramifiedDegree (v.1.adicCompletion K.1) (AlgebraicClosure (v.1.adicCompletion K.1))
  let ψ : Gal(AlgebraicClosure (v.1.adicCompletion K.1)/v.1.adicCompletion K.1) →* Multiplicative (ZMod (ℓ ^ b)) :=
    (AddMonoidHom.toMultiplicative (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩).toAddMonoidHom).comp deg
  have hψ : ∀ g, ψ g = Multiplicative.ofAdd
      (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (deg g)) : ZMod (ℓ ^ b)) :=
    fun _ => rfl
  have hker : (gsDecomp K S ιs v).ker ≤ ψ.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [hψ, proj_unramifiedDegree_eq_zero_of_gsDecomp_eq_one K S ιs v hℓ hS b g hg, ofAdd_zero]
    rfl
  let φ : (gsDecomp K S ιs v).range →* Multiplicative (ZMod (ℓ ^ b)) :=
    (QuotientGroup.lift _ ψ hker).comp
      (QuotientGroup.quotientKerEquivRange (gsDecomp K S ιs v)).symm.toMonoidHom
  have hφ : ∀ g, φ ((gsDecomp K S ιs v).rangeRestrict g) = ψ g := fun g => by
    have e : (QuotientGroup.quotientKerEquivRange (gsDecomp K S ιs v)).symm
        ((gsDecomp K S ιs v).rangeRestrict g) = (g : _ ⧸ (gsDecomp K S ιs v).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift _ ψ hker ((QuotientGroup.quotientKerEquivRange (gsDecomp K S ιs v)).symm
      ((gsDecomp K S ιs v).rangeRestrict g)) = ψ g
    rw [e, QuotientGroup.lift_mk]
  refine ⟨φ, ?_, ?_⟩
  · rw [← (isQuotientMap_rangeRestrict_gsDecomp K S ιs v).isOpen_preimage]
    have e : (gsDecomp K S ιs v).rangeRestrict ⁻¹' (φ.ker : Set (gsDecomp K S ιs v).range) =
        (fun g => (ProfiniteInteger.proj ⟨ℓ ^ b, pow_pos hℓ.pos b⟩ (Multiplicative.toAdd (deg g)) : ZMod (ℓ ^ b))) ⁻¹' {0} := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, hφ, hψ, Set.mem_singleton_iff]
      exact Iff.rfl
    rw [e]
    exact (isOpen_discrete _).preimage
      ((ProfiniteInteger.continuous_proj _).comp (continuous_toAdd.comp continuous_unramifiedDegree))
  · rw [hφ, hψ, hσ, toAdd_ofAdd, map_one]
    rfl

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem exists_isPrimePowGenerator_gsDecomp :
    ∃ σ : (gsDecomp K S ιs v).range, IsPrimePowGenerator ℓ σ := by
  obtain ⟨σ, hσ⟩ := exists_unramifiedDegree_eq_one (K := K) (v := v.1)
  exact ⟨(gsDecomp K S ιs v).rangeRestrict σ,
    ⟨isTopologicalGenerator_rangeRestrict_gsDecomp K S ιs v σ hσ,
      fun b => exists_hom_zmod_pow_rangeRestrict_gsDecomp K S ιs v hℓ hS σ hσ b⟩⟩

instance isDiscreteRep_res_range_gsDecomp :
    IsDiscreteRep (Rep.res (gsDecomp K S ιs v).range.subtype (trivRep (galUnramifiedOutside K.1 ℚ̄ S) QZ)) :=
  isDiscreteRep_res_subtype _ _

instance totallyDisconnectedSpace_range_gsDecomp : TotallyDisconnectedSpace (gsDecomp K S ιs v).range :=
  have := galUnramifiedOutside_isProfinite (F := K.1) (Ω := ℚ̄) S
  inferInstance

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem eq_zero_of_pow_nsmul_cohomology_range_gsDecomp {p : ℕ} (hp : 2 ≤ p)
    (x : cohomology (Rep.res (gsDecomp K S ιs v).range.subtype
      (trivRep (galUnramifiedOutside K.1 ℚ̄ S) QZ)) p) (k : ℕ) (hx : ℓ ^ k • x = 0) : x = 0 := by
  obtain ⟨σ, hσ⟩ := exists_isPrimePowGenerator_gsDecomp K S ιs v hℓ hS
  exact hσ.eq_zero_of_pow_nsmul hℓ _ isAddTorsion_QZ hp x hx

end Hom

end

end GroundTheory.ProfCoh
