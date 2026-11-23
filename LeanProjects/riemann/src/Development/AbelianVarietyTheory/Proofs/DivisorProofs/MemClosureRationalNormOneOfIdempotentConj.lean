import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtInvS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLocAdele
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.Unconj

section Top

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}

theorem continuous_re : Continuous (fun x : ℍ[R, a, b] => x.re) :=
  (continuous_apply 0).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) :=
  (continuous_apply 1).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) :=
  (continuous_apply 2).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) :=
  (continuous_apply 3).comp (continuous_induced_dom (f := (coords : ℍ[R, a, b] → Fin 4 → R)))

theorem continuous_of_coords {X : Type*} [TopologicalSpace X] {f : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (f x).re) (h1 : Continuous fun x => (f x).imI)
    (h2 : Continuous fun x => (f x).imJ) (h3 : Continuous fun x => (f x).imK) : Continuous f := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

attribute [local fun_prop] continuous_re continuous_imI continuous_imJ continuous_imK

scoped instance : ContinuousMul ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_mul]; fun_prop) (by simp only [QuaternionAlgebra.imJ_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_mul]; fun_prop)⟩

scoped instance : ContinuousAdd ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_add]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_add]; fun_prop) (by simp only [QuaternionAlgebra.imJ_add]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_add]; fun_prop)⟩

scoped instance : ContinuousNeg ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_neg]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_neg]; fun_prop) (by simp only [QuaternionAlgebra.imJ_neg]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_neg]; fun_prop)⟩

scoped instance : IsTopologicalRing ℍ[R, a, b] := {}

scoped instance : ContinuousSMul R ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_smul, smul_eq_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_smul, smul_eq_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imJ_smul, smul_eq_mul]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_smul, smul_eq_mul]; fun_prop)⟩

scoped instance : ContinuousStar ℍ[R, a, b] :=
  ⟨continuous_of_coords (by simp only [QuaternionAlgebra.re_star]; fun_prop)
    (by simp only [QuaternionAlgebra.imI_star]; fun_prop) (by simp only [QuaternionAlgebra.imJ_star]; fun_prop)
    (by simp only [QuaternionAlgebra.imK_star]; fun_prop)⟩

theorem continuous_nrm : Continuous (fun x : ℍ[R, a, b] => nrm x) := by
  unfold nrm; fun_prop

end Top

end GlobalTheory.QSA.Unconj

noncomputable section

namespace GlobalTheory.QSA.Unconj

variable {F : Type} [Field F] [NumberField F]

theorem isPlacesIdem_mul_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {η : AF F}
    (hη : IsPlacesIdem S₁ S₂ η) : η * η = η := by
  have h1 : fstA F (η * η) = fstA F η := by
    rw [map_mul]
    funext w
    change fstA F η w * fstA F η w = fstA F η w
    by_cases hw : w ∈ S₁
    · rw [hη.1 w hw, one_mul]
    · rw [hη.2.1 w hw, zero_mul]
  have h2 : sndA F (η * η) = sndA F η := by
    refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV F u (sndA F (η * η)) = evalV F u (sndA F η)
    rw [map_mul, map_mul]
    by_cases hu : u ∈ S₂
    · rw [hη.2.2.1 u hu, one_mul]
    · rw [hη.2.2.2 u hu, zero_mul]
  exact Prod.ext h1 h2

theorem rat_mul {a b : F} (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat] <;> ring

theorem rat_one {a b : F} : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem rat_star {a b : F} (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem rat_smul {a b : F} (t : F) (x : ℍ[F, a, b]) : rat (t • x) = algebraMap F (AF F) t • rat x := by
  ext <;> simp [rat, Algebra.smul_def]

theorem nrm_smul {R : Type*} [CommRing R] {a b : R} (s : R) (x : ℍ[R, a, b]) : nrm (s • x) = s ^ 2 * nrm x := by
  simp only [nrm, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  ring

theorem star_smul' {R : Type*} [CommRing R] {a b : R} (s : R) (x : ℍ[R, a, b]) : star (s • x) = s • star x := by
  ext <;> simp <;> ring

end GlobalTheory.QSA.Unconj

namespace GlobalTheory.QSA.Unconj
theorem conj_core {R : Type*} [CommRing R] {a b : R} (η s : R) (hηη : η * η = η) (X c c' h : ℍ[R, a, b])
    (hh : η • h = h) :
    (η • X) * c * h * (c' * ((η * s) • star (η • X))) = X * (c * h * c') * (s • star X) := by
  conv_rhs => rw [← hh]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, star_smul', mul_assoc]
  rw [hηη, mul_left_comm, hηη]
end GlobalTheory.QSA.Unconj

namespace GlobalTheory.QSA.Unconj

theorem conj_mem_closure_normOne_of_idempotent : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η →
    ∀ ε : AF F, ε * ε = ε → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → ∀ c c' : DA F a b, c * c' = 1 →
    c' * c = 1 → c * g * c' ∈ closure (H0 (a := a) (b := b) ε) → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b _ _ T₁ T₂ η hη ε hε g _ hgη c c' hcc' hc'c hx
  have hηη := isPlacesIdem_mul_self hη
  obtain ⟨-, -, hconj, -⟩ := GlobalTheory.T.closure_normOneProducts_h0_properties F a b ε hε
  by_cases hη0 : η = 0
  · have hg1 : g = 1 := by
      rw [hη0, zero_smul] at hgη
      exact (sub_eq_zero.1 hgη.symm)
    rw [hg1]
    exact subset_closure (one_mem_H0_weight_zero ε)
  rw [← closure_closure (s := H0 (a := a) (b := b) ε), mem_closure_iff_nhds]
  intro W hW
  have hnn : nrm c' * nrm c = 1 := by
    rw [← nrm_mul, hc'c]
    simp [nrm]
  have hcstar : nrm c • star c' = c := by
    have h1 : star c' = nrm c' • c := by
      calc star c' = c * (c' * star c') := by rw [← mul_assoc, hcc', one_mul]
        _ = nrm c' • c := by rw [mul_star_eq, Algebra.algebraMap_eq_smul_one (nrm c'), mul_smul_comm, mul_one]
    rw [h1, smul_smul, mul_comm, hnn, one_smul]
  let u : (AF F)ˣ := ⟨nrm c', nrm c, hnn, by rw [mul_comm]; exact hnn⟩
  let Ξ : DA F a b × AF F → DA F a b := fun p => 1 + (p.1 * c) * (g - 1) * (c' * (p.2 • star p.1))
  have hΞc : Continuous Ξ :=
    continuous_const.add (((continuous_fst.mul continuous_const).mul continuous_const).mul
      (continuous_const.mul (continuous_snd.smul (continuous_star.comp continuous_fst))))
  have hΞ0 : Ξ (η • c', η * nrm c) = g := by
    have e1 : (η • c') * c = η • 1 := by rw [smul_mul_assoc, hc'c]
    have e2 : c' * ((η * nrm c) • star (η • c')) = η • 1 := by
      have hs : η * nrm c * η = η * nrm c := by linear_combination (nrm c) * hηη
      rw [star_smul', smul_smul, hs, ← smul_smul, hcstar, mul_smul_comm, hc'c]
    have e3 : (η • (1 : DA F a b)) * (g - 1) * (η • 1) = g - 1 := by
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hgη]
    show 1 + ((η • c') * c) * (g - 1) * (c' * ((η * nrm c) • star (η • c'))) = g
    rw [e1, e2, e3]
    abel
  have hW' : Ξ ⁻¹' W ∈ 𝓝 (η • c', η * nrm c) :=
    hΞc.continuousAt.preimage_mem_nhds (by rw [hΞ0]; exact hW)
  obtain ⟨N1, hN1, N2, hN2, hN12⟩ := mem_nhds_prod_iff.1 hW'
  obtain ⟨V, hV, hVt⟩ := GlobalTheory.InvIdem.inv_cont F T₁ T₂ η hη u N2 hN2
  have hN3 : (fun X : DA F a b => nrm X) ⁻¹' V ∈ 𝓝 (η • c') :=
    continuous_nrm.continuousAt.preimage_mem_nhds (by rw [nrm_smul, pow_two, hηη]; exact hV)
  let e : (Fin 4 → AF F) → DA F a b := fun v => η • c' - ⟨v 0, v 1, v 2, v 3⟩
  have hec : Continuous e := by
    refine continuous_const.sub (continuous_of_coords ?_ ?_ ?_ ?_) <;> exact continuous_apply _
  have hN : e ⁻¹' (N1 ∩ (fun X : DA F a b => nrm X) ⁻¹' V) ∈ 𝓝 (0 : Fin 4 → AF F) := by
    refine hec.continuousAt.preimage_mem_nhds ?_
    have : e 0 = η • c' := by
      show η • c' - ⟨0, 0, 0, 0⟩ = η • c'
      rw [show (⟨0, 0, 0, 0⟩ : DA F a b) = 0 from rfl, sub_zero]
    rw [this]
    exact Filter.inter_mem hN1 hN3
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hU : (⋂ i, t i) ∈ 𝓝 (0 : AF F) := Filter.iInter_mem.2 ht
  choose q hq using fun i : Fin 4 => GlobalTheory.PlaceApprox.weak_approx_idem F T₁ T₂ η hη (coords c' i) (⋂ i, t i) hU
  let δ : ℍ[F, a, b] := ⟨q 0, q 1, q 2, q 3⟩
  have hδe : η • rat δ = e (fun i => η * (coords c' i - algebraMap F (AF F) (q i))) := by
    ext <;> simp [e, δ, rat, coords] <;> ring
  have hδN : η • rat δ ∈ N1 ∩ (fun X : DA F a b => nrm X) ⁻¹' V := by
    rw [hδe]
    exact hIt (show (fun i => η * (coords c' i - algebraMap F (AF F) (q i))) ∈ (I.pi t) from
      fun i _ => Set.mem_iInter.1 (hq i) i)
  have hnδ : η * algebraMap F (AF F) (nrm δ) ∈ V := by
    have h := hδN.2
    simp only [Set.mem_preimage, nrm_smul, nrm_rat, pow_two, hηη] at h
    exact h
  obtain ⟨hn0, hn⟩ := hVt (nrm δ) hnδ
  have hn0 := hn0 hη0
  set δ' : ℍ[F, a, b] := (nrm δ)⁻¹ • star δ with hδ'
  have hδδ' : δ * δ' = 1 := by
    rw [hδ', mul_smul_comm, mul_star_eq, Algebra.algebraMap_eq_smul_one (nrm δ), smul_smul, inv_mul_cancel₀ hn0, one_smul]
  refine ⟨rat δ * (c * g * c') * rat δ', ?_, hconj δ δ' hδδ' _ hx⟩
  have hmem := hN12 (Set.mk_mem_prod hδN.1 hn)
  have hval : Ξ (η • rat δ, η * algebraMap F (AF F) (nrm δ)⁻¹) = rat δ * (c * g * c') * rat δ' := by
    have hcg : c * g * c' = 1 + c * (g - 1) * c' := by
      rw [mul_sub, sub_mul, mul_one, hcc']
      abel
    have hr : rat δ * (c * g * c') * rat δ' = 1 + rat δ * (c * (g - 1) * c') * rat δ' := by
      rw [hcg, mul_add, add_mul, mul_one, ← rat_mul, hδδ', rat_one]
    rw [hr]
    show 1 + ((η • rat δ) * c) * (g - 1) * (c' * ((η * algebraMap F (AF F) (nrm δ)⁻¹) • star (η • rat δ))) = _
    refine congrArg (fun z => 1 + z) ?_
    rw [hδ', rat_smul, rat_star]
    exact conj_core η _ hηη (rat δ) c c' (g - 1) hgη
  rw [← hval]
  exact hmem

end GlobalTheory.QSA.Unconj
