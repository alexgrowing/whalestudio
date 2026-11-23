import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie.BallDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sum

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} {iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]} {b : Bool}
  (j : Fin D.R.m)

theorem valC_cuspOf_sum (z : FrC YS iC b ((j : ℕ) + 1)) {ι : Type} (s : Finset ι) (g : ι → NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (∑ t ∈ s, g t) : T0.R ((j : ℕ) + 1)) =
      ∑ t ∈ s, valC z (cuspOf YS fw j (g t) : T0.R ((j : ℕ) + 1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, map_zero, ZeroMemClass.coe_zero, valC_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, Submodule.coe_add, valC_add, ih]

end Sum

theorem ball_descent : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∀ (F' : Type) [Field F'] [NumberField F'] [Algebra S.Ks F'] (φ' : F' →+* ℂ_[D.ntw.l i]), (∀ a, φ' (algebraMap S.Ks F' a) = embS S iC b a) → (∀ a : S.Ks, vLa (placeAt φ') (algebraMap S.Ks F' a) = vLa (placeAt (embS S iC b)) a) → ∀ (n : ℕ) (a : Fin n → F') (f : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ z : Pts YS iC b ((j : ℕ) + 1), ‖∑ s, φ' (a s) * valC z.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1))‖ ≤ 1) → ∃ (m : ℕ) (β : Fin m → F') (g : Fin m → NX.FmK S ((j : ℕ) + 1)), (∀ t, ‖φ' (β t)‖ ≤ 1) ∧ (∀ t, g t ∈ locBall YS fw iC b j) ∧ ∑ s, a s ⊗ₜ[S.Ks] f s = ∑ t, β t ⊗ₜ[S.Ks] g t := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _hiC b j hball F' _ _ _ φ' hφ' hv n a f hz
  have := GlobalTheory.SupDescent.liesOver (K := S.Ks) (K' := F') (la := placeAt (embS S iC b)) (la' := placeAt φ') hv
  obtain ⟨d, bb, hb1, hb2⟩ := GlobalTheory.SupDescent.exists_residue_basis (la := placeAt (embS S iC b)) (la' := placeAt φ')
  choose c hc0 hcB using fun s => hball (f s)
  choose x ρ hρ hx using fun s => GlobalTheory.SupDescent.exists_approx (K := S.Ks) (K' := F') hv hb2 (a s) (hc0 s)
  let F : Fin d → NX.FmK S ((j : ℕ) + 1) := fun t => ∑ s, x s t • f s
  have hmem : ∀ g : NX.FmK S ((j : ℕ) + 1), (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) ∈
      sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n := cuspOf_mem_sec YS fw j
  have hF : ∀ t, F t ∈ locBall YS fw iC b j := by
    intro t z
    obtain ⟨T, io, k, hR, y, u, hT, hu, hval⟩ := PtC.exists_valC z (wtA (κ j)) (κ j).n
    rw [hval _ (hmem _), norm_mul, hu, one_mul]
    let io' : S.Ks →+* T.Fr := io.comp (eKs YS).toRingHom
    have hR' : IsReading (embS S iC b) T io' k :=
      ⟨fun a => (hR.comp (eKs YS a)).trans (embC_eKs YS iC b a), hR.int⟩
    obtain ⟨e, ho⟩ := GlobalTheory.ReadingOver.overLa_placeAt_of_isReading (embS S iC b) hR'
    refine (hR.int _).2 ?_
    refine GlobalTheory.SupDescent.inV_of_forall_emb (K := S.Ks) (K' := F') hb1 hT ho
      (fun t => evI y (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1))) ?_ t
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, ψ, hψ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ _ _ T T' io y i e' he' hi
    obtain ⟨k', hk'⟩ := GlobalTheory.GeoTie.ReadExist.exists_isReading _ F' φ' T' σ e'' ho' hT'
    have hR₁ : IsReading (embC YS iC b) T' (i.comp io) k' := by
      refine ⟨fun a => ?_, hk'.int⟩
      obtain ⟨a0, rfl⟩ := (eKs YS).surjective a
      rw [embC_eKs, ← hφ' a0, ← hk'.comp, hσ a0]
      rfl
    obtain ⟨z', hz'⟩ := PtC.exists_of_reading hR₁ y₁ hT'
    have h4 : ∀ g : NX.FmK S ((j : ℕ) + 1),
        k' (i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)))) = valC z'.1 (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
      intro g
      have h5 : i (evI y (cuspOf YS fw j g : T0.R ((j : ℕ) + 1))) = evI y₁ (cuspOf YS fw j g : T0.R ((j : ℕ) + 1)) := by
        letI := io.toAlgebra
        letI := (i.comp io).toAlgebra
        exact (DFunLike.congr_fun hψ _).symm.trans (GlobalTheory.FlagTan.evR_frMap (hmem g).1 hmap).symm
      rw [h5, hz' _ _ _ (hmem g)]
    refine (hk'.int _).1 ?_
    rw [map_sum]
    simp only [map_mul, hk'.comp, h4]
    have hid : ∑ t, φ' (bb t : F') * valC z'.1 (cuspOf YS fw j (F t) : T0.R ((j : ℕ) + 1)) =
        ∑ s, φ' (a s) * valC z'.1 (cuspOf YS fw j (f s) : T0.R ((j : ℕ) + 1)) -
          ∑ s, φ' (ρ s) * valC z'.1 (cuspOf YS fw j (c s • f s) : T0.R ((j : ℕ) + 1)) := by
      rw [eq_sub_iff_add_eq]
      simp only [F, valC_cuspOf_sum YS fw j, valC_cuspOf_smul YS fw j, Finset.mul_sum]
      rw [Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hx s]
      simp only [map_add, map_sum, map_mul, hφ', Finset.sum_mul, add_mul]
      congr 1
      · exact Finset.sum_congr rfl fun t _ => by ring
      · ring
    rw [hid]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz z') ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ s)) (norm_nonneg _) (hcB s z')
  refine ⟨d + n, Fin.append (fun t => (bb t : F')) ρ, Fin.append F fun s => c s • f s, fun t => ?_, fun t => ?_, ?_⟩
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact norm_int_le_one φ' (bb t)
    · rw [Fin.append_right]; exact GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ' (hρ t)
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · rw [Fin.append_left]; exact hF t
    · rw [Fin.append_right]; exact hcB t
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have e : ∀ s, a s = ∑ t, x s t • (bb t : F') + c s • ρ s := fun s => by
      rw [hx s]; simp only [Algebra.smul_def]; rw [mul_comm (algebraMap _ _ (c s))]
    have h1 : ∀ t s, (bb t : F') ⊗ₜ[S.Ks] (x s t • f s) = (x s t • (bb t : F')) ⊗ₜ[S.Ks] f s :=
      fun t s => (TensorProduct.smul_tmul _ _ _).symm
    have h2 : ∀ s, ρ s ⊗ₜ[S.Ks] (c s • f s) = (c s • ρ s) ⊗ₜ[S.Ks] f s := fun s => (TensorProduct.smul_tmul _ _ _).symm
    simp only [F, TensorProduct.tmul_sum, h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← TensorProduct.sum_tmul, ← TensorProduct.add_tmul, ← e s]

end GlobalTheory.GeoTie.BallDescent
