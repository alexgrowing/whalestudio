import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer

theorem finsum_comp_eq_comp_finsum {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (g : ι → W →ₗ[ℂ] W) (h : ι → V →ₗ[ℂ] V) (hc : ∀ i, g i ∘ₗ T = T ∘ₗ h i)
    (hs : ∀ i, g i = 0 ↔ h i = 0) : (∑ᶠ i, g i) ∘ₗ T = T ∘ₗ ∑ᶠ i, h i := by
  have hg : Function.support g = Function.support h := by
    ext i; simp only [Function.mem_support, ne_eq, hs]
  by_cases hfin : (Function.support h).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by rw [hg]; simp),
      finsum_eq_sum_of_support_subset h (s := hfin.toFinset) (by simp)]
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (hc i) x
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hg])]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RF_apply' (x : finU E n) (φ : UA E n → ℂ) (g : UA E n) : RF E n x φ g = φ (g * x.1) := rfl

theorem RF_ne_zero (x : finU E n) : RF E n x ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => (1 : ℂ))) 1
  simp at this
  exact one_ne_zero this

theorem rightReg_dual_ne_zero (lam : InfinitePlace E → DomWeight n) [Nontrivial (Wsp lam)] (x : finU E n) :
    rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Wsp lam)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Wsp lam), φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => φ)) 1
  have h2 : φ = 0 := by simpa [rightReg, LinearMap.funLeft] using this
  exact hφ (by rw [h2]; rfl)

theorem hop_phiFun (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU E n → Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  rcases subsingleton_or_nontrivial (Wsp lam) with hW | hW
  · rw [Subsingleton.elim w 0]; simp
  set T : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (UA E n → ℂ) := (phiFun lam).flip w with hT
  have key : (∑ᶠ q : finU E n ⧸ globLev S K', globFn S f q.out • (RF E n q.out ∘ₗ LinearMap.id)) ∘ₗ T =
      T ∘ₗ ∑ᶠ q : finU E n ⧸ globLev S K', globFn S f q.out •
        (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id) := by
    refine finsum_comp_eq_comp_finsum T _ _ (fun q => ?_) (fun q => ?_)
    · ext G g
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, hT, LinearMap.flip_apply,
        LinearMap.map_smul, Pi.smul_apply]
      rw [RF_apply', phiFun_mul_fin]
    · rw [smul_eq_zero, smul_eq_zero, LinearMap.comp_id, LinearMap.comp_id]
      simp only [RF_ne_zero, rightReg_dual_ne_zero, or_false]
  have := LinearMap.congr_fun key F
  simp only [LinearMap.comp_apply, hT, LinearMap.flip_apply] at this
  simp only [hop, hopM, levOp, LinearMap.smul_apply, this, LinearMap.map_smul]

theorem hop_phiFun_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU E n → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w :=
  fun _ _ _ _ _ S lam K' f F w => hop_phiFun S lam K' f F w

end GlobalTheory.BCT.TrKer
