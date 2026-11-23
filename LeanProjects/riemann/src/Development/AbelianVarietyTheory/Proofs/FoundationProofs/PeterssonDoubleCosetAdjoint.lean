import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetAdjointOfInvariantWeightStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.PetAdj

def toG (δ : M2) : GL (Fin 2) ℝ :=
  if hd : ((Int.castRingHom ℝ).mapMatrix δ).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

lemma toG_val (δ : M2) (hδ : δ.det ≠ 0) :
    (toG δ : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix δ := by
  have hd : ((Int.castRingHom ℝ).mapMatrix δ).det ≠ 0 := by
    rw [← RingHom.map_det]; simpa using hδ
  rw [toG, dif_pos hd]; rfl

lemma toG_det (δ : M2) (hδ : 0 < δ.det) : 0 < (toG δ).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toG_val δ hδ.ne', ← RingHom.map_det]
  simpa using hδ

def K (k N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (δ : M2) (τ : ℍ) : ℂ :=
  ch ε (δ 0 0) * (conj (h τ) * slz k δ f τ * (τ.im : ℂ) ^ k)

lemma ch_unit (N : ℕ) (ε : DirichletCharacter ℂ N) (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) :
    ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h0 : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγ
  have h2 : (((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ)) : ZMod N) = 1 := by rw [hdet]; simp
  push_cast at h2
  rw [h0, mul_zero, sub_zero] at h2
  simp only [ch, ← map_mul, h2, map_one]

lemma conj_ch_inv (N : ℕ) (ε : DirichletCharacter ℂ N) (x : ℤ) : conj (ch ε⁻¹ x) = ch ε x := by
  have := MulChar.star_apply' ε⁻¹ (x : ZMod N)
  simp only [inv_inv] at this
  exact this

lemma K_left (k L N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (hk : 1 ≤ k) (hNL : N ∣ L)
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (δ : M2) (hδ : 0 < δ.det)
    (hδN : (N : ℤ) ∣ δ 1 0) (τ : ℍ) :
    K k N ε h f ((γ : M2) * δ) τ = K k N ε h f δ τ := by
  obtain ⟨hcoc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k f hk
  have hγN : (N : ℤ) ∣ γ 1 0 := dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : slz k ((γ : M2) * δ) f τ = ch ε (γ 1 1) * slz k δ f τ := by
    rw [hcoc _ _ (by simp) hδ, (hinv L (ch ε)).mp hf γ hγ]
    simp only [slz]; ring
  have hd : ((δ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hδN
  have e : ch ε (((γ : M2) * δ) 0 0) = ch ε (γ 0 0) * ch ε (δ 0 0) := by
    simp only [ch, ← map_mul]
    congr 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  have hu := ch_unit N ε γ hγN
  simp only [K, h1, e]
  linear_combination (ch ε (δ 0 0) * (conj (h τ) * slz k δ f τ * (τ.im : ℂ) ^ k)) * hu

lemma K_right (k L N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (hk : 1 ≤ k) (hNL : N ∣ L)
    (hh : Inv k L (ch ε) h) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    K k N ε h f (δ * (γ : M2)) τ = K k N ε h f δ (γ • τ) := by
  have hcoc := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).1
  have hsl := (GlobalTheory.T.slashIntMatrixPosDet_properties k (slz k δ f) hk).2.1
  have hγN : (N : ℤ) ∣ γ 1 0 := dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have e2 := hh γ hγ τ
  have e1 := (congrFun (hcoc δ (γ : M2) hδ (by simp)) τ).trans (hsl γ τ)
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hj : ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have e3 := ModularGroup.im_smul_eq_div_normSq γ τ
  rw [hden] at e3
  generalize ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) = j at *
  have e3' : ((γ • τ).im : ℂ) = (τ.im : ℂ) / (j * conj j) := by
    rw [e3, Complex.mul_conj]; push_cast; rfl
  have hd : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγN
  have e4 : ch ε ((δ * (γ : M2)) 0 0) = ch ε (δ 0 0) * ch ε (γ 0 0) := by
    simp only [ch, ← map_mul]
    congr 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  have hu := ch_unit N ε γ hγN
  have hc : conj (ch ε (γ 1 1)) = ch ε (γ 0 0) := by
    have h1 : conj (ch ε (γ 1 1)) = (ch ε (γ 1 1))⁻¹ := by
      have := MulChar.star_apply' ε ((γ 1 1 : ℤ) : ZMod N)
      rw [MulChar.inv_apply_eq_inv'] at this
      exact this
    rw [h1]; exact (eq_inv_of_mul_eq_one_left hu).symm
  have hj' : conj j ≠ 0 := by simpa using hj
  simp only [K, e1, e2, e3', e4, map_mul, map_pow, hc, div_pow, mul_pow]
  field_simp

lemma K_adj (k N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (α : M2) (hα : 0 < α.det) (s : ℍ) :
    K k N ε h f α s = conj (ch ε⁻¹ (α 0 0) * slz k α.adjugate h (toG α • s)) * f (toG α • s) *
      ((toG α • s).im : ℂ) ^ k := by
  have hv := toG_val α hα.ne'
  have hden : denom (toG α) (s : ℂ) = ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) := by
    simp [denom, hv]
  have hnum : num (toG α) (s : ℂ) = ((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ) := by
    simp [num, hv]
  have hj : ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have ht := coe_smul_of_det_pos (toG_det α hα) s
  have him := im_smul_eq_div_normSq (toG α) s
  have hdet : (toG α).det.val = (α.det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hv, ← RingHom.map_det]; simp
  rw [abs_of_pos (toG_det α hα), hdet, hden] at him
  rw [hden, hnum] at ht
  generalize toG α • s = t at *
  have hQ : ((α.det : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hQe : ((α.det : ℤ) : ℂ) = (α 0 0 : ℂ) * (α 1 1 : ℂ) - (α 0 1 : ℂ) * (α 1 0 : ℂ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  have hda : α.adjugate.det = α.det := by
    rw [Matrix.det_adjugate]; simp
  have hA : ((α.adjugate 1 0 : ℤ) : ℂ) * t + ((α.adjugate 1 1 : ℤ) : ℂ)
      = ((α.det : ℤ) : ℂ) / (((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ)) := by
    rw [hQe, ht, Matrix.adjugate_fin_two, eq_div_iff hj]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (-((α 1 0 : ℤ) : ℂ) * (((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ))) * mul_inv_cancel₀ hj
  have hB : ((α.adjugate 0 0 : ℤ) : ℂ) * t + ((α.adjugate 0 1 : ℤ) : ℂ)
      = ((α.det : ℤ) : ℂ) * s / (((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ)) := by
    rw [hQe, ht, Matrix.adjugate_fin_two, eq_div_iff hj]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (((α 1 1 : ℤ) : ℂ) * (((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ))) * mul_inv_cancel₀ hj
  simp only [K, slz]
  rw [hA, hB, ← ht, hda, ofComplex_apply]
  generalize ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) = j at *
  have hs : ((α.det : ℤ) : ℂ) * s / j / (((α.det : ℤ) : ℂ) / j) = s := by field_simp
  have him' : (t.im : ℂ) = ((α.det : ℤ) : ℂ) * (s.im : ℂ) / (j * conj j) := by
    rw [him, Complex.mul_conj, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hj' : conj j ≠ 0 := by simpa using hj
  rw [hs, ofComplex_apply, him']
  simp only [map_mul, map_pow, map_inv₀, map_div₀, map_intCast, conj_ch_inv, div_pow, mul_pow]
  field_simp

end GlobalTheory.EisM.PetAdj

open GlobalTheory.EisM.PetAdj in

theorem GlobalTheory.EisM.pet_hsum_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (α : κ → M2) (h f : ℍ → ℂ), 1 ≤ k → 0 < N → N ∣ L → 0 < q → q.Coprime N → Wt L ρ → (∀ δ ∈ Δ, δ.det = q ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → RRep L Δ α → Inv k L (ch ε) h → Inv k L (ch ε) f → Continuous h → Continuous f → (∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (h τ) * slz k (β i) f τ * (τ.im : ℂ) ^ k))) → pet k ρ h (hsum k (ch ε) β f) = pet k ρ (fun τ => ∑ j, ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h τ) f := by
  intro k L N q ε ρ Δ ι κ _ _ β α h f hk _ hNL hq _ hρ hΔ hL hR hh hf hhc hfc hint
  have hcont := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).2.2.2.1
  have hβ : ∀ i, β i ∈ Δ := fun i => by
    simpa using hL.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
  have hα : ∀ j, α j ∈ Δ := fun j => by
    simpa using hR.mapsTo (Set.mem_univ (j, (1 : Gamma0 L)))
  have hdet : ∀ δ ∈ Δ, 0 < δ.det := fun δ hδ => by rw [(hΔ δ hδ).1]; exact_mod_cast hq
  have hΓ : ∀ γ : Gamma0 L, (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := fun γ =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  let eL : Gamma0 L × ι ≃ Δ := (Equiv.Set.univ _).symm.trans (Set.BijOn.equiv _ hL)
  let eR : κ × Gamma0 L ≃ Δ := (Equiv.Set.univ _).symm.trans (Set.BijOn.equiv _ hR)
  obtain ⟨e, he⟩ : ∃ e : Gamma0 L × ι ≃ κ × Gamma0 L, ∀ p : Gamma0 L × ι,
      ((p.1 : SL(2, ℤ)) : M2) * β p.2 = α (e p).1 * (((e p).2 : SL(2, ℤ)) : M2) :=
    ⟨eL.trans eR.symm, fun p => (congrArg Subtype.val (eR.apply_symm_apply (eL p))).symm⟩
  let φ : Gamma0 L →* GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ).comp (Gamma0 L).subtype
  have hφv : ∀ γ : Gamma0 L, (φ γ : Matrix (Fin 2) (Fin 2) ℝ)
      = (Int.castRingHom ℝ).mapMatrix ((γ : SL(2, ℤ)) : M2) := fun γ => rfl
  have hP : ∀ i, Integrable (fun x : ℍ => (ρ x : ℂ) * K k N ε h f (β i) x) := fun i => by
    refine ((hint i).const_mul (ch ε (β i 0 0))).congr (Eventually.of_forall fun x => ?_)
    simp only [K]; ring
  haveI : Countable SL(2, ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix; infer_instance
  obtain ⟨hQ, key⟩ := GlobalTheory.T.double_coset_adjoint_of_invariant_weight (GL (Fin 2) ℝ) ℍ (Gamma0 L) ι κ volume φ ρ (fun i => toG (β i))
    (fun j => toG (α j)) e (fun i => K k N ε h f (β i)) (fun j => K k N ε h f (α j))
    hρ.meas hρ.nonneg hρ.sum
    (fun p => by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hφv, hφv, toG_val _ (hdet _ (hβ _)).ne',
        toG_val _ (hdet _ (hα _)).ne', ← map_mul, ← map_mul, he])
    (fun p x => by
      rw [← K_left k L N ε h f hk hNL hf p.1 (hΓ _) _ (hdet _ (hβ _)) (hΔ _ (hβ _)).2, he,
        K_right k L N ε h f hk hNL hh _ (hΓ _) _ (hdet _ (hα _))]
      rfl)
    hP
    (fun j => by
      refine Continuous.aestronglyMeasurable ?_
      have := hcont _ (hdet _ (hα j)) hfc
      have him : Continuous fun τ : ℍ => (τ.im : ℂ) :=
        Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
      exact continuous_const.mul (((Complex.continuous_conj.comp hhc).mul this).mul (him.pow k)))
  have hC : ∀ j (x : ℍ), K k N ε h f (α j) ((toG (α j))⁻¹ • x) =
      conj (ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h x) * f x * (x.im : ℂ) ^ k := fun j x => by
    rw [K_adj k N ε h f _ (hdet _ (hα j)), smul_inv_smul]
  rw [← integral_finset_sum _ fun i _ => hP i, ← integral_finset_sum _ fun j _ => hQ j] at key
  simp only [hC] at key
  unfold pet hsum
  refine Eq.trans ?_ (key.trans ?_)
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [K, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul]

end
