import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

variable {l : ℕ} [Fact l.Prime]

private lemma exists_solve {B : Type} [CommRing B] {d : ℕ} (U : Matrix (Fin d) (Fin d) B) (hU : IsUnit U)
    (f₁ f₂ : B →+* B) (V : Matrix (Fin d) (Fin d) B) (s : B) (z : Fin d → B)
    (hV : V * U.map ⇑f₂ = s • U.map ⇑f₁) :
    ∃ w₀ : Fin d → B, U.map ⇑f₂ *ᵥ w₀ = z ∧ V *ᵥ z = s • (U.map ⇑f₁ *ᵥ w₀) := by
  obtain ⟨u, hu⟩ := hU.map (RingHom.mapMatrix f₂)
  have hu' : (u : Matrix (Fin d) (Fin d) B) = U.map ⇑f₂ := hu
  have hw : U.map ⇑f₂ *ᵥ ((↑u⁻¹ : Matrix (Fin d) (Fin d) B) *ᵥ z) = z := by
    rw [Matrix.mulVec_mulVec, ← hu', Units.mul_inv, Matrix.one_mulVec]
  refine ⟨(↑u⁻¹ : Matrix (Fin d) (Fin d) B) *ᵥ z, hw, ?_⟩
  conv_lhs => rw [← hw]
  rw [Matrix.mulVec_mulVec, hV, Matrix.smul_mulVec]

private lemma key_sum {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {d : ℕ}
    (M : Matrix (Fin d) (Fin d) (Per.Bcris l)) (w₀ : Fin d → Per.Bcris l) (t : Fin d → Om l) :
    (∑ j, ((1 : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm (w₀ j)) : Bst P) : OB P) *
      ∑ i, (t i ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm (M i j)) : Bst P) : OB P)) =
    ∑ i, (t i ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm ((M *ᵥ w₀) i)) : Bst P) : OB P) := by
  simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← TensorProduct.tmul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma tmul_zB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (L : FinExt l)
    (x : ↥L.1) (z : ℤ_[l]) :
    (((x : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm (Per.zB l z)) : Bst P) : OB P) =
      ((((z : ℚ_[l]) • x : ↥L.1)) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (1 : Bst P) := by
  have h1 : T.eB.symm (Per.zB l z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
    rw [← T.zB z, RingEquiv.symm_apply_apply]
  have h2 : (Polynomial.C (algebraMap ℚ_[l] P.R.B (z : ℚ_[l])) : Bst P) =
      (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • (1 : Bst P) := by
    rw [algebraMap_smul, Algebra.smul_def, mul_one]
    rfl
  have h3 : ((((z : ℚ_[l]) • x : ↥L.1)) : Om l) =
      (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • ((x : ↥L.1) : Om l) := by
    rw [algebraMap_smul]
    rfl
  rw [h1, h2, h3, TensorProduct.smul_tmul]

private lemma coord_sum {P : LocPrime l} {L : FinExt l} {a d : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀)
    (v : Fin d → Fin a → ↥L.1) (y : Fin d → Bst P) (i' : Fin a) :
    ψ₀ (∑ i, v i ⊗ₜ[ℚ_[l]] y i) i' = ∑ i, ((v i i' : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] y i := by
  rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => h _ _ _

end UpperTheory.Gal.ClosedPhiFromClosedTrace

set_option maxHeartbeats 4000000 in
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.tieRep_holds :
    TrLin → CoordEx → CoordWD → ColInv → WeilPhi2 → TestTr → TieRep2 := by
  intro hTr hCE hCW hCI hWP hTT l _ ι P AI T E Ω _ _ _ _ _ w A h O _ _ _ Bw hj g n₁ n₂ hα L a d R _
    hdim ρ b e hb he s V hOp
  classical
  obtain ⟨U, hU, hV⟩ := hOp
  have hh := exists_solve U hU.unit (Per.φB l ^ n₁) (Per.φB l ^ n₂) V s (fun i => Per.zB l (e i)) hV
  obtain ⟨w₀, hw⟩ := hh
  obtain ⟨hw₀, hv₀⟩ := hw
  obtain ⟨ψ₀, hψ₀⟩ := hCE l P L a
  obtain ⟨ψ, hψs, hψm⟩ := hCW l P ι Bw.Kw L a R ψ₀ hψ₀
  have hcol := fun (j : Fin d) (k : Fin a) =>
    hCI l P AI T Bw.Kw L a d ρ R (fun i i' => b i i' k) (fun g j => hb g j k) U hU j
  choose x hx₂ hx₁ using fun (j : Fin d) (k : Fin a) =>
    hWP l P E Ω w A h O Bw g n₁ n₂ hα L a R _ (hcol j k).1
  have hψ₂ : ∀ j k i', ψ (wdMk P ι R (x j k)) i' =
      ∑ i, ((b i i' k : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
        (Polynomial.C (T.eB.symm ((U.map ⇑(Per.φB l ^ n₂)) i j)) : Bst P) := by
    intro j k i'
    rw [hψm, hx₂, (hcol j k).2 n₂]
    exact coord_sum hψ₀ _ _ i'
  have hψ₁ : ∀ j k i', ψ (wdRho P ι Bw h hj R g (wdMk P ι R (x j k))) i' =
      ∑ i, ((b i i' k : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
        (Polynomial.C (T.eB.symm ((U.map ⇑(Per.φB l ^ n₁)) i j)) : Bst P) := by
    intro j k i'
    rw [wdRho_mk, hψm, hx₁, (hcol j k).2 n₁]
    exact coord_sum hψ₀ _ _ i'
  let κ : ℂ →+* OB P := (Algebra.TensorProduct.includeLeftRingHom :
    Om l →+* Om l ⊗[↥(MaximalUnramifiedExtension l)] Bst P).comp ι.symm.toRingHom
  let β : Per.Bcris l → OB P := fun y => (1 : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] (Polynomial.C (T.eB.symm y) : Bst P)
  have hframe : ∀ i i', ∑ j, β (w₀ j) * ψ (wdMk P ι R (x j i')) i = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : ∑ j, β (w₀ j) * ψ (wdMk P ι R (x j i')) i = ∑ j, β (w₀ j) *
        ∑ i₂, ((b i₂ i i' : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
          (Polynomial.C (T.eB.symm ((U.map ⇑(Per.φB l ^ n₂)) i₂ j)) : Bst P) :=
      Finset.sum_congr rfl fun j _ => by rw [hψ₂]
    rw [h1, key_sum T _ w₀ (fun i₂ => ((b i₂ i i' : ↥L.1) : Om l)), hw₀]
    simp only [tmul_zB T L]
    rw [← TensorProduct.sum_tmul]
    have hs : ∑ i₂, ((((e i₂ : ℚ_[l]) • b i₂ i i' : ↥L.1)) : Om l) = if i = i' then 1 else 0 := by
      have h2 := congrFun (congrFun he i) i'
      rw [Matrix.sum_apply] at h2
      simp only [Matrix.smul_apply] at h2
      rw [← AddSubmonoidClass.coe_finset_sum, h2, Matrix.one_apply]
      split_ifs <;> rfl
    rw [hs]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _
  have hmain := hTr ℂ (OB P) (WDSpace P ι R) (Fin d) a hdim κ ψ hψs (wdRho P ι Bw h hj R g)
    (fun j k => wdMk P ι R (x j k)) (fun j => β (w₀ j)) hframe
  refine hTT l P AI T d s _ ((U.map ⇑(Per.φB l ^ n₁)) *ᵥ w₀) _ _ hv₀ (Eq.trans ?_ hmain)
  have h3 : ∀ i, ∑ j, β (w₀ j) * ψ (wdRho P ι Bw h hj R g (wdMk P ι R (x j i))) i =
      ∑ i₂, ((b i₂ i i : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)]
        (Polynomial.C (T.eB.symm (((U.map ⇑(Per.φB l ^ n₁)) *ᵥ w₀) i₂)) : Bst P) := fun i => by
    rw [← key_sum T _ w₀ (fun i₂ => ((b i₂ i i : ↥L.1) : Om l))]
    exact Finset.sum_congr rfl fun j _ => by rw [hψ₁]
  simp only [h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i₂ _ => ?_
  rw [← TensorProduct.sum_tmul]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply]
  exact AddSubmonoidClass.coe_finset_sum _ _

end
