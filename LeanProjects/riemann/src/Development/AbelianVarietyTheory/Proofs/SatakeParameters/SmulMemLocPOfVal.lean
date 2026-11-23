import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeFactsAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHomogeneousOfMemWeyl
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

noncomputable section

namespace GlobalTheory.JetOpWeylLat

open GlobalTheory.JetPoint GlobalTheory.LiftTypePrime Formalism.GradedWeylDivisibility

section Expand

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_mul_monomial (J : (DVar ι a b →₀ ℕ) → K) (P : Pol K ι b) (m : DVar ι a b →₀ ℕ) :
    jetLin J (rename Sum.inl P * rename Sum.inr (monomial m (1 : K))) = J m • P := by
  induction P using MvPolynomial.induction_on' with
  | monomial p c =>
    rw [rename_monomial, rename_monomial, monomial_mul, mul_one, jetLin, constr_monomial]
    have h1 : (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inl Sum.inl_injective.injOn = p := by
      ext x
      rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective,
        Finsupp.mapDomain_notin_range _ _ (by simp), add_zero]
    have h2 : (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inr Sum.inr_injective.injOn = m := by
      ext x
      rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inr_injective,
        Finsupp.mapDomain_notin_range _ _ (by simp), zero_add]
    rw [h1, h2, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_comm]
  | add p q hp hq => rw [map_add, add_mul, map_add, hp, hq, smul_add]

def joinExp (α : ι → (Fin b × Fin a →₀ ℕ)) : DVar ι a b →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k => α k.1 k.2

theorem subD_ten [DecidableEq ι] (h : a ≤ b) (F : ι → MvPolynomial (Fin a × Fin a) ℤ) :
    subD K ι a b (ten fun τ => map (Int.castRingHom K) (F τ)) =
      ∑ α ∈ Fintype.piFinset fun τ => (subGen h (F τ)).support,
        rename Sum.inl (ten fun τ => map (Int.castRingHom K) ((subGen h (F τ)).coeff (α τ))) *
          rename Sum.inr (monomial (joinExp α) (1 : K)) := by
  have e1 : subD K ι a b (ten fun τ => map (Int.castRingHom K) (F τ)) =
      ∏ τ, aeval (fun v : Fin a × Fin a => ∑ β : Fin b,
        (X (Sum.inl (τ, β, Fin.castLE h v.2)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) *
          X (Sum.inr (τ, β, v.1))) (F τ) := by
    unfold subD ten blockEmb
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [aeval_rename]
    refine (aeval_map_algebraMap K _ (F τ)).trans ?_
    congr 2
    funext v
    have hv : (v.2 : ℕ) < b := lt_of_lt_of_le v.2.2 h
    simp only [Function.comp_apply, dif_pos hv]
    rfl
  rw [e1]
  refine (Finset.prod_congr rfl fun τ _ => aeval_subGen h
    (fun v : Fin b × Fin a => (X (Sum.inr (τ, v)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K))
    (fun v : Fin b × Fin b => X (Sum.inl (τ, v))) (F τ)).trans ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  · unfold ten blockEmb
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [rename_rename, rename_eq_aeval]
    exact (aeval_map_algebraMap K _ _).symm
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    refine (Finsupp.prod_fintype (α τ)
      (fun v e => (X (Sum.inr (τ, v)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) ^ e) (by simp)).trans ?_
    simp [joinExp]

theorem jetMap_ten [DecidableEq ι] (h : a ≤ b) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (f : ι → MvPolynomial (Fin a × Fin a) ℤ) :
    jetMap J n (ten fun τ => map (Int.castRingHom K) (f τ)) =
      ∑ α ∈ Fintype.piFinset fun τ => (subGen h (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ)).support,
        J (joinExp α) • ten fun τ =>
          map (Int.castRingHom K) ((subGen h (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ)).coeff (α τ)) := by
  have e : (ten fun τ => map (Int.castRingHom K) (f τ)) * ∏ τ, frDet K a τ ^ n τ =
      ten fun τ => map (Int.castRingHom K) (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ) := by
    rw [← GlobalTheory.WeylMinorDual.ten_gdet]
    simp only [ten, map_mul, map_pow, GlobalTheory.WeylMinorDual.map_gdet, Finset.prod_mul_distrib]
  change jetLin J (subD K ι a b (_ * _)) = _
  rw [e, subD_ten h, map_sum]
  exact Finset.sum_congr rfl fun α _ => jetLin_mul_monomial _ _ _

end Expand

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem toK_map_int {σ : Type} (f : MvPolynomial σ ℤ) :
    toK K σ (map (Int.castRingHom (𝓞 K)) f) = map (Int.castRingHom K) f := by
  change map (algebraMap (𝓞 K) K) _ = _
  rw [map_map]
  congr 1

theorem ten_mem_delStd (lam : ι → DomWeight a) {f : ι → MvPolynomial (Fin a × Fin a) ℤ}
    (hf : ∀ τ, f τ ∈ delSq ℤ a (lam τ)) : (ten fun τ => map (Int.castRingHom K) (f τ)) ∈ delStd K lam :=
  Submodule.subset_span ⟨_, fun τ => ⟨_, GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) _ _ _ (hf τ),
    toK_map_int _⟩, rfl⟩

theorem delStd_le_span (lam : ι → DomWeight a) :
    delStd K lam ≤ Submodule.span (𝓞 K) {P | ∃ f : ι → MvPolynomial (Fin a × Fin a) ℤ,
      (∀ τ, f τ ∈ delSq ℤ a (lam τ)) ∧ P = ten fun τ => map (Int.castRingHom K) (f τ)} := by
  have h : ∀ τ, (delSq (𝓞 K) a (lam τ)).map (toK K _) = Submodule.span (𝓞 K) (Set.range fun u =>
      map (Int.castRingHom K) (applyWord ℤ u (hw ℤ (le_refl a) (lam τ).natW))) := fun τ => by
    rw [delSq, weyl, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext u
    rw [← toK_map_int, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
    rfl
  unfold delStd
  simp only [h]
  rw [GlobalTheory.WeylMinorDual.tensorLat_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨_, fun τ => Submodule.subset_span ⟨u τ, rfl⟩, rfl⟩

theorem mem_localization_weylLattice_iff (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight a)
    {M : ι → Submodule (𝓞 K) (Fin a → K)} (hM : LatWithBasis w M 1) (F : Formalism.L2.DIV.VV K lam) :
    F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)) ↔ (F : Pol K ι a) ∈ localization₂ w.asIdeal (delStd K lam) := by
  have h1 : F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)) ↔
      (F : Pol K ι a) ∈ localization₂ w.asIdeal (delP lam fun τ => dualFr (M τ)) := Iff.rfl
  have h2 := (GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam (fun τ => dualFr (M τ))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.HAtBasis.isLattice_of_basisAt w (hM τ).1 (hM τ).2)) w
    (fun τ => inside₂ K a ((1 : ι → GL (Fin a) K) τ))
    (fun τ => GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hM τ).1 (hM τ).2)).2
  rw [h1, h2, GlobalTheory.TransLoc.mem_map_actP, GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  simp only [Pi.one_apply, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul, blockAct_one,
    AlgHom.id_apply]

theorem smul_mem_localizationAt_of_valuation (w : HeightOneSpectrum (𝓞 K)) {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    [IsScalarTower (𝓞 K) K Z] {T : Submodule (𝓞 K) Z} {x : K}
    (hx : w.valuation K x ≤ 1) {P : Z} (hP : P ∈ T) : x • P ∈ localization₂ w.asIdeal T := by
  obtain ⟨r, ⟨d, hd⟩, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have h' : algebraMap (𝓞 K) K d * x = algebraMap (𝓞 K) K r := (mul_comm _ _).trans h
  have e : d • x • P = r • P := by
    rw [← algebraMap_smul K d (x • P), smul_smul, h', algebraMap_smul]
  exact ⟨d, hd, e ▸ T.smul_mem r hP⟩

theorem jetMap_ten_mem (w : HeightOneSpectrum (𝓞 K)) {hab : a < b} {lam : ι → DomWeight a} {lam' : ι → DomWeight b}
    {s s' : ι → ℤ} {n : ι → ℕ} (hw : WtCompat hab lam lam' s s' n) {c : K} {J : (DVar ι a b →₀ ℕ) → K}
    (hJ : ∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) {f : ι → MvPolynomial (Fin a × Fin a) ℤ}
    (hf : ∀ τ, f τ ∈ delSq ℤ a (lam τ)) :
    c • jetMap J n (ten fun τ => map (Int.castRingHom K) (f τ)) ∈ localization₂ w.asIdeal (delStd K lam') := by
  classical
  have hF : ∀ τ, f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ ∈ weyl ℤ a a le_rfl fun r => (lam τ).natW r + n τ := fun τ => by
    rw [GlobalTheory.WeylMinorDual.weyl_add]
    exact ⟨f τ, hf τ, rfl⟩
  have hν : ∀ τ (j : Fin b), (lam' τ).natW j = if h : (j : ℕ) < a then (lam τ).natW ⟨j, h⟩ + n τ else 0 := by
    intro τ j
    have e0 := GlobalTheory.WeylMinorDual.natW_cast (lam' τ) j
    have e5 := detShift_eq hw τ
    split_ifs with h
    · have e1 : (lam' τ).w j + s τ = _ := hw.1 τ ⟨j, h⟩
      have e2 := GlobalTheory.WeylMinorDual.natW_cast (lam τ) ⟨j, h⟩
      have e3 := hw.2.2 τ
      omega
    · have e1 := hw.2.1 τ j (not_lt.1 h)
      omega
  rw [jetMap_ten hab.le, Finset.smul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [smul_smul]
  refine smul_mem_localizationAt_of_valuation w (hJ _ fun τ => ?_)
    (ten_mem_delStd lam' fun τ => coeff_subGen_mem hab.le (natW_anti _) (hν τ) (hF τ) _)
  have h1 := subGen_isHomogeneous hab.le (isHomogeneous_of_mem_weyl
    (fun _ _ h => Nat.add_le_add_right (natW_anti _ h) _) (hF τ)) (mem_support_iff.1 (Fintype.mem_piFinset.1 hα τ))
  have h2 : (∑ β : Fin b, ∑ γ : Fin a, joinExp α (τ, β, γ)) = ∑ r, ((lam τ).natW r + n τ) := by
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
    simp [joinExp]
  rw [h2, Nat.cast_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.cast_add, GlobalTheory.WeylMinorDual.natW_cast, hw.2.2 τ]
  ring

theorem jetOpWeyl : GlobalTheory.ColPeriod.JetOpWeyl := by
  intro K _ _ w ι _ a b hab lam lam' s s' n hw M MW _ _ hM hMW c J hJ F hF
  have hmem : jetMap J n (F : Pol K ι a) ∈ Formalism.L2.DIV.VV K lam' :=
    jetMap_mem hab.le n _ _ (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hab lam lam' s s' n hw ap _ F.2) J
  rw [mem_localization_weylLattice_iff w lam hM] at hF
  rw [mem_localization_weylLattice_iff w lam' hMW, Submodule.coe_smul, coe_jetOp _ _ _ _ _ hmem]
  have key : delStd K lam ≤ (localization₂ w.asIdeal (delStd K lam')).comap ((c • jetMap J n).restrictScalars (𝓞 K)) := by
    refine (delStd_le_span lam).trans (Submodule.span_le.2 ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact jetMap_ten_mem w hw hJ hf
  obtain ⟨t, ht, hF⟩ := hF
  obtain ⟨u, hu, h⟩ := key hF
  refine ⟨u * t, mul_mem hu ht, ?_⟩
  rw [map_smul] at h
  rw [mul_smul]
  exact h

end GlobalTheory.JetOpWeylLat
