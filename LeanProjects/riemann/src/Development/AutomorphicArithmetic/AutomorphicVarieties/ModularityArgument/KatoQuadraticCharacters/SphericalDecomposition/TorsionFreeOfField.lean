import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PRepNew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpoEqZeroOfPow

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform

local instance (priority := high + 1) torsionFreeOfField (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] :
    Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

private theorem cofinite_notMem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem mem_of_normV_dvd {N : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)} (h : normV w ∣ N) :
    ((N : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  obtain ⟨c, rfl⟩ := h
  have e : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [Nat.cast_mul, e]
  exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)

private theorem charpoly_scale {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂ)
    (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by linear_combination e0
  have ht : φ M.trace = x + y := by linear_combination e0 - e1
  simp only [hd, ht, C_add, C_mul]
  ring

private theorem scale_sat {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂˣ) (q : ℕ)
    (u : ℂˣ) (hu : φ c = u) (P Q : ℂ[X]) (h : M.charpoly.map φ = P)
    (hP : ((algSat 2 q B).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = P)
    (hQ : ((algSat 2 q (B.map (· * u))).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = Q) :
    (c • M).charpoly.map φ = Q := by
  simp only [zpow_zero, one_mul] at hP hQ
  rw [charpoly_scale φ M c (algSat 2 q B) (h.trans hP.symm), ← hQ, hu]
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply, Units.val_mul]
  ring_nf

private theorem ss_twist {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 hW', hc⟩

private theorem isOpen_ker {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] {N : ℕ} (hN : 1 ≤ N)
    {κ : G ℚ Ω →* C} (hκ : KillsMu N κ) : IsOpen (κ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ N = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hN] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hκ s fun ζ hζ => hs ζ hζ

theorem twist_att (P : Af.HypothesesH) {k : ℕ} (hk : 2 ≤ k) (f : Newform k) {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hf : f.Att ι V)
    (κ : G ℚ Ω →* (Qbar l)ˣ) {N : ℕ} (hN : 1 ≤ N) (hκ : KillsMu N κ) :
    ∃ g : Newform k, g.Att ι (tw V κ) := by
  obtain ⟨art, ha⟩ : ∃ art : Neutral.B1.Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  have ho := isOpen_ker hN hκ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfi : Finite (G ℚ Ω ⧸ κ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hm : 0 < κ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι κ (continuous_of_isOpen_ker' κ ho) hm
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact κ.ker.pow_index_mem s)
  have hexpo : ∀ v, TR.expo χ v = 0 := GlobalTheory.HenQ.expo_eq_zero_of_pow χ hm h1
  obtain ⟨π, hinf, hsat⟩ := P.toClassicalTheorems.newform k hk f 0
  obtain ⟨g, hg⟩ := UpperTheory.V.Af.repNewform k hk 0 (π.twist χ) fun v => by
    have := (hinf v).twist χ
    rw [hexpo v] at this
    simpa using this
  refine ⟨g, ss_twist _ _ hf.1, ?_⟩
  filter_upwards [hf.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ), cofinite_notMem l hl.out.ne_zero,
    cofinite_notMem f.M f.pos.ne', cofinite_notMem g.M g.pos.ne'] with w hw hu hwl hwf hwg A hA
  obtain ⟨B, hB, hpB⟩ := hsat w fun h => hwf (mem_of_normV_dvd h)
  obtain ⟨S, hS, hpS⟩ := hg w fun h => hwg (mem_of_normV_dvd h)
  obtain rfl : S = B.map (· * χ.val w) := hS.unique (hB.twist hu)
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have e1 : κ s = 1 := (hL.unr_iff ha (Or.inl hwl) hA).2 hu s hs
    apply Units.ext
    rw [tw_val, e1, (hw A hA).1 s hs, Units.val_one, one_smul, Units.val_one]
  · have e1 : ι.toRingHom ((κ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (χ.val w : ℂ) := by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inl hwl) hu hA hσ, inv_inv]
      exact ι.apply_symm_apply _
    rw [tw_val]
    exact scale_sat ι.toRingHom _ _ B _ _ e1 _ _ ((hw A hA).2 σ hσ) hpB hpS

end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform

open UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twNew :
    Af.HypothesesH → GlobalTheory.Ord2.TwNewQ := by
  intro P l _ Ω _ _ _ ι e W _ he hA M φ hM hφ
  obtain ⟨f, M', φ', hM', hφ', hf⟩ := hA.modular
  have hMM : 1 ≤ M * M' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hκ : KillsMu (M * M') (φ * φ'⁻¹) := fun s hs => by
    have h1 : φ s = 1 := hφ s fun ζ hζ => hs ζ (by rw [pow_mul, hζ, one_pow])
    have h2 : φ' s = 1 := hφ' s fun ζ hζ => hs ζ (by rw [mul_comm, pow_mul, hζ, one_pow])
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, one_mul]
  obtain ⟨g, hg⟩ := twist_att P (by omega) f ι _ hf (φ * φ'⁻¹) hMM hκ
  refine ⟨g, ?_⟩
  convert hg using 1
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul]
  congr 2
  rw [mul_comm (φ s) (φ' s)⁻¹, mul_assoc, ← mul_assoc (φ s), mul_comm _ (φ' s), inv_mul_cancel_left, mul_comm]
