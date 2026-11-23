import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_common_eigenvector_of_charpoly_split_characters :
    ∀ {Γ I W : Type} [Group Γ] [Group I] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (i : I →* Γ) (Φ : Γ) (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ), (∀ σ s, ∃ t, σ * i s = i t * σ) → (∀ σ, ∃ (m : ℤ) (s : I), σ = Φ ^ m * i s) → (Set.range fun s => ρ (i s)).Finite → (∀ σ, (ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ))) → ∀ j, ∃ y : W, y ≠ 0 ∧ ∀ σ, ρ σ y = (μ j σ : ℂ) • y := by
  intro Γ I W _ _ _ _ _ n i Φ ρ μ hnorm hgen hfin hchar j
  classical
  have htr : ∀ σ, LinearMap.trace ℂ W (ρ σ) = ∑ k, (μ k σ : ℂ) := by
    intro σ
    rw [LinearMap.trace_eq_matrix_trace ℂ (Module.Free.chooseBasis ℂ W),
      Matrix.trace_eq_neg_charpoly_nextCoeff, LinearMap.charpoly_toMatrix, hchar,
      Polynomial.prod_X_sub_C_nextCoeff, neg_neg]
  have heig : ∀ σ k, (ρ σ).HasEigenvalue (μ k σ : ℂ) := by
    intro σ k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  let φ : I →* (Module.End ℂ W)ˣ := (ρ.toHomUnits).comp i
  have hφ : ∀ s, ((φ s : (Module.End ℂ W)ˣ) : Module.End ℂ W) = ρ (i s) := fun s => rfl
  have hker : ∀ k, φ.ker ≤ ((μ k).comp i).ker := by
    intro k s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have h1 : ρ (i s) = 1 := by rw [← hφ, hs]; rfl
    obtain ⟨v, hv⟩ := (heig (i s) k).exists_hasEigenvector
    have hv1 := hv.apply_eq_smul
    rw [h1, Module.End.one_apply] at hv1
    have h2 : ((μ k (i s) : ℂ) - 1) • v = 0 := by rw [sub_smul, one_smul, ← hv1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · apply Units.ext
      simp only [MonoidHom.comp_apply, Units.val_one]
      exact sub_eq_zero.mp h
    · exact absurd h hv.2
  have hfinU : (Set.range φ).Finite := by
    refine (Set.Finite.preimage (Function.Injective.injOn (fun a b h => Units.ext h)) hfin).subset ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hr : ∀ q : I ⧸ φ.ker, QuotientGroup.kerLift φ q ∈ Set.range φ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨s, (QuotientGroup.kerLift_mk φ s).symm⟩
  haveI : Finite (I ⧸ φ.ker) := by
    haveI := hfinU.to_subtype
    exact Finite.of_injective (fun q => (⟨_, hr q⟩ : Set.range φ))
      (fun a b hab => QuotientGroup.kerLift_injective φ (congrArg Subtype.val hab))
  letI : Fintype (I ⧸ φ.ker) := Fintype.ofFinite _
  let R : I ⧸ φ.ker →* Module.End ℂ W := (Units.coeHom (Module.End ℂ W)).comp (QuotientGroup.kerLift φ)
  let c : Fin n → (I ⧸ φ.ker →* ℂˣ) := fun k => QuotientGroup.lift φ.ker ((μ k).comp i) (hker k)
  have hR : ∀ s : I, R (s : I ⧸ φ.ker) = ρ (i s) := fun s => rfl
  have hc : ∀ k (s : I), c k (s : I ⧸ φ.ker) = μ k (i s) := fun k s => rfl
  let E : Submodule ℂ W := ⨅ s, (ρ (i s)).eigenspace (μ j (i s) : ℂ)
  have hmemE : ∀ y, y ∈ E ↔ ∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y := by
    intro y
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hEinv : ∀ y ∈ E, ρ Φ y ∈ E := by
    intro y hy
    rw [hmemE] at hy ⊢
    intro s
    obtain ⟨t, ht⟩ := hnorm Φ⁻¹ s
    have e1 : i s * Φ = Φ * i t := by
      calc i s * Φ = Φ * (Φ⁻¹ * i s) * Φ := by group
        _ = Φ * (i t * Φ⁻¹) * Φ := by rw [ht]
        _ = Φ * i t := by group
    have e2 : μ j (i s) = μ j (i t) := by
      have h3 := congrArg (μ j) e1
      simp only [map_mul] at h3
      rw [mul_comm (μ j Φ)] at h3
      exact mul_right_cancel h3
    calc ρ (i s) (ρ Φ y) = ρ (i s * Φ) y := by rw [map_mul]; rfl
      _ = ρ (Φ * i t) y := by rw [e1]
      _ = ρ Φ (ρ (i t) y) := by rw [map_mul]; rfl
      _ = (μ j (i s) : ℂ) • ρ Φ y := by rw [hy t, map_smul, e2]
  have hmain : ∃ y ∈ E, y ≠ 0 ∧ ρ Φ y = (μ j Φ : ℂ) • y := by
    by_contra hno
    push_neg at hno
    let A : Module.End ℂ E := (ρ Φ).restrict hEinv
    let p := LinearMap.charpoly A
    have hp : p.eval (μ j Φ : ℂ) ≠ 0 := by
      intro h0
      have hA : A.HasEigenvalue (μ j Φ : ℂ) := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr h0
      obtain ⟨v, hv⟩ := hA.exists_hasEigenvector
      have hv0 : (v : W) ≠ 0 := by
        intro h
        apply hv.2
        exact Subtype.ext h
      apply hno v v.2 hv0
      have h5 := congrArg Subtype.val hv.apply_eq_smul
      simpa [A] using h5
    let S := Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) ≠ μ j Φ)
    let h := ∏ k ∈ S, (Polynomial.X - Polynomial.C (μ k Φ : ℂ))
    let f := h * p
    have key : ∀ y (hy : y ∈ E), Polynomial.aeval (ρ Φ) p y = ((Polynomial.aeval A p) ⟨y, hy⟩ : W) := by
      intro y hy
      rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
      simp [A, Module.End.pow_restrict, LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Module.End.pow_restrict]
      rfl
    have hfE : ∀ y ∈ E, Polynomial.aeval (ρ Φ) f y = 0 := by
      intro y hy
      rw [Polynomial.aeval_mul, Module.End.mul_apply, key y hy, LinearMap.aeval_self_charpoly]
      simp
    let P : Module.End ℂ W := ∑ q : I ⧸ φ.ker, (((c j q)⁻¹ : ℂˣ) : ℂ) • R q
    have hRP : ∀ a, R a * P = ((c j a : ℂˣ) : ℂ) • P := by
      intro a
      simp only [P, Finset.mul_sum, mul_smul_comm, ← map_mul, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun q => ?_)
      simp only [Equiv.coe_mulLeft, smul_smul, map_mul]
      congr 1
      rw [← Units.val_mul, _root_.mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
    have hPE : ∀ w, P w ∈ E := by
      intro w
      rw [hmemE]
      intro s
      rw [← hR s, ← Module.End.mul_apply, hRP, LinearMap.smul_apply, hc]
    have hfP : Polynomial.aeval (ρ Φ) f * P = 0 := by
      apply LinearMap.ext
      intro w
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      exact hfE _ (hPE w)
    have htrq : ∀ s : I, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * ρ (i s)) =
        ∑ k, f.eval (μ k Φ : ℂ) * (μ k (i s) : ℂ) := by
      intro s
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul, map_sum]
      simp_rw [smul_mul_assoc, map_smul, ← map_pow, ← map_mul, htr]
      simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, Polynomial.eval_eq_sum_range,
        Finset.sum_mul, Finset.mul_sum, smul_eq_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun m _ => by ring))
    have hq : ∀ q, LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * R q) =
        ∑ k, f.eval (μ k Φ : ℂ) * (c k q : ℂ) := by
      intro q
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hR, htrq]
      rfl
    have htot : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) =
        ∑ k, f.eval (μ k Φ : ℂ) * ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) := by
      simp only [P, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, hq]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun q _ => by ring))
    have hψ : ∀ k, ∑ q : I ⧸ φ.ker, (((c k q : ℂˣ) : ℂ) * (((c j q)⁻¹ : ℂˣ) : ℂ)) =
        ((if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0 : ℕ) : ℂ) := by
      intro k
      rw [← sum_hom_units]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp [div_eq_mul_inv]
    have hzero : ∀ k, (μ k Φ : ℂ) ≠ μ j Φ → f.eval (μ k Φ : ℂ) = 0 := by
      intro k hk
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (i := k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩) (by simp), zero_mul]
    have hfl : f.eval (μ j Φ : ℂ) ≠ 0 := by
      simp only [f, Polynomial.eval_mul, h, Polynomial.eval_prod]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)) hp
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hk).2)
    let N : ℕ := ∑ k ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ),
      (if (Units.coeHom ℂ).comp (c k / c j) = 1 then Fintype.card (I ⧸ φ.ker) else 0)
    have hN : N ≠ 0 := by
      have hj : j ∈ Finset.univ.filter (fun k : Fin n => (μ k Φ : ℂ) = μ j Φ) := by simp
      have h7 : (Units.coeHom ℂ).comp (c j / c j) = 1 := by simp
      intro h8
      have h9 := (Finset.sum_eq_zero_iff.mp h8) j hj
      rw [if_pos h7] at h9
      exact Fintype.card_ne_zero h9
    have heq : LinearMap.trace ℂ W (Polynomial.aeval (ρ Φ) f * P) = f.eval (μ j Φ : ℂ) * N := by
      rw [htot]
      simp only [hψ, N, Nat.cast_sum, Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : (μ k Φ : ℂ) = μ j Φ
      · rw [if_pos hk, hk]
      · rw [if_neg hk, hzero k hk, zero_mul]
    rw [hfP, map_zero] at heq
    exact mul_ne_zero hfl (Nat.cast_ne_zero.mpr hN) heq.symm
  obtain ⟨y, hyE, hy0, hyΦ⟩ := hmain
  refine ⟨y, hy0, ?_⟩
  let G : Subgroup Γ :=
    { carrier := {σ | ρ σ y = (μ j σ : ℂ) • y}
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) y = (μ j (a * b) : ℂ) • y
        rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, map_mul, Units.val_mul, mul_comm]
      one_mem' := by
        show ρ 1 y = (μ j 1 : ℂ) • y
        simp
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ y = (μ j a⁻¹ : ℂ) • y
        have h4 : y = ρ a⁻¹ (ρ a y) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [ha, map_smul] at h4
        rw [map_inv (μ j), Units.val_inv_eq_inv_val]
        calc ρ a⁻¹ y = (μ j a : ℂ)⁻¹ • ((μ j a : ℂ) • ρ a⁻¹ y) := by
              rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
          _ = (μ j a : ℂ)⁻¹ • y := by rw [← h4] }
  intro σ
  obtain ⟨m, s, rfl⟩ := hgen σ
  have h1 : Φ ∈ G := hyΦ
  have h2 : i s ∈ G := (hmemE y).1 hyE s
  exact G.mul_mem (G.zpow_mem h1 m) h2
