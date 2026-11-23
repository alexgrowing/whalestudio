import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARKinv

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Tens

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem sgE_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := M) (n := n)) cmT a b = LinearMap.lTensor M (sgE ε cpFock cmFock a b) := by
  unfold sgE
  split_ifs
  · apply TensorProduct.ext'
    intro m f
    simp [cpT, cmT, LinearMap.sum_apply, TensorProduct.tmul_sum]
  · apply TensorProduct.ext'
    intro m f
    simp [cpT, cmT, LinearMap.sum_apply, TensorProduct.tmul_sum]
  · simp

theorem diagE_eT (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    diagE ε (eT (n := n) E) cpT cmT = fun a b => (TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b) : Module.End ℂ (TensorProduct ℂ M (Fock n))) := by
  funext a b
  rw [diagE, sgE_tensor]
  rfl

theorem casimir_eT (E : Fin n → Fin n → Module.End ℂ M) :
    casimir (eT (n := n) E) = TensorProduct.map (casimir E) LinearMap.id := by
  apply TensorProduct.ext'
  intro m f
  simp [casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]

theorem cfp_map_sub_smul_one (T : Module.End ℂ M) (c : ℂ) :
    TensorProduct.map (T - c • 1) (LinearMap.id : Fock n →ₗ[ℂ] Fock n) =
      TensorProduct.map T LinearMap.id - c • 1 := by
  apply TensorProduct.ext'
  intro m f
  simp [TensorProduct.sub_tmul, TensorProduct.smul_tmul']

theorem rng_lTensor {L : Submodule ℂ M} (g : Module.End ℂ (Fock n)) {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))) :
    TensorProduct.map LinearMap.id g y ∈
      LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
  have h : (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)).comp
      (TensorProduct.map LinearMap.id g) =
      (TensorProduct.map LinearMap.id g).comp
        (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
    apply TensorProduct.ext'
    intro u f
    simp
  exact LinearMap.mem_range.mpr ⟨_, DFunLike.congr_fun h z⟩

theorem rng_map {L L' : Submodule ℂ M} (f : Module.End ℂ M) (hf : ∀ v ∈ L, f v ∈ L')
    {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))) :
    TensorProduct.map f LinearMap.id y ∈
      LinearMap.range (TensorProduct.map L'.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
  have h : (TensorProduct.map L'.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)).comp
      (TensorProduct.map (f.restrict hf) (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) =
      (TensorProduct.map f LinearMap.id).comp
        (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
    apply TensorProduct.ext'
    intro u f'
    simp
  exact LinearMap.mem_range.mpr ⟨_, DFunLike.congr_fun h z⟩

end Tens

theorem casimir_eq_casVal_of_no {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0) :
    ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
  obtain ⟨x, hx, -, hx0, hxK⟩ := lowFock_exists ε hE hmono hV
  have hxr : x ∈ LinearMap.range
      (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := hx
  have key : ∀ (a i : Fin n) (s : ℂ),
      ((if ε a = true then (1 : ℂ) else 0) - (if ε i = true then (1 : ℂ) else 0)) = s →
      ε a ≠ ε i → ∀ v ∈ V, E a i v ∈ layer ε E V 1 ⊓
        LinearMap.ker (zPlus ε E - ((∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) + s) • 1) := by
    intro a i s hs hne v hv
    refine Submodule.mem_inf.mpr ⟨mem_layer_one hv hne, ?_⟩
    rw [LinearMap.mem_ker]
    have h1 := LinearMap.congr_fun (zPlus_comm (ε := ε) hE a i) v
    rw [hs] at h1
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1
    rw [zPlus_V hE hV v hv, map_smul] at h1
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h1, add_smul]
    abel
  have hKHW : ∀ D : Module.End ℂ (TensorProduct ℂ M (Fock n)),
      (∀ a b, ε a = ε b → D * diagE ε (eT E) cpT cmT a b = diagE ε (eT E) cpT cmT a b * D) →
      IsKHWVec ε (fun a b => (TensorProduct.map (E a b) LinearMap.id +
        LinearMap.lTensor M (sgE ε cpFock cmFock a b) : Module.End ℂ (TensorProduct ℂ M (Fock n))))
        (lam - rhoC ε + rhoHol ε) (D x) := by
    intro D hD
    have h : IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) (D x) := by
      refine ⟨fun a => ?_, fun a b hab he => ?_⟩
      · have e := LinearMap.congr_fun (hD a a rfl) x
        simp only [Module.End.mul_apply] at e
        rw [← e, hxK.1 a, map_smul]
      · have e := LinearMap.congr_fun (hD a b he) x
        simp only [Module.End.mul_apply] at e
        rw [← e, hxK.2 a b hab he, map_zero]
    have e := diagE_eT (M := M) (n := n) ε E
    rw [e] at h
    exact h
  have hp : dOp ε (eT E) cpT x = 0 := by
    apply tens_khw_vanish hmono hE hU hV hNo
      (t := (∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) + (-1))
    · intro h
      have : (-1 : ℂ) = 0 := by linear_combination h
      norm_num at this
    · simp only [dOp, LinearMap.sum_apply, Module.End.mul_apply]
      refine Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun a ha => ?_
      have hi' : ε i = true := (Finset.mem_filter.mp hi).2
      have ha' : ε a = false := (Finset.mem_filter.mp ha).2
      exact rng_map (E a i) (key a i (-1) (by simp [hi', ha']) (by simp [hi', ha']))
        (rng_lTensor (cpFock i a) hxr)
    · exact hKHW _ fun a b hab =>
        dOp_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab
  have hm : dOp' ε (eT E) cmT x = 0 := by
    apply tens_khw_vanish hmono hE hU hV hNo
      (t := (∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) + 1)
    · intro h
      have : (1 : ℂ) = 0 := by linear_combination h
      norm_num at this
    · simp only [dOp', LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun a ha => ?_)
      have hi' : ε i = true := (Finset.mem_filter.mp hi).2
      have ha' : ε a = false := (Finset.mem_filter.mp ha).2
      exact rng_map (E i a) (key i a 1 (by simp [hi', ha']) (by simp [hi', ha']))
        (rng_lTensor (cmFock i a) hxr)
    · exact hKHW _ fun a b hab =>
        dOp'_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab
  have hL : ((2 : ℂ) • ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) *
      (dOp ε (eT E) cpT + dOp' ε (eT E) cmT))) x = 0 := by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.add_apply, hp, hm, add_zero,
      map_zero, smul_zero]
  rw [two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε] at hL
  have hK := casimirK_khwVec_compact ε (fun a b h =>
    diagE_compact (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b h) hxK
  have hS : (∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε (eT E) cpT cmT a a) x =
      ((dot (rhoHol ε) (lam - rhoC ε + rhoHol ε) : ℝ) : ℂ) • x := by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hxK.1, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [dot]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply] at hL
  rw [hK, hS] at hL
  have hr : nsq (lam - rhoC ε + rhoHol ε + rhoC ε) - nsq (rhoC ε) -
      2 * dot (rhoHol ε) (lam - rhoC ε + rhoHol ε) = casVal lam := by
    have := khw_real_identity ε (lam - rhoC ε)
    rw [sub_add_cancel] at this
    rw [casVal]
    exact this
  have hC : casimir (eT E) x = ((casVal lam : ℝ) : ℂ) • x := by
    have h2 : casimir (eT E) x =
        ((nsq (lam - rhoC ε + rhoHol ε + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • x -
          (2 : ℂ) • (((dot (rhoHol ε) (lam - rhoC ε + rhoHol ε) : ℝ) : ℂ) • x) := by
      apply eq_of_sub_eq_zero
      rw [← neg_eq_zero, ← hL]
      abel
    rw [h2, ← hr]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_smul, mul_smul]
  rw [casimir_eT] at hC
  have hTw : ∀ w : M, (casimir E - ((casVal lam : ℝ) : ℂ) • 1) w =
      casimir E w - ((casVal lam : ℝ) : ℂ) • w := fun w => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hTx : TensorProduct.map (casimir E - ((casVal lam : ℝ) : ℂ) • 1)
      (LinearMap.id : Fock n →ₗ[ℂ] Fock n) x = 0 := by
    rw [cfp_map_sub_smul_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hC,
      sub_self]
  obtain ⟨v₀, hv₀V, hv₀0, hTv₀⟩ := tens_ker_nontrivial _ hxr hx0 hTx
  have hstab : IsKStableSub ε E (V ⊓ LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • 1)) := by
    intro a b hab w hw
    obtain ⟨hwV, hwK⟩ := Submodule.mem_inf.mp hw
    rw [LinearMap.mem_ker, hTw, sub_eq_zero] at hwK
    refine Submodule.mem_inf.mpr ⟨hV.2.1 a b hab w hwV, ?_⟩
    rw [LinearMap.mem_ker, hTw]
    have hc := LinearMap.congr_fun (casimir_comm hE a b) w
    simp only [Module.End.mul_apply] at hc
    rw [hc, hwK, map_smul, sub_self]
  rcases hV.2.2.1 _ inf_le_left hstab with h | h
  · exfalso
    have hmem : v₀ ∈ V ⊓ LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • 1) :=
      Submodule.mem_inf.mpr ⟨hv₀V, hTv₀⟩
    rw [h] at hmem
    exact hv₀0 ((Submodule.mem_bot ℂ).mp hmem)
  · intro v hv
    have hmem : v ∈ V ⊓ LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • 1) := by
      rw [h]
      exact hv
    have hk := (Submodule.mem_inf.mp hmem).2
    rw [LinearMap.mem_ker, hTw] at hk
    exact sub_eq_zero.mp hk

end ReciprocityTheory.ChartRestriction.DS
