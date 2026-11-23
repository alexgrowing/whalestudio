import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_kstable_fin (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V0 : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V0) (hVK : IsKStableSub ε E V0) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : D} (hv : v ∈ V0) : σ k (v : H) ∈ V0.map D.subtype := by
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk
  have hE := hD.glRep
  have hv0 : v ∈ layer ε E V0 0 := hv
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_inK hE hVK hVf hZ 0
  have hs : Summable fun m : ℕ => C ^ m * ‖v‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_right ‖v‖
    refine this.congr fun m => ?_
    simp
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv0 m) 0 1 hs
  rw [exp_zero_smul, hσ.1.1] at hsum
  simp only [Complex.ofReal_one, one_smul, ContinuousLinearMap.one_apply] at hsum
  have : FiniteDimensional ℂ (V0.map D.subtype) := Module.Finite.map _ _
  have hcl : IsClosed ((V0.map D.subtype : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
  refine hcl.mem_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact Submodule.mem_map_of_mem (actM_pow_mem_layer_of_inK hE hVK hZ hv0 m)

theorem tf_tensGrp_kDiag (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ k f = kDiag dual σ k f := by
  have hu : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hu
  funext c
  simp only [tensGrp, kDiag, hinv, Matrix.conjTranspose_apply]

theorem tf_kirr_map {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    {E₁ : Fin n → Fin n → Module.End ℂ M} {E₂ : Fin n → Fin n → Module.End ℂ M'} {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E₁ Λ V) (Ψ : M →ₗ[ℂ] M')
    (hΨ : ∀ a b, ∀ x ∈ V, Ψ (E₁ a b x) = E₂ a b (Ψ x)) (hinj : ∀ x ∈ V, Ψ x = 0 → x = 0) :
    IsKIrrHW ε E₂ Λ (V.map Ψ) := by
  have := hV.1
  refine ⟨Module.Finite.map _ _, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨x, hx, rfl⟩
    exact ⟨E₁ a b x, hV.2.1 a b hab x hx, hΨ a b x hx⟩
  · intro S' hS' hst
    have hT : IsKStableSub ε E₁ (S'.comap Ψ ⊓ V) := by
      rintro a b hab x ⟨hx1, hx2⟩
      refine ⟨?_, hV.2.1 a b hab x hx2⟩
      show Ψ (E₁ a b x) ∈ S'
      rw [hΨ a b x hx2]
      exact hst a b hab _ hx1
    rcases hV.2.2.1 _ inf_le_right hT with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨x, hx, rfl⟩ := hS' hs
      have hx0 : x ∈ S'.comap Ψ ⊓ V := ⟨hs, hx⟩
      rw [h, Submodule.mem_bot] at hx0
      rw [hx0, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ S'.comap Ψ ⊓ V := by rw [h]; exact hx
      exact hx'.1
  · obtain ⟨w, hwV, hw0, hw1, hw2⟩ := hV.2.2.2
    refine ⟨Ψ w, ⟨w, hwV, rfl⟩, fun h => hw0 (hinj w hwV h), fun a => ?_, fun a b hab h => ?_⟩
    · rw [← hΨ a a w hwV, hw1 a, map_smul]
    · rw [← hΨ a b w hwV, hw2 a b hab h, map_zero]

theorem tf_kfin_tens (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ f ∈ W ∧ W ≤ tensSub (genSub E V) ∧
      ∀ k ∈ Kset ε, ∀ w ∈ W, ∃ w' ∈ W,
        (fun c => ((w' c : D) : H)) = kDiag dual σ k (fun c => ((w c : D) : H)) := by
  have hE := hD.glRep
  have hmono : Monotone (layer ε E V) := fun k l hkl => layer_mono hkl
  have hlay : ∀ c, ∃ m, f c ∈ layer ε E V m := fun c => by
    have h1 := (tset_mem.1 hf) c
    rw [genSub_eq_iSup_layer hE hVk] at h1
    exact (Submodule.mem_iSup_of_directed _ hmono.directed_le).1 h1
  choose m hm using hlay
  set M := Finset.univ.sup m with hM
  have hfM : ∀ c, f c ∈ layer ε E V M := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hLf : FiniteDimensional ℂ (layer ε E V M) := finiteDimensional_layer hVf M
  have hLk : IsKStableSub ε E (layer ε E V M) := layer_kStable hE hVk M
  refine ⟨tensSub (layer ε E V M), ?_, tset_mem.2 hfM,
    fun w hw => tset_mem.2 fun c => layer_le_genSub M ((tset_mem.1 hw) c), ?_⟩
  · exact Module.Finite.of_injective (LinearMap.pi fun c => LinearMap.codRestrict (layer ε E V M)
      ((LinearMap.proj c : (Fin n → D) →ₗ[ℂ] D) ∘ₗ (tensSub (layer ε E V M)).subtype) fun f => tset_mem.mp f.2 c)
      (fun f f' h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  · intro k hk w hw
    have hu : ∀ d, ∃ u ∈ layer ε E V M, (u : H) = σ k ((w d : D) : H) := fun d => by
      obtain ⟨u, hu, e⟩ := tf_kstable_fin hσ hD hLf hLk hk ((tset_mem.1 hw) d)
      exact ⟨u, hu, e⟩
    choose u hu hue using hu
    refine ⟨fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • u d,
      tset_mem.2 fun c => Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hu d), ?_⟩
    funext c
    simp only [kDiag, Submodule.coe_sum, Submodule.coe_smul, hue]

section Datum

variable [CompleteSpace H]

theorem tf_phi (dual : Bool) {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {y : D} (hy : y ∈ genSub E V) :
    ∃ Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε),
      (∀ f, ((Φ f : smD ε (tfRdiag ε)) : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H))) ∧
      ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
        Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := by
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _
    (tf_single_smul_mem c (tfSgn ε c) hy) f hf
  simp only [tf_coe_single] at hce
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, mul_sum, mul_left_comm]) }
  refine ⟨Φ, fun f => rfl, fun a b f => Subtype.ext (vectorL2_ext fun c => ?_)⟩
  refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
  refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
  exact (hce c f.1 f.2).2.1 a b g hg

end Datum

end ReciprocityTheory.ChartRestriction.DS.G2
