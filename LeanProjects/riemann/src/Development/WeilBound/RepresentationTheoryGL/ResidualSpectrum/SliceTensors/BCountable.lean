import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableParabolic

noncomputable section

open NumberField MeasureTheory Set
open scoped NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

section Box

variable {ι : Type} [Fintype ι]

variable (K ι) in

def B_lat : AddSubgroup (ι → 𝔸[K]) := (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom ι).range

instance B_countable : Countable (B_lat K ι) := by
  have := GroundTheory.Global.countable_numberField K
  have e : (B_lat K ι : Set (ι → 𝔸[K])) =
      Set.range (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom ι) := AddMonoidHom.coe_range _
  have hc : (B_lat K ι : Set (ι → 𝔸[K])).Countable := e ▸ Set.countable_range _
  exact hc.to_subtype

theorem B_isFD : IsAddFundamentalDomain (B_lat K ι) (Set.univ.pi fun _ : ι => GroundTheory.Global.fundamentalSet K)
    (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K) := by
  classical
  refine IsAddFundamentalDomain.mk'
    (MeasurableSet.univ_pi fun _ => GroundTheory.Global.measurableSet_fundamentalSet K).nullMeasurableSet fun X => ?_
  choose k hk huniq using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)
  refine ⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, ?_, ?_⟩
  · intro p _
    change algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K
    rw [map_neg, neg_add_eq_sub]
    exact hk p
  · rintro ⟨_, ξ, rfl⟩ h
    refine Subtype.ext (funext fun p => ?_)
    have : -ξ p = k p := huniq p (-ξ p) (by
      show X p - algebraMap K 𝔸[K] (-ξ p) ∈ GroundTheory.Global.fundamentalSet K
      have hp : algebraMap K 𝔸[K] (ξ p) + X p ∈ GroundTheory.Global.fundamentalSet K := h p (mem_univ p)
      rwa [map_neg, sub_neg_eq_add, add_comm])
    change algebraMap K 𝔸[K] (ξ p) = algebraMap K 𝔸[K] (-k p)
    rw [← this, neg_neg]

theorem B_translate (f : (ι → 𝔸[K]) → ℂ)
    (hper : ∀ (ξ : ι → K) x, f (fun i => algebraMap K 𝔸[K] (ξ i) + x i) = f x) (c : ι → 𝔸[K]) :
    ∫ x, f (x + c) ∂(Measure.pi fun _ : ι => boxMeasure K) = ∫ x, f x ∂(Measure.pi fun _ : ι => boxMeasure K) := by
  rw [← setIntegral_box_eq, ← setIntegral_box_eq]
  set μ := Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K
  set D := Set.univ.pi fun _ : ι => GroundTheory.Global.fundamentalSet K
  have hD : IsAddFundamentalDomain (B_lat K ι) D μ := B_isFD
  have hf : ∀ (g : B_lat K ι) x, f (g +ᵥ x) = f x := by
    rintro ⟨_, ξ, rfl⟩ x
    exact hper ξ x
  have hD' : IsAddFundamentalDomain (B_lat K ι) ((fun y => y - c) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_sub_right μ c).quasiMeasurePreserving
      (e := id) Function.bijective_id fun g x => by
        change (g +ᵥ x) - c = g +ᵥ (x - c)
        simp only [vadd_eq_add, AddSubgroup.vadd_def]
        abel
  have hmp : MeasurePreserving (fun x : ι → 𝔸[K] => x + c) μ μ := measurePreserving_add_right μ c
  have e1 : (fun x : ι → 𝔸[K] => x + c) ⁻¹' ((fun y => y - c) ⁻¹' D) = D := by
    ext x; simp
  have h2 := hmp.setIntegral_preimage_emb (measurableEmbedding_addRight c) f ((fun y => y - c) ⁻¹' D)
  rw [e1] at h2
  rw [h2]
  exact (hD.setIntegral_eq hD' hf).symm

end Box

section Fubini

variable {ι : Type} [Fintype ι]

theorem B_fubini (P : ι → Prop) [DecidablePred P] (G : (ι → 𝔸[K]) → ℂ) (hG : Continuous G) :
    ∫ x, G x ∂(Measure.pi fun _ : ι => boxMeasure K) =
      ∫ v, ∫ u, G (fun i => if h : P i then u ⟨i, h⟩ else v ⟨i, h⟩)
        ∂(Measure.pi fun _ : {i // P i} => boxMeasure K) ∂(Measure.pi fun _ : {i // ¬ P i} => boxMeasure K) := by
  obtain ⟨e, he⟩ : ∃ e, e = MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔸[K]) P := ⟨_, rfl⟩
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι => boxMeasure K)
      ((Measure.pi fun _ : {i // P i} => boxMeasure K).prod (Measure.pi fun _ : {i // ¬ P i} => boxMeasure K)) :=
    he ▸ measurePreserving_piEquivPiSubtypeProd (fun _ : ι => boxMeasure K) P
  have hsymm : ∀ u v, e.symm (u, v) = fun i => if h : P i then u ⟨i, h⟩ else v ⟨i, h⟩ := by
    intro u v
    subst he
    funext i
    simp [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  have hGi := integrable_box (K := K) (ι := ι) hG
  have hGe : Integrable (G ∘ e.symm)
      ((Measure.pi fun _ : {i // P i} => boxMeasure K).prod (Measure.pi fun _ : {i // ¬ P i} => boxMeasure K)) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hGi
  have e1 : ∫ x, G x ∂(Measure.pi fun _ : ι => boxMeasure K) =
      ∫ z, (G ∘ e.symm) z ∂((Measure.pi fun _ : {i // P i} => boxMeasure K).prod
        (Measure.pi fun _ : {i // ¬ P i} => boxMeasure K)) := by
    rw [← hmp.integral_comp' (G ∘ e.symm)]
    simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  rw [e1, integral_prod_symm _ hGe]
  simp only [Function.comp_apply, hsymm]

theorem B_shear (P : ι → Prop) [DecidablePred P] (f : (ι → 𝔸[K]) → ℂ) (hf : Continuous f)
    (hper : ∀ (ξ : ι → K) x, f (fun i => algebraMap K 𝔸[K] (ξ i) + x i) = f x)
    (ℓ : (ι → 𝔸[K]) → (ι → 𝔸[K])) (hℓc : Continuous ℓ) (hℓ1 : ∀ x i, ¬ P i → ℓ x i = 0)
    (hℓ2 : ∀ x y, (∀ i, ¬ P i → x i = y i) → ℓ x = ℓ y) :
    ∫ x, f (x - ℓ x) ∂(Measure.pi fun _ : ι => boxMeasure K) = ∫ x, f x ∂(Measure.pi fun _ : ι => boxMeasure K) := by
  rw [B_fubini P (fun x => f (x - ℓ x)) (hf.comp (continuous_id.sub hℓc)), B_fubini P f hf]
  congr 1
  funext v
  let J : ({i // P i} → 𝔸[K]) → (ι → 𝔸[K]) := fun u i => if h : P i then u ⟨i, h⟩ else v ⟨i, h⟩
  let c : {i // P i} → 𝔸[K] := fun i => ℓ (J 0) i.1
  have key : ∀ u, J u - ℓ (J u) = J (u + -c) := by
    intro u
    have hl : ℓ (J u) = ℓ (J 0) := hℓ2 _ _ fun i hi => by simp [J, hi]
    funext i
    rw [hl]
    by_cases hi : P i
    · simp [J, hi, c, sub_eq_add_neg]
    · simp [J, hi, hℓ1 _ i hi]
  change ∫ u, f (J u - ℓ (J u)) ∂_ = ∫ u, f (J u) ∂_
  simp_rw [key]
  refine B_translate (fun u => f (J u)) (fun ξ u => ?_) (-c)
  have e : J (fun i => algebraMap K 𝔸[K] (ξ i) + u i) =
      fun i => algebraMap K 𝔸[K] ((fun i => if h : P i then ξ ⟨i, h⟩ else 0) i) + J u i := by
    funext i
    by_cases hi : P i <;> simp [J, hi]
  rw [e, hper]

end Fubini

end PositivityTheory.Rg.Rs.SliceClasses

end
