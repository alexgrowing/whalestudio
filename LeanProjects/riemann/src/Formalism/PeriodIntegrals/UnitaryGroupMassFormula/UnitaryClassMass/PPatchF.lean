import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.AlgebraMapIntIntAf

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Eps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adT (T : Set (HeightOneSpectrum (𝓞 F))) : AF F := (show Ainf F × Af F from ((0 : Ainf F), evT T))

theorem adT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : adT T * adT T = adT T := by
  show ((0 : Ainf F), evT T) * ((0 : Ainf F), evT T) = ((0 : Ainf F), evT T)
  exact Prod.ext (mul_zero _) (evT_mul_of_subset (subset_refl T))

variable (E) in

def epsT (T : Set (HeightOneSpectrum (𝓞 F))) : AF F ⊗[F] E := adT T ⊗ₜ[F] (1 : E)

theorem epsT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : epsT E T * epsT E T = epsT E T := by
  unfold epsT
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, adT_idem]

theorem finE_epsT (T : Set (HeightOneSpectrum (𝓞 F))) : finE F E (epsT E T) = evT T ⊗ₜ[F] (1 : E) := by
  unfold epsT
  rw [finE, Algebra.TensorProduct.map_tmul]
  rfl

theorem finE_one_sub_epsT (T : Set (HeightOneSpectrum (𝓞 F))) :
    finE F E (1 - epsT E T) = evT Tᶜ ⊗ₜ[F] (1 : E) := by
  rw [map_sub, map_one, finE_epsT, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
  congr 1
  rw [← evT_compl Tᶜ, compl_compl]

theorem sigR_epsT (σ : E →ₐ[F] E) (T : Set (HeightOneSpectrum (𝓞 F))) : PI.UJClassFin.sigR (AF F) σ (epsT E T) = epsT E T := by
  unfold epsT PI.UJClassFin.sigR
  simp [Algebra.TensorProduct.map_tmul]

end Eps

theorem floc_gmap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (v : HeightOneSpectrum (𝓞 F)) (u : V ≃ₗ[E] V) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Floc v (gmap u L) ↔ u.symm x ∈ Floc v L := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [mem_gmap_iff] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨s, hs, ?_⟩
    rw [← equiv_smul_O u.symm, ← hyx]
    simpa using hy
  · rintro ⟨s, hs, hsx⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    refine ⟨_, hsx, ?_⟩
    rw [equiv_smul_O u, LinearEquiv.apply_symm_apply]

theorem local_patching : PatchF := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hL hsat γ T
  classical
  let ε : AF F ⊗[F] E := epsT E (T : Set (HeightOneSpectrum (𝓞 F)))
  have hε : ε * ε = ε := epsT_idem _
  let e : Bool → AF F ⊗[F] E := fun i => if i then ε else 1 - ε
  have he : ∀ i j, e i * e j = if i = j then e i else 0 := by
    intro i j
    cases i <;> cases j <;> simp only [e, if_true, if_false, Bool.false_eq_true, ↓reduceIte]
    · calc (1 - ε) * (1 - ε) = 1 - ε - (ε - ε * ε) := by ring
        _ = 1 - ε := by rw [hε, sub_self, sub_zero]
    · calc (1 - ε) * ε = ε - ε * ε := by ring
        _ = 0 := by rw [hε, sub_self]
    · calc ε * (1 - ε) = ε - ε * ε := by ring
        _ = 0 := by rw [hε, sub_self]
    · exact hε
  have hs : ∑ i, e i = 1 := by
    rw [Fintype.sum_bool]
    simp only [e, if_true, Bool.false_eq_true, ↓reduceIte]
    abel
  have hσe : ∀ i, PI.UJClassFin.sigR (AF F) σ (e i) = e i := by
    intro i
    cases i <;> simp only [e, if_true, Bool.false_eq_true, ↓reduceIte]
    · rw [map_sub, map_one, sigR_epsT]
    · exact sigR_epsT σ _
  let γB : Bool → GL (Fin M) E := fun i => if i then (γ : GL (Fin M) E) else 1
  have hγB : ∀ i, γB i ∈ PI.UJClassFin.UJ (σ : E →+* E) J := by
    intro i
    cases i
    · exact (PI.UJClassFin.UJ (σ : E →+* E) J).one_mem
    · exact γ.2
  have hf : ∀ i j, finE F E (e i) * finE F E (e j) = if i = j then finE F E (e i) else 0 := by
    intro i j
    rw [← map_mul, he i j]
    split_ifs <;> simp
  have hfe : ∀ i, finE F E (e i) = evT (if i then (T : Set (HeightOneSpectrum (𝓞 F))) else (↑T)ᶜ) ⊗ₜ[F] (1 : E) := by
    intro i
    cases i
    · exact finE_one_sub_epsT _
    · exact finE_epsT _
  have hO : ∀ i, finE F E (e i) ∈ Oh F E := by
    intro i
    rw [hfe i]
    exact tmul_mem_Oh (evT_int _) isIntegral_one
  refine ⟨patchHA σ J e he hs hσe γB hγB, ?_⟩
  ext x
  rw [Set.mem_setOf_eq]
  show (finMat σ J (patchHA σ J e he hs hσe γB hγB)⁻¹).mulVec
      (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (b.equivFun x)) ∈ latHat F E (crdOf b L0) ↔ _
  rw [patch_mulVec, latHat_split (crdOf b L0) (crd_int_smul b L0) _ hf hO, Bool.forall_bool]
  have hterm : ∀ i, (((γB i)⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun x) =
      b.equivFun ((linOf b (γB i)).symm x) := fun i => (equivFun_linOf_symm b (γB i) x).symm
  rw [hterm, hterm, hfe, hfe]
  have e0 : (linOf b (γB false)).symm x = x := linOf_one_symm_apply b x
  rw [e0, flocHat b L0 hL hsat, flocHat b L0 hL hsat]
  have e1 : γB true = (γ : GL (Fin M) E) := rfl
  rw [e1]
  simp only [if_true, Bool.false_eq_true, ↓reduceIte, Set.mem_compl_iff, Finset.mem_coe]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun v hv => (floc_gmap v _ L0 x).2 (h1 v hv), h0⟩
  · rintro ⟨h1, h0⟩
    exact ⟨h0, fun v hv => (floc_gmap v _ L0 x).1 (h1 v hv)⟩

theorem surjStep_of_herm (hH : HermApprox) (hO : LSOne) : SurjStep :=
  surjStep_of_patchF_herm local_patching hH hO

end PI.UnitaryGroupMassFormula.UJClassMass

end
