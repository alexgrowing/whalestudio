import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TsubValInjective

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem ff_cmFock_nonphys {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {j b : Fin n}
    (hjb : ¬(ε j = true ∧ ε b = false)) (f : Fock n) : cmFock j b (ff ε k f) = ff ε k (cmFock j b f) := by
  have hk' : kᴴ ∈ Kset ε := kset_conjTranspose hk
  have hkk : kᴴ * k = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff').1 hk.1
  have hkk' : k * kᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff).1 hk.1
  have hcomm : ∀ g : Fock n, ff ε kᴴ (cmFock j b g) = cmFock j b (ff ε kᴴ g) := by
    intro g
    rw [ff_cmFock_apply hk' j b g, Finset.sum_eq_single (j, b)]
    · simp [adMat, IsPhys, hjb]
    · intro z _ hz
      have : adMat ε kᴴ z (j, b) = 0 := by
        unfold adMat
        by_cases h1 : IsPhys ε z
        · rw [if_pos h1, if_neg (show ¬IsPhys ε (j, b) from hjb)]
        · rw [if_neg h1, if_neg hz]
      rw [this, star_zero, zero_smul]
    · simp
  have h1 : ff ε kᴴ (ff ε k f) = f := by
    rw [← AlgHom.comp_apply, ← ff_mul hk' hk, hkk, ff_one, AlgHom.id_apply]
  have h2 : ∀ g : Fock n, ff ε k (ff ε kᴴ g) = g := by
    intro g
    rw [← AlgHom.comp_apply, ← ff_mul hk hk', hkk', ff_one, AlgHom.id_apply]
  have := congrArg (ff ε k) (hcomm (ff ε k f))
  rw [h1, h2] at this
  exact this

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem cmT_wK (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {j b : Fin n}
    (hjb : ¬(ε j = true ∧ ε b = false)) :
    cmT (N := D) j b ∘ₗ wK hD hk = wK hD hk ∘ₗ cmT j b := by
  apply TensorProduct.ext'
  intro v f
  simp only [LinearMap.comp_apply, wK, cmT, TensorProduct.map_tmul, LinearMap.id_apply,
    AlgHom.toLinearMap_apply, ff_cmFock_nonphys hk hjb]

theorem wK_physSub (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ physicalSubspace ε) : wK hD hk y ∈ physicalSubspace ε := by
  rw [mem_physicalSubspace_iff] at hy ⊢
  intro j b hjb
  have := LinearMap.congr_fun (cmT_wK hD hk hjb) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy j b hjb, map_zero]

theorem sigD_genSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : D} (hv : v ∈ genSub E V) : sigD hD hk v ∈ genSub E V := by
  let T : Submodule ℂ D := (genSub E V).comap (sigD hD hk)
  have hVG : V ≤ genSub E V := fun v hv => Submodule.mem_sInf.2 fun T hT => hT.1 hv
  have hT : genSub E V ≤ T := by
    refine sInf_le ⟨fun x hx => ?_, fun a b x hx => ?_⟩
    · obtain ⟨w, hw, hweq⟩ := hVK k hk x hx
      have : sigD hD hk x = w := Subtype.ext hweq.symm
      show sigD hD hk x ∈ genSub E V
      rw [this]
      exact hVG hw
    · show sigD hD hk (E a b x) ∈ genSub E V
      rw [sigD_E hσ hD hk a b x, actM]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun d _ =>
        Submodule.smul_mem _ _ (generatedSub_stable E V c d hx)
  exact hT hv

theorem wK_tensFock_genSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {y : TensorProduct ℂ D (Fock n)} (hy : y ∈ tensFock (genSub E V)) : wK hD hk y ∈ tensFock (genSub E V) := by
  obtain ⟨x, rfl⟩ := hy
  let sG : genSub E V →ₗ[ℂ] genSub E V := (sigD hD hk).restrict fun v hv => sigD_genSub hσ hD hVK hk hv
  refine ⟨TensorProduct.map sG (ff ε k).toLinearMap x, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  show _ = (TensorProduct.map (sigD hD hk) (ff ε k).toLinearMap ∘ₗ
    TensorProduct.map (genSub E V).subtype LinearMap.id) x
  rw [← TensorProduct.map_comp]
  rfl

theorem wK_KK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    ∀ y ∈ LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε,
      wK hD hk y ∈ LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε := by
  rintro y ⟨⟨hyD, hyT⟩, hyP⟩
  refine ⟨⟨?_, wK_tensFock_genSub hσ hD hVK hk hyT⟩, wK_physSub hD hk hyP⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hyD ⊢
  have h1 := LinearMap.congr_fun (wK_dOp hσ hD hk) y
  have h2 := LinearMap.congr_fun (wK_dOp' hσ hD hk) y
  simp only [Module.End.mul_apply] at h1 h2
  rw [LinearMap.add_apply, ← h1, ← h2, ← map_add, ← LinearMap.add_apply, hyD, map_zero]

theorem kType_clause {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {lam : Fin n → ℝ} {h : ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hanti : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (hthr : thrStar ε < h) (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) :
    ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (_ : FiniteDimensional ℂ W)
      (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)),
      Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T (gaW ε lam) ⊤ ∧
      ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε),
        LinearMap.trace ℂ W (T k : W →ₗ[ℂ] W) =
          LinearMap.trace ℂ (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓
            physicalSubspace ε : Submodule ℂ (TensorProduct ℂ D (Fock n))) ((wK hD hk).restrict (wK_KK hσ hD hVK k hk)) := by
  obtain ⟨z, _, _, _, _, hKK, hirr⟩ := ker_D_eq_kLowSpan hσ hD hV hc hVK hint hanti hgap hthr hp hq
  have hirr' : IsKIrrHW ε (diagE ε (eT E) cpT cmT) (gaW ε lam)
      (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε) := by
    rw [hKK]
    exact hirr
  have : FiniteDimensional ℂ
      (LinearMap.ker (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) ⊓ tensFock (genSub E V) ⊓ physicalSubspace ε :
        Submodule ℂ (TensorProduct ℂ D (Fock n))) := hirr'.1
  exact ⟨TSub _, inferInstance, inferInstance, inferInstance, tOp hD (wK_KK hσ hD hVK),
    tSub_nontrivial hirr', tOp_isURepOn hD _ hσ, tOp_isKTypeOf hD _ hσ hirr', fun k hk => tOp_trace hD _ hk⟩

end ReciprocityTheory.ChartRestriction.DS.TRGap
