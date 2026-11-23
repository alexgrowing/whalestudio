import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamEquivData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharDataA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Two

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

theorem data_equiv_derived (hgap : StdGap ε lam)
    (hσ₁ : IsURepOn (UJset ε) σ₁) (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v)
    (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v)
    (U : closGen E₁ V₁ ≃ₗᵢ[ℂ] closGen E₂ V₂)
    (hU : ∀ g ∈ UJset ε, ∀ x y : closGen E₁ V₁,
      (x : H₁) = σ₁ g (y : H₁) → ((U x : closGen E₂ V₂) : H₂) = σ₂ g ((U y : closGen E₂ V₂) : H₂))
    (x : D₁) (hx : x ∈ genSub E₁ V₁) (x' : closGen E₁ V₁) (hx' : (x' : H₁) = x) :
    ∃ y : D₂, y ∈ genSub E₂ V₂ ∧ ((U x' : closGen E₂ V₂) : H₂) = y ∧
      ∀ (a b : Fin n) (x'' : closGen E₁ V₁), (x'' : H₁) = ((E₁ a b x : D₁) : H₁) →
        ((U x'' : closGen E₂ V₂) : H₂) = ((E₂ a b y : D₂) : H₂) := by
  classical
  have hst₁ := closGen_stable hgap hσ₁ hD₁ hV₁ hc₁ hVK₁
  have hint : ∀ g ∈ UJset ε, ∀ z ∈ closGen E₁ V₁, ICD.ext U (σ₁ g z) = σ₂ g (ICD.ext U z) :=
    fun g hg z hz => ICD.ext_intertw U hU hst₁ hg hz

  have hV12 : ∀ v ∈ V₁, ∃ w ∈ V₂, (w : H₂) = ICD.ext U (v : H₁) := by
    have hK := data_isKTypeOf hgap hσ₁ hD₁ hV₁ hc₁ hVK₁
    have hle : V₁.map D₁.subtype ≤ closGen E₁ V₁ := by
      rintro _ ⟨v, hv, rfl⟩
      exact ICD.mem_closGen (ICD.le_gen E₁ V₁ hv)
    have hT := ICD.ktype_map (σ₂ := σ₂) (closGen E₁ V₁) (ICD.ext U : H₁ →ₗ[ℂ] H₂)
      (fun z hz w hw h => ICD.ext_inj U hz hw h)
      (fun g hg z hz => hint g (smd_inUJ_of_Kset hg) z hz)
      (fun g hg z hz => hst₁ g (smd_inUJ_of_Kset hg) z hz) hle hK
    have hS2 : (V₁.map D₁.subtype).map (ICD.ext U : H₁ →ₗ[ℂ] H₂) ≤ closGen E₂ V₂ := by
      rintro _ ⟨z, -, rfl⟩
      exact ICD.ext_mem U z
    have heq := data_lowK_eq hgap hσ₂ hD₂ hV₂ hc₂ hVK₂ _ hS2 hT
    intro v hv
    have hm : (ICD.ext U : H₁ →ₗ[ℂ] H₂) (D₁.subtype v) ∈
        (V₁.map D₁.subtype).map (ICD.ext U : H₁ →ₗ[ℂ] H₂) :=
      Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hv)
    rw [heq] at hm
    obtain ⟨w, hw, e⟩ := hm
    exact ⟨w, hw, e⟩

  let P : Submodule ℂ D₁ :=
    { carrier := {z | z ∈ genSub E₁ V₁ ∧ ∃ y : D₂, y ∈ genSub E₂ V₂ ∧ ICD.ext U (z : H₁) = (y : H₂)}
      add_mem' := by
        rintro a b ⟨ha, ya, hya, ea⟩ ⟨hb, yb, hyb, eb⟩
        exact ⟨add_mem ha hb, ya + yb, add_mem hya hyb, by simp [ea, eb]⟩
      zero_mem' := ⟨zero_mem _, 0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ya, hya, ea⟩
        exact ⟨Submodule.smul_mem _ c ha, c • ya, Submodule.smul_mem _ c hya, by simp [ea]⟩ }
  have hle : genSub E₁ V₁ ≤ P := by
    refine ICD.gen_le (fun v hv => ?_) (fun a b z hz => ?_)
    · obtain ⟨w, hw, e⟩ := hV12 v hv
      exact ⟨ICD.le_gen E₁ V₁ hv, w, ICD.le_gen E₂ V₂ hw, e.symm⟩
    · obtain ⟨hz1, y, hy, e⟩ := hz
      exact ⟨ICD.gen_stable hz1 a b, E₂ a b y, ICD.gen_stable hy a b,
        ICD.map_E hD₁ hD₂ (ICD.ext U) (closGen E₁ V₁) hint z (ICD.mem_closGen hz1) y e a b⟩
  obtain ⟨-, y, hy, e⟩ := hle hx
  refine ⟨y, hy, ?_, fun a b x'' hx'' => ?_⟩
  · rw [← ICD.ext_apply', hx', e]
  · rw [← ICD.ext_apply', hx'',
      ICD.map_E hD₁ hD₂ (ICD.ext U) (closGen E₁ V₁) hint x (ICD.mem_closGen hx) y e a b]

end Two

namespace ICD

theorem qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => f (E a b)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod,
    List.map_ofFn, Function.comp_def, map_add, apply_ite (⇑f), map_zero, AlgHom.commutes]

theorem qdet_mem {B : Type*} [Ring B] [Algebra ℂ B] (S : Subalgebra ℂ B) (F : Fin n → Fin n → B)
    (hF : ∀ a b, F a b ∈ S) (u : ℂ) : Formalism.REAL.qdet F u ∈ S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine S.sum_mem fun τ _ => S.mul_mem ?_ (list_prod_mem fun z hz => ?_)
  · rw [← zsmul_one]
    exact zsmul_mem S.one_mem _
  · obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hz
    unfold Formalism.REAL.Tm
    refine S.add_mem ?_ (hF _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

def relAlg (R : M₁ → M₂ → Prop) (hadd : ∀ x y x' y', R x y → R x' y' → R (x + x') (y + y'))
    (hsmul : ∀ (c : ℂ) x y, R x y → R (c • x) (c • y)) :
    Subalgebra ℂ (Module.End ℂ M₁ × Module.End ℂ M₂) where
  carrier := {p | ∀ x y, R x y → R (p.1 x) (p.2 y)}
  mul_mem' := fun ha hb x y h => ha _ _ (hb x y h)
  add_mem' := fun ha hb x y h => hadd _ _ _ _ (ha x y h) (hb x y h)
  algebraMap_mem' := fun c x y h => by
    simp only [Prod.algebraMap_apply, Module.algebraMap_end_apply]
    exact hsmul c x y h

end ICD

section One

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
  {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem ICD.transfer (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hV0 : V ≠ ⊥) (hP : IsPsiFor ε lam T Ψ)
    {p₁ : Module.End ℂ D} {p₂ : Module.End ℂ (smD ε (rreg ε))}
    (hp : (p₁, p₂) ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)))
    (c : ℂ) (hc2 : ∀ v₀ : T.V, v₀ ≠ 0 → ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), p₂ y = c • y)
    (x : D) (hx : x ∈ genSub E V) : p₁ x = c • x := by
  classical
  have hv₀ : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨U, hU⟩ := sigLam_equiv_data hgap hP hv₀ hσ hD hV hc hVK hV0
  have hσ₂ := rreg_isURepOn ε
  have hD₂ := isDerivedOn_smE hσ₂
  have hU' : ∀ g ∈ UJset ε, ∀ x y : closGen E V,
      (x : H) = σ g (y : H) → ((U.symm x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g ((U.symm y : Hlam ε Ψ T.w) : L2 ε) := by
    intro g hg x y hxy
    have h1 := hU g hg (U.symm y)
    rw [U.apply_symm_apply] at h1
    have : x = U (sigLam ε Ψ T.w g (U.symm y)) := Subtype.ext (hxy.trans h1.symm)
    rw [this, U.symm_apply_apply, sigLam_coe hgap hP hv₀ hg]
  have hst := closGen_stable hgap hσ hD hV hc hVK
  have hint : ∀ g ∈ UJset ε, ∀ z ∈ closGen E V, ICD.ext U.symm (σ g z) = rreg ε g (ICD.ext U.symm z) :=
    fun g hg z hz => ICD.ext_intertw U.symm hU' hst hg hz
  let R : D → smD ε (rreg ε) → Prop := fun x y =>
    x ∈ genSub E V ∧ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) ∧ ICD.ext U.symm (x : H) = (y : L2 ε)
  let S := ICD.relAlg R
    (fun x y x' y' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩ => ⟨add_mem h1 h1', add_mem h2 h2', by simp [h3, h3']⟩)
    (fun c x y ⟨h1, h2, h3⟩ => ⟨Submodule.smul_mem _ c h1, Submodule.smul_mem _ c h2, by simp [h3]⟩)
  have hgen : Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show ∀ x y, R x y → R (E a b x) (smE ε (rreg ε) a b y)
    rintro x y ⟨h1, h2, h3⟩
    exact ⟨ICD.gen_stable h1 a b, ICD.gen_stable h2 a b,
      ICD.map_E hD hD₂ (ICD.ext U.symm) (closGen E V) hint x (ICD.mem_closGen h1) y h3 a b⟩
  obtain ⟨y, hy, hxy, -⟩ := data_equiv_derived hgap hσ hD hV hc hVK hσ₂ hD₂ (datumV_isKIrrHW hP hv₀)
    (datumV_casimir hP T.w) (datumV_kStable hP T.w) U.symm hU' x hx ⟨x, ICD.mem_closGen hx⟩ rfl
  have hR : R x y := ⟨hx, hy, by rw [ICD.ext_apply U.symm _ (ICD.mem_closGen hx)]; exact hxy⟩
  have hpS : ∀ x y, R x y → R (p₁ x) (p₂ y) := hgen hp
  obtain ⟨h1, -, h3⟩ := hpS x y hR
  refine Subtype.ext (ICD.ext_inj U.symm (ICD.mem_closGen h1)
    (ICD.mem_closGen (Submodule.smul_mem _ c hx)) ?_)
  rw [h3, hc2 T.w hv₀ y hy, Submodule.coe_smul, Submodule.coe_smul, map_smul, hR.2.2]

theorem ICD.pair_mem_adjoin {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) (a b : Fin n) :
    (E₁ a b, E₂ a b) ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E₁ ab.1 ab.2, E₂ ab.1 ab.2)) :=
  Algebra.subset_adjoin ⟨(a, b), rfl⟩

theorem capelli_data (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hV0 : V ≠ ⊥) (hP : IsPsiFor ε lam T Ψ)
    (hcap : ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) Ψ g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • Ψ g)
    (Y : ℂ) (x : D) (hx : x ∈ genSub E V) :
    Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) x = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • x := by
  classical
  have hF : ∀ a b, (E a b, smE ε (rreg ε) a b) ∈
      Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)) :=
    ICD.pair_mem_adjoin _ _
  have hm := ICD.qdet_mem _ (fun a b => (E a b, smE ε (rreg ε) a b)) hF (Y + ((n : ℂ) - 1) / 2)
  have h1 := ICD.qdet_map (AlgHom.fst ℂ _ _) (fun a b => (E a b, smE ε (rreg ε) a b)) (Y + ((n : ℂ) - 1) / 2)
  have h2 := ICD.qdet_map (AlgHom.snd ℂ _ _) (fun a b => (E a b, smE ε (rreg ε) a b)) (Y + ((n : ℂ) - 1) / 2)
  simp only [AlgHom.fst_apply, AlgHom.snd_apply] at h1 h2
  have hp : (Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2), Formalism.REAL.qdet (smE ε (rreg ε)) (Y + ((n : ℂ) - 1) / 2)) ∈
      Algebra.adjoin ℂ (Set.range fun ab : Fin n × Fin n => (E ab.1 ab.2, smE ε (rreg ε) ab.1 ab.2)) := by
    rw [← h1, ← h2]
    exact hm
  exact ICD.transfer hgap hσ hD hV hc hVK hV0 hP hp _
    (fun v₀ hv₀ y hy => capelli_sigLam hgap hP hv₀ hcap Y y hy) x hx

end One

end ReciprocityTheory.ChartRestriction.DS
