import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.Div.eigen_line_bilinear

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem bar_bar (σ : E →+* K) : bar (bar σ) = σ := by
  ext x
  simp [bar, IsCMField.complexConj_apply_apply]

theorem inK_ne_zero (hfree : Module.Free O H) {h : H} (hh : h ≠ 0) : inK (O := O) K H h ≠ 0 := by
  have hloc : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).2 (TensorProduct.isBaseChange O H K)
  intro h0
  have h0' : TensorProduct.mk O K H 1 h = 0 := h0
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) _).1 h0'
  rw [Submonoid.smul_def] at ht
  exact hh ((smul_eq_zero.1 ht).resolve_left (nonZeroDivisors.ne_zero t.2))

theorem eq_smul_of_line {ρ : orderC c →+* Module.End O H} {τ : E →+* K} (hline : Module.finrank K (eigK ρ τ) = 1)
    {v : K ⊗[O] H} (hv : v ∈ eigK ρ τ) (hv0 : v ≠ 0) {x : K ⊗[O] H} (hx : x ∈ eigK ρ τ) : ∃ a : K, x = a • v := by
  have hne : (⟨v, hv⟩ : eigK ρ τ) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hline ⟨x, hx⟩
  exact ⟨a, (congrArg Subtype.val ha).symm⟩

theorem lower_apply {ρ : orderC c →+* Module.End O H} {τ : E →+* K} {e f : H} {N : Module.End K (K ⊗[O] H)}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (hline : Module.finrank K (eigK ρ τ) = 1)
    (he : inK (O := O) K H e ∈ eigK ρ τ) (he0 : inK (O := O) K H e ≠ 0) (hN : IsLower ρ τ e f N) (x : K ⊗[O] H) :
    ∃ a : K, N x = a • inK (O := O) K H f := by
  have hx : x ∈ ⨆ σ : E →+* K, eigK ρ σ := by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun x => ∃ a : K, N x = a • inK (O := O) K H f) hx
    ?_ ⟨0, by simp⟩ ?_
  · intro σ y hy
    by_cases hσ : σ = τ
    · subst hσ
      obtain ⟨a, rfl⟩ := eq_smul_of_line hline he he0 hy
      exact ⟨a, by rw [map_smul, hN.1]⟩
    · exact ⟨0, by rw [hN.2 σ hσ y hy, zero_smul]⟩
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb, add_smul]⟩

theorem bilin_zero_of_eig {ρ : orderC c →+* Module.End O H}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (S : LinearMap.BilinForm K (K ⊗[O] H))
    (h : ∀ σ σ' : E →+* K, ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', S x y = 0) (x y : K ⊗[O] H) : S x y = 0 := by
  have hmem : ∀ z : K ⊗[O] H, z ∈ ⨆ σ : E →+* K, eigK ρ σ := fun z => by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun x => ∀ y, S x y = 0) (hmem x)
    ?_ (fun y => by simp) ?_ y
  · intro σ x hx y
    refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun y => S x y = 0) (hmem y)
      (fun σ' y hy => h σ σ' x hx y hy) (by simp) ?_
    intro y y' h1 h2
    rw [map_add, h1, h2, add_zero]
  · intro x x' h1 h2 y
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]

end SlopeTestRemainingChoices

theorem lower_skew_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧ ∀ i j x y, B.baseChange K (N i x) (N j y) = 0 := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ hCM H _ _ ρ Fil B hL hEC e f hG N hN
  obtain ⟨hfree, -, -, hlines, -, -, -, halt, -⟩ := hL
  obtain ⟨hdir, hlat, -, -, horth⟩ := hEC
  have he_mem : ∀ i, inK (O := O) K H (e i) ∈ eigK ρ (φ i) := fun i => by
    have hm : e i ∈ eigLat ρ (φ i) := by rw [(hG i).1]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hf_mem : ∀ i, inK (O := O) K H (f i) ∈ eigK ρ (bar (φ i)) := fun i => by
    have hm : f i ∈ eigLat ρ (bar (φ i)) := by rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact hm
  have he0 : ∀ i, inK (O := O) K H (e i) ≠ 0 := fun i => by
    refine inK_ne_zero hfree fun he => ?_
    obtain ⟨-, ⟨g, hg0, hg⟩, -⟩ := hlat (φ i)
    have hgm : g ∈ O ∙ e i := by rw [← (hG i).1, hg]; exact Submodule.mem_span_singleton_self g
    rw [he, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hgm
    exact hg0 hgm
  have hlow : ∀ i z, ∃ a : K, N i z = a • inK (O := O) K H (f i) := fun i z =>
    lower_apply hdir (hlines (φ i)) (he_mem i) (he0 i) (hN i) z
  have himg : ∀ i z, N i z ∈ eigK ρ (bar (φ i)) := fun i z => by
    obtain ⟨a, ha⟩ := hlow i z
    rw [ha]; exact Submodule.smul_mem _ a (hf_mem i)
  refine ⟨fun i x y => ?_, fun i j x y => ?_⟩
  · let S : LinearMap.BilinForm K (K ⊗[O] H) :=
      (B.baseChange K).compl₁₂ (N i) LinearMap.id + (B.baseChange K).compl₁₂ LinearMap.id (N i)
    have hS : ∀ x y, S x y = B.baseChange K (N i x) y + B.baseChange K x (N i y) := fun x y => rfl
    rw [← hS]
    refine bilin_zero_of_eig hdir S (fun σ σ' x hx y hy => ?_) x y
    rw [hS]
    have t1 : σ' ≠ φ i → B.baseChange K (N i x) y = 0 := fun h =>
      horth (bar (φ i)) σ' (by rwa [bar_bar]) _ (himg i x) y hy
    have t2 : σ ≠ φ i → B.baseChange K x (N i y) = 0 := fun h => by
      refine horth σ (bar (φ i)) (fun h' => h ?_) x hx _ (himg i y)
      have := congrArg bar h'
      rwa [bar_bar, bar_bar, eq_comm] at this
    by_cases h1 : σ = φ i
    · by_cases h2 : σ' = φ i
      · subst h1
        rw [h2] at hy
        obtain ⟨a, rfl⟩ := eq_smul_of_line (hlines _) (he_mem i) (he0 i) hx
        obtain ⟨b, rfl⟩ := eq_smul_of_line (hlines _) (he_mem i) (he0 i) hy
        have key : B.baseChange K (inK (O := O) K H (f i)) (inK (O := O) K H (e i)) +
            B.baseChange K (inK (O := O) K H (e i)) (inK (O := O) K H (f i)) = 0 := by
          simp only [inK, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, mul_one]
          rw [← add_smul, ← LinearMap.IsAlt.neg halt (e i) (f i), neg_add_cancel, zero_smul]
        simp only [map_smul, (hN i).1, LinearMap.smul_apply, smul_eq_mul]
        linear_combination (a * b) * key
      · rw [t1 h2, (hN i).2 σ' h2 y hy, map_zero, add_zero]
    · rw [t2 h1, (hN i).2 σ h1 x hx, map_zero, LinearMap.zero_apply, add_zero]
  · obtain ⟨a, ha⟩ := hlow i x
    obtain ⟨b, hb⟩ := hlow j y
    rw [ha, hb]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      have : B.baseChange K (inK (O := O) K H (f i)) (inK (O := O) K H (f i)) = 0 := by
        simp only [inK, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, halt (f i), zero_smul]
      rw [this, mul_zero, mul_zero]
    · have hne : bar (φ j) ≠ bar (bar (φ i)) := by
        rw [bar_bar]
        intro h
        obtain ⟨k, -, hk⟩ := hCM (φ i)
        exact hij ((hk i (Or.inl rfl)).trans (hk j (Or.inr h.symm)).symm)
      rw [horth (bar (φ i)) (bar (φ j)) hne _ (hf_mem i) _ (hf_mem j), mul_zero, mul_zero]

end GlobalTheory.Div.eigen_line_bilinear
