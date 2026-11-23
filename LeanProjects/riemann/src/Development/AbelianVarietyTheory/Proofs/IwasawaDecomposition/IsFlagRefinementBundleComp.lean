import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ}

theorem mat_chain {K₁ K₂ K₃ : Type} [Field K₁] [Field K₂] [Field K₃] (ψ : K₁ →+* K₂) (ψ' : K₂ →+* K₃)
    (A'' : Mat m K₃) (A' : Mat m K₂) (A : Mat m K₁) (hA' : ∀ τ, (A' τ).det ≠ 0) :
    A'' * (A'.map ψ')⁻¹ * (A' * (A.map ψ)⁻¹).map ψ' = A'' * (A.map (ψ'.comp ψ))⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv, mul_assoc, ← mul_assoc (A'.map ψ')⁻¹,
    Mat.inv_mul (fun τ => by rw [Mat.det_map]; exact (map_ne_zero ψ').2 (hA' τ)), one_mul]
  congr 2

def valAt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) : (M.O (q (IsLocalRing.closedPoint K))).toSubring →+* K :=
  RatModel.valHom q _ (RatModel.range_eq_singleton q (IsLocalRing.closedPoint K))

theorem valAt_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) (x : (M.O (q (IsLocalRing.closedPoint K))).toSubring) : M.val q x = valAt M q x := rfl

end GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ} {F : Type} [Field F] {Ω Ω' Ω'' : Type} [Field Ω] [Algebra F Ω] [Field Ω']
  [Algebra F Ω'] [Field Ω''] [Algebra F Ω'']

theorem val_chain {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} (hf' : M'.IsHom M'' φ' f') {K : Type} [Field K] (q : Sp K ⟶ M''.Z)
    {k k' : ι → ℕ} {A'' : Mat m Ω''} {A' : Mat m Ω'} {A : Mat m Ω} (hA' : ∀ τ, (A' τ).det ≠ 0)
    (h2 : Par k' (M''.O (q (IsLocalRing.closedPoint K))).toSubring (A'' * (A'.map φ')⁻¹))
    (h1 : Par k (M'.O (f' (q (IsLocalRing.closedPoint K)))).toSubring (A' * (A.map φ)⁻¹)) :
    (A'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
      (A'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val (q ≫ f')) := by
  have h1' : Par k (M''.O (q (IsLocalRing.closedPoint K))).toSubring ((A' * (A.map φ)⁻¹).map φ') :=
    h1.map (φ' : Ω' →+* Ω'') fun x hx => hf'.map_mem_O hx
  have e := mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A hA'
  have e2 : (A'' * (A.map (φ'.comp φ))⁻¹) = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' := e.symm
  rw [e2, Par.map_mul_of h2 h1' (M''.val q) (valAt M'' q) (valAt_apply M'' q)]
  congr 1
  funext τ
  ext i j
  show M''.val q (φ' ((A' * (A.map φ)⁻¹) τ i j)) = M'.val (q ≫ f') ((A' * (A.map φ)⁻¹) τ i j)
  exact (hf'.val_comp q (IsLocalRing.closedPoint K) ((h1 τ).1 i j)).symm

theorem Refines.comp {M : RatModel F Ω} {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} {k k' k'' : ι → ℕ} {S : Fr M m k}
    {S' : Fr M' m k'} {S'' : Fr M'' m k''} (h1 : Refines S S' φ f) (h2 : Refines S' S'' φ' f') :
    Refines S S'' (φ'.comp φ) (f' ≫ f) where
  le := le_trans h1.le h2.le
  hom := h1.hom.comp h2.hom
  sub z'' A'' hA'' A hA := by
    obtain ⟨A', hA'⟩ := S'.nonempty (f' z'')
    have e : A'' * (A.map (φ'.comp φ))⁻¹ = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' :=
      (mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A (Fr.det_ne hA')).symm
    rw [e]
    exact ((h2.sub z'' A'' hA'' A' hA').mono h1.le le_rfl).mul
      ((h1.sub (f' z'') A' hA' A hA).map (φ' : Ω' →+* Ω'') fun x hx => h2.hom.map_mem_O hx)
  rad z'' g hg := h2.rad z'' (φ g) (h1.rad (f' z'') g hg)
  lifts K _ x A hA h hh := by
    obtain ⟨p', ⟨hp'x, A', hA', hP'⟩, hu1⟩ := h1.lifts K x A hA h hh
    obtain ⟨p'', ⟨hp'', A'', hA'', hP''⟩, hu2⟩ :=
      h2.lifts K p' A' hA' (h * ((A' * (A.map φ)⁻¹).map (M'.val p'))⁻¹) hP'
    have hAx : A ∈ S.S (f (p' (IsLocalRing.closedPoint K))) := by
      have h0 := hA; rw [← hp'x] at h0; exact h0
    have fac : ∀ q : Sp K ⟶ M''.Z, q ≫ f' = p' → ∀ B'' ∈ S''.S (q (IsLocalRing.closedPoint K)),
        (B'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
          (B'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val p') := by
      intro q hq B'' hB''
      have hq' : p' (IsLocalRing.closedPoint K) = f' (q (IsLocalRing.closedPoint K)) := by
        rw [← hq]; rfl
      have hA'q : A' ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := by rw [← hq']; exact hA'
      have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by rw [← hq']; exact hAx
      rw [val_chain h2.hom q (Fr.det_ne hA') (h2.sub _ B'' hB'' A' hA'q) (h1.sub _ A' hA'q A hAq), hq]
    refine ⟨p'', ⟨by rw [← Category.assoc, hp'', hp'x], A'', hA'', ?_⟩, ?_⟩
    · rw [fac p'' hp'' A'' hA'', Mat.mul_inv_rev, ← mul_assoc]
      exact hP''
    · rintro q ⟨hqx, B'', hB'', hPq⟩
      have hq1 : q ≫ f' = p' := by
        refine hu1 (q ≫ f') ⟨by rw [Category.assoc, hqx], ?_⟩
        obtain ⟨A₁, hA₁⟩ := S'.nonempty ((q ≫ f') (IsLocalRing.closedPoint K))
        refine ⟨A₁, hA₁, ?_⟩
        have hA₁' : A₁ ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := hA₁
        have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by
          have h0 := hA; rw [← hqx] at h0; exact h0
        have h2s := h2.sub _ B'' hB'' A₁ hA₁'
        rw [val_chain h2.hom q (Fr.det_ne hA₁') h2s (h1.sub _ A₁ hA₁' A hAq)] at hPq
        have hG : Par k' ⊤ ((B'' * (A₁.map φ')⁻¹).map (M''.val q)) :=
          h2s.map_of _ (valAt M'' q) (valAt_apply M'' q)
        have e : h * ((A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ =
            h * ((B'' * (A₁.map φ')⁻¹).map (M''.val q) * (A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ *
              (B'' * (A₁.map φ')⁻¹).map (M''.val q) := by
          rw [Mat.mul_inv_rev, mul_assoc, mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
        rw [e]
        exact (hPq.mono h2.le le_rfl).mul hG
      refine hu2 q ⟨hq1, B'', hB'', ?_⟩
      rw [fac q hq1 B'' hB'', Mat.mul_inv_rev, ← mul_assoc] at hPq
      exact hPq

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.refines_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => h1.comp h2
