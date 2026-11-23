import Formalism.WachLatticeTwists.HodgeTateChains.StatWChain
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.CancelRight

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

lemma map_smul_hom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

lemma pow_nzd {R : Type} [CommRing R] {y : R} (h : ∀ a : R, y * a = 0 → a = 0) (k : ℕ) :
    ∀ a : R, y ^ k * a = 0 → a = 0 := by
  induction k with
  | zero => intro a ha; simpa using ha
  | succ k ih => intro a ha; exact ih a (h _ (by rw [← mul_assoc, ← pow_succ']; exact ha))

theorem wActU : StatWActU := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ A g gA τ u hι hal hA hg hϑ hx
    hnz
  set R : Matrix (Fin r) (Fin r) AA := (ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)
    with hR
  have hRι : R.map ι = (ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC) := by
    ext i j; simp [hR, hal]
  have h1 : (A.map gA).map ι = (A.map ι).map (act g) := by
    ext i j; simp [hg]
  have h2 : (A.map ι).map (act g) = (ι (gA (jA x))) ^ M0 • W.Xx.map (act g) := by
    rw [hA]
    ext i j
    simp [hg]

  have h3 : (jA x) ^ M0 • (A.map gA * R) = (gA (jA x)) ^ M0 • ((W.Gm g).map jA * A) := by
    have hinj : Function.Injective (fun M : Matrix (Fin r) (Fin r) AA => M.map ι) := by
      intro M N h
      ext i j
      exact hι (congrFun (congrFun h i) j)
    apply hinj
    show ((jA x) ^ M0 • (A.map gA * R)).map ι = ((gA (jA x)) ^ M0 • ((W.Gm g).map jA * A)).map ι
    rw [map_smul_hom, map_smul_hom, Matrix.map_mul, Matrix.map_mul, h1, h2, hRι, Matrix.smul_mul, W.W2, hA,
      Matrix.mul_smul, map_pow, map_pow, smul_comm]
  have h4 := congrArg (fun M : Matrix (Fin r) (Fin r) AA => M.map ϑ) h3
  simp only [map_smul_hom, Matrix.map_mul, map_pow, hϑ, hx] at h4
  have h5 : (A.map gA).map ϑ = (A.map ϑ).map τ := by
    ext i j; simp [hϑ]
  rw [h5] at h4
  have h7 : ((u ^ M0 • W.Gm g).map jA).map ϑ * A.map ϑ
      = (ϑ (jA u)) ^ M0 • (((W.Gm g).map jA).map ϑ * A.map ϑ) := by
    rw [map_smul_hom, map_smul_hom, Matrix.smul_mul, map_pow, map_pow]
  rw [h7]
  ext i j
  have h6 := congrFun (congrFun h4 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h6 ⊢
  refine sub_eq_zero.1 (pow_nzd hnz M0 _ ?_)
  rw [mul_sub, h6, mul_pow]
  ring

theorem wAct : StatWAct := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ A g gA τ hι hal hA hg hϑ hx hnz
  have h := wActU ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A g gA τ 1 hι hal hA hg hϑ
    (by rw [map_one, map_one, one_mul]; exact hx) hnz
  rwa [one_pow, one_smul] at h

theorem xNzd : StatXNzd := by
  intro ℓ OC _ y c k hk hc hl a ha
  apply hl
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [← hc, pow_succ]
  calc y ^ k * y * c * a = y ^ k * c * (y * a) := by ring
    _ = 0 := by rw [ha, mul_zero]

lemma mapmap_sub_one {As AA OC : Type} [CommRing As] [CommRing AA] [CommRing OC] (jA : As →+* AA)
    (ϑ : AA →+* OC) {r : ℕ} (M : Matrix (Fin r) (Fin r) As) (i j : Fin r) :
    ((M.map jA).map ϑ - 1) i j = (ϑ.comp jA) ((M - 1) i j) := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem wChain : StatWChain := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ c γ σ gA τ z ϖ ϖ' s
    hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ hgA hϑ hτ hl
  obtain ⟨A, Y', hA, h1, h2⟩ := wSandwich' ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ c
    hL hι hx hξ hc
  have hk : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos (Fact.out : ℓ.Prime).pos _) (by have := (Fact.out : ℓ.Prime).two_le; omega)
  refine ⟨A, Y', hA, h1, h2, ?_, ?_⟩
  · exact wAct ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A _ gA τ hι hal hA hgA hϑ hτ
      (xNzd ℓ OC _ c _ hk hc hl)
  · intro i j
    rw [mapmap_sub_one]
    exact wUm ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W γ σ (ϑ.comp jA) z ϖ ϖ' s
      (n0 ℓ (M0 + h0)) hfix (hι.comp hj) hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ i j

theorem wD : StatWD := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ c γ σ actA actO z ϖ ϖ' s
    hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ hgA hϑ hτ hl hH hu
  obtain ⟨A, Y', hA, h1, h2, h3, h4⟩ := wChain ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ c γ σ
    (actA (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) : AA →+* AA) (actO (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) : OC →+* OC)
    z ϖ ϖ' s hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ (hgA _) (hϑ _) hτ hl
  have hk : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos (Fact.out : ℓ.Prime).pos _) (by have := (Fact.out : ℓ.Prime).two_le; omega)
  have hnz := xNzd ℓ OC _ c _ hk hc hl
  have hU : ∀ (g : Gg) (u : As), act g (ι (jA x)) = ι (jA (u * x)) →
      (A.map ϑ).map (actO g) *
        (((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ)
          = ((u ^ M0 • W.Gm g).map jA).map ϑ * A.map ϑ := by
    intro g u hgu
    refine wActU ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A g (actA g : AA →+* AA)
      (actO g : OC →+* OC) u hι hal hA (hgA g) (hϑ g) ?_ hnz
    have : actA g (jA x) = jA (u * x) := hι (by rw [hgA, hgu])
    show actO g (ϑ (jA x)) = _
    rw [← hϑ, this, map_mul, map_mul]
  refine ⟨A, Y', hA, h1, h2, ?_, ?_, ?_, h3, h4⟩
  · intro h hh
    have e := hU h 1 (by rw [one_mul]; exact hH h hh x)
    rw [one_pow, one_smul, wFix ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W (hι.comp hj) h hh] at e
    rw [e, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  · intro g
    obtain ⟨u, hgu⟩ := hu g
    exact ⟨_, hU g u hgu⟩
  · exact wEnd ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A hι hal hA

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
