import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordQ

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

section Norm

variable {E : Type} [Field E] [NumberField E]

theorem natAbs_norm_eq_prod (x : 𝓞 E) :
    ((Algebra.norm ℤ x).natAbs : ℝ) = ∏ φ : E →+* ℂ, ‖φ (x : E)‖ := by
  have h1 : ((Algebra.norm ℤ x).natAbs : ℝ) = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := by
    rw [Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  have h3 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ (x : E))‖ = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := by
    simp
  rw [h1, ← h3, Algebra.norm_eq_prod_embeddings ℚ ℂ (x : E), norm_prod]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

end Norm

section Had

variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions

def GramFac (S : HSpace E) : Prop :=
  ∀ φ : E →+* ℂ, ∃ (m : Type) (_ : Fintype m) (ℓ : S.V → m → ℂ) (s : ℂ), ‖s‖ = 1 ∧
    ∀ x y, φ (S.hT x y) = s * (star (ℓ x) ⬝ᵥ ℓ y)

theorem gramFac_of_definite (S : HSpace E) (hstar : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a))
    (hsig : S.SigOK) (hdef : S.IsDefinite) : GramFac S := by
  intro φ
  obtain ⟨e, Q, s, hs1, hG⟩ := factor_of_sig (S.gram.map φ) _ _ (hsig φ)
    (by rcases hdef φ with h | h <;> simp [h])
  refine ⟨_, inferInstance, fun x ↦ Q *ᵥ ((fun i ↦ φ (S.frame.repr x i)) ∘ e.symm), s, hs1, fun x y ↦ ?_⟩
  rw [phi_hT S φ (hstar φ), ← dot_reindex e, hG, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec, star_mulVec, smul_eq_mul]

theorem gramFac_of_isomEmb (S S' : HSpace E) (ι : S.V →ₗ[E] S'.V) (hι : HSpace.IsIsomEmb S S' ι)
    (h : GramFac S') : GramFac S := by
  intro φ
  obtain ⟨m, hm, ℓ, s, hs, h'⟩ := h φ
  exact ⟨m, hm, ℓ ∘ ι, s, hs, fun x y => by rw [← hι x y]; exact h' _ _⟩

theorem norm_eq_re_of_nonneg {z : ℂ} (h : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← h2])
  conv_lhs => rw [hz]
  exact Complex.norm_of_nonneg h1

theorem had_gram (S : HSpace E) (hF : GramFac S) (φ : E →+* ℂ) {k : ℕ} (x : Fin k → S.V)
    (M : Matrix (Fin k) (Fin k) E) (hM : ∀ i j, M i j = S.hT (x i) (x j)) :
    ‖φ M.det‖ ≤ ∏ c, ‖φ (S.hT (x c) (x c))‖ := by
  classical
  obtain ⟨m, hm, ℓ, s, hs, hℓ⟩ := hF φ
  let A : Matrix m (Fin k) ℂ := Matrix.of fun a i ↦ ℓ (x i) a
  have hAA : ∀ i j, (Aᴴ * A) i j = star (ℓ (x i)) ⬝ᵥ ℓ (x j) := by
    intro i j
    simp [A, Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
  have hB : M.map φ = s • (Aᴴ * A) := by
    ext i j
    rw [Matrix.map_apply, hM, hℓ, Matrix.smul_apply, hAA, smul_eq_mul]
  have hP := posSemidef_conjTranspose_mul_self A
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hB, Matrix.det_smul, norm_mul, norm_pow, hs, one_pow, one_mul,
    norm_eq_re_of_nonneg hP.det_nonneg]
  refine le_trans (Formalism.HermitianLattices.LatticeEstimates.hadamard_inequality_bound k _ hP) (le_of_eq (Finset.prod_congr rfl fun c _ ↦ ?_))
  rw [hℓ, norm_mul, hs, one_mul, ← hAA, norm_eq_re_of_nonneg hP.diag_nonneg]

theorem prod_le_of_mean (S : HSpace E) {k : ℕ} (x : Fin k → S.V) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hx : ∀ c, meanAbs (S.hT (x c) (x c)) ≤ ρ) :
    ∏ φ : E →+* ℂ, ∏ c, ‖φ (S.hT (x c) (x c))‖ ≤ ρ ^ (Module.finrank ℚ E * k) := by
  have hcard := NumberField.Embeddings.card E ℂ
  have hd : (0 : ℝ) < Fintype.card (E →+* ℂ) := by exact_mod_cast Fintype.card_pos
  have key : ∀ c, ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖ ≤ ρ ^ Module.finrank ℚ E := by
    intro c
    have hg := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ))
      (fun φ : E →+* ℂ => ‖φ (S.hT (x c) (x c))‖) (by simp) (by simpa using hd)
      (fun _ _ => norm_nonneg _)
    simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      one_mul] at hg
    have hmean : (∑ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖) / (Fintype.card (E →+* ℂ) : ℝ) ≤ ρ := by
      have := hx c
      simp only [meanAbs] at this
      rwa [hcard]
    have hP : 0 ≤ ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [← hcard]
    calc ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖
        = ((∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖) ^ ((Fintype.card (E →+* ℂ) : ℝ)⁻¹)) ^
            Fintype.card (E →+* ℂ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hd.ne', Real.rpow_one]
      _ ≤ ρ ^ Fintype.card (E →+* ℂ) := pow_le_pow_left₀ (Real.rpow_nonneg hP _) (hg.trans hmean) _
  rw [Finset.prod_comm]
  calc ∏ c, ∏ φ : E →+* ℂ, ‖φ (S.hT (x c) (x c))‖ ≤ ∏ _c : Fin k, ρ ^ Module.finrank ℚ E :=
        Finset.prod_le_prod (fun c _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) (fun c _ => key c)
    _ = ρ ^ (Module.finrank ℚ E * k) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

end Had

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem hT_equivFun_symm (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i : Fin S.rank)
    (z : Fin S.rank → E) :
    S.hT (b i) (b.equivFun.symm z) = ((fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ z) i := by
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gram_det_ne (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) :
    Matrix.det (fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hy0 : b.equivFun.symm z ≠ 0 := by
    intro h
    apply hz
    have := b.equivFun.apply_symm_apply z
    rw [h, map_zero] at this
    exact this.symm
  apply hy0
  apply S.nondeg.2
  intro x
  rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_equivFun_symm, hGz]
  simp

theorem gram_int (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V)
    (hq : LatT S q L) (hbL : ∀ c, b c ∈ L) (i j : Fin S.rank) :
    S.hT (b i) (b j) ∈ (algebraMap (𝓞 E) E).range :=
  hq.1 (b j) (hbL j) (b i) (hbL i)

theorem key_between (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V)
    (hL : Submodule.IsLattice E L) (hq : LatT S q L) (hbL : ∀ c, b c ∈ L) :
    (keyOf S b L).2 ∈ Between (keyOf S b L).1 := by
  simp only [keyOf, Between, Set.mem_setOf_eq]
  have hG := gram_det_ne S b
  refine ⟨?_, ?_, hL.fg.map _⟩
  · rintro v ⟨w, rfl⟩
    refine ⟨b.equivFun.symm (incl S.rank w), ?_, b.equivFun.apply_symm_apply _⟩
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    unfold incl
    simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
    rw [algebraMap_smul]
    exact L.smul_mem _ (hbL c)
  · rintro v ⟨x, hx, rfl⟩
    choose w hw using fun i => hq.1 x hx (b i) (hbL i)
    refine ⟨w, ?_⟩
    have hx' : incl S.rank w =
        (fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ b.equivFun x := by
      funext i
      unfold incl
      simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply]
      rw [hw i, ← hT_equivFun_symm S b i (b.equivFun x), LinearEquiv.symm_apply_apply]
    have key : ∀ (M : Matrix (Fin S.rank) (Fin S.rank) E), M.det ≠ 0 → ∀ v, M⁻¹ *ᵥ (M *ᵥ v) = v := by
      intro M hM v
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.one_mulVec]
    unfold psi
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearMap.compLeft_apply, Algebra.linearMap_apply, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    rw [hx']
    exact key _ hG _

theorem coordCount_of (S : HSpace E) (q : ℕ) (ρ B2 : ℝ) (hρ : 0 ≤ ρ) (hF : GramFac S)
    (hB : ρ ^ (Module.finrank ℚ E * S.rank * S.rank) ≤ Real.exp B2) : CoordCount S q ρ B2 := by
  classical
  let Good : Matrix (Fin S.rank) (Fin S.rank) E → Submodule (𝓞 E) (Fin S.rank → E) → Prop := fun G C ↦
    ∃ (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V), Submodule.IsLattice E L ∧ LatT S q L ∧
      (∀ c, b c ∈ L) ∧ (∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ) ∧ keyOf S b L = (G, C)
  let St : Matrix (Fin S.rank) (Fin S.rank) E → Set (Submodule (𝓞 E) (Fin S.rank → E)) := fun G ↦ {C | Good G C}
  have hbound : ∀ (L : Submodule (𝓞 E) S.V) (b : Module.Basis (Fin S.rank) E S.V), Submodule.IsLattice E L →
      LatT S q L → (∀ c, b c ∈ L) → (∀ c, meanAbs (S.hT (b c) (b c)) ≤ ρ) →
      (St (keyOf S b L).1).Finite ∧ ((St (keyOf S b L).1).ncard : ℝ) ≤ Real.exp B2 := by
    intro L b hL hq hbL hbs
    set G : Matrix (Fin S.rank) (Fin S.rank) E := (keyOf S b L).1 with hG
    have hint := gram_int S q L b hq hbL
    choose Gm0 hGm using hint
    set Gm : Matrix (Fin S.rank) (Fin S.rank) (𝓞 E) := Matrix.of Gm0 with hGm0
    have hGmG : Gm.map ((↑) : 𝓞 E → E) = G := by
      ext i j
      exact hGm i j
    have hdet : (Gm.map ((↑) : 𝓞 E → E)).det ≠ 0 := by
      rw [hGmG]; exact gram_det_ne S b
    obtain ⟨hfin, hcard⟩ := between_finite_card Gm hdet
    rw [hGmG] at hfin hcard
    have hsub : St G ⊆ Between G := by
      rintro C ⟨L', b', hL', hq', hbL', _, hk⟩
      have := key_between S q L' b' hL' hq' hbL'
      rw [hk] at this
      exact this
    refine ⟨hfin.subset hsub, ?_⟩
    have h1 : ((St G).ncard : ℝ) ≤ ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ^ S.rank := by
      exact_mod_cast (Set.ncard_le_ncard hsub hfin).trans hcard
    have hdetE : ((Gm.det : 𝓞 E) : E) = G.det := by
      rw [← hGmG]
      exact RingHom.map_det (algebraMap (𝓞 E) E) Gm
    have h2 : ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ≤ ρ ^ (Module.finrank ℚ E * S.rank) := by
      rw [natAbs_norm_eq_prod, hdetE]
      refine le_trans (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun φ _ ↦ had_gram S hF φ b G fun i j ↦ rfl) ?_
      exact prod_le_of_mean S b hρ hbs
    refine h1.trans (le_trans ?_ hB)
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) h2 _
  refine ⟨fun G ↦ if h : (St G).Finite ∧ ((St G).ncard : ℝ) ≤ Real.exp B2 then h.1.toFinset else ∅, ?_, ?_⟩
  · intro G
    dsimp only
    split_ifs with h
    · rw [← Set.ncard_eq_toFinset_card _ h.1]
      exact h.2
    · simp [(Real.exp_pos B2).le]
  · intro L b hL hq hbL hbs
    have hgood : (keyOf S b L).2 ∈ St (keyOf S b L).1 := ⟨L, b, hL, hq, hbL, hbs, rfl⟩
    dsimp only
    rw [dif_pos (hbound L b hL hq hbL hbs), Set.Finite.mem_toFinset]
    exact hgood

end Coord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
