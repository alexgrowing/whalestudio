import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointPermutationSignStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantNonzeroDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolydiscCmUniformizationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EisRuleProof

theorem card_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem isHolForm_mul {F : Type} [Field F] [NumberField F] {𝔞 𝔟 : FracId F} {k : ℕ}
    {g : ((F →+* ℝ) → ℂ) → ℂ} (h : IsHolForm 𝔞 𝔟 k g) (K : ℂ) : IsHolForm 𝔞 𝔟 k (fun z ↦ K * g z) := by
  refine ⟨h.1.const_mul K, fun a b c d hm z hz ↦ ?_⟩
  simp only
  rw [h.2 a b c d hm z hz]; ring

theorem dF_pos (F : Type) [Field F] [NumberField F] : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF
  exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)

theorem omegaFactor_ne_zero {F : Type} [Field F] [NumberField F] (𝔞 : FracId F) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ≠ 0 := by
  have hn : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 ≠ 0 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
    exact_mod_cast mt FractionalIdeal.absNorm_eq_zero_iff.1 𝔞.ne_zero
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor
  exact_mod_cast mul_ne_zero (Real.rpow_pos_of_pos (dF_pos F) _).ne' hn

theorem cK_ne_zero (F : Type) [Field F] [NumberField F] (k : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) ≠ 0 := by
  have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK
    exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)
  exact_mod_cast this.ne'

def smulGen {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {X : Obj F 𝔠 (Sp ℂ)} (δ : X.DetGen) (c : ℂ)
    (hc : c ≠ 0) : X.DetGen :=
  ⟨c • δ.1, by rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]; exact δ.2⟩

theorem sign_pow_even (x : ℤˣ) (s : ℕ) : ((x : ℤ) : ℂ) ^ (2 * s) = 1 := by
  rcases Int.units_eq_one_or x with h | h <;> simp [h, pow_mul]

theorem eisRule_of (hQ : GlobalTheory.RealMult.QExpansionOnAll) (hExp : EisExp) (hMod : EisMod) (hFour : EisFourier)
    (hTor : TorusForm) : EisRule := by
  intro E _ _ _ hf 𝔠 s hs zv hzv R₀ m hm hmz
  have key : ∀ 𝔞 𝔟 𝔠' : FracId (FR E), 𝔠' = 𝔞 * 𝔟⁻¹ → ∃ r : Rule (trivialObjectCondition 𝔠') R₀ (2 * s),
      ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ →
        IsEisRule φ (lattice c y) m r := by
    intro 𝔞 𝔟 𝔠' h𝔠
    subst h𝔠
    have e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ) := (Fintype.equivFinOfCardEq (card_emb (FR E))).symm
    obtain ⟨G, hG, hGd, hGexp⟩ := hExp (FR E) hf 𝔞 𝔟 s hs
    have hGmod := hMod (FR E) 𝔞 𝔟 s hs G hG hGd
    obtain ⟨Z, a, hZ, hfo, ha0, hint⟩ := hFour (FR E) 𝔞 𝔟 (2 * s) (by omega) G hGexp
    have hω0 := omegaFactor_ne_zero 𝔞
    have hck0 := cK_ne_zero (FR E) (2 * s)
    set ω : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) with hω
    set ck : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK (FR E) (2 * s) : ℂ) with hck
    have hcw : (cWt E (2 * s) : ℂ) = ck := rfl
    set gF : ((FR E →+* ℝ) → ℂ) → ℂ := fun z ↦ (m * ck / ω ^ (2 * s)) * G z with hgFdef
    have hgF : IsHolForm 𝔞 𝔟 (2 * s) gF := isHolForm_mul hGmod _
    have hfoF : HasFourier 𝔞 𝔟 gF (fun ξ ↦ m * a ξ) := by
      intro z hz
      have := (hfo z hz).mul_left m
      convert this using 1 <;> first | rfl | (funext ξ; ring) | (simp only [gF]; ring)
    have hcoef : ∀ ξ, m * a ξ ∈ R₀ := by
      intro ξ
      by_cases hξ : ξ = 0
      · subst hξ
        rw [ha0]
        obtain ⟨Z', hZ', hZ'v⟩ := hzv (ClassGroup.mk (FR E) 𝔞)⁻¹
        have hne : (1 - ((2 * s : ℕ) : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
          have : ((2 * s : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * s ≠ 0)
          simpa using this
        have heq := GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn (F := FR E) ⟨hZ.1, hZ.2⟩ ⟨hZ'.1, hZ'.2⟩ hne
        rw [heq, hZ'v]
        have h5 : m * ((2 : ℂ)⁻¹ ^ Module.finrank ℚ (FR E) * ((zv (ClassGroup.mk (FR E) 𝔞)⁻¹ : ℚ) : ℂ)) =
            m * (((zv (ClassGroup.mk (FR E) 𝔞)⁻¹ / 2 ^ Module.finrank ℚ (FR E) : ℚ)) : ℂ) := by
          rw [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, div_eq_mul_inv, inv_pow]; ring
        rw [h5]; exact hmz _
      · obtain ⟨n, hn⟩ := hint ξ hξ
        rw [hn]
        exact R₀.mul_mem hm (intCast_mem R₀ n)
    obtain ⟨r, hrv, -⟩ := hQ (FR E) hf e 𝔞 𝔟 (2 * s) R₀ gF (fun ξ ↦ m * a ξ) hgF hfoF hcoef
    refine ⟨r, fun I _ φ c y hφ hc ↦ ?_⟩
    intro g hg z hz X U δ C hdet
    obtain ⟨e', τ, lam, he', hτ, hlam, hΛ, htp⟩ := hTor E I 𝔞 𝔟 φ c y hφ hc z hz X U
    have hgz := GlobalTheory.T.polydisc_cm_uniformization E I 𝔞 𝔟 φ c y hφ hc s hs z hz U.e e' τ lam he' hτ hlam
      (fun w ↦ (U.lat w).symm.trans (hΛ w)) G hG g hg
    have hlamp : ∏ j, lam j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hlam j
    set K : ℂ := ω / ∏ j, lam j with hK
    have hK0 : K ≠ 0 := div_ne_zero hω0 hlamp
    have hval : ∀ δ' : X.DetGen, U.IsDet δ'.1 K → r.val ℂ X trivial δ' = gF τ := by
      intro δ' hδ'
      have htp' := htp δ'.1 hδ'
      let π : Equiv.Perm (Fin (Module.finrank ℚ (FR E))) := e.trans e'.symm
      have hπ : π.trans e' = e := by ext j; simp [π]
      have hA := GlobalTheory.T.torus_point_permutation_sign (FR E) e' π 𝔞 𝔟 τ X δ'.1 htp'
      rw [hπ] at hA
      have hsg : (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) ≠ 0 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
      have h1 := hrv τ hτ X trivial (smulGen δ' _ hsg) hA
      have h2 := r.homog ℂ X trivial δ' (smulGen δ' _ hsg) _ rfl
      rw [sign_pow_even, _root_.one_mul] at h2
      rw [← h2, h1]
    by_cases hdeg : ∃ (v : Fin (Module.finrank ℚ (FR E)) → X.Lie)
        (W : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ),
        (∀ j, U.u.IsDiff (W j) (v j).hom) ∧ W.det ≠ 0
    · obtain ⟨v, W, hv, hW⟩ := hdeg
      have hδv := GlobalTheory.T.determinant_nonzero_differentials (FR E) _ X _ U.u δ v W hv hW
      have hC : C ≠ 0 := by
        intro h0; apply hδv; rw [hdet v W hv, h0, zero_mul]
      have hδ' : U.IsDet (smulGen δ (K / C) (div_ne_zero hK0 hC)).1 K := by
        intro v W hv
        show ((K / C) • δ.1) v = K * W.det
        rw [AlternatingMap.smul_apply, hdet v W hv, smul_eq_mul]
        field_simp
      have h1 := hval _ hδ'
      have h2 := r.homog ℂ X trivial δ (smulGen δ (K / C) (div_ne_zero hK0 hC)) (K / C) rfl
      rw [h1] at h2
      have hCK : C ^ (2 * s) * (K / C) ^ (2 * s) = K ^ (2 * s) := by
        rw [← mul_pow]; congr 1; field_simp
      rw [← h2, ← _root_.mul_assoc, hCK, hgz, hcw, hK, hgFdef]
      simp only
      rw [div_pow, inv_pow]
      field_simp
    · push_neg at hdeg
      have hδK : U.IsDet δ.1 K := fun v W hv ↦ by rw [hdet v W hv, hdeg v W hv]; simp
      have hδ2 : U.IsDet (smulGen δ 2 two_ne_zero).1 K := by
        intro v W hv
        show ((2 : ℂ) • δ.1) v = K * W.det
        rw [AlternatingMap.smul_apply, hdet v W hv, hdeg v W hv]; simp
      have h1 := hval _ hδK
      have h2 := hval _ hδ2
      have h3 := r.homog ℂ X trivial δ (smulGen δ 2 two_ne_zero) 2 rfl
      rw [h1, h2] at h3
      have hg0 : gF τ = 0 := by
        have h4 : ((2 : ℂ) ^ (2 * s) - 1) * gF τ = 0 := by rw [sub_mul, h3]; ring
        refine (mul_eq_zero.1 h4).resolve_left ?_
        have : (1 : ℝ) < 2 ^ (2 * s) := one_lt_pow₀ (by norm_num) (by omega)
        intro h5
        have h6 : (2 : ℂ) ^ (2 * s) = 1 := sub_eq_zero.1 h5
        have h7 : ((2 : ℝ) ^ (2 * s) : ℂ) = 1 := by push_cast; exact h6
        have h8 : (2 : ℝ) ^ (2 * s) = 1 := by exact_mod_cast h7
        linarith
      have hmG : m * G τ = 0 := by
        simp only [gF] at hg0
        have := mul_eq_zero.1 hg0
        rcases this with h | h
        · rcases mul_eq_zero.1 (div_eq_zero_iff.1 h |>.resolve_right (pow_ne_zero _ hω0)) with h' | h'
          · rw [h', zero_mul]
          · exact absurd h' hck0
        · rw [h, mul_zero]
      rw [h1, hgz, hg0, mul_zero]
      linear_combination (-(cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s)) * hmG

  exact key 𝔠 1 𝔠 (by simp)

end GlobalTheory.EisRuleProof
