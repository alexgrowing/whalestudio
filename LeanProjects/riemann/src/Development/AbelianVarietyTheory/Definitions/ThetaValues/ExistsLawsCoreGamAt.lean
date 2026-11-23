import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply

noncomputable section

namespace GlobalTheory.RunIn.Check

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section L1

variable {K : Type} [Field K] {ι : Type} (σ : K →+* ℂ)

theorem l1At_nonneg (P : MvPolynomial ι K) : 0 ≤ l1At σ P := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem l1At_eq_zero_iff (P : MvPolynomial ι K) : l1At σ P = 0 ↔ P = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [l1At, h]⟩
  rw [l1At, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _] at h
  ext m
  by_contra hm
  have := h m (MvPolynomial.mem_support_iff.2 (by simpa using hm))
  simp at this
  exact hm (by simpa using this)

theorem l1At_eq_sum (P : MvPolynomial ι K) (s : Finset (ι →₀ ℕ)) (hs : P.support ⊆ s) :
    l1At σ P = ∑ m ∈ s, ‖σ (P.coeff m)‖ :=
  Finset.sum_subset hs fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]

theorem l1At_add_le (P Q : MvPolynomial ι K) : l1At σ (P + Q) ≤ l1At σ P + l1At σ Q := by
  classical
  rw [l1At_eq_sum σ (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    l1At_eq_sum σ P (P.support ∪ Q.support) Finset.subset_union_left,
    l1At_eq_sum σ Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add]
  exact norm_add_le _ _

theorem l1At_monomial (m : ι →₀ ℕ) (a : K) : l1At σ (MvPolynomial.monomial m a) = ‖σ a‖ := by
  classical
  rw [l1At_eq_sum σ _ {m} MvPolynomial.support_monomial_subset]
  simp

theorem l1At_smul (a : K) (P : MvPolynomial ι K) : l1At σ (a • P) = ‖σ a‖ * l1At σ P := by
  rw [l1At_eq_sum σ (a • P) P.support MvPolynomial.support_smul, l1At, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

theorem norm_eval₂_le (P : MvPolynomial ι K) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖MvPolynomial.eval₂ σ z P‖ ≤ l1At σ P := by
  rw [MvPolynomial.eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_)
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hz i)

end L1

variable {D : D7}

theorem gamAt_iff (T : Core D) : GamAt T ↔ ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    GlobalTheory.FrameNorm.HasPrinc (⟨(T.U j σ).Comp, (T.U j σ).X, (T.U j σ).un⟩ : Formalism.L2.PjFree.Unf _ _ σ _) T.Q.l.M :=
  Iff.rfl

theorem range_nonempty (T : Core D) : ∃ j, InR D j ∧ ∃ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ :=
  ⟨_, ⟨Formalism.L2.Geo.one_le_jcl D 0, Formalism.L2.Geo.jcl_le D 0⟩, T.σ₀, T.good_σ₀⟩

theorem mem_of_modelBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {r g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ}
    {F : FamilyUnif Xo σ' ty} {M : ModelsOf F r} (hM : ModelBase M) (hA : l.A ∣ l.M) (k : Fin F.n)
    (γ : GL (Fin r) E) (hγ : IsUStab (M.X k).Gm (M.X k).Λ γ)
    (h : ∀ x ∈ (M.X k).Λ, ∃ y ∈ (M.X k).Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (l.M : E) • y) :
    γ ∈ (M.X k).Γ :=
  (hM.gam k γ).2 ⟨hγ, fun a _ => GlobalTheory.FrameUnif.congr_of_dvd_modulus _ (M.φ k) _ dvd_rfl h a,
    fun a => GlobalTheory.FrameUnif.congr_of_dvd_modulus _ (M.φ k) _ hA h a⟩

theorem exists_lawsCore_gamAt {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}
    (L : LawsRemainingRows hN Q hpq) (hQ : Q.Pins) : ∃ T : Core D, T.Q = Q ∧ LawsCore T ∧ GamAt T := by
  have hex : ∀ j (σ : Q.c.F →+* ℂ), ∃ p : PkgT Q j σ, InR D j → GoodEmb Q.c σ → PkgOK2 Q j σ p ∧
      ∀ k (γ : GL (Fin D.R.r) D.host.E), IsUStab (p.1.X k).Gm (p.1.X k).Λ γ →
        (∀ x ∈ (p.1.X k).Λ, ∃ y ∈ (p.1.X k).Λ,
          Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (Q.l.M : D.host.E) • y) →
        γ ∈ (p.1.X k).Γ := by
    intro j σ
    by_cases hj : InR D j
    · by_cases hσ : GoodEmb Q.c σ
      · refine ⟨pkgJ (L.pkg j hj σ hσ), fun _ _ => ⟨pkgJ_ok _ (L.allTest j hj) (xiConst_holds D) (L.wtC j hj σ hσ)
          (muOK_one (L.pkg j hj σ hσ).unitFr), fun k γ hγ h => ?_⟩⟩
        exact mem_of_modelBase (L.pkg j hj σ hσ).modelEx.choose_spec.1 (hQ.2.1.2 ▸ one_dvd _) k γ hγ h
      · exact ⟨Classical.choice (L.dataAll j σ), fun _ h => absurd h hσ⟩
    · exact ⟨Classical.choice (L.dataAll j σ), fun h => absurd h hj⟩
  choose pk hpk using hex
  exact ⟨coreOfP Q pk L.half.choose, rfl,
    lawsCore_coreOfP L.toBaseRows pk (fun j hj σ hσ => (hpk j σ hj hσ).1) hQ,
    fun j hj σ hσ => (hpk j σ hj hσ).2⟩

theorem exists_xi {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ ξ : E, cc ξ = -ξ ∧ ξ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [sq] at h1 h2
    have him : z.im ≠ 0 := by
      intro h; rw [h] at h1; nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have hk := key (τ (H.rt : E)) (by rw [← map_pow, hE, map_neg, map_natCast])
    have : τ (cc (H.rt : E)) = starRingEnd ℂ (τ (H.rt : E)) := IsCMField.complexEmbedding_complexConj E τ _
    rw [this, map_neg]
    apply Complex.ext <;> simp [hk.1]
  have h0 : (H.rt : E) ≠ 0 := by
    intro h
    rw [h] at hE
    have : (H.d : E) = 0 := by linear_combination hE
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, h0, fun τ hτ => hτ ▸ h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 h0, fun τ hτ => by rw [map_neg, hτ]; simpa using h⟩
    have : cc (-(H.rt : E)) = -cc (H.rt : E) := by simp [cc]
    rw [this, hcc]

theorem exists_gamAt (T : Core D) (hQ : T.Q.Pins) : ∃ T' : Core D, T'.Q = T.Q ∧ GamAt T' ∧
    ∀ j, InR D j → ∀ σ, GoodEmb T'.Q.c σ → IsUnf (T'.U j σ) ∧ Nonempty (T'.U j σ).Comp := by
  obtain ⟨ξ, hξ, hξ0, hneg⟩ := exists_xi T.Q.H
  have hex : ∀ j (σ : T.Q.c.F →+* ℂ), ∃ (U : Unf (T.Q.Xo j) T.Q.c σ D.R.r) (_ : Σ k, Frame (U.X k).Ψ D.R.r),
      InR D j → GoodEmb T.Q.c σ → IsUnf U ∧ Nonempty U.Comp ∧
      GlobalTheory.FrameNorm.HasPrinc (⟨U.Comp, U.X, U.un⟩ : Formalism.L2.PjFree.Unf _ _ σ _) T.Q.l.M := by
    intro j σ
    by_cases h : InR D j ∧ GoodEmb T.Q.c σ
    · obtain ⟨hj, hσ⟩ := h
      have hr : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := by
        rw [(hQ.2.2.2 j hj).1, (hQ.2.2.2 j hj).2.1, Formalism.L2.Geo.sigW_sum D hj.1 hj.2]
      obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum _ T.Q.H (T.Q.Dw j) (-ξ)
        (by have : cc (-ξ) = -cc ξ := by simp [cc]
            rw [this, hξ]) (neg_ne_zero.2 hξ0) _ hr
      obtain ⟨U, hU, hP, ⟨k⟩, -⟩ := GlobalTheory.FrameUnif.exists_unf_hasPrinc _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ
        D.R.r ξ Gm φ (by have := Formalism.L2.Geo.two_le_r D; omega) hσ hξ hneg hφ
      have hM : T.Q.l.M' = T.Q.l.M := by rw [Level.M', hQ.2.1.2, Nat.lcm_one_right]
      exact ⟨⟨U.Comp, U.X, U.un⟩, ⟨k, 0⟩, fun _ _ => ⟨hU, ⟨k⟩, hM ▸ hP⟩⟩
    · exact ⟨T.U j σ, T.dict j σ 1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose U d hU using hex
  exact ⟨⟨T.Q, U, T.V, fun j σ _ => d j σ, T.mu, T.Kf, T.pb⟩, rfl, fun j hj σ hσ => (hU j σ hj hσ).2.2,
    fun j hj σ hσ => ⟨(hU j σ hj hσ).1, (hU j σ hj hσ).2.1⟩⟩

end GlobalTheory.RunIn.Check
