import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoverDictionaryAdelicElementComponent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf

noncomputable section

namespace GlobalTheory.CoverIndep

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Matrix
open GlobalTheory.ShortMove GlobalTheory.ShortMoveIso GlobalTheory.TwistTie

theorem rmul_mem_bor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b b' : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (hb' : b' ∈ Bor Ψ r) : rmul b b' ∈ Bor Ψ r := by
  intro τ
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have ht' : (mat b' τ).BlockTriangular id := fun a c h => (hb' τ).2 a c h
  refine ⟨?_, fun a c h => (ht.mul ht') h⟩
  show (mat b τ * mat b' τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero (hb τ).1 (hb' τ).1

theorem rmul_lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x b b' : Frame Ψ r) :
    rmul (lact γ (rmul x b)) b' = rmul (lact γ x) (rmul b b') := by
  funext τ
  show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)) * mat b' τ =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * (mat b τ * mat b' τ)
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in

theorem dict_onto {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (k : U.Comp) (x : Frame (U.X k).Ψ r) (hxd : x ∈ (U.X k).dom) :
    ∃ h, ∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, dict h = ⟨k, rmul (lact γ x) b⟩ := by
  subst hr
  have hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  obtain ⟨h1, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  obtain ⟨x₁, b, hb, ho, hx₁⟩ := h1 x hxd
  have hx₁d : x₁ ∈ (U.X k).dom := ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm).2.1 x₁ ho).1
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hmem : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
    intro k τ
    rw [(hU.2.1 k).2 τ, hι.rt, hι.rt0]
  have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (U.X k).Ψ,
      uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x₁ ⟨τ, hτ⟩ = u * x₀ τ := by
    intro τ
    by_cases hτ : τ ∈ (U.X k).Ψ
    · obtain ⟨u, hu⟩ := h4 τ (x₀ τ) (mat x₁ ⟨τ, hτ⟩) (hx₀ k τ hτ) ((ho ⟨τ, hτ⟩).trans (hx₀ k τ hτ).symm)
      rw [hG] at hu
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hτ⟩
  choose u hu using hex
  obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem k τ).2 hτ)).1
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  obtain ⟨h₀, hh₀⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨a₀, ha₀, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h₀
  have hfin : finHom V (a₀ * f) = finHom V (a * f) := by
    rw [map_mul, map_mul, show finHom V a₀ = 1 from ha₀, show finHom V a = 1 from ha]
  have hh : Marked V rfl io l (U.X k).Λ (fun a => (φ k (F.t (ik k) a) : Fin V.rank → D.host.E)) (a * f) := by
    obtain ⟨e₁, e₂⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.1 _ _ hfin
    unfold Marked at hh₀ ⊢
    rwa [e₁, e₂, hfin] at hh₀
  refine ⟨a * f, ?_⟩
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 (a * f)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨gam, e₁, t₁, hgam⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (a * f)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id (a * f) γ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ hδu hδf rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ, hm⟩)
  obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x₁, hx₁d⟩
  obtain ⟨P', hPe', hP', hy', hd'⟩ := hD.1.2 (dict (a * f)).1 ⟨_, hdom _⟩
  obtain ⟨γ', hγ', b', hb', hk⟩ := (hU.2.2.2.1 k (dict (a * f)).1 ⟨x₁, hx₁d⟩ ⟨_, hdom _⟩).1
    (GlobalTheory.CoverOnto.frBor_of_isometry e F hpq hσ hA gam e₁ t₁ hP hP' (fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      refine perFr_of_unitary _ _ (fun τ => by rw [hmem, hmem]) (by rw [hG, hG])
        (by rw [(hU.2.1 _).1, (hU.2.1 _).1]) (by rw [hG]; exact hδu) (fun τ h h' => ?_) _ _ _
      rw [hfr ⟨τ, h'⟩, GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h'⟩) (hθ τ), (hAr τ).2.1, (hAr τ).2.1,
        (hAr τ).2.2.1 f hf, hδa τ _ (hθ τ), hau τ ((hmem k τ).1 h), (hu τ h).2, Matrix.mul_one, ← Matrix.mul_assoc]
      rfl) _ _ hy hy' hd hd')
  refine ⟨γ', hγ', rmul b b', rmul_mem_bor hb hb', ?_⟩
  rw [← rmul_lact_rmul, ← hx₁]
  exact hk

theorem bchar_ne_zero' {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have hχ : (X k).χ (la k) γ ≠ 0 := by
      obtain ⟨N, hN, hN1⟩ := (X k).χ_fin (la k)
      intro h0'
      have := hN1 γ hγ
      rw [h0', zero_pow hN.ne'] at this
      exact zero_ne_one this
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * (X k).χ (la k) γ * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, mul_assoc]
    have hne := mul_ne_zero (hν g) (mul_ne_zero (bchar_ne_zero' (la k) hb) hχ)
    have key : ν g * (bchar (la k) b * (X k).χ (la k) γ) * ∑ i, c i * P i k x =
        ∑ i, c i * (ν g * P i (dict g).1 (dict g).2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
    rw [h] at key
    exact (mul_eq_zero.1 key).resolve_left hne
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]

open GlobalTheory.CoverRead GlobalTheory.Member in
set_option maxHeartbeats 1000000 in

theorem cover_rd_linearIndependent : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) → LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => C.rd a (f i)) := by
  intro D T hT j hj σ hσ C hC hcc a n hdn m f hf hind
  obtain ⟨-, hA, hinc, hU, hdom, hr, g, e, F, ik, φ, th, hW, hth, hD⟩ := hC
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hσ₂ : GoodEmb C.d.c₂ C.σ₂ := by
    rw [← hinc] at hσ
    exact hσ
  have hI : LinearIndependent ℂ (fun i => rdU C.U₂ (f i)) :=
    (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ _ _ _ _
      (Formalism.L2.PjFree.Unf.ofPj C.U₂) hU a n).1 m f hf hind
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along C.U₂.X (laU C.U₂ a n) C.dict₂
    (fun k x hx => dict_onto (T.V j σ) hr C.U₂ C.dict₂ _ e F ik φ th _ hσ₂ hA (by omega) hU hW hD hio hth hx₀ hdom
      k x hx)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (C.cc₂ (C.dict₂ g).1 * T.mu j σ g)) ?_
    (fun i => rdU C.U₂ (f i)) (fun i k => hU.2.2.2.2.1 a n hdn _ (hf i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [hcc]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(hT.muVal j hj σ hσ).norm g]; exact one_ne_zero)
  · intro i g
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

end GlobalTheory.CoverIndep
