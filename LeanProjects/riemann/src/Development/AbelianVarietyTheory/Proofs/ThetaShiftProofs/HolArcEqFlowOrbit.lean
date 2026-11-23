import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfTraceLattice
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorantStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentEigenbasisExponential
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseBlock
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodsEqFramePeriods

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix

namespace GlobalTheory.ArcFlow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {r : ℕ} (X : Data E r)

lemma perFr_smul (x : Frame X.Ψ r) (a : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (a • v) τ i = τ a * perFr X x v τ i := by
  have hemb : ∀ ρ : E →+* ℂ, Data.emb ρ (a • v) = ρ a • Data.emb ρ v := fun ρ => by
    funext k; simp [Data.emb]
  unfold perFr
  split_ifs
  · rw [hemb, Matrix.mulVec_smul]; rfl
  · simp
  · rw [hemb, hermC_smul_right]; simp [conjEmb]
  · simp
  · simp

lemma eq_of_hermC_lattice (τ : E →+* ℂ) (u u' : Fin r → ℂ)
    (h : ∀ v ∈ X.Λ, hermC τ X.Gm u (Data.emb τ v) = hermC τ X.Gm u' (Data.emb τ v)) : u = u' := by
  have h1 : ∀ v, hermC τ X.Gm u (Data.emb τ v) = hermC τ X.Gm u' (Data.emb τ v) := fun v => by
    obtain ⟨d, hd, hv⟩ := HermitianTraceFormVanishing.exists_smul_mem (R := 𝓞 E) (F := E) X.Λ (x := v) (by rw [X.Λ_span]; trivial)
    have h2 := h _ hv
    have hemb : Data.emb τ (d • v) = τ d • Data.emb τ v := by
      funext k; simp [Data.emb, Algebra.smul_def]
    rw [hemb, hermC_smul_right, hermC_smul_right] at h2
    refine mul_left_cancel₀ ?_ h2
    simpa using hd
  have hdet : (X.Gm.map τ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; simpa using X.Gm_det
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hdet
  funext b
  have h2 := h1 (Pi.single b 1)
  simp only [hermC, Data.emb, Pi.single_apply, apply_ite τ, apply_ite (starRingEnd ℂ), map_one, map_zero,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  simp [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib, h2]

lemma flow_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) (h : ∀ (τ : X.Ψ) (a : Fin r), (a : ℕ) < X.p0 →
      FD.col (mat (X.flow ξ s x) τ) a = FD.col (mat x' τ) a) : X.flow ξ s x ∈ X.dom := by
  refine AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · have hm : mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl
    rw [hm, Matrix.det_mul]
    refine mul_ne_zero (fun h0 => ?_) (hx τ).1
    have := congrArg Matrix.det (EmbeddingHermitianPairs.flowMat_mul X hξ τ (s τ) (-s τ))
    rw [add_neg_cancel, EmbeddingHermitianPairs.flowMat_zero, Matrix.det_mul, h0] at this
    simp at this
  · have hg : X.gramPos (X.flow ξ s x) τ = X.gramPos x' τ := by
      ext a b
      rw [Data.gramPos_apply, Data.gramPos_apply]
      unfold Data.colP
      rw [h τ _ a.2, h τ _ b.2]
    rw [hg]
    exact X.gramPos_posDef hx' τ

end Frames

lemma exists_comb_single {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (z : ∀ τ : T, Fin (m τ) → (Fin g → ℂ))
    (hz : ∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (e jj).1 = τ) (j : Fin g) :
    ∃ a : Fin (m (e j).1) → ℂ, ∑ i, a i • z (e j).1 i = Pi.single j 1 := by
  classical
  obtain ⟨⟨τ, k⟩, rfl⟩ := e.symm.surjective j
  rw [Equiv.apply_symm_apply]
  dsimp only
  let A : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := Matrix.of fun i i' => z τ i (e.symm ⟨τ, i'⟩)
  have hext : ∀ (a : Fin (m τ) → ℂ) (u : Fin g → ℂ), (∀ jj, u jj ≠ 0 → (e jj).1 = τ) →
      (∀ i', Matrix.vecMul a A i' = u (e.symm ⟨τ, i'⟩)) → ∑ i, a i • z τ i = u := by
    intro a u hu h
    funext jj
    obtain ⟨⟨τ', k'⟩, rfl⟩ := e.symm.surjective jj
    by_cases hτ : τ' = τ
    · subst hτ
      rw [← h]
      simp [A, Matrix.vecMul, dotProduct, Finset.sum_apply]
    · have h1 : u (e.symm ⟨τ', k'⟩) = 0 := by
        by_contra hh; exact hτ (by simpa using hu _ hh)
      rw [h1, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h2 : z τ i (e.symm ⟨τ', k'⟩) = 0 := by
        by_contra hh; exact hτ (by simpa using (hz τ).2 i _ hh)
      simp [h2]
  have hinj : Function.Injective A.vecMul := by
    intro a a' haa
    have h0 : ∑ i, (a - a') i • z τ i = 0 := hext _ 0 (fun _ h => absurd rfl h) fun i' => by
      rw [Matrix.sub_vecMul]; simp [show Matrix.vecMul a A = Matrix.vecMul a' A from haa]
    have := Fintype.linearIndependent_iff.1 (hz τ).1 _ h0
    exact sub_eq_zero.1 (funext this)
  obtain ⟨a, ha⟩ := Matrix.vecMul_surjective_iff_isUnit.2 (Matrix.vecMul_injective_iff_isUnit.1 hinj)
    (Pi.single k 1)
  refine ⟨a, hext a _ (fun jj hjj => ?_) fun i' => ?_⟩
  · by_contra hne
    exact hjj (Pi.single_eq_of_ne (fun hh => hne (by rw [hh, Equiv.apply_symm_apply])) _)
  · rw [show Matrix.vecMul a A = Pi.single k 1 from ha]
    by_cases h : i' = k
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne fun hh => h (by simpa using hh)]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (Uw : UnfWit U)

lemma exists_comp (hL : Out.Laws) (hU : IsUnf U) (i : Fin Uw.F.n) (P : (Uw.F.Di i).La →+ (Fin Uw.g → ℂ))
    (hP : IsPeriod (Uw.F.Di i) (fun j => relab c σ (Uw.e j).1) P) :
    ∃ k, Uw.ik k = i ∧ Nonempty (U.X k).dom := by
  obtain ⟨u, -, h2, h3, h4⟩ := GlobalTheory.LieFrame.exists_eigenbasis E H Dw l Xo c σ Uw.g Uw.e Uw.F i P hP
  obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.Frames.exists_local_generator hL.secBaseChange E H Dw l Xo ℂ (Uw.F.u i P)
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hg' : IsUnit ((RingHom.id ℂ) g) := isUnit_iff_ne_zero.2 fun h => hg h
  let ψ : Localization.Away g →+* ℂ := IsLocalization.Away.lift g hg'
  have hψ : ψ.comp (algebraMap ℂ (Localization.Away g)) = RingHom.id ℂ := IsLocalization.Away.lift_comp g hg'
  have hx : Uw.F.u i P = spMap ψ ≫ spMap (algebraMap ℂ (Localization.Away g)) ≫ Uw.F.u i P := by
    have : spMap ψ ≫ spMap (algebraMap ℂ (Localization.Away g)) = 𝟙 _ := by
      unfold spMap
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      exact Spec.map_id _
    rw [← Category.assoc, this, Category.id_comp]
  obtain ⟨θ', hθ', -⟩ := GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo _ _ ψ 1 _ _ hx θ
  have hgen := (hθ ℂ ψ _ θ' hx hθ').1
  let y : FrPt Xo c (CAt σ) := ⟨Uw.F.u i P, Uw.F.over_σ i P hP, u, h2, h3, h4, θ', hgen⟩
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y
  exact ⟨k, Uw.F.disj _ _ _ _ (Uw.period k x) hP ((Uw.lie k x).1.symm.trans ht.1.symm), ⟨x⟩⟩

lemma exists_idx (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) :
    ∃ idx : Fin Uw.g ≃ (U.X k).Ψ × Fin r,
      (∀ j, relab c σ (Uw.e j).1 =
        if ((idx j).2 : ℕ) < Dw.q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧
      (∀ j, ((idx j).2 : ℕ) < Dw.q → ((Uw.e j).2 : ℕ) < Dw.q) ∧
      ∀ (x : Frame (U.X k).Ψ r) (v : Fin r → E) j, perFr (U.X k) x v (relab c σ (Uw.e j).1) (Uw.e j).2 =
        if ((idx j).2 : ℕ) < Dw.q then
          hermC (idx j).1.1 (U.X k).Gm (FD.col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin Uw.g ≃ (U.X k).Ψ × Fin r, ∀ j,
      (relab c σ (Uw.e j).1 ∈ (U.X k).Ψ ∧ (idx j).1.1 = relab c σ (Uw.e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (Uw.e j).2) ∨
      (relab c σ (Uw.e j).1 ∉ (U.X k).Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (Uw.e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (Uw.e j).2 ∧ ((Uw.e j).2 : ℕ) < Dw.q) :=
    ⟨Uw.e.trans f, fun j => hf (Uw.e j)⟩
  refine ⟨idx, fun j => ?_, fun j hj => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · omega
    · exact d
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (Uw.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl

lemma exists_frame (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (hκ : (U.X k).κ0 = 2 * (U.X k).ξ0)
    (P : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ))
    (hP : IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) P) : ∃ x, Uw.Pm k x = P := by
  obtain ⟨idx, hty, -, hper⟩ := exists_idx Uw hσ hU k
  obtain ⟨hp, hq⟩ := Uw.F.sig (Uw.ik k)
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  rw [← hq] at hty hper hp0
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  have hrange : LinearMap.range φ = (U.X k).Λ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨x, hx, h⟩ := exists_frame_of_isPeriod E H (Uw.F.Di (Uw.ik k)) r (-(U.X k).ξ0) (U.X k).Gm φ (U.X k).Ψ hΨ
    Uw.g idx _ hty (by rw [HermitianTraceFormVanishing.cc_neg, (U.X k).ξ0_im]) (fun τ hτ => by
      have := (U.X k).κ0_sign ⟨τ, hτ⟩
      rw [hκ, map_mul, map_ofNat] at this
      simp at this ⊢
      linarith)
    ⟨Subtype.val_injective.comp (Uw.φ k).injective, by rw [← LinearMap.coe_range, hrange]; exact (U.X k).Λ_span,
      (U.X k).Gm_herm, (U.X k).Gm_det, Uw.iso k⟩ (by rw [hp, hq]; exact hU.1) P hP
  rw [← hp0] at hx
  exact ⟨⟨x, hx⟩, AddMonoidHom.ext fun v => funext fun j =>
    (Uw.Pm_eq k _ v j).trans ((hper x _ j).trans (h v j).symm)⟩

lemma flow_period (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (hκ : (U.X k).κ0 = 2 * (U.X k).ξ0)
    (nn : (Uw.F.Di (Uw.ik k)).La → (Uw.F.Di (Uw.ik k)).La) (ξ' : Fin r → E) (hξ' : herm (U.X k).Gm ξ' ξ' = 0)
    (sE : E) (hs : cc sE = sE)
    (hnn : ∀ v, (Uw.φ k (nn v) : Fin r → E) =
      (-(sE * (U.X k).κ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) • ξ')
    (x : (U.X k).dom) (d : ℂ) (P : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ))
    (hP : IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) P)
    (hPx : ∀ v, P v = Uw.Pm k x v + d • Uw.Pm k x (nn v)) :
    ∃ hx : (U.X k).flow ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1 ∈ (U.X k).dom, Uw.Pm k ⟨_, hx⟩ = P := by
  obtain ⟨idx, hty, hlt, hper⟩ := exists_idx Uw hσ hU k
  obtain ⟨hp0, -⟩ := hU.2.1 k
  have hre : ∀ τ : E →+* ℂ, ((τ sE).re : ℂ) = τ sE := fun τ => by
    have := map_cc τ sE
    rw [hs] at this
    exact Complex.conj_eq_iff_re.1 this.symm
  have key : ∀ v j, perFr (U.X k) ((U.X k).flow ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1)
      (Uw.φ k v : Fin r → E) (relab c σ (Uw.e j).1) (Uw.e j).2 = P v j := by
    intro v j
    rw [hPx, Pi.add_apply, Pi.smul_apply, Uw.Pm_eq, Uw.Pm_eq, hnn, perFr_smul, hty j]
    split_ifs with hj
    · have h := GlobalTheory.PerFlow.flow_conj (U.X k) ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1 (Uw.φ k v : Fin r → E)
        (idx j).1 (Uw.e j).2 (hp0 ▸ hlt j hj)
      have h2 : conjEmb (idx j).1.1 sE = (((idx j).1.1 sE).re : ℂ) := by
        rw [← hre (conjEmb (idx j).1.1)]; simp [conjEmb]
      change perFr _ _ _ (conjEmb (idx j).1.1) _ = perFr _ _ _ (conjEmb (idx j).1.1) _ +
        d • (conjEmb (idx j).1.1 _ * perFr _ _ _ (conjEmb (idx j).1.1) _)
      rw [h, mul_assoc sE, map_neg, map_mul _ sE, h2, smul_eq_mul]
      ring
    · rw [GlobalTheory.PerFlow.flow_mem (U.X k) hξ', mul_assoc sE, map_neg, map_mul _ sE, hre, smul_eq_mul]
      ring
  obtain ⟨x', hx'⟩ := exists_frame Uw hσ hU k hκ P hP
  have hx : (U.X k).flow ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1 ∈ (U.X k).dom := by
    refine flow_mem_dom (U.X k) hξ' _ x.2 x'.2 fun τ a ha => eq_of_hermC_lattice (U.X k) τ.1 _ _ fun w hw => ?_
    have h1 := key ((Uw.φ k).symm ⟨w, hw⟩) (idx.symm (τ, a))
    rw [← hx', Uw.Pm_eq, hper, hper] at h1
    rw [hp0] at ha
    simpa only [Equiv.apply_symm_apply, if_pos ha, LinearEquiv.apply_symm_apply] using h1
  exact ⟨hx, AddMonoidHom.ext fun v => funext fun j => (Uw.Pm_eq k _ v j).trans (key v j)⟩

lemma orbit (hL : Out.Laws) (hσ : GoodEmb c σ) (hU : IsUnf U) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (hY : Module.finrank (𝓞 E) Y = 1) (be : LinearMap.BilinForm ℤ Y)
    (hsym : ∀ a b, be a b = be b a) (hpos : ∀ a, a ≠ 0 → 0 < be a a) (i : Fin Uw.F.n) (T : ℝ)
    (Pw : ℂ → ((Uw.F.Di i).La →+ (Fin Uw.g → ℂ))) (y : (Uw.F.Di i).La →ₗ[𝓞 E] Y) (hy : Function.Surjective y)
    (hPw : ∀ w : ℂ, T < w.im → IsPeriod (Uw.F.Di i) (fun j => relab c σ (Uw.e j).1) (Pw w))
    (nn : (Uw.F.Di i).La →ₗ[𝓞 E] (Uw.F.Di i).La)
    (hlin : ∀ w w₁ v, Pw w v = Pw w₁ v + (w - w₁) • Pw w₁ (nn v))
    (hnn : ∀ v v', -(Uw.F.Di i).EF (nn v) v' = be (y v) (y v'))
    (hker : ∀ t, (∀ v', y v' = 0 → (Uw.F.Di i).EF t v' = 0) → y t = 0)
    (hrep : ∀ η : Module.Dual ℤ Y, ∃ t, ∀ v', -(Uw.F.Di i).EF t v' = η (y v'))
    (ξ : Module.Dual ℤ Y) (hξ : ξ ≠ 0) (w₁ : ℂ) (hw₁ : T < w₁.im) :
    ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E), (U.X k).IsIso ξ' ∧ IsBePar ξ be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ ∀ (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ x ∈ (U.X k).dom, ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di i).EF t v' = ξ (y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ∀ w : ℂ, T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x ∈ (U.X k).dom, (∀ v, Uw.Pm k ⟨_, hx⟩ (γ v) = L (Pw w v)) ∧ AnLie Uw.F i (Pw w) (U.un k ⟨_, hx⟩) z := by
  classical
  obtain ⟨k, rfl, ⟨x₀⟩⟩ := exists_comp Uw hL hU i _ (hPw w₁ hw₁)
  obtain ⟨t, ht⟩ := hrep ξ
  have hyt : y t = 0 := hker t fun v' hv' => by
    have := ht v'
    rw [hv', map_zero] at this
    exact neg_eq_zero.1 this
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      have ht0 : t = 0 := (Uw.φ k).injective (Subtype.ext (Subsingleton.elim _ _))
      refine absurd (LinearMap.ext fun a => ?_) hξ
      obtain ⟨v, rfl⟩ := hy a
      rw [← ht, ht0]; simp
    · exact h
  obtain ⟨-, -, -, -, Hm, hHm⟩ := Uw.period k x₀
  have hκ := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x₀ Hm hσ hU hHm).2.1 hr
  obtain ⟨sE, hiso, hbe, hsp, hlev, hform⟩ := rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) y hY hκ hy be hsym hpos nn hnn
    hrep ξ hξ t ht hyt
  refine ⟨k, _, sE, hiso, hbe, fun τ => hsp τ.1, hlev, fun z hz => ?_⟩
  obtain ⟨V, hVu, hVt, hVw⟩ := GlobalTheory.CoverFrame.exists_inverse_block Uw.e (fun j => z (Uw.e j).1 (Uw.e j).2)
    (fun j => by
      obtain ⟨a, ha⟩ := exists_comb_single Uw.e z hz j
      refine ⟨a, ?_⟩
      rw [← ha]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.apply_symm_apply])
  have hVz : ∀ τ i, V *ᵥ z τ i = Pi.single (Uw.e.symm ⟨τ, i⟩) 1 := fun τ i => by
    have := hVw (Uw.e.symm ⟨τ, i⟩)
    rwa [Equiv.apply_symm_apply] at this
  have hP' : ∀ w : ℂ, T < w.im → ∃ P', IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) P' ∧
      ∀ a, P' a = V *ᵥ Pw w a := fun w hw =>
    GlobalTheory.PeriodLin.exists_period_mulVec E H _ _ _ _ V (hPw w hw) hVu (fun j j' h => by rw [hVt j j' h])
  obtain ⟨P₁, hP₁, hP₁e⟩ := hP' w₁ hw₁
  obtain ⟨x, hx⟩ := exists_frame Uw hσ hU k hκ P₁ hP₁
  have hu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).2 hVu
  refine ⟨x.1, x.2, LinearEquiv.ofBijective V.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hu, Matrix.mulVec_surjective_iff_isUnit.2 hu⟩,
    LinearEquiv.refl _ _, fun _ _ => rfl, hVz, ⟨t, ht, rfl⟩, fun w hw => ?_⟩
  obtain ⟨P, hP, hPe⟩ := hP' w hw
  obtain ⟨hxw, hPw'⟩ := flow_period Uw hσ hU k hκ nn _ hiso.2.1 sE hbe.1 hform x (w - w₁) P hP fun v => by
    rw [hx, hPe, hP₁e, hP₁e, hlin w w₁ v, Matrix.mulVec_add, Matrix.mulVec_smul]
  obtain ⟨-, hpt, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ _ _ Uw.F _ (Pw w) P
    (LinearEquiv.refl _ _) V (hPw w hw) hP (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hPe
  have hlie := Uw.lie k ⟨_, hxw⟩
  rw [hPw'] at hlie
  refine ⟨hxw, fun v => by rw [hPw']; exact hPe v, hlie.1.trans hpt.symm, fun τ i => ?_⟩
  refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F _ _ (hPw w hw) _ P (Matrix.mulVecLin V) hP hex
    _ _).2 ?_
  rw [Matrix.mulVecLin_apply, hVz]
  exact hlie.2 τ i

theorem holArc_eq_flow_orbit : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F), GoodEmb c σ → IsUnf U → Module.finrank (𝓞 E) a.D₀.X = 1 → ∀ ξ : Module.Dual ℤ a.D₀.X, ξ ≠ 0 → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ ∀ (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ x ∈ (U.X k).dom, ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ∀ w : ℂ, Ha.T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x ∈ (U.X k).dom, (∀ v, Uw.Pm k ⟨_, hx⟩ (γ v) = L (Ha.Pw w v)) ∧ AnLie Uw.F Ha.i (Ha.Pw w) (U.un k ⟨_, hx⟩) z := by
  intro hL _ E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha hσ hU hY ξ hξ w₁ hw₁
  obtain ⟨nn, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
  refine orbit Uw hL hσ hU hY a.be a.be_symm a.be_pos Ha.i Ha.T Ha.Pw Ha.y Ha.y_onto Ha.period nn
    (fun w w₁ v => ?_) h2 h5 (fun η => (h6 η).exists) ξ hξ w₁ hw₁
  rw [Ha.Pw_eq, Ha.Pw_eq, Ha.Pw_eq, h1 (nn v), h4 _ (h3 v), map_zero, smul_zero, add_zero, ← h1, sub_smul]
  abel

end GlobalTheory.ArcFlow
