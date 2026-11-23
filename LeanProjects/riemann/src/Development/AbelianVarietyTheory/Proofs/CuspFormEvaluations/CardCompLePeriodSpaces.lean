import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompInj

open ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Frames
open scoped Matrix ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem dom_nonempty {r : ℕ} (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP0 hP using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP0 τ, fun i => ?_⟩⟩
  apply GlobalTheory.PeriodOnto.lminor_sign
  have h1 : GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (mat (fun τ => P τ) τ) = 1 := by
    change GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (P τ) = 1
    rw [hP, GlobalTheory.PeriodOnto.sgnMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> simp
  rw [h1]
  exact Matrix.PosDef.one

theorem im_eq_of_span {g : ℕ} {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ) (h : ∀ x y, (hermForm A (P x) (P y)).im = (hermForm B (P x) (P y)).im)
    (z z' : Fin g → ℂ) : (hermForm A z z').im = (hermForm B z z').im := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  have hz' : z' ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  unfold hermForm at *
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    induction hz' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact h x y
    | zero => simp
    | add _ _ _ _ h1 h2 =>
      simp only [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h1, h2]
    | smul c _ _ h1 =>
      simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h1]
  | zero => simp
  | add _ _ _ _ h1 h2 => simp only [add_dotProduct, Complex.add_im, h1, h2]
  | smul c _ _ h1 => simp only [smul_dotProduct, Complex.smul_im, h1]

theorem not_im_neg (H : Host E) (D : Datum H) {r : ℕ} (hr : 1 ≤ r) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La → (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r)
    (ty : Fin g → (E →+* ℂ)) (q : ℕ) (hξ : cc ξ = -ξ) (hG : ∀ a b, cc (Gm a b) = Gm b a)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (x : Frame Ψ r) (hx : x ∈ GG Ψ Gm q) (P : D.La →+ (Fin g → ℂ))
    (hP : ∀ v k, P v k = GlobalTheory.FramePeriod.locPer (idx k).1.1 Gm q (mat x (idx k).1) (Data.emb (idx k).1.1 (φ v))
      (idx k).2) (hper : IsPeriod D ty P) (hneg : ∀ τ ∈ Ψ, (τ ξ).im < 0) : False := by
  classical
  obtain ⟨-, -, -, hspan, Hm, -, hpos, hIm⟩ := hper
  choose Hl hH hp hI using fun τ : Ψ =>
    (GlobalTheory.FramePeriod.exists_loc τ.1 Gm hG q (mat x τ) (hx τ).1 (hx τ).2).2
  have hblk : ∀ v (τ : Ψ), (fun a => P v (idx.symm (τ, a))) =
      GlobalTheory.FramePeriod.locPer τ.1 Gm q (mat x τ) (Data.emb τ.1 (φ v)) := by
    intro v τ
    funext a
    rw [hP, idx.apply_symm_apply]
  have key := im_eq_of_span P hspan Hm (Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0) (by
    intro v w
    rw [GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, hIm]
    have h1 : ((D.EF v w : ℤ) : ℝ) = ((Algebra.trace ℚ E (ξ * herm Gm (φ v) (φ w)) : ℚ) : ℝ) := by
      rw [← hEF]; simp
    rw [h1, GlobalTheory.FramePeriod.trace_re Ψ hcm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hblk, hblk, Complex.im_ofReal_mul, hI, map_mul, ← hermC_emb]
    have h2 : (τ.1 ξ).re = 0 := by
      have h3 := congrArg Complex.re (emb_cc τ.1 ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.conj_re] at h3
      linarith
    rw [Complex.mul_re, h2]
    ring)
  have hI' : ∀ (A : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ),
      (hermForm A (Complex.I • z) z).im = (hermForm A z z).re := by
    intro A z
    simp [hermForm]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
    by_cases h : ComplexEmbedding.conjugate σ ∈ Ψ
    · exact ⟨_, h⟩
    · exact ⟨σ, (hcm σ).2 h⟩
  have hz : (fun _ => 1 : Fin g → ℂ) ≠ 0 := fun h => by
    simpa using congrFun h (idx.symm (⟨τ, hτ⟩, ⟨0, hr⟩))
  have h1 := key (Complex.I • fun _ => 1) (fun _ => 1)
  rw [hI', hI', GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum] at h1
  have h2 := hpos _ hz
  rw [h1] at h2
  refine absurd h2 (not_lt.2 (Finset.sum_nonpos fun t _ => ?_))
  rw [Complex.re_ofReal_mul]
  have h3 := hp t (fun _ => 1) (fun h => by simpa using congrFun h ⟨0, hr⟩)
  have h4 := hneg t.1 t.2
  nlinarith

variable {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_idx {c : Coeff l} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {r g : ℕ} (hr : r = Dw.p + Dw.q)
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j, relab c σ (e j).1 =
      if ((idx j).2 : ℕ) < Dw.q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < Dw.q then hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
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
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl

theorem exists_frame {c : Coeff l} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {r g : ℕ} (h1 : 1 ≤ r)
    (hr : r = Dw.p + Dw.q) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) (D : Datum H) (hp : D.p = Dw.p) (hq : D.q = Dw.q)
    (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (hEF : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (x₀ : Frame X.Ψ r) (hx₀ : x₀ ∈ X.dom) (P₀ : D.La →+ (Fin g → ℂ))
    (hP₀ : ∀ a j, P₀ a j = perFr X x₀ (φ a : Fin r → E) (relab c σ (e j).1) (e j).2)
    (hper₀ : IsPeriod D (fun j => relab c σ (e j).1) P₀) (P : D.La →+ (Fin g → ℂ))
    (hper : IsPeriod D (fun j => relab c σ (e j).1) P) :
    ∃ x ∈ X.dom, ∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2 := by
  obtain ⟨idx, hi, hper'⟩ := exists_idx hσ hr e X hp0 hty
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    rcases X.κ0_xi with h | h
    · intro τ hτ
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
    · exfalso
      refine not_im_neg H D h1 (-X.ξ0) X.Gm (fun a => (φ a : Fin r → E)) X.Ψ X.cmType idx _ Dw.q hξ X.Gm_herm hEF
        x₀ (hp0 ▸ hx₀) P₀ (fun v k => by rw [hP₀, hper']; rfl) hper₀ fun τ hτ => ?_
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_neg, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
  let ψ : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  have hψ : Set.range ψ = (X.Λ : Set (Fin r → E)) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (φ a).2
    · intro hy
      exact ⟨φ.symm ⟨y, hy⟩, by simp [ψ]⟩
  obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm ψ X.Ψ hty g idx _
    (by rw [hq]; exact hi) hξ hpos
    ⟨fun a b hab => φ.injective (Subtype.ext hab), by rw [hψ]; exact X.Λ_span, X.Gm_herm, X.Gm_det, hEF⟩
    (by rw [hp, hq]; exact hr) P hper
  refine ⟨x, by rw [hq, ← hp0] at hx; exact hx, fun a j => ?_⟩
  rw [hper', hPx, hq]
  rfl

theorem frBor_of_eq {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) (hx : y'.x = y.x) (hu : ∀ τ i, y'.u τ i = y.u τ i) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨g, a, h⟩ := Model.exists_frChg y y' hx
  have ha := Model.FrChg.isUnit h
  refine ⟨fun k => Option.elim k ha.unit (fun _ => 1), (Model.frBor_iff _ _ _).2 ⟨fun _ => 1, fun τ i => ?_,
    fun τ i j hij => Matrix.one_apply_ne hij.ne, hx, fun τ i => ?_, h.2.2⟩⟩
  · exact Matrix.one_apply_eq i
  · rw [hu]
    exact (GlobalTheory.Reg.BorelGroupoid.chg_refl y).2.1 τ i

end GlobalTheory.CompInj

namespace GlobalTheory

open CompInj

theorem card_comp_le_periodSpaces : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  intro _ E _ _ _ H D l Xo c σ r U h1 hσ hU
  obtain ⟨hr, hX, -, hfib, -, g, e, F, ik, φ, hEF, hP⟩ := hU
  refine ⟨g, _, F, (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 D g e, ?_⟩
  suffices hinj : Function.Injective ik by simpa using Fintype.card_le_of_injective ik hinj
  intro k k' hk
  obtain ⟨x, hx⟩ := dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2 ψ hEF'
    x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨γ, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

end GlobalTheory
