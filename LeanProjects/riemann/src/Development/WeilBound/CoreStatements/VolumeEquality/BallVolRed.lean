import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
  GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)

def permQ (π : Ψ ≃ Ψ) : Ψ × Fin j × Fin j' ≃ Fin n := (π.prodCongr (Equiv.refl _)).trans q

theorem ballDom_permQ (π : Ψ ≃ Ψ) : ballDom (permQ q π) = ballDom q :=
  Set.ext fun t => ⟨fun h τ => by
    obtain ⟨τ, rfl⟩ := π.surjective τ
    exact h τ, fun h τ => h (π τ)⟩

theorem ballPot_permQ (π : Ψ ≃ Ψ) (t : Fin n → ℂ) : ballPot (permQ q π) t = ballPot q t :=
  congrArg Neg.neg (π.sum_comp fun τ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)

theorem ballMeas_permQ (π : Ψ ≃ Ψ) : ballMeas (permQ q π) = ballMeas q := by
  simp only [ballMeas, ballDens, ballDom_permQ, ballPot_permQ]

theorem star_measurePreserving : MeasurePreserving (star : (Fin n → ℂ) → Fin n → ℂ) volume volume :=
  volume_preserving_pi (f := fun _ => Complex.conjLIE) fun _ => Complex.conjLIE.measurePreserving

theorem ballMeas_star {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ballMeas q (star ⁻¹' S) = ballMeas q S := by
  have hemb : MeasurableEmbedding (star : (Fin n → ℂ) → Fin n → ℂ) :=
    (Homeomorph.mk ⟨star, star, star_star, star_star⟩ continuous_star continuous_star).measurableEmbedding
  rw [ballMeas_apply q hS hD, ballMeas_apply q (hemb.measurable hS)
    (fun t ht => by simpa using star_mem_ballDom (hD ht)),
    ← star_measurePreserving.setLIntegral_comp_preimage_emb hemb _ S]
  simp only [ballDens, ballPot_star]

theorem integral_ballDens {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ∫ t in S, ballDens q t = (ballMeas q S).toReal := by
  rw [ballMeas_apply q hS hD]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
    (DictMeas.measurable_ballDens q).aestronglyMeasurable

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

def permFam (F : UnivFam E Ψ j j' n g Λ) (π : Ψ ≃ Ψ) : UnivFam E Ψ j j' n g Λ where
  q := permQ F.q π
  σ τ := F.σ (π τ)
  cm := ⟨F.cm.1.comp π.injective, fun s => by
    rw [π.exists_congr_right (q := fun τ => F.σ τ = s),
      π.exists_congr_right (q := fun τ => F.σ τ = (starRingEnd ℂ).comp s)]
    exact F.cm.2 s⟩
  form := F.form
  R := F.R
  form_eq := F.form_eq
  hol := by rw [ballDom_permQ]; exact F.hol
  sig t ht τ := F.sig t (ballDom_permQ F.q π ▸ ht) (π τ)
  b τ := F.b (π τ)
  frames := by
    rw [ballDom_permQ]
    exact ⟨fun τ => F.frames.1 (π τ), fun t ht τ => F.frames.2 t ht (π τ)⟩
  logDet_eq t ht := by
    rw [ballPot_permQ, ← F.logDet_eq t (ballDom_permQ F.q π ▸ ht)]
    exact π.sum_comp fun τ => Real.log ((F.R t).gram fun i => F.b τ i t).det.re
  univ R' hf hs := by
    rw [ballDom_permQ]
    exact F.univ R' hf fun τ => by
      obtain ⟨τ, rfl⟩ := π.surjective τ
      exact hs τ

theorem permFam_fund {F : UnivFam E Ψ j j' n g Λ} (π : Ψ ≃ Ψ) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (permFam F π).IsFundSet Γ FF := by
  have e : ballDom (permFam F π).q = ballDom F.q := ballDom_permQ F.q π
  unfold UnivFam.IsFundSet
  rw [e]
  exact h

theorem conjFam_fund {F : UnivFam E Ψ j j' n g Λ} {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (conjFam F).IsFundSet Γ (star ⁻¹' FF) := by
  refine ⟨continuous_star.measurable h.1, fun t ht => ?_, fun t ht => ?_, fun t ht t' ht' ⟨γ, hγ, he⟩ => ?_⟩
  · show t ∈ ballDom F.q
    simpa using star_mem_ballDom (h.2.1 ht)
  · obtain ⟨t', ht', γ, hγ, he⟩ := h.2.2.1 (star t) (star_mem_ballDom (q := F.q) ht)
    refine ⟨star t', by simpa using ht', γ, hγ, eqvBy_conj (fun x => rfl) (fun x => ?_) he⟩
    show star ((F.R (star (star t'))).P x) = _
    rw [star_star]
  · refine star_injective (h.2.2.2 _ ht _ ht' ⟨γ, hγ, eqvBy_conj (fun x => ?_) (fun x => ?_) he⟩)
    · exact (star_star _).symm
    · exact (star_star _).symm

theorem normalise (F : UnivFam E Ψ j j' n g Λ) (r : 𝓞 E) (d : ℕ) (hr : r ^ 2 = -(d : 𝓞 E))
    (hc : ∀ τ τ', F.σ τ r = F.σ τ' r) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)} (h : F.IsFundSet Γ FF) :
    ∃ (F₁ : UnivFam E Ψ j j' n g Λ) (FF₁ : Set (Fin n → ℂ)), (∀ τ, F₁.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ∧
      (F₁.form = F.form ∨ F₁.form = -F.form) ∧ F₁.IsFundSet Γ FF₁ ∧ ballMeas F₁.q FF₁ = ballMeas F.q FF := by
  by_cases h0 : ∀ τ, F.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)
  · exact ⟨F, FF, h0, Or.inl rfl, h, rfl⟩
  · obtain ⟨τ₀, h1⟩ := not_forall.1 h0
    have h2 : F.σ τ₀ r ^ 2 = (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 := by
      rw [← map_pow, hr, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      simp
    have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left h1
    refine ⟨conjFam F, star ⁻¹' FF, fun τ => ?_, Or.inr rfl, conjFam_fund h, ballMeas_star F.q h.1 h.2.1⟩
    show starRingEnd ℂ (F.σ τ r) = _
    rw [hc τ τ₀, h3]
    simp

omit [NumberField E] [IsCMField E] in
theorem exists_perm {σ σ' : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) (h' : IsCMFam σ') (r : 𝓞 E) {c : ℝ} (hc : 0 < c)
    (hs : ∀ τ, σ τ r = Complex.I * (c : ℂ)) (hs' : ∀ τ, σ' τ r = Complex.I * (c : ℂ)) :
    ∃ π : Ψ ≃ Ψ, ∀ τ, σ' (π τ) = σ τ := by
  have : ∀ τ, ∃ τ', σ' τ' = σ τ := fun τ => (h'.2 _).2 fun ⟨τ', e⟩ => by
    have e1 := hs' τ'
    rw [e, RingHom.comp_apply, hs] at e1
    have := congrArg Complex.im e1
    simp at this
    linarith
  choose f hf using this
  have hi : Function.Injective f := fun a b e => h.1 (by rw [← hf, ← hf, e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hi), hf⟩

theorem label_rt {H : Host E} {l : Level H} (c : Coeff l) (τ τ' : CMType H) :
    labelEmb c (.inr τ) H.rt = labelEmb c (.inr τ') H.rt := by
  refine Subtype.ext ?_
  show τ.1 ((H.bar H.rt : 𝓞 E) : E) = τ'.1 ((H.bar H.rt : 𝓞 E) : E)
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj, τ.2, τ'.2]

theorem ballVolEq_of (h : FamVol) : BallVolEq := by
  intro _ E _ _ _ _ H D l Xo c Y n B FF hq hp hF k k'
  have hn := fun k => normalise (B.F k) H.rt H.d H.rt_sq
    (fun τ τ' => by rw [B.σ_eq, B.σ_eq, RingHom.comp_apply, RingHom.comp_apply, label_rt c τ τ']) (hF k)
  obtain ⟨F₁, FF₁, s₁, f₁, u₁, m₁⟩ := hn k
  obtain ⟨F₂, FF₂, s₂, f₂, u₂, m₂⟩ := hn k'
  have hd : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
  obtain ⟨π, hπ⟩ := exists_perm F₁.cm F₂.cm H.rt hd s₁ s₂
  have hf : ∀ k (f : _ →ₗ[ℤ] _ →ₗ[ℤ] ℤ), (f = (B.F k).form ∨ f = -(B.F k).form) → f = (B.Di k).EF ∨ f = -(B.Di k).EF := by
    intro k f hf
    rcases hf with rfl | rfl <;> rcases B.form_eq k with e | e <;> rw [e] <;> simp
  have key := h E H l (B.Di k) (B.Di k') (CMType H) D.p D.q n B.g F₁ (permFam F₂ π) (B.Γ k) (B.Γ k') FF₁ FF₂ _
    (by omega) (by omega) (by omega) hd (funext hπ) s₁ (hf k _ f₁) (hf k' _ f₂) (B.mem_Γ k) (B.mem_Γ k') u₁
    (permFam_fund π u₂)
  rw [integral_ballDens _ (hF k).1 (hF k).2.1, integral_ballDens _ (hF k').1 (hF k').2.1, ← m₁, ← m₂, key]
  exact congrArg (fun μ : Measure (Fin n → ℂ) => (μ FF₂).toReal) (ballMeas_permQ F₂.q π)

end SheetDecomposition
