import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableEmbeddingOfInjectiveProperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta

section Tuples

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem linearIndependent_mulVec {M n : ℕ} (A : GL (Fin M) E) {X : Fin n → Fin M → E}
    (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ z : Fin M → E,
        ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((A : Matrix (Fin M) (Fin M) E) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem linearIndependent_gact (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (gact σ g X) :=
  linearIndependent_mulVec (g : GL (Fin M) E) hX

theorem linearIndependent_consTup {M n : ℕ} (X : Fin n → Fin M → E) :
    LinearIndependent E (consTup X) ↔ LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h c hc a
    have h1 := h (Fin.cons 0 c) (by
      rw [Fin.sum_univ_succ]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consTup, Finset.sum_apply]
      · have := congrFun hc i
        simpa [consTup, Finset.sum_apply] using this) a.succ
    simpa using h1
  · intro h c hc
    have h0 : c 0 = 0 := by
      have := congrFun hc 0
      rw [Fin.sum_univ_succ] at this
      simpa [consTup, Finset.sum_apply] using this
    have h1 : ∀ a : Fin n, c a.succ = 0 := h (fun a => c a.succ) (by
      funext i
      have := congrFun hc i.succ
      rw [Fin.sum_univ_succ] at this
      simpa [consTup, Finset.sum_apply] using this)
    intro a
    exact Fin.cases h0 h1 a

theorem tsum_gact_frames (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) (T : Matrix (Fin n) (Fin n) E) (f : (Fin n → Fin M → E) → ℝ≥0∞) :
    ∑' X : framesE σ J T, f (gact σ g X.1) = ∑' X : framesE σ J T, f X.1 := by
  let e : framesE σ J T ≃ framesE σ J T :=
    { toFun := fun X => ⟨gact σ g X.1, linearIndependent_gact σ g X.2.1, by
        rw [gramE_gact]; exact X.2.2⟩
      invFun := fun X => ⟨gact σ g⁻¹ X.1, linearIndependent_gact σ g⁻¹ X.2.1, by
        rw [gramE_gact]; exact X.2.2⟩
      left_inv := fun X => Subtype.ext (gact_inv_gact σ g X.1)
      right_inv := fun X => Subtype.ext (gact_gact_inv σ g X.1) }
  exact e.tsum_eq (fun X => f X.1)

theorem tsum_block_frames (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) {t : E} (ht : t ≠ 0)
    (T : Matrix (Fin n) (Fin n) E)
    (rr : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} →
      UJ (σ : E →+* E) (blockOne t J))
    (hrr : ∀ q, gact σ (rr q) q.1 = fun _ => Fin.cons 1 (fun _ => 0))
    (f : (Fin (n + 1) → Fin (M + 1) → E) → ℝ≥0∞) :
    ∑' Y : framesE σ (blockOne t J) (blockOne t T), f Y.1 =
      ∑' q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t},
        ∑' X : framesE σ J T, f (gact σ (rr q)⁻¹ (consTup X.1)) := by
  have hrow : ∀ (q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t})
      (X : Fin n → Fin M → E), gact σ (rr q)⁻¹ (consTup X) 0 = q.1 0 := by
    intro q X
    have h := congrArg (gact σ (rr q)⁻¹) (hrr q)
    rw [gact_inv_gact] at h
    exact (congrFun h 0).symm
  let m : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} ×
      framesE σ J T → framesE σ (blockOne t J) (blockOne t T) :=
    fun p => ⟨gact σ (rr p.1)⁻¹ (consTup p.2.1),
      linearIndependent_gact σ _ ((linearIndependent_consTup _).2 p.2.2.1), by
      rw [gramE_gact, BlockAlg.gramE_consTup]
      exact congrArg (blockOne t) p.2.2.2⟩
  have hinj : Function.Injective m := by
    rintro ⟨q, X⟩ ⟨q', X'⟩ h
    have h1 : gact σ (rr q)⁻¹ (consTup X.1) = gact σ (rr q')⁻¹ (consTup X'.1) :=
      congrArg Subtype.val h
    have hq : q = q' := by
      apply Subtype.ext
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      rw [← hrow q X.1, ← hrow q' X'.1, h1]
    subst hq
    have h2 := congrArg (gact σ (rr q)) h1
    rw [gact_gact_inv, gact_gact_inv] at h2
    exact Prod.ext rfl (Subtype.ext (consTup_injective h2))
  have hsurj : Function.Surjective m := by
    rintro ⟨Y, hYl, hY'⟩
    have hy : gramE σ (blockOne t J) (fun _ : Fin 1 => Y 0) = fun _ _ => t := by
      funext a b
      exact congrFun (congrFun hY' 0) 0
    let q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} := ⟨_, hy⟩
    have h0 : gact σ (rr q) Y 0 = Fin.cons 1 (fun _ => 0) := congrFun (hrr q) 0
    have hG : gramE σ (blockOne t J) (gact σ (rr q) Y) = blockOne t T := by
      rw [gramE_gact]; exact hY'
    obtain ⟨X, hX, hYX⟩ := BlockAlg.exists_consTup_of_gramE σ J ht T _ h0 hG
    have hXl : LinearIndependent E X := by
      rw [← linearIndependent_consTup, ← hYX]
      exact linearIndependent_gact σ _ hYl
    refine ⟨(q, ⟨X, hXl, hX⟩), Subtype.ext ?_⟩
    change gact σ (rr q)⁻¹ (consTup X) = Y
    rw [← hYX, gact_inv_gact]
  let e := Equiv.ofBijective m ⟨hinj, hsurj⟩
  rw [← e.tsum_eq (fun Y => f Y.1), ENNReal.tsum_prod']
  rfl

end Tuples

set_option maxHeartbeats 1000000 in

theorem theta_stage_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J T))) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 (framesE σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T))) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
  intro F E _ _ _ _ _ σ hσ M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ Φ Ψ hΦ hΨ hyp
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  have ht' : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨b1, b2, -, -⟩ := BlockAlg.block_alg F E σ hσ M J t
  have hJb : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨b2 hJ.1, by rw [b1]; exact mul_ne_zero ht' hJ.2⟩
  obtain ⟨tg, lc, sc, t2, bs, act⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ (M + 1) _ hJb (AF F)
  obtain ⟨tg₁, lc₁, sc₁, t2₁, bs₁, act₁⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := tg
  haveI := lc
  haveI := sc
  haveI := t2
  haveI := bs
  haveI := tg₁
  haveI := lc₁
  haveI := sc₁
  haveI := t2₁
  haveI := bs₁
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hσ (AF F)
  haveI := hB (n + 1) (M + 1)
  haveI := hB 1 (M + 1)
  haveI := hB n M
  haveI := hB n (M + 1)
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ₁.IsHaarMeasure := hμ₁
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI hc : Countable (HFinIn (AF F) σ (blockOne (algebraMap F E t) J)) :=
    (rational_countable_discrete F E σ hσ (M + 1) _ hJb).1
  haveI hc₁ : Countable (HFinIn (AF F) σ J) := (rational_countable_discrete F E σ hσ M J hJ).1
  let Γ : Subgroup (HA (AF F) σ (blockOne (algebraMap F E t) J)) :=
    HFinIn (AF F) σ (blockOne (algebraMap F E t) J)
  let Γ₁ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI hc' : Countable Γ := hc
  haveI hc₁' : Countable Γ₁ := hc₁
  have hfin : μ₁ 𝓕₁ < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ₁ hμ₁).2 𝓕₁ h𝓕₁
  obtain ⟨ι, hιc, -, hιrange, hιF, hιcons⟩ :=
    StabFirst.stab_first F E σ hσ M J hJ t ht (AF F)
  have hmul : ∀ (g h : HA (AF F) σ (blockOne (algebraMap F E t) J)) {k : ℕ}
      (X : Fin k → Fin (M + 1) → AF F ⊗[F] E), actW (AF F) σ _ (g * h) X =
        actW (AF F) σ _ g (actW (AF F) σ _ h X) := fun g h {k} X => (act k).2.2.1 g h X
  have hW : ∀ q : {y : Fin 1 → Fin (M + 1) → E |
      gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t},
      ∃ g : UJ (σ : E →+* E) (blockOne (algebraMap F E t) J),
        gact σ g q.1 = fun _ => Fin.cons 1 (fun _ => 0) := by
    intro q
    have hq : gramE σ (blockOne (algebraMap F E t) J) q.1 = fun _ _ => algebraMap F E t := q.2
    obtain ⟨g, hg, hgy⟩ := GlobalTheory.T.witt_extension_global F E σ hσ (M + 1) _ hJb 1 q.1
      (fun _ => Fin.cons 1 (fun _ => 0)) (by rw [hq, gram_first])
      (by rw [hq]; intro h; exact ht' ((Matrix.det_fin_one (fun _ _ => algebraMap F E t : Matrix (Fin 1) (Fin 1) E)).symm.trans h))
    exact ⟨⟨g, hg⟩, funext hgy⟩
  choose rr hrr using hW
  let r := fun q => ratH (AF F) σ (blockOne (algebraMap F E t) J) (rr q)
  let φ : HA (AF F) σ (blockOne (algebraMap F E t) J) → ℝ≥0∞ := fun g =>
    ∑' X : framesE σ J T,
      Φ (actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) X.1)))
  have hφ : Measurable φ := by
    refine Measurable.ennreal_tsum fun X => hΦ.comp ?_
    have : Continuous fun g : HA (AF F) σ (blockOne (algebraMap F E t) J) =>
        actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) X.1)) :=
      (act (n + 1)).1.comp (continuous_inv.prodMk continuous_const)
    exact this.measurable
  have hinv : ∀ u ∈ HFinIn (AF F) σ J, ∀ g, φ (ι u * g) = φ g := by
    intro u hu g
    obtain ⟨w, rfl⟩ := exists_ratH (AF F) σ J u hu
    have e : ∀ X : Fin n → Fin M → E,
        actW (AF F) σ _ (ι (ratH (AF F) σ J w) * g)⁻¹ (consTup (ratTup (AF F) X)) =
          actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) (gact σ w⁻¹ X))) := by
      intro X
      rw [mul_inv_rev, hmul, ← map_inv ι, hιcons, ratH_inv, actW_ratH']
    change ∑' X : framesE σ J T,
        Φ (actW (AF F) σ _ (ι (ratH (AF F) σ J w) * g)⁻¹ (consTup (ratTup (AF F) X.1))) = φ g
    simp only [e]
    exact tsum_gact_frames σ w⁻¹ T (fun X => Φ (actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) X))))
  have hΓ : ∀ u ∈ HFinIn (AF F) σ J, ι u ∈ HFinIn (AF F) σ (blockOne (algebraMap F E t) J) :=
    fun u hu => (mem_HFinIn_iff _ σ _ _).2 ((hιF u).2 ((mem_HFinIn_iff _ σ _ _).1 hu))
  have hfix : ∀ (g : UJ (σ : E →+* E) (blockOne (algebraMap F E t) J)),
      actW (AF F) σ _ (ratH (AF F) σ _ g)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
      ratTup (AF F) (gact σ g (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E))) := by
    intro g
    rw [← ratTup_first, actW_ratH']
  have hrinv : ∀ q, gact σ (rr q)⁻¹ (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E)) = q.1 := by
    intro q
    rw [← hrr q, gact_inv_gact]
  have hstab : ∀ u, actW (AF F) σ _ (ι u)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
      fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E) :=
    fun u => (hιrange (ι u)).1 ⟨u, rfl⟩
  have huniq : ∀ γ ∈ HFinIn (AF F) σ (blockOne (algebraMap F E t) J), ∃! q, ∃ u ∈ HFinIn (AF F) σ J,
      γ = ι u * r q := by
    intro γ hγ
    obtain ⟨g, rfl⟩ := exists_ratH (AF F) σ _ γ hγ
    have hy : gramE σ (blockOne (algebraMap F E t) J)
        (gact σ g⁻¹ (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E))) =
        fun _ _ => algebraMap F E t := by
      rw [gramE_gact, gram_first]
    let q : {y : Fin 1 → Fin (M + 1) → E |
      gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t} := ⟨_, hy⟩
    have hrange : ratH (AF F) σ _ g * (r q)⁻¹ ∈ ι.range := by
      refine (hιrange _).2 ?_
      have e1 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      rw [hmul, e1, hfix, hrinv, actW_ratH']
      change ratTup (AF F) (gact σ g (gact σ g⁻¹ _)) = _
      rw [gact_gact_inv, ratTup_first]
    obtain ⟨u, hu⟩ := hrange
    have hmemu : u ∈ HFinIn (AF F) σ J := by
      refine (mem_HFinIn_iff _ σ _ _).2 ((hιF u).1 ((mem_HFinIn_iff _ σ _ _).1 ?_))
      rw [hu]
      exact Subgroup.mul_mem _ (ratH_mem _ σ _ g) (Subgroup.inv_mem _ (ratH_mem _ σ _ (rr q)))
    refine ⟨q, ⟨u, hmemu, by rw [hu, inv_mul_cancel_right]⟩, ?_⟩
    rintro q' ⟨u', -, he⟩
    apply Subtype.ext
    apply ratTup_adele_injective (F := F)
    have e1 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
        ratTup (AF F) q.1 := by
      rw [ratH_inv, hfix]
    have e2 : actW (AF F) σ _ (ratH (AF F) σ _ g)⁻¹
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → AF F ⊗[F] E)) =
        ratTup (AF F) q'.1 := by
      have e3 : (r q')⁻¹ = ratH (AF F) σ _ (rr q')⁻¹ := ratH_inv _ σ _ _
      have h6 : (ratH (AF F) σ _ g)⁻¹ = (r q')⁻¹ * ι u'⁻¹ := by
        rw [he, mul_inv_rev]
        exact congrArg _ (map_inv ι u').symm
      rw [h6, hmul, hstab, e3, hfix, hrinv]
    rw [← e1, ← e2]
  have key := GlobalTheory.T.quotient_measure_tower _ _ ι hιc μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hfin hΓ _ r (fun q => ratH_mem _ σ _ _) huniq φ hφ hinv
  have hA : ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J),
      ∑' Y : framesE σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T),
        Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y.1)) =
      ∑' q, φ (r q * h) := by
    intro h
    rw [tsum_block_frames σ J ht' T rr hrr (fun Y => Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y)))]
    refine tsum_congr fun q => tsum_congr fun X => ?_
    have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
    rw [mul_inv_rev, hmul, e3, ← ratTup_consTup, actW_ratH']
  have hC : ∀ g : HA (AF F) σ (blockOne (algebraMap F E t) J),
      (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁ =
        Ψ (actW (AF F) σ _ g⁻¹ (fun _ => Fin.cons 1 (fun _ => 0))) := by
    intro g
    have hm : Measurable fun X : Fin n → Fin M → AF F ⊗[F] E =>
        Φ (actW (AF F) σ _ g⁻¹ (consTup X)) := by
      refine hΦ.comp ?_
      have : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
          actW (AF F) σ _ g⁻¹ (consTup X) :=
        (act (n + 1)).1.comp (continuous_const.prodMk continuous_consTup)
      exact this.measurable
    rw [hyp g⁻¹, GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ₁ 𝓕₁ hμ₁ h𝓕₁ n _ _ hm]
    congr 1
    refine lintegral_congr fun u => tsum_congr fun X => ?_
    rw [mul_inv_rev, hmul, ← map_inv ι, hιcons]
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 1) _ hJb μ 𝓕 hμ h𝓕 (n + 1) _ Φ hΦ,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ (M + 1) _ hJb μ 𝓕 hμ h𝓕 1 _ Ψ hΨ]
  congr 1
  calc _ = ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ := lintegral_congr hA
    _ = _ := key
    _ = _ := by
      refine lintegral_congr fun h => tsum_congr fun q => ?_
      have e3 : (r q)⁻¹ = ratH (AF F) σ _ (rr q)⁻¹ := ratH_inv _ σ _ _
      rw [hC, mul_inv_rev, hmul, e3, hfix, hrinv]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta
