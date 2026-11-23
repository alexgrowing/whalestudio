import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SimTheta

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_UJ_smul_iff (s : A →+* A) (J : Matrix n n A) (c d : A) (hdc : d * c = 1) (u : GL n A) :
    u ∈ UJ s (c • J) ↔ u ∈ UJ s J := by
  have hscale : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) =
      c • (cT s (u : Matrix n n A) * J * (u : Matrix n n A)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro h
    have h' : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J := h
    rw [hscale] at h'
    change cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J
    have h2 := congrArg (fun B : Matrix n n A => d • B) h'
    simpa only [smul_smul, hdc, one_smul] using h2
  · intro h
    have h' : cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J := h
    change cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J
    rw [hscale, h']

theorem conj_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G * u * G⁻¹ ∈ UJ s J := by
  refine GlobalTheory.CompanionTheory.SW.HIsom.conj_mem_UJ s J G u ?_
  rw [hG]
  exact (mem_UJ_smul_iff s J c d hdc u).2 hu

theorem conj_inv_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s J := by
  have h := GlobalTheory.CompanionTheory.SW.HIsom.conj_inv_mem_UJ s J G u hu
  rw [hG] at h
  exact (mem_UJ_smul_iff s J c d hdc _).1 h

end Generic

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_smul (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (c : E)
    (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (c • J) = inclR (F := F) R c • JR (F := F) R J := by
  ext i j
  simp [JR, Matrix.map_apply]

theorem gramE_smul (σ : E →ₐ[F] E) {M n : ℕ} (c : E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramE σ (c • J) X = c • gramE σ J X := by
  ext a b
  simp only [gramE, hE, hform, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def gramEquiv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) (c : E)
    (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    (T : Matrix (Fin n) (Fin n) E) :
    {X : Fin n → Fin M → E | gramE σ J X = T} ≃ {X : Fin n → Fin M → E | gramE σ J X = c • T} where
  toFun X := ⟨SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E) X.1, by
    have := X.2
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [SWIsom.gramE_ratAct, hg, gramE_smul, this]⟩
  invFun Y := ⟨SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1, by
    have hY := Y.2
    simp only [Set.mem_setOf_eq] at hY ⊢
    have h1 : gramE σ J (SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E)
        (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1)) =
        c • gramE σ J (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1) := by
      rw [SWIsom.gramE_ratAct, hg, gramE_smul]
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one, hY] at h1
    exact (smul_right_injective _ hc h1).symm⟩
  left_inv X := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ X.1) = X.1
    rw [SWIsom.ratAct_mul, Units.inv_mul, SWIsom.ratAct_one]
  right_inv Y := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ Y.1) = Y.1
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one]

end Alg

theorem unitaryConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (l : F) (hl : l ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) =
      (algebraMap F E l) • J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    ∃ e : HA R σ J ≃ₜ* HA R σ J,
      (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J u * (bc (inclR R) g)⁻¹) ∧
      ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J u ∈ HFin R σ J := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hdcE : algebraMap F E l⁻¹ * algebraMap F E l = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hl, map_one]
  have hdcR : inclR (F := F) R (algebraMap F E l⁻¹) * inclR (F := F) R (algebraMap F E l) = 1 := by
    rw [← map_mul, hdcE, map_one]
  have hGR : cT (sigR R σ) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = inclR (F := F) R (algebraMap F E l) • JR R J := by
    rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g, hg, JR_smul]
  have h₁ : ∀ u ∈ HR R σ J, G * u * G⁻¹ ∈ HR R σ J := fun u hu =>
    conj_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  have h₂ : ∀ u ∈ HR R σ J, G⁻¹ * u * G ∈ HR R σ J := fun u hu =>
    conj_inv_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  refine ⟨GlobalTheory.CompanionTheory.SW.HIsom.conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ J u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ J u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ J u := hwu
    simp only [map_mul, map_inv, this, ← hG]

section Theta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem theta_map (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E) (c : E) (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    [LocallyCompactSpace (AF F)] [SecondCountableTopology (AF F)] [T2Space (AF F)]
    (He : HA (AF F) σ J ≃ᵐ HA (AF F) σ J)
    (hmat : ∀ u, HA.mat (AF F) σ J (He u) =
      bc (inclR (AF F)) g * HA.mat (AF F) σ J u * (bc (inclR (AF F)) g)⁻¹)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (T : Matrix (Fin n) (Fin n) E) :
    (thetaMeas σ J (μ.map He.symm) (He ⁻¹' 𝓕) {X | gramE σ J X = T}).map
        (actTup (AF F) (bc (inclR (AF F)) g)) =
      thetaMeas σ J μ 𝓕 {X | gramE σ J X = c • T} := by
  obtain ⟨tg, -, -, -, bs, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
  have hmG := SWIsom.measurable_actTup (n := n) σ hCM (AF F) G
  have hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y := fun Y =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕 := by
    rw [He.symm.map_apply]
    congr 1
    ext x
    simp
  have hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕 := by
    rw [← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]
    simp
  unfold thetaMeas
  rw [Measure.map_smul, hmass]
  congr 1
  rw [Measure.map_sum hmG.aemeasurable, ← SWIsom.sum_reindex (gramEquiv σ J g c hc hg T)]
  congr 1
  funext X
  rw [Measure.map_map hmG (hmf _)]
  have hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) =
      (fun h => actW (AF F) σ J h⁻¹
        (ratTup (AF F) ((gramEquiv σ J g c hc hg T X : _) : Fin n → Fin M → E))) ∘ He := by
    funext h
    have := SWIsom.act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))
    simp only [Function.comp]
    rw [this, ← SWIsom.ratTup_ratAct]
    rfl
  rw [hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]

end Theta

theorem theta_simil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ 𝓕 hμ h𝓕 γ l hl hγ
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := unitaryConj F E σ hCM M J γ l hl hγ (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M J (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M J (μ.map He.symm) (He ⁻¹' 𝓕) :=
    SWIsom.isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hc : algebraMap F E l ≠ 0 := by
    simpa using hl
  refine ⟨_, _, hμ', h𝓕', ?_⟩
  intro n T T' hT'
  subst hT'
  exact theta_map σ hCM J hJ γ _ hc hγ He hmat μ 𝓕 T

end GlobalTheory.CompanionTheory.SW.SimTheta
