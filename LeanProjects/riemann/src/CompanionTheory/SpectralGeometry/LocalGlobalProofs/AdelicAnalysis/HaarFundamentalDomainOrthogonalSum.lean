import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientMeasureTowerStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegativeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionGlobalStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThetaStage

section Alg

theorem hform_eq_dot {A : Type} [CommRing A] (s : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_act {A : Type} [CommRing A] (s : A →+* A) {M : ℕ} (J g : Matrix (Fin M) (Fin M) A)
    (hg : cT s g * J * g = J) (x y : Fin M → A) : hform s J (g *ᵥ x) (g *ᵥ y) = hform s J x y := by
  have h1 : (fun i => s ((g *ᵥ x) i)) = (fun i => s (x i)) ᵥ* cT s g := by
    funext i
    simp [Matrix.vecMul, dotProduct, Matrix.mulVec, cT, map_sum, mul_comm]
  rw [hform_eq_dot, hform_eq_dot, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hg]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gramE_act (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : UJ (σ : E →+* E) J) (X : Fin n → Fin M → E) :
    gramE σ J (fun a => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ X a) = gramE σ J X := by
  ext a b
  exact hform_act (σ : E →+* E) J _ g.2 (X a) (X b)

variable (R : Type) [CommRing R] [Algebra F R]

theorem bc_mem_HR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : UJ (σ : E →+* E) J) : bc (inclR R) (g : GL (Fin M) E) ∈ HR R σ J := by
  have hg : cT (σ : E →+* E) ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) * J *
      ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = J := g.2
  have h2 : cT (sigR R σ) (((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR R)) =
      (cT (σ : E →+* E) ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)).map (inclR R) := by
    ext i j
    simp [cT, sigR, inclR]
  change cT (sigR R σ) (((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR R)) * JR R J *
    (((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR R)) = JR R J
  rw [h2, JR, ← Matrix.map_mul, ← Matrix.map_mul, hg]

def ratH (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : UJ (σ : E →+* E) J) :
    HA R σ J :=
  (⟨bc (inclR R) (g : GL (Fin M) E), bc_mem_HR R σ J g⟩ : HR R σ J)

theorem mat_ratH (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : UJ (σ : E →+* E) J) :
    HA.mat R σ J (ratH R σ J g) = bc (inclR R) (g : GL (Fin M) E) := rfl

theorem ratH_inv (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : UJ (σ : E →+* E) J) :
    (ratH R σ J g)⁻¹ = ratH R σ J g⁻¹ := by
  apply Subtype.ext
  change (bc (inclR R) (g : GL (Fin M) E))⁻¹ = bc (inclR R) ((g : GL (Fin M) E)⁻¹)
  rw [map_inv]

theorem actW_ratH (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : UJ (σ : E →+* E) J)
    (X : Fin n → Fin M → E) :
    actW R σ J (ratH R σ J g) (ratTup R X) =
      ratTup R (fun a => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  funext a i
  change (∑ j, inclR R (((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j) * inclR R (X a j)) =
    inclR R (∑ j, ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j * X a j)
  rw [map_sum]
  simp only [map_mul]

theorem ratTup_consTup {M n : ℕ} (X : Fin n → Fin M → E) :
    ratTup (F := F) R (consTup X) = consTup (ratTup (F := F) R X) := by
  funext a i
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [ratTup, consTup]

theorem ratTup_first {M : ℕ} :
    ratTup (F := F) R (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E)) =
      fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) := by
  funext a i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [ratTup]

end Alg

section Tuples

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def gact (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J)
    (X : Fin n → Fin M → E) : Fin n → Fin M → E :=
  fun a => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ X a

theorem gact_inv_gact (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) (X : Fin n → Fin M → E) : gact σ g⁻¹ (gact σ g X) = X := by
  funext a
  change (((g⁻¹ : UJ (σ : E →+* E) J) : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
    (((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ X a) = X a
  rw [Matrix.mulVec_mulVec, ← Units.val_mul]
  simp

theorem gact_gact_inv (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) (X : Fin n → Fin M → E) : gact σ g (gact σ g⁻¹ X) = X := by
  have := gact_inv_gact σ g⁻¹ X
  rwa [inv_inv] at this

theorem gramE_gact (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) (X : Fin n → Fin M → E) : gramE σ J (gact σ g X) = gramE σ J X :=
  gramE_act σ J g X

theorem tsum_gact (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) (T : Matrix (Fin n) (Fin n) E) (f : (Fin n → Fin M → E) → ℝ≥0∞) :
    ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T}, f (gact σ g X.1) =
      ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T}, f X.1 := by
  let e : {X : Fin n → Fin M → E | gramE σ J X = T} ≃ {X : Fin n → Fin M → E | gramE σ J X = T} :=
    { toFun := fun X => ⟨gact σ g X.1, by
        change gramE σ J _ = T
        rw [gramE_gact]; exact X.2⟩
      invFun := fun X => ⟨gact σ g⁻¹ X.1, by
        change gramE σ J _ = T
        rw [gramE_gact]; exact X.2⟩
      left_inv := fun X => Subtype.ext (gact_inv_gact σ g X.1)
      right_inv := fun X => Subtype.ext (gact_gact_inv σ g X.1) }
  exact e.tsum_eq (fun X => f X.1)

theorem consTup_injective {K : Type} [Zero K] [One K] {M n : ℕ} :
    Function.Injective (consTup : (Fin n → Fin M → K) → Fin (n + 1) → Fin (M + 1) → K) := by
  intro X Y h
  funext a i
  exact congrFun (congrFun h a.succ) i.succ

theorem continuous_consTup {K : Type} [Zero K] [One K] [TopologicalSpace K] {M n : ℕ} :
    Continuous (consTup : (Fin n → Fin M → K) → Fin (n + 1) → Fin (M + 1) → K) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_apply i).comp (continuous_apply a)

theorem gram_first (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : E) :
    gramE σ (blockOne t J) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → E)) =
      fun _ _ => t := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  funext a b
  change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 1 (fun _ => 0)) = t
  rw [BlockAlg.hE_blockOne_cons, hz, BlockAlg.hE_zero_left]
  simp

theorem tsum_block (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) {t : E} (ht : t ≠ 0)
    (T : Matrix (Fin n) (Fin n) E)
    (rr : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} →
      UJ (σ : E →+* E) (blockOne t J))
    (hrr : ∀ q, gact σ (rr q) q.1 = fun _ => Fin.cons 1 (fun _ => 0))
    (f : (Fin (n + 1) → Fin (M + 1) → E) → ℝ≥0∞) :
    ∑' Y : {Y : Fin (n + 1) → Fin (M + 1) → E | gramE σ (blockOne t J) Y = blockOne t T}, f Y.1 =
      ∑' q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t},
        ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T}, f (gact σ (rr q)⁻¹ (consTup X.1)) := by
  have hrow : ∀ (q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t})
      (X : Fin n → Fin M → E), gact σ (rr q)⁻¹ (consTup X) 0 = q.1 0 := by
    intro q X
    have h := congrArg (gact σ (rr q)⁻¹) (hrr q)
    rw [gact_inv_gact] at h
    exact (congrFun h 0).symm
  let m : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} ×
      {X : Fin n → Fin M → E | gramE σ J X = T} →
      {Y : Fin (n + 1) → Fin (M + 1) → E | gramE σ (blockOne t J) Y = blockOne t T} :=
    fun p => ⟨gact σ (rr p.1)⁻¹ (consTup p.2.1), by
      change gramE σ (blockOne t J) _ = _
      rw [gramE_gact, BlockAlg.gramE_consTup]
      exact congrArg (blockOne t) p.2.2⟩
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
    rintro ⟨Y, hY⟩
    have hY' : gramE σ (blockOne t J) Y = blockOne t T := hY
    have hy : gramE σ (blockOne t J) (fun _ : Fin 1 => Y 0) = fun _ _ => t := by
      funext a b
      exact congrFun (congrFun hY' 0) 0
    let q : {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne t J) y = fun _ _ => t} := ⟨_, hy⟩
    have h0 : gact σ (rr q) Y 0 = Fin.cons 1 (fun _ => 0) := congrFun (hrr q) 0
    have hG : gramE σ (blockOne t J) (gact σ (rr q) Y) = blockOne t T := by
      rw [gramE_gact]; exact hY'
    obtain ⟨X, hX, hYX⟩ := BlockAlg.exists_consTup_of_gramE σ J ht T _ h0 hG
    refine ⟨(q, ⟨X, hX⟩), Subtype.ext ?_⟩
    change gact σ (rr q)⁻¹ (consTup X) = Y
    rw [← hYX, gact_inv_gact]
  let e := Equiv.ofBijective m ⟨hinj, hsurj⟩
  rw [← e.tsum_eq (fun Y => f Y.1), ENNReal.tsum_prod']
  rfl

end Tuples

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem mem_HFinIn_iff (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) :
    h ∈ HFinIn R σ J ↔ HA.mat R σ J h ∈ HFin R σ J :=
  Subgroup.mem_subgroupOf

theorem ratH_mem (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : UJ (σ : E →+* E) J) :
    ratH R σ J g ∈ HFinIn R σ J :=
  (mem_HFinIn_iff R σ J _).2 ⟨g.1, g.2, rfl⟩

theorem exists_ratH (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (hh : h ∈ HFinIn R σ J) : ∃ g, h = ratH R σ J g := by
  obtain ⟨g, hg, e⟩ := (mem_HFinIn_iff R σ J h).1 hh
  exact ⟨⟨g, hg⟩, Subtype.ext e.symm⟩

theorem actW_ratH' (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : UJ (σ : E →+* E) J) (X : Fin n → Fin M → E) :
    actW R σ J (ratH R σ J g) (ratTup R X) = ratTup R (gact σ g X) :=
  actW_ratH R σ J g X

end Rat

theorem ratTup_adele_injective {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M n : ℕ} : Function.Injective (ratTup (F := F) (E := E) (M := M) (n := n) (AF F)) := by
  intro X Y h
  have hi : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  funext a i
  exact hi (congrFun (congrFun h a) i)

set_option maxHeartbeats 1000000 in

theorem theta_stage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ {X | gramE σ J X = T})) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 {X | gramE σ (blockOne (algebraMap F E t) J) X = blockOne (algebraMap F E t) T}) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
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
    ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T},
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
    change ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T},
        Φ (actW (AF F) σ _ (ι (ratH (AF F) σ J w) * g)⁻¹ (consTup (ratTup (AF F) X.1))) = φ g
    simp only [e]
    exact tsum_gact σ w⁻¹ T (fun X => Φ (actW (AF F) σ _ g⁻¹ (consTup (ratTup (AF F) X))))
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
      ∑' Y : {Y : Fin (n + 1) → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) Y =
          blockOne (algebraMap F E t) T},
        Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y.1)) =
      ∑' q, φ (r q * h) := by
    intro h
    rw [tsum_block σ J ht' T rr hrr (fun Y => Φ (actW (AF F) σ _ h⁻¹ (ratTup (AF F) Y)))]
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

end GlobalTheory.CompanionTheory.SW.ThetaStage
