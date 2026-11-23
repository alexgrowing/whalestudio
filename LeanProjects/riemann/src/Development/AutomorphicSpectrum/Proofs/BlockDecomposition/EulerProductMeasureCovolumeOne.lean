import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjections
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure

theorem map_consA {K L : Type} [Zero K] [One K] [Zero L] [One L] (f : K → L) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {M n : ℕ} (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    (fun p i => f (consA a Y p i)) = consA (fun x j => f (a x j)) (fun j i => f (Y j i)) := by
  funext p i
  induction p using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simp [consA, h1]
    | succ i => simp [consA, h0]
  | succ p =>
    induction i using Fin.cases with
    | zero => simp [consA]
    | succ i =>
      induction i using Fin.cases with
      | zero => simp [consA, h0]
      | succ i => simp [consA]

theorem map_e0 {K L : Type} [Zero K] [One K] [Zero L] [One L] (f : K → L) (h0 : f 0 = 0)
    (h1 : f 1 = 1) (M : ℕ) : (fun p i => f (e0 K M p i)) = e0 L M := by
  funext p i
  induction i using Fin.cases with
  | zero => simp [e0, h1]
  | succ i => simp [e0, h0]

theorem measurable_consA {K : Type} [Zero K] [One K] [MeasurableSpace K] (M n : ℕ) :
    Measurable (fun q : (Fin n → Fin M → K) × (Fin 1 → Fin n → K) => consA q.2 q.1) := by
  refine measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i => ?_
  induction p using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simpa [consA] using measurable_const
    | succ i => simpa [consA] using measurable_const
  | succ p =>
    induction i using Fin.cases with
    | zero =>
      simpa [consA, Function.comp_def] using
        (measurable_pi_apply p).comp ((measurable_pi_apply 0).comp measurable_snd)
    | succ i =>
      induction i using Fin.cases with
      | zero => simpa [consA] using measurable_const
      | succ i =>
        simpa [consA, Function.comp_def] using
          (measurable_pi_apply i).comp ((measurable_pi_apply p).comp measurable_fst)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurable_actW (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hR : IsLocR R) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    Measurable (actW R σ J g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  have hk := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI : IsTopologicalRing (R ⊗[F] E) := hk.1
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hk.2.2.2.2.2.2.2.1 n M
  have hc : Continuous (actW R σ J g : (Fin n → Fin M → R ⊗[F] E) → _) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [actW, actTup, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul
      ((continuous_apply j).comp (continuous_apply a))
  exact hc.measurable

theorem measurable_stage (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (M n : ℕ)
    (f : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun Y : Fin n → Fin M → R ⊗[F] E => ∫⁻ a, f (consA a Y) ∂(coordW R b lam 1 n) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  have hk := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  have hKf : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) R b) := hk.2.2.2.2.2.2.1 d b
  haveI : SigmaFinite lam := inferInstance
  haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK R hKf lam
  haveI : SFinite (coordW R b lam 1 n) := by unfold coordW; infer_instance
  exact Measurable.lintegral_prod_right (f := fun Y a => f (consA a Y))
    (hf.comp (measurable_consA M n))

end Loc

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_consA {M n : ℕ} (a : Fin 1 → Fin n → AF F ⊗[F] E) (Y : Fin n → Fin M → AF F ⊗[F] E) :
    projInf (consA a Y) = consA (projInf a) (projInf Y) :=
  map_consA (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (map_zero _) (map_one _) a Y

theorem projFin_consA {M n : ℕ} (a : Fin 1 → Fin n → AF F ⊗[F] E) (Y : Fin n → Fin M → AF F ⊗[F] E) :
    projFin (consA a Y) = consA (projFin a) (projFin Y) :=
  map_consA (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (map_zero _) (map_one _) a Y

theorem projV_consA (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (a : Fin 1 → Fin n → Af F ⊗[F] E)
    (Y : Fin n → Fin M → Af F ⊗[F] E) : projV v (consA a Y) = consA (projV v a) (projV v Y) :=
  map_consA (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) (map_zero _) (map_one _) a Y

theorem projInf_e0 (M : ℕ) : projInf (e0 (AF F ⊗[F] E) M) = e0 _ M :=
  map_e0 (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (map_zero _) (map_one _) M

theorem projV_projFin_e0 (v : HeightOneSpectrum (𝓞 F)) (M : ℕ) :
    projV v (projFin (e0 (AF F ⊗[F] E) M)) = e0 _ M := by
  have h1 : projFin (e0 (AF F ⊗[F] E) M) = e0 _ M :=
    map_e0 (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (map_zero _) (map_one _) M
  rw [h1]
  exact map_e0 (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) (map_zero _) (map_one _) M

theorem consA_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ}
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F)
    (a : Fin 1 → Fin n → Fv F v ⊗[F] E) (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    (consA a Y : Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) ∈ latV b v ↔
      a ∈ latV b v ∧ Y ∈ latV b v := by
  constructor
  · intro h
    refine ⟨fun x j k => ?_, fun j i k => ?_⟩
    · obtain rfl : x = 0 := Subsingleton.elim _ _
      simpa [consA] using h j.succ 0 k
    · simpa [consA] using h j.succ i.succ.succ k
  · rintro ⟨ha, hY⟩ p i k
    induction p using Fin.cases with
    | zero =>
      induction i using Fin.cases with
      | zero => simpa [consA] using h1 k
      | succ i => simp [consA, zero_mem]
    | succ p =>
      induction i using Fin.cases with
      | zero => simpa [consA] using ha 0 p k
      | succ i =>
        induction i using Fin.cases with
        | zero => simp [consA, zero_mem]
        | succ i => simpa [consA] using hY p i k

theorem pureL_consA {d M n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v, v ∉ S → ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F)
    (f : (Fin (n + 1) → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (a : Fin 1 → Fin n → AF F ⊗[F] E) (Y : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S f fv (consA a Y) = (intOff b S).indicator 1 Y *
      pureL b S (fun a' => f (consA a' (projInf Y)))
        (fun v a' => fv v (consA a' (projV v (projFin Y)))) a := by
  have hV : ∀ v, projV v (projFin (consA a Y)) = consA (projV v (projFin a)) (projV v (projFin Y)) :=
    fun v => by rw [projFin_consA, projV_consA]
  have hmem : consA a Y ∈ intOff b S ↔ a ∈ intOff b S ∧ Y ∈ intOff b S := by
    constructor
    · intro h
      exact ⟨fun v hv => by
        have := h v hv
        rw [hV] at this
        exact ((consA_mem_latV b v (hS v hv) _ _).1 this).1, fun v hv => by
        have := h v hv
        rw [hV] at this
        exact ((consA_mem_latV b v (hS v hv) _ _).1 this).2⟩
    · rintro ⟨h1, h2⟩ v hv
      rw [hV]
      exact (consA_mem_latV b v (hS v hv) _ _).2 ⟨h1 v hv, h2 v hv⟩
  unfold pureL
  by_cases hY : Y ∈ intOff b S
  · by_cases ha : a ∈ intOff b S
    · rw [Set.indicator_of_mem (hmem.2 ⟨ha, hY⟩), Set.indicator_of_mem hY, Set.indicator_of_mem ha,
        projInf_consA]
      simp only [hV, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem (fun h => ha (hmem.1 h).1), Set.indicator_of_notMem ha, mul_zero]
  · rw [Set.indicator_of_notMem (fun h => hY (hmem.1 h).2), Set.indicator_of_notMem hY, zero_mul]

variable [DecidableEq (HeightOneSpectrum (𝓞 F))]

theorem pureL_act {d M n : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
    (Jp : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S S' : Finset (HeightOneSpectrum (𝓞 F)))
    (hSS : S ⊆ S')
    (hinf : ∀ X : Fin n → Fin M → AF F ⊗[F] E,
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (X : Fin n → Fin M → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ S' → ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf φ (actW (AF F) σ Jp h X) =
      pureL b S' (fun Y => φinf (actW (Ainf F) σ Jp ginf Y))
        (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ Jp (g v) Y)
          else (latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) Y)) X := by
  unfold pureL
  by_cases hX : X ∈ intOff b S'
  · rw [Set.indicator_of_mem hX]
    by_cases hA : ∀ v ∈ S' \ S, actW (Fv F v) σ Jp (g v) (projV v (projFin X)) ∈ latV b v
    · have hY : actW (AF F) σ Jp h X ∈ intOff b S := by
        intro v hv
        rw [hfin]
        by_cases hvh : v ∈ S'
        · exact hA v (Finset.mem_sdiff.2 ⟨hvh, hv⟩)
        · exact (hSh v hvh _).2 (hX v hvh)
      rw [Set.indicator_of_mem hY, hinf]
      congr 1
      rw [← Finset.prod_subset hSS fun v hv hvS => ?_]
      · refine Finset.prod_congr rfl fun v hv => ?_
        rw [hfin]
        simp only [if_pos hv]
      · simp only [if_neg hvS]
        rw [Set.indicator_of_mem (hA v (Finset.mem_sdiff.2 ⟨hv, hvS⟩))]
        rfl
    · push Not at hA
      obtain ⟨v, hv, hvl⟩ := hA
      have hY : actW (AF F) σ Jp h X ∉ intOff b S := by
        intro hm
        have := hm v (Finset.mem_sdiff.1 hv).2
        rw [hfin] at this
        exact hvl this
      rw [Set.indicator_of_notMem hY, Finset.prod_eq_zero (Finset.mem_sdiff.1 hv).1
        (by simp only [if_neg (Finset.mem_sdiff.1 hv).2]; rw [Set.indicator_of_notMem hvl])]
      simp
  · have hY : actW (AF F) σ Jp h X ∉ intOff b S := by
      intro hm
      apply hX
      intro v hv
      have := hm v (fun hs => hv (hSS hs))
      rw [hfin] at this
      exact (hSh v hv _).1 this
    rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hY]

end Glob

section Main

theorem inner_int {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hE : ∀ (φinf : (Fin 1 → Fin n → Ainf F ⊗[F] E) → ℝ≥0∞)
      (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℝ≥0∞),
      Measurable φinf → (∀ v, Measurable (φ v)) →
      ∫⁻ X, pureL b S φinf φ X ∂dA =
        ((1 : ℝ≥0) : ℝ≥0∞) * ((∫⁻ X, φinf X ∂(coordW (Ainf F) b laminf 1 n)) *
          ∏ v ∈ S, ∫⁻ X, φ v X ∂(coordW (Fv F v) b (lam v) 1 n)) *
          ENNReal.ofReal (∏' v : {v // v ∉ S}, (coordW (Fv F v.1) b (lam v.1) 1 n (latV b v.1)).toReal))
    (hmass : ∀ v, coordW (Fv F v) b (lam v) 1 n (latV b v) = 1)
    (hS : ∀ v, v ∉ S → ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F)
    (f : (Fin (n + 1) → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (hf : Measurable f) (hfv : ∀ v, Measurable (fv v)) (Y : Fin n → Fin M → AF F ⊗[F] E) :
    ∫⁻ a, pureL b S f fv (consA a Y) ∂dA =
      pureL b S (fun Y' => ∫⁻ a, f (consA a Y') ∂(coordW (Ainf F) b laminf 1 n))
        (fun v Y' => ∫⁻ a, fv v (consA a Y') ∂(coordW (Fv F v) b (lam v) 1 n)) Y := by
  by_cases hY : Y ∈ intOff b S
  · have h1 : ∀ a, pureL b S f fv (consA a Y) = pureL b S (fun a' => f (consA a' (projInf Y)))
        (fun v a' => fv v (consA a' (projV v (projFin Y)))) a := fun a => by
      rw [pureL_consA b S hS f fv a Y, Set.indicator_of_mem hY]
      simp
    simp_rw [h1]
    have m1 : Measurable fun a' : Fin 1 → Fin n → Ainf F ⊗[F] E => f (consA a' (projInf Y)) :=
      hf.comp ((measurable_consA M n).comp measurable_prodMk_left)
    have m2 : ∀ v, Measurable fun a' : Fin 1 → Fin n → Fv F v ⊗[F] E =>
        fv v (consA a' (projV v (projFin Y))) := fun v =>
      (hfv v).comp ((measurable_consA M n).comp measurable_prodMk_left)
    rw [hE _ _ m1 m2]
    unfold pureL
    rw [Set.indicator_of_mem hY]
    simp [hmass]
  · have h1 : ∀ a, pureL b S f fv (consA a Y) = 0 := fun a => by
      rw [pureL_consA b S hS f fv a Y, Set.indicator_of_notMem hY, zero_mul]
    simp_rw [h1]
    unfold pureL
    rw [Set.indicator_of_notMem hY]
    simp

theorem inner_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsEulerProd b dA 1 (coordW (Ainf F) b laminf 1 n) (fun v => coordW (Fv F v) b (lam v) 1 n) → ∀ (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₂ ⊆ S → ∀ (φinf : (Fin (n + 1) → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ G : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → (∀ g : HA (Ainf F) σ (hypOne J), Ψinf (actW (Ainf F) σ (hypOne J) g (e0 _ M)) = stageInt (Ainf F) σ J b laminf minf φinf g) → (∀ v, ∀ g : HA (Fv F v) σ (hypOne J), Ψ v (actW (Fv F v) σ (hypOne J) g (e0 _ M)) = stageInt (Fv F v) σ J b (lam v) (m v) (φ v) g) → (∀ v, ∀ g : HA (Fv F v) σ (hypOne J), G v (actW (Fv F v) σ (hypOne J) g (e0 _ M)) = stageInt (Fv F v) σ J b (lam v) (m v) ((latV b v).indicator 1) g) → ∀ h : HA (AF F) σ (hypOne J), ∃ Sh : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ Sh ∧ ∀ S', Sh ⊆ S' → ∫⁻ Y, ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂I = ENNReal.ofReal (∏' v : {v // v ∉ S'}, (m v.1 (latV b v.1)).toReal) * purePr σ J b S' Ψinf (fun v => if v ∈ S then Ψ v else G v) (actW (AF F) σ (hypOne J) h (e0 _ M)) := by
  intro F E _ _ _ _ _ _ σ hCM M J hJ n d b laminf lam hinf hlam dA hdA I minf m hI
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hJ' := (hypOne_isHermND_and_e0_mem F E σ hCM M J hJ).1
  obtain ⟨pinf, p, hcomp, hlat, -⟩ := GlobalTheory.CompanionTheory.SW.HProj.components F E σ hCM (M + 2) _ hJ'
  have hcons := (GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b 0 0).2.2
  obtain ⟨-, -, S₀, hS₀⟩ := hdA
  obtain ⟨-, -, S₁, hS₁⟩ := hI
  refine ⟨S₀ ∪ S₁ ∪ (Filter.eventually_cofinite.1 hcons).toFinset,
    fun S hS φinf φ Ψinf Ψ G hφinf hφ hΨinf hΨ hG h => ?_⟩
  refine ⟨S ∪ (Filter.eventually_cofinite.1 (hlat d b h)).toFinset, Finset.subset_union_left,
    fun S' hS' => ?_⟩
  have hSS : S ⊆ S' := Finset.subset_union_left.trans hS'
  have hsub0 : S₀ ⊆ S' := fun x hx => hSS (hS (by simp [hx]))
  have hsub1 : S₁ ⊆ S' := fun x hx => hSS (hS (by simp [hx]))
  have hSl : ∀ v, v ∉ S' → ∀ (k : ℕ) (X : Fin k → Fin (M + 2) → Fv F v ⊗[F] E),
      actW (Fv F v) σ (hypOne J) (p v h) X ∈ latV b v ↔ X ∈ latV b v := fun v hv => by
    have hv' : v ∉ (Filter.eventually_cofinite.1 (hlat d b h)).toFinset :=
      fun hm => hv (hS' (Finset.mem_union_right _ hm))
    simpa using hv'
  have hone : ∀ v, v ∉ S' → ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F := fun v hv k => by
    have hv' : v ∉ (Filter.eventually_cofinite.1 hcons).toFinset :=
      fun hm => hv (hSS (hS (Finset.mem_union_right _ hm)))
    have hv2 : ∀ X : Fin 0 → Fin 0 → Fv F v ⊗[F] E, consTup X ∈ latV b v ↔ X ∈ latV b v := by
      simpa using hv'
    have := (hv2 (fun a => a.elim0)).2 (fun a => a.elim0) 0 0 k
    simpa [consTup] using this
  obtain ⟨fI, hfI⟩ : ∃ f : (Fin (n + 1) → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞,
      f = fun X => φinf (actW (Ainf F) σ (hypOne J) (pinf h) X) := ⟨_, rfl⟩
  obtain ⟨fv, hfv⟩ : ∃ f : ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞,
      f = fun v X => if v ∈ S then φ v (actW (Fv F v) σ (hypOne J) (p v h) X)
        else (latV b v).indicator 1 (actW (Fv F v) σ (hypOne J) (p v h) X) := ⟨_, rfl⟩
  have hact : ∀ (a : Fin 1 → Fin n → AF F ⊗[F] E) (Y : Fin n → Fin M → AF F ⊗[F] E),
      pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) = pureL b S' fI fv (consA a Y) := by
    intro a Y
    rw [hfI, hfv]
    exact pureL_act b σ _ h (pinf h) (fun v => p v h) S S' hSS (fun X => (hcomp _ h X).1)
      (fun X v => (hcomp _ h X).2 v) (fun v hv => hSl v hv _) φinf φ _
  have mI : Measurable fI := by
    rw [hfI]
    exact hφinf.comp (measurable_actW σ hCM _ hLi _ _)
  have mv : ∀ v, Measurable (fv v) := fun v => by
    rw [hfv]
    by_cases hv : v ∈ S
    · simp only [hv, if_true]
      exact (hφ v).comp (measurable_actW σ hCM _ (hLv v) _ _)
    · simp only [hv, if_false]
      exact (measurable_one.indicator
        (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM b _ _ v)).comp
        (measurable_actW σ hCM _ (hLv v) _ _)
  have e1 : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      ∫⁻ a, pureL b S φinf φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA =
      pureL b S' (fun Y' => ∫⁻ a, fI (consA a Y') ∂(coordW (Ainf F) b laminf 1 n))
        (fun v Y' => ∫⁻ a, fv v (consA a Y') ∂(coordW (Fv F v) b (lam v) 1 n)) Y := fun Y => by
    simp_rw [hact]
    exact inner_int b laminf lam dA S' (hS₀ S' hsub0)
      (fun v => GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.coordW_latV σ hCM b lam hlam 1 n v) hone fI fv mI mv Y
  have mFinf := measurable_stage σ hCM (Ainf F) hLi b laminf hinf.1 M n fI mI
  have mFv := fun v => measurable_stage σ hCM (Fv F v) (hLv v) b (lam v) (hlam v).1 M n (fv v) (mv v)
  simp_rw [e1]
  rw [hS₁ S' hsub1 _ _ mFinf mFv]
  have i1 : ∫⁻ Y, ∫⁻ a, fI (consA a Y) ∂(coordW (Ainf F) b laminf 1 n) ∂minf =
      Ψinf (actW (Ainf F) σ (hypOne J) (pinf h) (e0 _ M)) := by
    rw [hΨinf (pinf h), hfI]
    rfl
  have i2 : ∀ v, ∫⁻ Y, ∫⁻ a, fv v (consA a Y) ∂(coordW (Fv F v) b (lam v) 1 n) ∂(m v) =
      (if v ∈ S then Ψ v else G v) (actW (Fv F v) σ (hypOne J) (p v h) (e0 _ M)) := fun v => by
    by_cases hv : v ∈ S
    · rw [if_pos hv, hΨ v (p v h), hfv]
      simp only [hv, if_true]
      rfl
    · rw [if_neg hv, hG v (p v h), hfv]
      simp only [hv, if_false]
      rfl
  rw [i1, Finset.prod_congr rfl (fun v _ => i2 v)]
  have hmemP : actW (AF F) σ (hypOne J) h (e0 _ M) ∈
      {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S' → projV v (projFin y) ∈ primV σ J b v} := by
    intro v hv
    rw [(hcomp 1 h _).2 v, projV_projFin_e0]
    exact ⟨p v h, fun x => hSl v hv 1 x, rfl⟩
  unfold purePr
  rw [Set.indicator_of_mem hmemP, (hcomp 1 h _).1, projInf_e0]
  simp only [fun v => (hcomp 1 h (e0 _ M)).2 v, projV_projFin_e0, ENNReal.coe_one, one_mul]
  rw [mul_comm]

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Pure
