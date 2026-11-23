import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarEqProductLocalMeasures
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x)
    (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r e => simp [sigR, hinv]

def tVec {K : Type} [One K] {M : ℕ} (c d : K) : Fin (M + 2) → K :=
  Fin.cons c (Fin.cons d fun _ => 1)

variable (R : Type) [CommRing R] [Algebra F R]

def tGL (σ : E →ₐ[F] E) (M : ℕ) (u : (R ⊗[F] E)ˣ) : GL (Fin (M + 2)) (R ⊗[F] E) where
  val := Matrix.diagonal (tVec (u : R ⊗[F] E) (sigR R σ ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)))
  inv := Matrix.diagonal (tVec ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) (sigR R σ (u : R ⊗[F] E)))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · simp [tVec]
    · simp only [tVec, Fin.cons_zero, Fin.cons_succ]
      rw [← map_mul, Units.inv_mul, map_one]
    · simp [tVec]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · simp [tVec]
    · simp only [tVec, Fin.cons_zero, Fin.cons_succ]
      rw [← map_mul, Units.mul_inv, map_one]
    · simp [tVec]

theorem tGL_mem (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (u : (R ⊗[F] E)ˣ) : tGL R σ M u ∈ HR R σ (hypOne J) := by
  show cT (sigR R σ) (tGL R σ M u).1 * JR R (hypOne J) * (tGL R σ M u).1 = JR R (hypOne J)
  set t := tVec (M := M) (u : R ⊗[F] E) (sigR R σ ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) with ht
  have hv : (tGL R σ M u).1 = Matrix.diagonal t := rfl
  have hd : cT (sigR R σ) (Matrix.diagonal t) = Matrix.diagonal fun i => sigR R σ (t i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT]
    · have h' : j ≠ i := fun e => h e.symm
      simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']
  rw [hv, hd]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : sigR R σ (u : R ⊗[F] E) * sigR R σ ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : sigR R σ (sigR R σ ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) * (u : R ⊗[F] E) = 1 := by
    rw [sigR_sigR R σ hinv, Units.inv_mul]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals simp [ht, tVec, JR, hypOne, h1, h2, inclR, Matrix.of_apply, ← Algebra.TensorProduct.one_def]

theorem actW_mul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (k t : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) : actW R σ J (k * t) X = actW R σ J k (actW R σ J t X) := by
  funext a
  show ((HA.mat R σ J k).1 * (HA.mat R σ J t).1).mulVec (X a) = (HA.mat R σ J k).1.mulVec ((HA.mat R σ J t).1.mulVec (X a))
  rw [Matrix.mulVec_mulVec]

theorem actW_scalT (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (k : HA R σ J) (c : R ⊗[F] E)
    (X : Fin n → Fin M → R ⊗[F] E) : actW R σ J k (scalT c X) = scalT c (actW R σ J k X) := by
  funext a
  show (HA.mat R σ J k).1.mulVec (c • X a) = c • (HA.mat R σ J k).1.mulVec (X a)
  rw [Matrix.mulVec_smul]

def tHA (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (u : (R ⊗[F] E)ˣ) : HA R σ (hypOne J) := ⟨tGL R σ M u, tGL_mem R σ hinv J u⟩

theorem actW_tHA (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (u : (R ⊗[F] E)ˣ) (X : Fin n → Fin (M + 2) → R ⊗[F] E) (p : Fin n) (i : Fin (M + 2)) :
    actW R σ (hypOne J) (tHA R σ hinv J u) X p i =
      tVec (u : R ⊗[F] E) (sigR R σ ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) i * X p i := by
  show (Matrix.diagonal _).mulVec (X p) i = _
  rw [Matrix.mulVec_diagonal]

theorem actW_tHA_e0 (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (u : (R ⊗[F] E)ˣ) :
    actW R σ (hypOne J) (tHA R σ hinv J u) (e0 _ M) = scalT (u : R ⊗[F] E) (e0 _ M) := by
  funext p i
  rw [actW_tHA]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;> simp [tVec, e0, scalT]

end Alg

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_latV_iff_col {d M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    X ∈ latV b v ↔ ∀ p, (fun _ : Fin 1 => X p) ∈ latV b v :=
  ⟨fun h p _ i k => h p i k, fun h p i k => h p 0 i k⟩

theorem latStab_tuple (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {k : HA (Fv F v) σ J}
    (hk : latStab σ J b v k) (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    actW (Fv F v) σ J k X ∈ latV b v ↔ X ∈ latV b v := by
  rw [mem_latV_iff_col, mem_latV_iff_col (X := X)]
  exact forall_congr' fun p => hk fun _ => X p

theorem repr_zero_mem {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    (0 : Fv F v ⊗[F] E) ∈ intK b v := fun k => by
  simpa using (v.adicCompletionIntegers F).zero_mem

theorem tHA_consA_mem (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ)
    (hc : (u : Fv F v ⊗[F] E) ∈ intK b v) (a : Fin 1 → Fin n → Fv F v ⊗[F] E)
    (Y : Fin n → Fin M → Fv F v ⊗[F] E) :
    actW (Fv F v) σ (hypOne J) (tHA (Fv F v) σ hinv J u) (consA a Y) ∈ latV b v ↔
      (∀ j, (u : Fv F v ⊗[F] E) * a 0 j ∈ intK b v) ∧ Y ∈ latV b v := by
  have h0 := repr_zero_mem b v
  constructor
  · intro h
    refine ⟨fun j k => ?_, fun j i k => ?_⟩
    · have := h j.succ 0 k
      rw [actW_tHA] at this
      simpa [tVec, consA] using this
    · have := h j.succ i.succ.succ k
      rw [actW_tHA] at this
      simpa [tVec, consA] using this
  · rintro ⟨h1, h2⟩ p i k
    rw [actW_tHA]
    refine Fin.cases ?_ (fun j => ?_) p
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simpa [tVec, consA] using hc k
      · simpa [tVec, consA] using h0 k
      · simpa [tVec, consA] using h0 k
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simpa [tVec, consA] using h1 j k
      · simpa [tVec, consA] using h0 k
      · simpa [tVec, consA] using h2 j i k

end Lat

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intK_facts (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (hlam : IsStdV v lam) :
    MeasurableSet (intK b v) ∧ SigmaFinite (coordK (Fv F v) b lam) ∧ coordK (Fv F v) b lam (intK b v) = 1 := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -, -, hK, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI := hlam.1
  haveI hS : SigmaFinite (coordK (Fv F v) b lam) := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Fv F v) (hK d b) lam
  obtain ⟨-, hO, -, hm⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 1 v
  have hpre : intK b v = (fun (x : Fv F v ⊗[F] E) (_ : Fin 1) (_ : Fin 1) => x) ⁻¹' latV b v := by
    ext x
    exact ⟨fun h _ _ k => h k, fun h k => h 0 0 k⟩
  have hcont : Continuous (fun (x : Fv F v ⊗[F] E) (_ : Fin 1) (_ : Fin 1) => x) :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_id
  refine ⟨?_, hS, ?_⟩
  · rw [hpre]
    exact (hO.preimage hcont).measurableSet
  · have hbox : (latV b v : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intK b v := by
      ext X
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
      exact ⟨fun h p i k => h p i k, fun h p i k => h p i k⟩
    have := hm lam hlam
    rw [hbox, coordW, Measure.pi_pi] at this
    simpa [Measure.pi_pi] using this

theorem box_mass (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (n : ℕ) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (c : Fv F v ⊗[F] E) (a : ℝ≥0)
    (hmap : (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam) :
    MeasurableSet {x : Fin 1 → Fin n → Fv F v ⊗[F] E | ∀ j, c * x 0 j ∈ intK b v} ∧
      coordW (Fv F v) b lam 1 n {x | ∀ j, c * x 0 j ∈ intK b v} = (a : ℝ≥0∞) ^ n := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hI, hS, h1⟩ := intK_facts σ hσ b v lam hlam
  have hf : Measurable fun x : Fv F v ⊗[F] E => c * x := (continuous_const.mul continuous_id).measurable
  have hT : MeasurableSet ((fun x : Fv F v ⊗[F] E => c * x) ⁻¹' intK b v) := hf hI
  have hmass : coordK (Fv F v) b lam ((fun x : Fv F v ⊗[F] E => c * x) ⁻¹' intK b v) = a := by
    rw [← Measure.map_apply hf hI, hmap, Measure.smul_apply, h1]
    simp [ENNReal.smul_def]
  have hbox : {x : Fin 1 → Fin n → Fv F v ⊗[F] E | ∀ j, c * x 0 j ∈ intK b v} =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (fun x : Fv F v ⊗[F] E => c * x) ⁻¹' intK b v := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_preimage]
    exact ⟨fun h p i => by rw [Subsingleton.elim p 0]; exact h i, fun h i => h 0 i⟩
  rw [hbox]
  refine ⟨MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => hT, ?_⟩
  rw [coordW, Measure.pi_pi]
  simp [Measure.pi_pi, hmass]

end Meas

theorem stageInt_primV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m' : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (c : Fv F v ⊗[F] E) (a : ℝ≥0), IsUnit c → c ∈ intK b v → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → ∀ y ∈ primV σ J b v, ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = scalT c y ∧ stageInt (Fv F v) σ J b lam m' ((latV b v).indicator 1) g = (a : ℝ≥0∞) ^ n * m' (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ n d b v lam hlam m' c a hcu hc hmap y hy
  obtain ⟨k, hk, rfl⟩ := hy
  obtain ⟨u, rfl⟩ := hcu
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI hB := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M
  have hlat : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
    (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b n M v).2.1.measurableSet
  obtain ⟨hA, hAm⟩ := box_mass σ hσ n b v lam hlam (u : Fv F v ⊗[F] E) a hmap
  refine ⟨k * tHA (Fv F v) σ hinv J u, ?_, ?_⟩
  · rw [actW_mul, actW_tHA_e0, actW_scalT]
  · have hmem : ∀ (x : Fin 1 → Fin n → Fv F v ⊗[F] E) (Y : Fin n → Fin M → Fv F v ⊗[F] E),
        actW (Fv F v) σ (hypOne J) (k * tHA (Fv F v) σ hinv J u) (consA x Y) ∈ latV b v ↔
          (∀ j, (u : Fv F v ⊗[F] E) * x 0 j ∈ intK b v) ∧ Y ∈ latV b v := fun x Y => by
      rw [actW_mul, latStab_tuple σ (hypOne J) b v hk, tHA_consA_mem σ hinv J b v u hc]
    have hin : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E,
        ∫⁻ x, (latV b v).indicator 1 (actW (Fv F v) σ (hypOne J) (k * tHA (Fv F v) σ hinv J u) (consA x Y))
            ∂(coordW (Fv F v) b lam 1 n) =
          (latV b v).indicator (fun _ => (a : ℝ≥0∞) ^ n) Y := by
      intro Y
      by_cases hY : Y ∈ latV b v
      · rw [Set.indicator_of_mem hY, ← hAm, ← lintegral_indicator_one hA]
        refine lintegral_congr fun x => ?_
        by_cases hx : ∀ j, (u : Fv F v ⊗[F] E) * x 0 j ∈ intK b v
        · have e1 := Set.indicator_of_mem ((hmem x Y).2 ⟨hx, hY⟩) (1 : (Fin (n + 1) → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
          have e2 := Set.indicator_of_mem (s := {x : Fin 1 → Fin n → Fv F v ⊗[F] E |
            ∀ j, (u : Fv F v ⊗[F] E) * x 0 j ∈ intK b v}) hx (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℝ≥0∞)
          exact e1.trans e2.symm
        · rw [Set.indicator_of_notMem (fun h => hx ((hmem x Y).1 h).1),
            Set.indicator_of_notMem (s := {x : Fin 1 → Fin n → Fv F v ⊗[F] E | ∀ j, (u : Fv F v ⊗[F] E) * x 0 j ∈ intK b v}) hx]
      · rw [Set.indicator_of_notMem hY]
        refine (lintegral_congr fun x => ?_).trans lintegral_zero
        rw [Set.indicator_of_notMem (fun h => hY ((hmem x Y).1 h).2)]
    unfold stageInt
    simp only [hin]
    rw [lintegral_indicator_const hlat]

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal
