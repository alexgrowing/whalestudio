import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HermSplit

abbrev Pairs (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def pairMap (n : ℕ) : Fin n ⊕ Pairs n → Pairs (n + 1)
  | .inl j => ⟨(0, j.succ), Fin.succ_pos j⟩
  | .inr p => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.2 p.2⟩

theorem pairMap_bijective (n : ℕ) : Function.Bijective (pairMap n) := by
  constructor
  · rintro (j | ⟨⟨i, j⟩, h⟩) (j' | ⟨⟨i', j'⟩, h'⟩) hh <;>
      simp_all [pairMap, Subtype.ext_iff, Prod.ext_iff, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  · rintro ⟨⟨i, j⟩, h⟩
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd h (lt_irrefl _)
      | succ j => exact ⟨.inl j, rfl⟩
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (Fin.not_lt_zero _)
      | succ j => exact ⟨.inr ⟨(i, j), Fin.succ_lt_succ_iff.1 h⟩, rfl⟩

def pairEquiv (n : ℕ) : Fin n ⊕ Pairs n ≃ Pairs (n + 1) := Equiv.ofBijective _ (pairMap_bijective n)

abbrev Coords (R K : Type) (n : ℕ) := (Fin n → R) × (Pairs n → K)

def splitE (R K : Type) (n : ℕ) : Coords R K (n + 1) ≃ R × (Fin n → K) × Coords R K n where
  toFun c := (c.1 0, fun j => c.2 (pairEquiv n (.inl j)), fun i => c.1 i.succ,
    fun p => c.2 (pairEquiv n (.inr p)))
  invFun q := ((Fin.cons q.1 q.2.2.1 : Fin (n + 1) → R),
    fun p => Sum.elim q.2.1 q.2.2.2 ((pairEquiv n).symm p))
  left_inv c := by
    refine Prod.ext ?_ ?_
    · funext i
      exact Fin.cases rfl (fun j => rfl) i
    · funext p
      obtain ⟨x, rfl⟩ := (pairEquiv n).surjective p
      rcases x with j | q <;> simp
  right_inv q := by
    obtain ⟨s, r, d, u⟩ := q
    simp

theorem splitE_symm_fst_zero {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) :
    ((splitE R K n).symm q).1 0 = q.1 := rfl

theorem splitE_symm_fst_succ {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) (i : Fin n) :
    ((splitE R K n).symm q).1 i.succ = q.2.2.1 i := rfl

theorem splitE_symm_snd_inl {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) (j : Fin n) :
    ((splitE R K n).symm q).2 (pairEquiv n (.inl j)) = q.2.1 j := by
  simp [splitE]

theorem splitE_symm_snd_inr {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) (p : Pairs n) :
    ((splitE R K n).symm q).2 (pairEquiv n (.inr p)) = q.2.2.2 p := by
  simp [splitE]

def splitH (R K : Type) [TopologicalSpace R] [TopologicalSpace K] (n : ℕ) :
    Coords R K (n + 1) ≃ₜ R × (Fin n → K) × Coords R K n where
  toEquiv := splitE R K n
  continuous_toFun := by
    refine ((continuous_apply 0).comp continuous_fst).prodMk
      ((continuous_pi fun j => (continuous_apply _).comp continuous_snd).prodMk
        ((continuous_pi fun i => (continuous_apply _).comp continuous_fst).prodMk
          (continuous_pi fun p => (continuous_apply _).comp continuous_snd)))
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
    · induction i using Fin.cases with
      | zero => exact continuous_fst
      | succ i =>
        exact (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
    · rcases hx : (pairEquiv n).symm p with j | q
      · simp only [hx, Sum.elim_inl]
        exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
      · simp only [hx, Sum.elim_inr]
        exact (continuous_apply q).comp (continuous_snd.comp (continuous_snd.comp continuous_snd))

theorem shuffle_mp {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D) [SFinite a]
    [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun x : (A × B) × (C × D) => (x.1.1, x.2.1, x.1.2, x.2.2))
      ((a.prod b).prod (c.prod d)) (a.prod (c.prod (b.prod d))) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (measurePreserving_prodAssoc b c d).symm MeasurableEquiv.prodAssoc
  have h3 : MeasurePreserving (Prod.map Prod.swap id) ((b.prod c).prod d) ((c.prod b).prod d) :=
    (Measure.measurePreserving_swap).prod (MeasurePreserving.id d)
  have h4 := measurePreserving_prodAssoc c b d
  have h5 := (MeasurePreserving.id a).prod (h4.comp (h3.comp h2))
  exact h5.comp h1

theorem splitE_mp {R K : Type} [MeasurableSpace R] [MeasurableSpace K] (lam : Measure R) (κ : Measure K)
    [SigmaFinite lam] [SigmaFinite κ] (n : ℕ) :
    MeasurePreserving (splitE R K n)
      ((Measure.pi fun _ : Fin (n + 1) => lam).prod (Measure.pi fun _ : Pairs (n + 1) => κ))
      (lam.prod ((Measure.pi fun _ : Fin n => κ).prod
        ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : Pairs n => κ)))) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => lam) 0
  have h2 := measurePreserving_arrowCongr' (fun _ : Pairs (n + 1) => κ)
    (fun _ : Fin n ⊕ Pairs n => κ) (pairEquiv n).symm (MeasurableEquiv.refl K)
    (fun _ => MeasurePreserving.id κ)
  have h3 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Pairs n => K)
    (fun _ : Fin n ⊕ Pairs n => κ)
  have h4 := h1.prod (h3.comp h2)
  have h5 := (shuffle_mp lam (Measure.pi fun _ : Fin n => lam) (Measure.pi fun _ : Fin n => κ)
    (Measure.pi fun _ : Pairs n => κ)).comp h4
  convert h5 using 1
  funext c
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · funext i
    show c.1 i.succ = c.1 (Fin.succAbove 0 i)
    simp
  · rfl

section Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R]

def coordOf (σ : E →ₐ[F] E) (n : ℕ) (S : HermR R σ n) : Coords R (R ⊗[F] E) n :=
  ((fun i : Fin n => algebraMap F R (1 / 2) *
      Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)),
    (fun p : Pairs n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2))

def hermMat (σ : E →ₐ[F] E) (n : ℕ) (c : Coords R (R ⊗[F] E) n) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => if h : i < j then c.2 ⟨(i, j), h⟩ else
    if h' : j < i then sigR R σ (c.2 ⟨(j, i), h'⟩) else algebraMap R (R ⊗[F] E) (c.1 i)

theorem hermMat_mem (hσ : IsCMExt F E σ) (n : ℕ) (c : Coords R (R ⊗[F] E) n) :
    hermMat R σ n c ∈ HermR R σ n := by
  intro a b
  rcases lt_trichotomy a b with h | h | h
  · simp only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]
    exact GlobalTheory.GaussMean.OneVec.sigR_sigR R hσ _
  · subst h
    simp only [hermMat, lt_irrefl, dif_neg, not_false_eq_true]
    exact GlobalTheory.GaussMean.OneVec.sigR_algebraMap R _
  · simp [hermMat, h, not_lt_of_gt h]

def chart (hσ : IsCMExt F E σ) (n : ℕ) : HermR R σ n ≃ Coords R (R ⊗[F] E) n where
  toFun := coordOf R σ n
  invFun c := ⟨hermMat R σ n c, hermMat_mem R hσ n c⟩
  left_inv S := by
    apply Subtype.ext
    funext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [hermMat, coordOf, h]
    · subst h
      simpa [hermMat, coordOf] using GlobalTheory.GaussMean.OneVec.fixed_eq R hσ (S.2 i i)
    · simpa [hermMat, coordOf, h, not_lt_of_gt h] using S.2 i j
  right_inv c := by
    refine Prod.ext ?_ ?_
    · funext i
      simpa [hermMat, coordOf] using GlobalTheory.GaussMean.OneVec.half_trace R hσ (c.1 i)
    · funext p
      simp [hermMat, coordOf, p.2]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_algebraMapK : Continuous (algebraMap R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have : (algebraMap R (R ⊗[F] E) : R → R ⊗[F] E) = fun r => r • (1 : R ⊗[F] E) := by
    funext r
    exact Algebra.algebraMap_eq_smul_one r
  rw [this]
  exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))

def chartH (hσ : IsCMExt F E σ) (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    (hsig : Continuous (sigR R σ)) (n : ℕ) : HermR R σ n ≃ₜ Coords R (R ⊗[F] E) n where
  toEquiv := chart R hσ n
  continuous_toFun := by
    have hel : ∀ i j : Fin n, Continuous fun S : HermR R σ n =>
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => hel _ _)
    exact continuous_const.mul (htr.comp (hel i i))
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
    by_cases h : i < j
    · simp only [hermMat, dif_pos h]
      exact (continuous_apply _).comp continuous_snd
    · by_cases h' : j < i
      · simp only [hermMat, dif_neg h, dif_pos h']
        exact hsig.comp ((continuous_apply _).comp continuous_snd)
      · simp only [hermMat, dif_neg h, dif_neg h']
        exact (continuous_algebraMapK R).comp ((continuous_apply i).comp continuous_fst)

theorem hermMat_zero_zero (n : ℕ) (q : R × (Fin n → R ⊗[F] E) × Coords R (R ⊗[F] E) n) :
    hermMat R σ (n + 1) ((splitE R (R ⊗[F] E) n).symm q) 0 0 = q.1 ⊗ₜ[F] (1 : E) := by
  simp [hermMat, splitE_symm_fst_zero, Algebra.TensorProduct.algebraMap_apply]

theorem hermMat_zero_succ (n : ℕ) (q : R × (Fin n → R ⊗[F] E) × Coords R (R ⊗[F] E) n) (j : Fin n) :
    hermMat R σ (n + 1) ((splitE R (R ⊗[F] E) n).symm q) 0 j.succ = q.2.1 j := by
  have h : (0 : Fin (n + 1)) < j.succ := Fin.succ_pos j
  simp only [hermMat, dif_pos h]
  exact splitE_symm_snd_inl q j

theorem hermMat_succ_succ (n : ℕ) (q : R × (Fin n → R ⊗[F] E) × Coords R (R ⊗[F] E) n) (i j : Fin n) :
    hermMat R σ (n + 1) ((splitE R (R ⊗[F] E) n).symm q) i.succ j.succ = hermMat R σ n q.2.2 i j := by
  by_cases h : i < j
  · have h1 : i.succ < j.succ := Fin.succ_lt_succ_iff.2 h
    simp only [hermMat, dif_pos h, dif_pos h1]
    exact splitE_symm_snd_inr q ⟨(i, j), h⟩
  · have h1 : ¬ i.succ < j.succ := fun hh => h (Fin.succ_lt_succ_iff.1 hh)
    by_cases h' : j < i
    · have h2 : j.succ < i.succ := Fin.succ_lt_succ_iff.2 h'
      simp only [hermMat, dif_neg h, dif_neg h1, dif_pos h', dif_pos h2]
      exact congrArg _ (splitE_symm_snd_inr q ⟨(j, i), h'⟩)
    · have h2 : ¬ j.succ < i.succ := fun hh => h' (Fin.succ_lt_succ_iff.1 hh)
      simp only [hermMat, dif_neg h, dif_neg h1, dif_neg h', dif_neg h2]
      exact congrArg _ (splitE_symm_fst_succ q i)

end Chart

theorem herm_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, ∃ e : (R × (Fin n → R ⊗[F] E) × HermR R σ n) ≃ₜ HermR R σ (n + 1), (∀ p, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = p.1 ⊗ₜ[F] (1 : E)) ∧ (∀ p j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 (Fin.succ j) = p.2.1 j) ∧ (∀ p i j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (Fin.succ i) (Fin.succ j) = (p.2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) ∧ (lam.prod ((Measure.pi fun _ => coordK R b lam).prod (coordHerm R σ b lam n))).map e = coordHerm R σ b lam (n + 1) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b lam hlam n
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI := hlam
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI hκ := (GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam).1
  haveI hHerm : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  let C := fun m => chartH (F := F) (E := E) (σ := σ) R hσ htr hsig m
  haveI hsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m => (C m).secondCountableTopology
  have hC : ∀ m, coordHerm R σ b lam m = ((Measure.pi fun _ : Fin m => lam).prod
      (Measure.pi fun _ : Pairs m => coordK R b lam)).map (C m).symm := by
    intro m
    ext s hs
    rw [(C m).symm.measurableEmbedding.map_apply]
    show Measure.comap (C m) _ s = _
    rw [(C m).measurableEmbedding.comap_apply]
    congr 1
    exact (C m).toEquiv.image_eq_preimage_symm s
  let e : (R × (Fin n → R ⊗[F] E) × HermR R σ n) ≃ₜ HermR R σ (n + 1) :=
    ((Homeomorph.refl R).prodCongr ((Homeomorph.refl _).prodCongr (C n))).trans
      ((splitH R (R ⊗[F] E) n).symm.trans (C (n + 1)).symm)
  refine ⟨e, fun p => ?_, fun p j => ?_, fun p i j => ?_, ?_⟩
  · exact hermMat_zero_zero (σ := σ) R n _
  · exact hermMat_zero_succ (σ := σ) R n _ j
  · refine (hermMat_succ_succ (σ := σ) R n _ i j).trans ?_
    have h := congrArg Subtype.val ((chart R hσ n).left_inv p.2.2)
    exact congrFun (congrFun h i) j
  · have hmp := splitE_mp lam (coordK R b lam) n
    have hmp2 : MeasurePreserving (C n).symm ((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : Pairs n => coordK R b lam)) (((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : Pairs n => coordK R b lam)).map (C n).symm) :=
      ⟨(C n).symm.continuous.measurable, rfl⟩
    have hmp4 := ((MeasurePreserving.id lam).prod
      ((MeasurePreserving.id (Measure.pi fun _ : Fin n => coordK R b lam)).prod hmp2)).comp hmp
    rw [hC n, hC (n + 1), ← hmp4.map_eq, Measure.map_map e.continuous.measurable hmp4.measurable]
    congr 1
    funext c
    have hq : (C n) ((C n).symm ((splitE R (R ⊗[F] E) n) c).2.2) = ((splitE R (R ⊗[F] E) n) c).2.2 :=
      (C n).apply_symm_apply _
    show (C (n + 1)).symm ((splitE R (R ⊗[F] E) n).symm (((splitE R (R ⊗[F] E) n) c).1,
      ((splitE R (R ⊗[F] E) n) c).2.1, (C n) ((C n).symm ((splitE R (R ⊗[F] E) n) c).2.2))) = _
    rw [hq]
    exact congrArg _ ((splitE R (R ⊗[F] E) n).symm_apply_apply c)

end GlobalTheory.CompanionTheory.SW.HermSplit
