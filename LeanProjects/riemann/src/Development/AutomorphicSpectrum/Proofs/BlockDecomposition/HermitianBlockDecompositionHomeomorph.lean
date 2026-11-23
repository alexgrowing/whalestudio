import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split

abbrev UT (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

instance isEmpty_UT_one : IsEmpty (UT 1) :=
  ⟨fun p => absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)⟩

def utEquiv (n : ℕ) : Fin n ⊕ UT n ≃ UT (n + 1) :=
  Equiv.ofBijective
    (Sum.elim (fun j => ⟨(0, j.succ), Fin.succ_pos _⟩)
      (fun p => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.2 p.2⟩))
    (by
      constructor
      · rintro (j | ⟨⟨a, b⟩, h⟩) (j' | ⟨⟨a', b'⟩, h'⟩) hh
        · simpa using hh
        · simp at hh
          exact absurd hh.1.symm (Fin.succ_ne_zero _)
        · simp at hh
        · simp at hh
          simp [hh.1, hh.2]
      · rintro ⟨⟨a, b⟩, h⟩
        induction a using Fin.cases with
        | zero =>
          induction b using Fin.cases with
          | zero => exact absurd h (lt_irrefl _)
          | succ j => exact ⟨Sum.inl j, rfl⟩
        | succ i =>
          induction b using Fin.cases with
          | zero => exact absurd h (by simp)
          | succ j => exact ⟨Sum.inr ⟨(i, j), Fin.succ_lt_succ_iff.1 h⟩, rfl⟩)

theorem pi_split {ι κ τ B : Type} [Fintype ι] [Fintype κ] [Fintype τ] [MeasurableSpace B]
    (φ : κ ⊕ τ ≃ ι) (ν : Measure B) [SigmaFinite ν] :
    MeasurePreserving (fun x : ι → B => ((fun j => x (φ (Sum.inl j)), fun p => x (φ (Sum.inr p))) :
        (κ → B) × (τ → B)))
      (Measure.pi fun _ : ι => ν)
      ((Measure.pi fun _ : κ => ν).prod (Measure.pi fun _ : τ => ν)) := by
  classical
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : ι => B) (fun _ : ι => ν) φ).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : κ ⊕ τ => ν)
  convert h2.comp h1 using 1
  rfl

def blockT {A B : Type} (n : ℕ) (x : (Fin (n + 1) → A) × (UT (n + 1) → B)) :
    ((Fin 1 → A) × (UT 1 → B)) × ((Fin 1 → Fin n → B) × ((Fin n → A) × (UT n → B))) :=
  ((fun _ => x.1 0, fun p => isEmptyElim p),
    (fun _ j => x.2 (utEquiv n (Sum.inl j)),
      (fun i => x.1 i.succ, fun p => x.2 (utEquiv n (Sum.inr p)))))

theorem scalar_mp {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (lam : Measure A) (κ : Measure B)
    [SigmaFinite lam] :
    MeasurePreserving (fun r : A => (((fun _ => r), fun p => isEmptyElim p) : (Fin 1 → A) × (UT 1 → B)))
      lam ((Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : UT 1 => κ)) := by
  have h1 := (measurePreserving_funUnique lam (Fin 1)).symm
  have h2 : MeasurePreserving (fun f : Fin 1 → A => ((f, fun p => isEmptyElim p) : (Fin 1 → A) × (UT 1 → B)))
      (Measure.pi fun _ : Fin 1 => lam)
      ((Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : UT 1 => κ)) := by
    have hd : Measure.pi (fun _ : UT 1 => κ) = Measure.dirac (fun p => isEmptyElim p) :=
      Measure.pi_of_empty _ _
    rw [hd, Measure.prod_dirac]
    exact ⟨by fun_prop, rfl⟩
  exact h2.comp h1

theorem blockT_mp {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (lam : Measure A) (κ : Measure B)
    [SigmaFinite lam] [SigmaFinite κ] (n : ℕ) :
    MeasurePreserving (blockT (A := A) (B := B) n)
      ((Measure.pi fun _ : Fin (n + 1) => lam).prod (Measure.pi fun _ : UT (n + 1) => κ))
      (((Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : UT 1 => κ)).prod
        ((Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => κ).prod
          ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : UT n => κ)))) := by
  set Au := Measure.pi fun _ : Fin n => lam
  set Bw := Measure.pi fun _ : Fin n => κ
  set Cv := Measure.pi fun _ : UT n => κ
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => lam) 0
  have h2 := pi_split (utEquiv n) κ
  have h12 := h1.prod h2
  have m1 := measurePreserving_prodAssoc lam Au (Bw.prod Cv)
  have m2 := (MeasurePreserving.id lam).prod ((measurePreserving_prodAssoc Au Bw Cv).symm)
  have m3 := (MeasurePreserving.id lam).prod
    ((Measure.measurePreserving_swap (μ := Au) (ν := Bw)).prod (MeasurePreserving.id Cv))
  have m4 := (MeasurePreserving.id lam).prod (measurePreserving_prodAssoc Bw Au Cv)
  have g1 := scalar_mp (B := B) lam κ
  have g2 := (measurePreserving_funUnique Bw (Fin 1)).symm
  have m5 := g1.prod (g2.prod (MeasurePreserving.id (Au.prod Cv)))
  have all := m5.comp (m4.comp (m3.comp (m2.comp (m1.comp h12))))
  suffices hf : blockT (A := A) (B := B) n = _ by
    rw [hf]; exact all
  clear all m5 m4 m3 m2 m1 h12 h1 h2 g1 g2
  funext x
  obtain ⟨u, v⟩ := x
  simp [blockT, MeasurableEquiv.piFinSuccAbove, Prod.map]
  refine ⟨rfl, ?_, rfl⟩
  funext i
  rw [uniqueElim_const]
  rfl

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

def corner (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ (n + 1)) : HermR R σ 1 :=
  ⟨fun _ _ => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0, fun _ _ => S.2 0 0⟩

def firstRow (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ (n + 1)) : Fin 1 → Fin n → R ⊗[F] E :=
  fun _ j => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ

def lowerBlock (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ (n + 1)) : HermR R σ n :=
  ⟨fun i j => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ,
    fun a b => S.2 a.succ b.succ⟩

def glue (σ : E →ₐ[F] E) {n : ℕ} (t : HermR R σ 1) (w : Fin 1 → Fin n → R ⊗[F] E) (L : HermR R σ n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) := fun a b =>
  Fin.cases (Fin.cases ((t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) (fun j => w 0 j) b)
    (fun i => Fin.cases (sigR R σ (w 0 i)) (fun j => (L : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) b) a

theorem glue_mem {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {n : ℕ} (t : HermR R σ 1)
    (w : Fin 1 → Fin n → R ⊗[F] E) (L : HermR R σ n) : glue R σ t w L ∈ HermR R σ (n + 1) := by
  intro a b
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => exact t.2 0 0
    | succ j => exact HypStage.sigR_sigR R σ hinv _
  | succ i =>
    induction b using Fin.cases with
    | zero => rfl
    | succ j => exact L.2 i j

variable [TopologicalSpace R]

theorem continuous_entry (σ : E →ₐ[F] E) {m : ℕ} (a b : Fin m) :
    Continuous fun S : HermR R σ m => (S : Matrix (Fin m) (Fin m) (R ⊗[F] E)) a b :=
  (continuous_subtype_val (p := fun S => S ∈ HermR R σ m)).matrix_elem a b

def blockHomeo {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (hsig : Continuous (sigR R σ)) (n : ℕ) :
    HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n) where
  toFun S := (corner R σ S, firstRow R σ S, lowerBlock R σ S)
  invFun x := ⟨glue R σ x.1 x.2.1 x.2.2, glue_mem R hinv x.1 x.2.1 x.2.2⟩
  left_inv S := by
    apply Subtype.ext
    funext a b
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ j => rfl
    | succ i =>
      induction b using Fin.cases with
      | zero => exact S.2 _ _
      | succ j => rfl
  right_inv x := by
    obtain ⟨t, w, L⟩ := x
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply Subtype.ext
      funext a b
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : b = 0 := Subsingleton.elim _ _
      rfl
    · funext a j
      obtain rfl : a = 0 := Subsingleton.elim _ _
      rfl
    · apply Subtype.ext
      rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact continuous_induced_rng.2 (continuous_matrix fun _ _ => continuous_entry R σ _ _)
    · exact continuous_pi fun _ => continuous_pi fun _ => continuous_entry R σ _ _
    · exact continuous_induced_rng.2 (continuous_matrix fun _ _ => continuous_entry R σ _ _)
  continuous_invFun := by
    have ht : Continuous fun x : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
        (x.1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      (continuous_entry R σ 0 0).comp continuous_fst
    have hw : ∀ j : Fin n, Continuous fun x : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
        x.2.1 0 j := fun j =>
      (continuous_apply_apply _ _).comp (continuous_fst.comp continuous_snd)
    have hL : ∀ i j : Fin n, Continuous fun x : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
        (x.2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j := fun i j =>
      (continuous_entry R σ i j).comp (continuous_snd.comp continuous_snd)
    refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact ht
      | succ j => exact hw j
    | succ i =>
      induction b using Fin.cases with
      | zero => exact hsig.comp (hw i)
      | succ j => exact hL i j

end Herm

theorem coordHerm_equiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (m : ℕ) :
    ∃ h : HermR R σ m ≃ᵐ (Fin m → R) × (UT m → R ⊗[F] E),
      (∀ S, h S = HaarCoord.hermCoord R σ m S) ∧
      MeasurePreserving h (coordHerm R σ b lam m)
        ((Measure.pi fun _ : Fin m => lam).prod (Measure.pi fun _ : UT m => coordK R b lam)) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : BorelSpace (HermR R σ m) := ⟨rfl⟩
  have hh := HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ m t5 t6
  let ge := (hh.homeomorph _).toMeasurableEquiv
  refine ⟨ge, fun _ => rfl, ge.measurable, ?_⟩
  have hc : coordHerm R σ b lam m =
      Measure.map ge.symm ((Measure.pi fun _ : Fin m => lam).prod
        (Measure.pi fun _ : UT m => coordK R b lam)) :=
    (MeasurableEquiv.map_symm ge).symm
  rw [hc, Measure.map_map ge.measurable ge.symm.measurable]
  simp

theorem hermSplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∃ e : HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), (∀ S, ((e S).1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 ∧ (∀ j : Fin n, (e S).2.1 0 j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) ∧ ∀ i j : Fin n, ((e S).2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) ∧ MeasurePreserving e (coordHerm R σ b lam (n + 1)) ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ _ _ _ hloc n d b lam hlam
  obtain ⟨l1, l2, l3, l4, -⟩ := hloc
  haveI := l1
  haveI := l2
  haveI := l3
  haveI := l4
  obtain ⟨t1, t2, t3, t4, t5, t6, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  obtain ⟨hinv, -⟩ := HaarCoord.conj_facts hcm
  obtain ⟨hK, -, hH⟩ := coord_measures_haar F E σ hcm R d b lam hlam
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hcm R 1
  obtain ⟨c1, c2, c3, c4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hcm R n
  haveI : (coordHerm R σ b lam 1).IsAddHaarMeasure := hH 1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hH n
  haveI : SigmaFinite (coordW R b lam 1 n) := by
    unfold coordW
    infer_instance
  haveI : SigmaFinite (coordHerm R σ b lam 1) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  refine ⟨blockHomeo R hinv t5 n, fun S => ⟨rfl, fun j => rfl, fun i j => rfl⟩, ?_⟩
  obtain ⟨h1, hh1, mp1⟩ := coordHerm_equiv σ hcm R b lam 1
  obtain ⟨hn, hhn, mpn⟩ := coordHerm_equiv σ hcm R b lam n
  obtain ⟨hN, hhN, mpN⟩ := coordHerm_equiv σ hcm R b lam (n + 1)
  let G := h1.prodCongr ((MeasurableEquiv.refl (Fin 1 → Fin n → R ⊗[F] E)).prodCongr hn)
  have mG : MeasurePreserving G ((coordHerm R σ b lam 1).prod
      ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) _ :=
    mp1.prod ((MeasurePreserving.id (coordW R b lam 1 n)).prod mpn)
  have mT := blockT_mp lam (coordK R b lam) n
  have key : G ∘ (blockHomeo R hinv t5 n) = blockT n ∘ hN := by
    funext S
    have e1 : (G ∘ (blockHomeo R hinv t5 n)) S =
        (h1 (corner R σ S), firstRow R σ S, hn (lowerBlock R σ S)) := rfl
    rw [e1, hh1, hhn, Function.comp_apply, hhN]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i
      rfl
    · funext p
      exact isEmptyElim p
    · funext a j
      rfl
    · funext i
      rfl
    · funext p
      rfl
  refine (mG.comp_left_iff).1 ?_
  rw [key]
  exact mT.comp mpN

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split
