import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualHermMeasures
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SelfDualTransport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterTrivialAlmostEverywhere

noncomputable section

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermCov

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) [FiniteDimensional F E]
    (A : Matrix (Fin n) (Fin n) E) : Idx n d → F :=
  Sum.elim (fun a => 1 / 2 * Algebra.trace F E (A a a)) fun q => b.repr (A q.1.1.1 q.1.1.2) q.2

def ofVec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    Matrix (Fin n) (Fin n) E := fun a c =>
  if h : a < c then ∑ l, k (Sum.inr (⟨(a, c), h⟩, l)) • b l
  else if h' : c < a then σ (∑ l, k (Sum.inr (⟨(c, a), h'⟩, l)) • b l)
  else algebraMap F E (k (Sum.inl a))

theorem ofVec_herm {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (k : Idx n d → F) (a c : Fin n) : σ (ofVec σ b n k c a) = ofVec σ b n k a c := by
  rcases lt_trichotomy a c with h | h | h
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h), hinv]
  · subst h
    simp only [ofVec, lt_irrefl, dite_false, AlgHom.commutes]
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h)]

theorem ratVec_ofVec [FiniteDimensional F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    ratVec b n (ofVec σ b n k) = k := by
  funext i
  cases i with
  | inl a =>
    simp only [ratVec, Sum.elim_inl, ofVec, lt_irrefl, dite_false, Algebra.trace_algebraMap, h2]
    simp
  | inr q =>
    obtain ⟨p, l⟩ := q
    simp only [ratVec, Sum.elim_inr, ofVec, dif_pos p.2]
    rw [b.repr_sum_self]

variable (R : Type) [CommRing R] [Algebra F R]

theorem repr_inclR {d : ℕ} (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

variable [TopologicalSpace R]

theorem hermVec_map [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) E) (S : HermR R σ n)
    (hS : (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = A.map (inclR R)) (i : Idx n d) :
    hermVec R σ b n S i = algebraMap F R (ratVec b n A i) := by
  cases i with
  | inl a =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inl, ratVec, hS, Matrix.map_apply]
    change _ * Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] A a a) = _
    rw [trace_tmul, one_mul, map_mul]
  | inr q =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inr, ratVec, hS, Matrix.map_apply]
    exact repr_inclR R b _ _

end Alg

section Main

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth PositivityTheory.SiegelWeilFormula.KWhit.MeasP
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_ratHerm_iff {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2)
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (hinj : Function.Injective (hermVec (AF F) σ b n)) (S : HermR (AF F) σ n) :
    S ∈ ratHerm F E σ n ↔ ∃ k : Idx n d → F, ∀ i, hermVec (AF F) σ b n S i = algebraMap F (AF F) (k i) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨ratVec b n A, hermVec_map (AF F) σ b n A S hA.symm⟩
  · rintro ⟨k, hk⟩
    have hmem : (ofVec σ b n k).map (inclR (AF F)) ∈ HermR (AF F) σ n := by
      intro a c
      simp only [Matrix.map_apply]
      rw [← ofVec_herm hinv b n k a c]
      change sigR (AF F) σ ((1 : AF F) ⊗ₜ[F] _) = (1 : AF F) ⊗ₜ[F] _
      rw [HaarCoord.sigR_tmul]
    have hT : (⟨_, hmem⟩ : HermR (AF F) σ n) = S := by
      apply hinj
      funext i
      rw [hermVec_map (AF F) σ b n (ofVec σ b n k) _ rfl i, ratVec_ofVec h2, hk]
    refine ⟨ofVec σ b n k, ?_⟩
    rw [← hT]
    rfl

theorem existsUnique_sub_mem_pi {ι : Type} (x : ι → AF F) :
    ∃! k : ι → F, (fun i => x i - algebraMap F (AF F) (k i)) ∈
      Set.univ.pi fun _ : ι => fundamentalSet F := by
  choose k hk huniq using fun i => existsUnique_sub_mem_fundamentalSet F (x i)
  refine ⟨k, fun i _ => hk i, fun k' hk' => funext fun i => huniq i _ (hk' i (Set.mem_univ i))⟩

theorem hermCovol : HermCovol := by
  intro F E _ _ _ _ _ σ hCM ψ hψ n ν hν
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hCM
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let e := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x, map_zero, zero_mul, AddChar.map_zero_eq_one]
    simp
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (HermR (AF F) σ n) := inferInstance
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have hsd : ν.map e = adeleMeasurePi F := by
    refine GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_eq _ hs hdet _
      (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_transport e ?_ _ _ ?_ ν hν)
    · intro x y
      exact hermVec_add (AF F) b n x y
    · intro S T
      have h3 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
          algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
        ext p q
        exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
      rw [hξ, pair_eq (AF F) hinv h2 hδ hσδ b n S T, chiG, h3, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul]
      rfl
  set D : Set (Idx n 2 → AF F) := Set.univ.pi fun _ => fundamentalSet F with hD
  have hDm : MeasurableSet D := MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hinj : Function.Injective (hermVec (AF F) σ b n) := e.injective
  refine ⟨e ⁻¹' D, IsAddFundamentalDomain.mk' (hDm.preimage e.measurable).nullMeasurableSet ?_, ?_⟩
  · intro S
    obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_pi (e S)
    have hg : e.symm (fun i => algebraMap F (AF F) (-k i)) ∈ ratHerm F E σ n :=
      (mem_ratHerm_iff hinv h2 b n hinj _).2 ⟨fun i => -k i, fun i => by
        rw [← he, e.apply_symm_apply]⟩
    refine ⟨⟨_, hg⟩, ?_, ?_⟩
    · change e (e.symm _ + S) ∈ D
      rw [he, hermVec_add, ← he, ← he, e.apply_symm_apply]
      convert hk using 2 with i
      simp [sub_eq_add_neg, add_comm]
    · rintro ⟨g, hgm⟩ hg'
      obtain ⟨k', hk'⟩ := (mem_ratHerm_iff hinv h2 b n hinj _).1 hgm
      change e (g + S) ∈ D at hg'
      rw [he, hermVec_add, ← he] at hg'
      have hkk : (fun i => -k' i) = k := huniq _ (by
        convert hg' using 2 with i
        simp [he, hk', sub_eq_add_neg, add_comm])
      refine Subtype.ext (e.injective ?_)
      rw [e.apply_symm_apply]
      funext i
      rw [he, hk', ← hkk]
      simp
  · rw [← Measure.map_apply e.measurable hDm, hsd, adeleMeasurePi, hD, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SW.HermCov
