import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.PermGroup
variable {n : ℕ}

lemma memLp_equiv {ε ε' : Fin n → Bool} (e : UJ ε' ≃ₜ* UJ ε) (F : UJ ε → ℂ) (p : ENNReal) :
    MemLp F p (muG ε) ↔ MemLp (fun g => F (e g)) p (muG ε') := by
  have hE : (Measure.map e (muG ε')).IsHaarMeasure := e.isHaarMeasure_map (muG ε')
  have hc : Measure.map e (muG ε') =
      Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) • muG ε := Measure.isMulLeftInvariant_eq_smul _ _
  set c : ENNReal := ((Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) : NNReal) : ENNReal)
    with hcdef
  have hc' : Measure.map e (muG ε') = c • muG ε := by rw [hcdef, ← ENNReal.smul_def]; exact hc
  have hT : c ≠ ⊤ := ENNReal.coe_ne_top
  have h0 : c ≠ 0 := by
    intro hz
    have hz' : Measure.map e (muG ε') = 0 := by rw [hc', hz, zero_smul]
    rw [Measure.map_eq_zero_iff
      (show AEMeasurable (⇑e) (muG ε') from (map_continuous e).measurable.aemeasurable)] at hz'
    exact NeZero.ne _ hz'
  have hm := (e.toHomeomorph.toMeasurableEquiv).memLp_map_measure_iff (g := F) (p := p) (μ := muG ε')
  change MemLp F p (Measure.map e (muG ε')) ↔ MemLp (F ∘ e) p (muG ε') at hm
  change MemLp F p (muG ε) ↔ MemLp (F ∘ e) p (muG ε')
  rw [← hm, hc']
  constructor
  · intro h
    exact h.smul_measure hT
  · intro h
    have h' := h.smul_measure (ENNReal.inv_ne_top.2 h0)
    rwa [smul_smul, ENNReal.inv_mul_cancel h0 hT, one_smul] at h'

def homUJ {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) : UJ ε' →* UJ ε :=
  ((Units.map φ).comp (UJ ε').subtype).codRestrict (UJ ε) fun g => h _ g.2

lemma homUJ_cont {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (hc : Continuous φ) : Continuous (homUJ φ h) := by
  refine continuous_induced_rng.2 ?_
  rw [Units.continuous_iff]
  exact ⟨hc.comp (Units.continuous_val.comp continuous_subtype_val),
    hc.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩

lemma memLp_hom {ε ε' : Fin n → Bool} (φ ψ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (h' : ∀ g ∈ UJset ε, ψ g ∈ UJset ε')
    (hc : Continuous φ) (hc' : Continuous ψ) (h1 : ∀ g, ψ (φ g) = g) (h2 : ∀ g, φ (ψ g) = g)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal) :
    MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔
      MemLp (fun g : UJ ε' => f (φ (umat g))) p (muG ε') := by
  let e : UJ ε' ≃ₜ* UJ ε :=
    { toFun := homUJ φ h
      invFun := homUJ ψ h'
      left_inv := fun g => Subtype.ext (Units.ext (h1 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      right_inv := fun g => Subtype.ext (Units.ext (h2 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      map_mul' := fun a b => map_mul (homUJ φ h) a b
      continuous_toFun := homUJ_cont φ h hc
      continuous_invFun := homUJ_cont ψ h' hc' }
  exact memLp_equiv e (fun g => f (umat g)) p

def perm (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ ≃+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ s).toRingEquiv

lemma perm_apply (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    perm s g = g.submatrix s.symm s.symm := rfl

lemma perm_cont (s : Equiv.Perm (Fin n)) : Continuous (perm s) := by
  have h : ⇑(perm s) = fun g => g.submatrix s.symm s.symm := funext (perm_apply s)
  rw [h]
  exact continuous_id.matrix_submatrix _ _

lemma perm_ct (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : (perm s g)ᴴ = perm s gᴴ := rfl

lemma perm_Jm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Jm ε = perm s (Jm (ε ∘ s)) := by
  rw [perm_apply]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Jm]
  · have hij' : s.symm i ≠ s.symm j := fun h => hij (s.symm.injective h)
    simp [Jm, hij, hij']

lemma perm_UJ (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ UJset (ε ∘ s) ↔ perm s g ∈ UJset ε := by
  simp only [UJset, Set.mem_ofPred_eq, inUJ]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul]
  exact (perm s).injective.eq_iff.symm

lemma perm_K (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Kset (ε ∘ s) ↔ perm s g ∈ Kset ε := by
  simp only [Kset, Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, EmbeddingLike.map_eq_one_iff, (perm s).injective.eq_iff]

lemma perm_P (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    inP (ε ∘ s) g ↔ inP ε (perm s g) := by
  simp only [inP, inG]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, ← map_add, ← map_neg, EmbeddingLike.map_eq_zero_iff,
    (perm s).injective.eq_iff]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
lemma perm_exp (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (perm s g) = perm s (NormedSpace.exp g) := (NormedSpace.map_exp (perm s) (perm_cont s) g).symm

def permM (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.submatrix s.symm s.symm
  map_one' := map_one (perm s)
  map_mul' := map_mul (perm s)

lemma permM_symm (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s.symm (permM s g) = g := by
  show (g.submatrix s.symm s.symm).submatrix s.symm.symm s.symm.symm = g
  ext i j
  simp

lemma permM_symm' (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s (permM s.symm g) = g := by
  show (g.submatrix s.symm.symm s.symm.symm).submatrix s.symm s.symm = g
  ext i j
  simp

def conj : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.map star
  map_one' := FormF.map_star_one
  map_mul' := FormF.map_star_mul

lemma conj_cont : Continuous (conj (n := n)) := by
  show Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.map star
  exact continuous_id.matrix_map continuous_star

theorem permGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  intro n ε s
  have hpm : ∀ (t : Equiv.Perm (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ), permM t x = perm t x :=
    fun t x => (perm_apply t x).symm
  have hcont : ∀ t : Equiv.Perm (Fin n), Continuous (permM t) := fun t => by
    have h : ⇑(permM t) = ⇑(perm t) := funext (hpm t)
    rw [h]
    exact perm_cont t
  refine ⟨fun g => ⟨?_, ?_, ?_, ?_⟩, fun f p => ⟨?_, ?_⟩⟩
  · rw [← perm_apply]; exact perm_UJ ε s g
  · rw [← perm_apply]; exact perm_K ε s g
  · rw [← perm_apply]; exact perm_P ε s g
  · rw [← perm_apply, ← perm_apply]; exact perm_exp s g
  · refine memLp_hom (permM s) (permM s.symm) (fun g hg => ?_) (fun g hg => ?_) (hcont s)
      (hcont s.symm) (permM_symm s) (permM_symm' s) f p
    · rw [hpm]; exact (perm_UJ ε s g).1 hg
    · apply (perm_UJ ε s _).2
      rw [← hpm, permM_symm']
      exact hg
  · exact memLp_hom GlobalTheory.Dec.PermGroup.conj GlobalTheory.Dec.PermGroup.conj (fun g hg => FormF.UJ_star hg)
      (fun g hg => FormF.UJ_star hg) conj_cont conj_cont (fun g => FormF.map_star_star g)
      (fun g => FormF.map_star_star g) f p

end GlobalTheory.Dec.PermGroup
