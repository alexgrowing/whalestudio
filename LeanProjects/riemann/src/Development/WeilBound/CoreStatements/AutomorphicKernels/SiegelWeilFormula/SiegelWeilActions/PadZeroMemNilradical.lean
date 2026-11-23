import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzEqFlat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroupStatement

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def pad0 (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0

theorem pad_zero_embedding_alt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : pad0 L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [pad0, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]

theorem pad_zero_outside_range (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : pad0 L β i k = 0 := by
  simp only [pad0, dif_neg h]

theorem pad_zero_symm_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (pad0 L β i k) (pad0 L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [pad_zero_embedding_alt, pad_zero_embedding_alt]
    exact h1 a c
  · rw [pad_zero_outside_range L β i k h, pad_zero_outside_range L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0

theorem eps_common : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩

theorem pad_zero_mem_nilradical (β : nA σ L.Y L.b) : pad0 L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine pad_zero_symm_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this

def padN : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨pad0 L β.1, pad_zero_mem_nilradical L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine pad_zero_symm_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_embedding_alt]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_outside_range L _ i k h, add_zero]

theorem prj_padN (β : nA σ L.Y L.b) : prj L (padN L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [prj_val, Matrix.submatrix_apply]
  exact pad_zero_embedding_alt L β.1 a c

theorem continuous_padN : Continuous (padN L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [pad_zero_embedding_alt]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [pad_zero_outside_range L _ i k h]
    exact continuous_const

theorem countable_nF (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) : Countable (nF σ Y b) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  refine Function.Injective.countable (f := fun ν : nF σ Y b => Classical.choose (kunf.mem_nF_iff.1 ν.2)) ?_
  intro ν ν' h
  have h1 := Classical.choose_spec (kunf.mem_nF_iff.1 ν.2)
  have h2 := Classical.choose_spec (kunf.mem_nF_iff.1 ν'.2)
  apply Subtype.ext; apply Subtype.ext
  rw [h1, h2]
  exact congrArg _ h

theorem prj_nF {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : prj L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [prj_val, hT]
  rfl

theorem padN_nF {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : padN L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show pad0 L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [pad0, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [pad0, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]

theorem nA_inst (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    LocallyCompactSpace (nA σ Y b) ∧ T2Space (nA σ Y b) := by
  have h := GlobalTheory.T.adelic_skew_matrices_locally_compact_group F E σ n Y b ε fun β => by
    rw [kunf.mem_nA_iff hε, ← sub_eq_zero, sub_neg_eq_add]
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

theorem fiber {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (prj L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact GlobalTheory.T.haar_measure_split_exact_sequence (prj L) (padN L) (continuous_prj L) (continuous_padN L) (prj_padN L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => prj_nF L hγ)
    (fun γ hγ => padN_nF L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)

end PositivityTheory.SiegelWeilFormula.Act.C4

end
