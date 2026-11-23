import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Topology

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_intAt (v : HeightOneSpectrum (𝓞 E)) :
    IsOpen (v.adicCompletionIntegers E : Set (v.adicCompletion E)) := by
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem tendsto_af {α : Type} {l : Filter α} (g : α → Af E) (c : Af E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v c ∈ v.adicCompletionIntegers E)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (g a) = pLoc E v c) :
    Tendsto g l (𝓝 c) := by
  let c' : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun v => ⟨pLoc E v c, hc v⟩
  have hcc : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite c' = c := by
    apply RestrictedProduct.ext
    intro v
    rfl
  let g' : α → Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun a =>
    if h : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E then fun v => ⟨pLoc E v (g a), h v⟩
    else c'
  have hg' : Tendsto g' l (𝓝 c') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [h2, h3 v] with a ha hav
    simp only [g', dif_pos ha]
    exact Subtype.ext hav.symm
  have hmap := (tendsto_map (f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite)).comp hg'
  rw [← RestrictedProduct.nhds_eq_map_structureMap (fun v => isOpen_intAt v), hcc] at hmap
  apply hmap.congr'
  filter_upwards [h2] with a ha
  simp only [Function.comp_apply, g', dif_pos ha]
  apply RestrictedProduct.ext
  intro v
  rfl

theorem tendsto_ad {α : Type} {l : Filter α} (g : α → Ad E) (c : Ad E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E c) ∈ v.adicCompletionIntegers E)
    (h1 : ∀ᶠ a in l, (g a).1 = c.1)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E (g a)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (pFin E (g a)) = pLoc E v (pFin E c)) :
    Tendsto g l (𝓝 c) := by
  have hA : Tendsto (fun a => (g a).1) l (𝓝 c.1) := tendsto_const_nhds.congr' (h1.mono fun a ha => ha.symm)
  have hB : Tendsto (fun a => (g a).2) l (𝓝 c.2) := tendsto_af (fun a => (g a).2) c.2 hc h2 h3
  exact hA.prodMk_nhds hB

end GlobalTheory.FixLevOpen

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tendsto_mat {α : Type} {l : Filter α} (f : α → Matrix (Fin n) (Fin n) (Ad E))
    (h1 : ∀ᶠ a in l, ∀ i j, (f a i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1)
    (h2 : ∀ᶠ a in l, ∀ (v : HeightOneSpectrum (𝓞 E)) i j, pLoc E v (pFin E (f a i j)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, ∀ i j,
      pLoc E v (pFin E (f a i j)) = pLoc E v (pFin E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j))) :
    Tendsto f l (𝓝 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  apply tendsto_ad
  · intro v
    rcases eq_or_ne i j with rfl | h
    · rw [Matrix.one_apply_eq, map_one, map_one]
      exact one_mem _
    · rw [Matrix.one_apply_ne h, map_zero, map_zero]
      exact zero_mem _
  · exact h1.mono fun a ha => ha i j
  · exact h2.mono fun a ha v => ha v i j
  · exact fun v => (h3 v).mono fun a ha => ha i j

theorem inf_entry (u : finU E n) (i j : Fin n) :
    ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := by
  have hu : cInf (u : UA E n) = 1 := u.2
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) hu
  have h' : pInf E ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
      pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
    refine h.trans ?_
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.one_apply_eq]
    · simp [Matrix.one_apply_ne hij]
  have h'' : (infEq E).symm ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 =
      (infEq E).symm ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := h'
  exact (infEq E).symm.injective h''

theorem mem_of_isOpen_of_eq_one_on_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Set (finU E n)), IsOpen U →
    (1 : finU E n) ∈ U → ∃ T : Finset (Pl E), ∀ u : finU E n, (∀ v ∈ T, cLoc v (u : UA E n) = 1) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E) → u ∈ U := by
  intro E _ _ _ n U hU h1
  let S : Finset (Pl E) → Set (finU E n) := fun T => {u | (∀ v ∈ T, cLoc v (u : UA E n) = 1) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E)}
  have hanti : ∀ T₁ T₂ : Finset (Pl E), T₁ ⊆ T₂ → S T₂ ⊆ S T₁ := fun T₁ T₂ h u hu =>
    ⟨fun v hv => hu.1 v (h hv), hu.2.1, hu.2.2⟩
  have hdir : Directed (fun x1 x2 => x1 ≥ x2) (fun T => 𝓟 (S T)) := by
    intro T₁ T₂
    refine ⟨T₁ ∪ T₂, ?_, ?_⟩
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_left)
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_right)
  let l : Filter (finU E n) := ⨅ T, 𝓟 (S T)
  have hmem : ∀ T, S T ∈ l := fun T => mem_iInf_of_mem T (mem_principal_self _)
  let ι : finU E n → GA E n := fun u => ((u : UA E n) : GA E n)
  have hι : Topology.IsInducing ι := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hl : Tendsto id l (𝓝 (1 : finU E n)) := by
    rw [hι.tendsto_nhds_iff, Units.isEmbedding_embedProduct.isInducing.tendsto_nhds_iff]
    show Tendsto (fun u => (((ι u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)),
      MulOpposite.op (((ι u)⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)))) l
      (𝓝 ((1 : Matrix (Fin n) (Fin n) (Ad E)), MulOpposite.op (1 : Matrix (Fin n) (Fin n) (Ad E))))
    refine Tendsto.prodMk_nhds ?_ (MulOpposite.continuous_op.tendsto _ |>.comp ?_)
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u i j
      · filter_upwards [hmem ∅] with u hu
        exact fun v i j => hu.2.1 v i j
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (hu.1 v (Finset.mem_singleton_self v))
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u⁻¹ i j
      · filter_upwards [hmem ∅] with u hu
        intro v i j
        have := hu.2.2 v i j
        rwa [← map_inv] at this
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have hv : cLoc v ((u : UA E n)⁻¹) = 1 := by
          rw [map_inv, hu.1 v (Finset.mem_singleton_self v), inv_one]
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) hv
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
  have hU' : U ∈ l := hl (hU.mem_nhds h1)
  rw [mem_iInf_of_directed hdir] at hU'
  obtain ⟨T, hT⟩ := hU'
  exact ⟨T, fun u a b c => mem_principal.mp hT ⟨a, b, c⟩⟩

end GlobalTheory.FixLevOpen
