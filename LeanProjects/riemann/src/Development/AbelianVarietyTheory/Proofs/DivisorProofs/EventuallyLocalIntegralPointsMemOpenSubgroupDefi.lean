import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalCompactSmall
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic Topology

noncomputable section

namespace GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_one_entry {R : Type} [Ring R] (f : Ad E →+* R) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem sub_one_entry_mem {w : Pl E} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ w.adicCompletionIntegers E := by
  rw [mem_KGL_iff_val] at hg
  refine sub_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hg.1 i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

omit [IsCMField E] in

theorem af_ext {a b : Af E} (h : ∀ u : Pl E, pLoc E u a = pLoc E u b) : a = b := Subtype.ext (funext h)

omit [IsCMField E] in
theorem pLoc_singleNU_self (w : Pl E) (y : w.adicCompletion E) : pLoc E w (GlobalTheory.GLTwoHecke.singleNU w y) = y :=
  GlobalTheory.AdelicU.evalV_singleFin_self w y

omit [IsCMField E] in
theorem pLoc_singleNU_ne {u w : Pl E} (h : u ≠ w) (y : w.adicCompletion E) :
    pLoc E u (GlobalTheory.GLTwoHecke.singleNU w y) = 0 :=
  GlobalTheory.AdelicU.evalV_singleFin_ne h y

theorem entry_eq_one_add {w : Pl E} {N N' : Set (Af E)} (h0 : (0 : Af E) ∈ N')
    (hadd : ∀ a ∈ N', ∀ b ∈ N', a + b ∈ N)
    (hw : ∀ y ∈ w.adicCompletionIntegers E, GlobalTheory.GLTwoHecke.singleNU w y ∈ N')
    (hc : ∀ y ∈ (conjSrc (conjE E) w).adicCompletionIntegers E,
      GlobalTheory.GLTwoHecke.singleNU (conjSrc (conjE E) w) y ∈ N')
    (z : UA E n) (hz : z ∈ locU n w) (hK : cLoc w z ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    ∃ a ∈ N, ((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + (show Ad E from ((0 : InfiniteAdeleRing E), a)) := by
  have hKc := integral_conjSrc z w hK
  have hfin : z ∈ finU E n := (Subgroup.mem_inf.1 hz).1
  have hout : ∀ u : Pl E, u ≠ w → u ≠ conjSrc (conjE E) w → cLoc u z = 1 := by
    intro u huw huc
    have hne : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := fun h =>
      (eq_or_eq_conjSrc h).elim huw huc
    exact (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hz).2 u) hne)
  generalize conjSrc (conjE E) w = c at hc hKc hout
  refine ⟨GlobalTheory.GLTwoHecke.singleNU w ((cLoc w z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
    (if c = w then 0 else GlobalTheory.GLTwoHecke.singleNU c ((cLoc c z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j)),
    hadd _ (hw _ (sub_one_entry_mem hK i j)) _ ?_, ?_⟩
  · split_ifs
    · exact h0
    · exact hc _ (sub_one_entry_mem hKc i j)
  refine Prod.ext ?_ ?_
  · have h1 : GeneralLinearGroup.map (pInf E) (z : GA E n) = 1 := hfin
    have h2 : pInf E (((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
        pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
      rw [map_one_entry]
      have := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) h1
      simpa using this
    have h3 := (infEq E).symm.injective h2
    change _ = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 + 0
    rw [add_zero]
    exact h3
  · apply af_ext
    intro u
    change (cLoc u z).val i j = ((pLoc E u).comp (pFin E)) ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      (show Ad E from ((0 : InfiniteAdeleRing E), _)))
    rw [map_add, map_one_entry]
    change _ = _ + pLoc E u (GlobalTheory.GLTwoHecke.singleNU w _ + _)
    rw [map_add]
    by_cases huw : u = w
    · subst huw
      rw [pLoc_singleNU_self]
      split_ifs with hcw
      · rw [map_zero]; abel
      · rw [pLoc_singleNU_ne (Ne.symm hcw)]; abel
    · rw [pLoc_singleNU_ne huw]
      by_cases huc : u = c
      · subst huc
        rw [if_neg huw, pLoc_singleNU_self]; abel
      · rw [hout u huw huc]
        split_ifs
        · simp
        · rw [pLoc_singleNU_ne huc]; simp

theorem eventually_locU_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU E n)),
    IsOpen (L : Set (finU E n)) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w n →
      ∀ h : x ∈ finU E n, (⟨x, h⟩ : finU E n) ∈ L := by
  intro E _ _ _ n L hL
  have h1 : (L : Set (finU E n)) ∈ 𝓝 (1 : finU E n) := hL.mem_nhds L.one_mem
  rw [nhds_subtype, Filter.mem_comap] at h1
  obtain ⟨V1, hV1, hV1L⟩ := h1
  rw [nhds_subtype, Filter.mem_comap] at hV1
  obtain ⟨V, hV, hVV1⟩ := hV1
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  let Φ : Af E → Ad E := fun a => show Ad E from ((0 : InfiniteAdeleRing E), a)
  have hΦ : Continuous Φ := continuous_const.prodMk continuous_id
  have hΦ0 : Φ 0 = 0 := rfl
  let ψ : (Bool × Fin n × Fin n → Af E) →
      Matrix (Fin n) (Fin n) (Ad E) × (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    fun y => (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (false, i, j)),
      MulOpposite.op (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (true, i, j))))
  have hψ : Continuous ψ := by
    refine Continuous.prodMk ?_ (MulOpposite.continuous_op.comp ?_) <;>
    exact continuous_pi fun i => continuous_pi fun j => continuous_const.add (hΦ.comp (continuous_apply _))
  have hψ0 : ψ 0 = Units.embedProduct _ (1 : GA E n) := by
    refine Prod.ext ?_ ?_
    · ext i j; simp [ψ, hΦ0]
    · refine MulOpposite.unop_injective ?_
      ext i j; simp [ψ, hΦ0]
  have hS : ψ ⁻¹' W ∈ 𝓝 (0 : Bool × Fin n × Fin n → Af E) :=
    hψ.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hW)
  rw [nhds_pi, Filter.mem_pi'] at hS
  obtain ⟨I, t, ht, hIt⟩ := hS
  have hN : (⋂ i, t i) ∈ 𝓝 (0 : Af E) := Filter.iInter_mem.2 ht
  obtain ⟨N', hN', hadd⟩ := exists_nhds_zero_half hN
  have h0 : (0 : Af E) ∈ N' := mem_of_mem_nhds hN'
  have hev := GlobalTheory.GLTwoHecke.eventually_singleNU_mem hN'
  have hev2 := (conjSrc_injective (conjE E)).tendsto_cofinite.eventually hev
  filter_upwards [hev, hev2] with w hw hw2 x hxw hxK hx
  have hxw' : x⁻¹ ∈ locU n w := inv_mem hxw
  have hxK' : cLoc w x⁻¹ ∈ GlobalTheory.LFun.KGL w n := by rw [map_inv]; exact inv_mem hxK
  choose a ha hxa using entry_eq_one_add h0 hadd hw hw2 x hxw hxK
  choose b hb hxb using entry_eq_one_add h0 hadd hw hw2 x⁻¹ hxw' hxK'
  let y : Bool × Fin n × Fin n → Af E := fun p => if p.1 then b p.2.1 p.2.2 else a p.2.1 p.2.2
  have hy : y ∈ ψ ⁻¹' W := hIt fun p _ => by
    rcases p with ⟨_ | _, i, j⟩
    · exact Set.mem_iInter.1 (ha i j) _
    · exact Set.mem_iInter.1 (hb i j) _
  apply hV1L
  apply hVV1
  apply hWV
  have e : ψ y = Units.embedProduct _ ((x : GA E n)) := by
    refine Prod.ext ?_ ?_
    · ext i j
      exact (hxa i j).symm
    · refine MulOpposite.unop_injective ?_
      ext i j
      exact (hxb i j).symm
  show Units.embedProduct _ (x : GA E n) ∈ W
  rw [← e]
  exact hy

end GlobalTheory.BCT.GlobLev
