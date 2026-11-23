import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.SDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_int {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (t : w.adicCompletion E) (ht : t ∈ w.adicCompletionIntegers E) : cj w t ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht ⊢
  have h1 : e.symm t ∈ (algebraMap K.O K.E).range := (hB.2.1 _).2 (by simpa using ht)
  obtain ⟨o, ho⟩ := h1
  obtain ⟨o', ho'⟩ := K.c_int o
  have h2 : cj w t = e (algebraMap K.O K.E o') := by
    rw [← ho', ho, hB.1, RingEquiv.apply_symm_apply]
  rw [h2]
  exact (hB.2.1 _).1 ⟨o', rfl⟩

theorem cj_cj {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (t : w.adicCompletion E) : cj w (cj w t) = t := by
  obtain ⟨a, rfl⟩ := e.surjective t
  rw [← hB.1, ← hB.1, K.c_c]

theorem stdH_unitary {w : Pl E} {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hM : Formalism.UG.cT (cj w) M * 1 * M = 1)
    (v v' : Fin n → w.adicCompletion E) : stdH w (M *ᵥ v) (M *ᵥ v') = stdH w v v' := by
  have hM' : Mᵀ * M.map (cj w) = 1 := by
    have h := congrArg (fun X => X.map (cj w)) hM
    simp only [Formalism.UG.cT, Matrix.mul_one] at h
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h
    have hid : (cj w) ∘ (cj w) = id := funext (cj_cj hB)
    rw [hid, Matrix.map_id, Matrix.map_one _ (map_zero _) (map_one _)] at h
    exact h
  have hc : ∀ u : Fin n → w.adicCompletion E, (fun k => cj w ((M *ᵥ u) k)) = M.map (cj w) *ᵥ (fun k => cj w (u k)) := by
    intro u; funext k
    exact RingHom.map_mulVec (cj w) M u k
  have hs : ∀ u u' : Fin n → w.adicCompletion E, stdH w u u' = u ⬝ᵥ (fun k => cj w (u' k)) := fun _ _ => rfl
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hM', Matrix.vecMul_one]

theorem pullLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ g ∈ UL n w, GlobalTheory.UnitLemma.IsLat K.O K.E (pullLat w B ψ g) ∧ ∀ y, y ∈ pullLat w B ψ g ↔ ∀ z ∈ pullLat w B ψ g, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  intro E _ _ _ w hw K e hB B x n ψ hlin hherm g hg
  set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (g⁻¹ : GLw n w).val with hMdef
  have hgi : g⁻¹ ∈ UL n w := inv_mem hg
  have hMu : Formalism.UG.cT (cj w) M * 1 * M = 1 := by
    have h := hgi
    unfold UL at h
    rw [if_neg hw] at h
    exact h
  have hMg : M * g.val = 1 := by rw [hMdef]; exact Units.inv_mul g
  have hgM : g.val * M = 1 := by rw [hMdef]; exact Units.mul_inv g
  have hint : ∀ a : K.E, a ∈ (algebraMap K.O K.E).range ↔ e a ∈ w.adicCompletionIntegers E := by
    intro a; rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hB.2.1 a
  let φ : B.A →+ (Fin n → w.adicCompletion E) :=
    (Matrix.mulVecLin M).toAddMonoidHom.comp ψ.toAddMonoidHom
  have hφ : ∀ y, φ y = M *ᵥ ψ y := fun y => rfl
  have hφs : ∀ (c : K.E) y, φ (c • y) = e c • φ y := by
    intro c y; rw [hφ, hφ, hlin, Matrix.mulVec_smul]
  have hφinj : ∀ y z, φ y = φ z → y = z := by
    intro y z h
    rw [hφ, hφ] at h
    apply ψ.injective
    have := congrArg (fun u => g.val *ᵥ u) h
    simpa only [Matrix.mulVec_mulVec, hgM, Matrix.one_mulVec] using this
  let pre : (Fin n → w.adicCompletion E) → B.A := fun v => ψ.symm (g.val *ᵥ v)
  have hpre : ∀ v, φ (pre v) = v := by
    intro v; rw [hφ]; simp only [pre, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hMg, Matrix.one_mulVec]
  have hmem : ∀ y, y ∈ pullLat w B ψ g ↔ ∀ i, φ y i ∈ w.adicCompletionIntegers E := by
    intro y
    have key : y ∈ pullLat w B ψ g ↔ ∀ (c : K.O) (i : Fin n),
        ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E := Iff.rfl
    rw [key]
    constructor
    · intro h i
      have := h 1 i
      rwa [one_smul] at this
    · intro h c i
      rw [← algebraMap_smul K.E c y, ← hMdef, ← hφ, hφs, Pi.smul_apply, smul_eq_mul]
      exact mul_mem ((hint _).1 ⟨c, rfl⟩) (h i)
  let z : Fin n → B.A := fun i => pre (Pi.single i 1)
  have hz : ∀ i, z i ∈ pullLat w B ψ g := by
    intro i; rw [hmem]; intro j
    simp only [z, hpre, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hdecomp : ∀ (a : Fin n → K.E) y, (∀ i, e (a i) = φ y i) → y = ∑ i, a i • z i := by
    intro a y ha
    apply hφinj
    rw [map_sum]
    funext j
    rw [Finset.sum_apply]
    simp only [hφs, z, hpre, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (ha j).symm
  have hsd : ∀ y, (∀ i, φ y i ∈ w.adicCompletionIntegers E) ↔
      ∀ z' ∈ pullLat w B ψ g, B.herm x y z' ∈ (algebraMap K.O K.E).range := by
    intro y
    have hh : ∀ z', B.herm x y z' ∈ (algebraMap K.O K.E).range ↔ stdH w (φ y) (φ z') ∈ w.adicCompletionIntegers E := by
      intro z'
      rw [hint, ← hherm, hφ, hφ, SDual.stdH_unitary hB M hMu]
    constructor
    · intro hy z' hz'
      rw [hh]
      rw [hmem] at hz'
      unfold stdH
      exact sum_mem fun k _ => mul_mem (hy k) (SDual.cj_int hB _ (hz' k))
    · intro h i
      have := (hh _).1 (h (z i) (hz i))
      have hcalc : stdH w (φ y) (φ (z i)) = φ y i := by
        rw [show φ (z i) = Pi.single i 1 from hpre _]
        unfold stdH
        rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      rwa [hcalc] at this
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.fg_def]
    refine ⟨Set.range z, Set.finite_range z, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩; exact hz i
    · intro y hy
      rw [hmem] at hy
      have hc : ∀ i, ∃ o : K.O, e (algebraMap K.O K.E o) = φ y i := by
        intro i
        obtain ⟨o, ho⟩ := (hint (e.symm (φ y i))).2 (by simpa using hy i)
        exact ⟨o, by rw [ho, RingEquiv.apply_symm_apply]⟩
      choose o ho using hc
      rw [hdecomp (fun i => algebraMap K.O K.E (o i)) y ho]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro y _
    rw [hdecomp (fun i => e.symm (φ y i)) y (fun i => by simp)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hz i))
  · intro y
    rw [hmem]
    exact hsd y

end GlobalTheory.KapOrb.SDual
