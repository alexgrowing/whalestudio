import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem evT_eq_blockPoint_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (hq : q ≠ 0) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    ∃ g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ, g ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g ∧
      ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
  classical
  set φ : Fin d.D × Fin (d.N + 1) → TVar d.D d.N := fun p => (p.1.succ, p.2) with hφ
  have hφi : Function.Injective φ := fun p p' h => by
    simp only [hφ, Prod.mk.injEq] at h
    exact Prod.ext (Fin.succ_injective _ h.1) h.2
  have hvars : (q.vars : Set (TVar d.D d.N)) ⊆ Set.range φ := by
    intro v hv
    rw [Finset.mem_coe, MvPolynomial.mem_vars] at hv
    obtain ⟨s, hs, hsv⟩ := hv
    have h0 : v.1 ≠ 0 := by
      intro h0
      have h1 := hqm s hs 0
      rw [hm] at h1
      have hz := (Finset.sum_eq_zero_iff.1 h1) v.2 (Finset.mem_univ _)
      apply (Finsupp.mem_support_iff.1 hsv)
      have e : v = (0, v.2) := Prod.ext h0 rfl
      rw [e]; exact hz
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.2 h0
    exact ⟨(i, v.2), Prod.ext hi rfl⟩
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q φ hφi hvars
  set g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ := MvPolynomial.map sg q' with hgdef
  have heval : ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
    intro z
    rw [← hq', evT, MvPolynomial.eval₂_rename, hgdef, MvPolynomial.eval_map]
    congr 1
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hq (by rw [← hq', map_zero])
  have hg0 : g ≠ 0 := by
    intro h0
    apply hq'0
    apply MvPolynomial.map_injective sg sg.injective
    rw [← hgdef, h0, map_zero]
  have hgm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun i : Fin d.D => m i.succ) g := by
    intro s hs b
    have hs' : s ∈ q'.support := MvPolynomial.support_map_subset _ _ hs
    have hsq : Finsupp.mapDomain φ s ∈ q.support := by
      rw [← hq', MvPolynomial.support_rename_of_injective hφi]
      exact Finset.mem_image_of_mem _ hs'
    show _ = m b.succ
    rw [← hqm _ hsq b.succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (Finsupp.mapDomain_apply hφi s (b, j)).symm
  exact ⟨g, hg0, hgm, heval⟩

theorem logInt_evT_of_mh (sg : K →+* ℂ) (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) q‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  by_cases hq : q = 0
  · subst hq
    simp [evT]
  · obtain ⟨g, hg, hgm, heq⟩ := d.evT_eq_blockPoint_of_mh sg q hq m hm hqm
    simp_rw [heq]
    exact ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable d.D (d.N + 1) _ g hg hgm

theorem integrable_log_norm_sub_log_norm (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  obtain ⟨-, -, m, hm0, hma, hmb⟩ := hab
  exact (d.logInt_evT_of_mh sg a m hm0 hma).sub (d.logInt_evT_of_mh sg b m hm0 hmb)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
