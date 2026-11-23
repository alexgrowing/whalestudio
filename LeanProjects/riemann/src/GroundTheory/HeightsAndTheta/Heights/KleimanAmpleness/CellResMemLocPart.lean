import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldChartRingOverPnPtZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ConstVanishHypSegment
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver mConeMapOver chartRingOver quotPart)

namespace CechPointVanish

set_option linter.unusedSectionVars false

section Cells

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

theorem map_constD {V W : Type} [AddCommGroup V] [AddCommGroup W] (g : V →+ W) (n : ℕ)
    (f : Cell K ι n → V) (I : Cell K ι (n + 1)) :
    g (constD K ι V n f I) = constD K ι W n (fun J => g (f J)) I := by
  unfold constD
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [map_zsmul]

theorem constD_congr {V : Type} [AddCommGroup V] (G : ∀ k, Finset (ι k)) (n : ℕ) {f f' : Cell K ι n → V}
    (h : ∀ J : Cell K ι n, (∀ k, J.1 k ⊆ G k) → f J = f' J) (I : Cell K ι (n + 1)) (hI : ∀ k, I.1 k ⊆ G k) :
    constD K ι V n f I = constD K ι V n f' I := by
  unfold constD
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · exact congrArg _ (h _ fun l => (face_subset I.1 k i l).trans (hI l))
  · rfl

variable {S : Type} [CommRing S]

theorem cellMon_mono {J I : ∀ k, Finset (ι k)} (h : ∀ k, J k ⊆ I k) : cellMon S J ≤ cellMon S I := by
  apply Submonoid.closure_mono
  rintro f ⟨k, i, hi, rfl⟩
  exact ⟨k, i, h k hi, rfl⟩

theorem cellRes_mk {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : cellMon S J ≤ cellMon S I) (m : M) (t : cellMon S J) :
    cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

open Classical in

theorem cechD_apply {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : Cell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

end Cells

section Point

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω}

theorem subsingleton_of_bad {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} (hi : i ∈ I k) (hy : y ⟨k, i⟩ = 0) :
    Subsingleton (LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y)) := by
  have hX : (X ⟨k, i⟩ : MRingOver F ι) ∈ cellMon F I := Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hmem : (X ⟨k, i⟩ : MRingOver F ι) ∈ mIdealOver F y := by
    simp [mIdealOver, mConeMapOver, RingHom.mem_ker, hy]
  have hz : ∀ w : MRingOver F ι ⧸ mIdealOver F y, (X ⟨k, i⟩ : MRingOver F ι) • w = 0 := by
    intro w
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hmem
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | h m t =>
    induction b using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨_, hX⟩, ?_⟩
      simp only [Submonoid.smul_def]
      rw [hz, hz]

theorem cellRes_smul {J I : ∀ k, Finset (ι k)} (s : F)
    (x : LocalizedModule (cellMon F J) (MRingOver F ι ⧸ mIdealOver F y)) :
    cellRes F _ J I (s • x) = s • cellRes F _ J I x := by
  by_cases h : cellMon F J ≤ cellMon F I
  · induction x using LocalizedModule.induction_on with
    | h m t => rw [LocalizedModule.smul'_mk, cellRes_mk h, cellRes_mk h, LocalizedModule.smul'_mk]
  · unfold cellRes
    rw [dif_neg h]
    simp

theorem cellRes_mem_locPart {J I : ∀ k, Finset (ι k)} (h : cellMon F J ≤ cellMon F I) (β : K → ℤ)
    {x : LocalizedModule (cellMon F J) (MRingOver F ι ⧸ mIdealOver F y)}
    (hx : x ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F J) β) :
    cellRes F _ J I x ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [cellRes_mk h]
    exact Submodule.subset_span ⟨m, ⟨t.1, h t.2⟩, a, ht, hm, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul s x _ h' => rw [cellRes_smul]; exact Submodule.smul_mem _ s h'

theorem cechD_mem_locPart (β : K → ℤ) (n : ℕ) {f : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) n}
    (hf : f ∈ cechCc ι (quotPart F (mIdealOver F y)) β n) (I : Cell K ι (n + 1)) :
    cechD F ι _ n f I ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F I.1) β := by
  rw [cechD_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hc
  · have hJ : f ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ ∈ locPart ι (quotPart F (mIdealOver F y))
        (cellMon F (Function.update I.1 k ((I.1 k).erase i))) β :=
      Submodule.mem_pi.mp hf ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ (Set.mem_univ _)
    have hm := cellRes_mem_locPart (J := Function.update I.1 k ((I.1 k).erase i)) (I := I.1)
      (cellMon_mono (face_subset I.1 k i)) β hJ
    exact zsmul_mem hm _
  · exact Submodule.zero_mem _

end Point

theorem proof (h₁ : CechConstVanish.Statement) (h₂ : CechPointEval.Statement) : CechPointVanish.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y hfield β
  classical
  obtain ⟨V, φ, hφ⟩ := h₂ F K ι Ω y hfield β
  let G : ∀ k, Finset (ι k) := fun k => Finset.univ.filter fun i => y ⟨k, i⟩ ≠ 0
  have hG : ∀ I : ∀ k, Finset (ι k), (∀ k, I k ⊆ G k) ↔ ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0 := by
    intro I
    simp [G, Finset.subset_iff]
  have hbad : ∀ I : ∀ k, Finset (ι k), ¬ (∀ k, I k ⊆ G k) →
      Subsingleton (LocalizedModule (cellMon F I) (MRingOver F ι ⧸ mIdealOver F y)) := by
    intro I hI
    rw [hG] at hI
    push Not at hI
    obtain ⟨k, i, hi, hy⟩ := hI
    exact subsingleton_of_bad hi hy
  have hres : ∀ J I : ∀ k, Finset (ι k), (∀ k, J k ⊆ I k) → (∀ k, (J k).Nonempty) → (∀ k, I k ⊆ G k) →
      ∀ x, φ I (cellRes F _ J I x) = φ J x := by
    intro J I hJI hJ hI x
    have hIg := (hG I).mp hI
    have hJg := (hG J).mp fun k => (hJI k).trans (hI k)
    have hIn : ∀ k, (I k).Nonempty := fun k => (hJ k).mono (hJI k)
    induction x using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [cellRes_mk (cellMon_mono hJI), (hφ I hIn hIg).1, (hφ J hJ hJg).1]
  have hdiff : ∀ (n : ℕ) (x : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) n) (I : Cell K ι (n + 1)),
      (∀ k, I.1 k ⊆ G k) → φ I.1 (cechD F ι _ n x I) = constD K ι Ω n (fun J => φ J.1 (x J)) I := by
    intro n x I hI
    rw [cechD_apply]
    simp only [constD, map_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hc
    · rw [map_zsmul, hres _ _ (face_subset I.1 k i) hc.1 hI]
    · simp
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  rintro ⟨z, hz⟩ -
  obtain ⟨hzC, hzK⟩ := Submodule.mem_inf.mp hz
  have hzK' : cechD F ι _ 1 z = 0 := hzK
  have hzC' : ∀ J : Cell K ι 1, z J ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F J.1) β :=
    fun J => Submodule.mem_pi.mp hzC J (Set.mem_univ _)

  let zh : Cell K ι 1 → V := fun J => if hJ : ∀ k, J.1 k ⊆ G k then
    ⟨φ J.1 (z J), by
      rw [← (hφ J.1 J.2.1 ((hG _).mp hJ)).2.2]
      exact Submodule.mem_map_of_mem (hzC' J)⟩ else 0
  have hzh : ∀ J : Cell K ι 1, (∀ k, J.1 k ⊆ G k) → ((zh J : V) : Ω) = φ J.1 (z J) := by
    intro J hJ
    simp only [zh, dif_pos hJ]
  have hcoc : ∀ I : Cell K ι 2, (∀ k, I.1 k ⊆ G k) → constD K ι V 1 zh I = 0 := by
    intro I hI
    apply Subtype.ext
    have e := map_constD V.subtype.toAddMonoidHom 1 zh I
    simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] at e
    rw [e, constD_congr G 1 hzh I hI, ← hdiff 1 z I hI, hzK']
    simp
  obtain ⟨fh, hfh⟩ := h₁ K ι V G zh hcoc

  have hlift : ∀ c : Cell K ι 0, (∀ k, c.1 k ⊆ G k) →
      ∃ w ∈ locPart ι (quotPart F (mIdealOver F y)) (cellMon F c.1) β, φ c.1 w = fh c := by
    intro c hc
    have h : ((fh c : V) : Ω) ∈ (locPart ι (quotPart F (mIdealOver F y)) (cellMon F c.1) β).map (φ c.1) := by
      rw [(hφ c.1 c.2.1 ((hG _).mp hc)).2.2]
      exact (fh c).2
    exact Submodule.mem_map.mp h
  let f : CechC F ι (MRingOver F ι ⧸ mIdealOver F y) 0 := fun c =>
    if hc : ∀ k, c.1 k ⊆ G k then (hlift c hc).choose else 0
  have hfC : f ∈ cechCc ι (quotPart F (mIdealOver F y)) β 0 := by
    refine Submodule.mem_pi.mpr fun c _ => ?_
    by_cases hc : ∀ k, c.1 k ⊆ G k
    · simp only [f, dif_pos hc]
      exact (hlift c hc).choose_spec.1
    · simp only [f, dif_neg hc]
      exact Submodule.zero_mem _
  have hfφ : ∀ c : Cell K ι 0, (∀ k, c.1 k ⊆ G k) → φ c.1 (f c) = ((fh c : V) : Ω) := by
    intro c hc
    simp only [f, dif_pos hc]
    exact (hlift c hc).choose_spec.2
  have hfz : cechD F ι _ 0 f = z := by
    funext J
    by_cases hJ : ∀ k, J.1 k ⊆ G k
    · refine (hφ J.1 J.2.1 ((hG _).mp hJ)).2.1 (cechD_mem_locPart β 0 hfC J) (hzC' J) ?_
      have e := map_constD V.subtype.toAddMonoidHom 0 fh J
      simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype] at e
      rw [hdiff 0 f J hJ, constD_congr G 0 hfφ J hJ, ← e, hfh J hJ, hzh J hJ]
    · have := hbad J.1 hJ
      exact Subsingleton.elim _ _
  show z ∈ (cechCc ι (quotPart F (mIdealOver F y)) β 0).map ((cechD F ι _ 0).restrictScalars F)
  exact ⟨f, hfC, hfz⟩

end CechPointVanish

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
