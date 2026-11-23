import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichLApply

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unimod_int (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {x v : (VS D).V} (hx : x ∈ Λ) (hv : v ∈ Λ) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT x v := by
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' x hx)
  exact ⟨o, ho⟩

theorem smul_int_mem (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {k : D.host.E}
    (hk : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = k) {v : (VS D).V} (hv : v ∈ Λ) : k • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := hk
  rw [algebraMap_smul]
  exact Λ.smul_mem o hv

theorem eich_conds (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (D.sp.hypE a) = 0 ∧ (VS D).hT (D.sp.hypE a) ((2 : D.host.E) • y0) = 0 ∧
    (VS D).hT ((2 : D.host.E) • y0) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) + (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 ∧
    (-2 * (VS D).hT y0 y0) + star (-2 * (VS D).hT y0 y0) +
      (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 0 := by
  have hh : star ((VS D).hT y0 y0) = (VS D).hT y0 y0 := (VS D).herm.eq y0 y0
  have h22 : (VS D).hT ((2 : D.host.E) • y0) ((2 : D.host.E) • y0) = 4 * (VS D).hT y0 y0 := by
    rw [LinearMap.map_smulₛₗ₂, map_smul, map_ofNat, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨D.sp.hyp_ee a a, ?_, ?_, ?_, ?_⟩
  · rw [map_smul, hy.1 a, smul_zero]
  · rw [LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a, map_zero, smul_zero]
  · rw [h22]
    ring
  · have hs2 : star (-2 : D.host.E) = -2 := by simp
    rw [h22, star_mul', hs2, hh]
    ring

theorem eich_conds_neg (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) {y0 : (VS D).V} (hy : InW D y0) :
    (VS D).hT (D.sp.hypE a) (-((2 : D.host.E) • y0)) = 0 ∧
    (VS D).hT (-((2 : D.host.E) • y0)) (D.sp.hypE a) = 0 ∧
    (-2 * (VS D).hT y0 y0) + (-2 * (VS D).hT y0 y0) +
      (VS D).hT (-((2 : D.host.E) • y0)) (-((2 : D.host.E) • y0)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [map_neg, map_smul, hy.1 a, smul_zero, neg_zero]
  · rw [map_neg, LinearMap.neg_apply, LinearMap.map_smulₛₗ₂, ← (VS D).herm.eq (D.sp.hypE a) y0, hy.1 a,
      map_zero, smul_zero, neg_zero]
  · rw [map_neg, map_neg, LinearMap.neg_apply, neg_neg, LinearMap.map_smulₛₗ₂, map_smul, map_ofNat,
      smul_eq_mul, smul_eq_mul]
    ring

def eichE (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) :
    (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0))
    (eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0))
    (LinearMap.ext fun v => by
      obtain ⟨he, -, -, -, -⟩ := eich_conds D a hy
      obtain ⟨n2, n3, n4⟩ := eich_conds_neg D a hy
      have := eich_inv D he n2 n3 n4 v
      rw [neg_neg] at this
      exact this)
    (LinearMap.ext fun v => by
      obtain ⟨he, h2, h3, h4, -⟩ := eich_conds D a hy
      exact eich_inv D he h2 h3 h4 v)

theorem eichE_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    eichE D a y0 hy v = eichL D (D.sp.hypE a) ((2 : D.host.E) • y0) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichE_symm_apply (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    (eichE D a y0 hy).symm v = eichL D (D.sp.hypE a) (-((2 : D.host.E) • y0)) (-2 * (VS D).hT y0 y0) v := rfl

theorem eichL_lat (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {e y : (VS D).V} {c : D.host.E} (he : e ∈ Λ) (hy : y ∈ Λ)
    (hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = c) {v : (VS D).V} (hv : v ∈ Λ) :
    eichL D e y c v ∈ Λ := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply]
  exact Λ.add_mem (Λ.sub_mem (Λ.add_mem hv (smul_int_mem D (unimod_int D hU he hv) hy))
    (smul_int_mem D (unimod_int D hU hy hv) he)) (smul_int_mem D hc (smul_int_mem D (unimod_int D hU he hv) he))

theorem eichE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {y0 : (VS D).V}
    (hy : InW D y0) (hyΛ : y0 ∈ Λ) : eichE D a y0 hy ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hF.2.1
  have hea : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hFe] at h1
  obtain ⟨he, h2, h3, -, h5⟩ := eich_conds D a hy
  have hy2 : (2 : D.host.E) • y0 ∈ Λ := smul_int_mem D (k := (2 : D.host.E)) ⟨2, map_ofNat _ 2⟩ hyΛ
  have hc : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = -2 * (VS D).hT y0 y0 := by
    obtain ⟨o, ho⟩ := unimod_int D hU hyΛ hyΛ
    exact ⟨-2 * o, by rw [map_mul, ho, map_neg, map_ofNat]⟩
  have hP : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE),
      (∀ b, (VS D).hT (D.sp.hypE b) x = 0) ∧ (VS D).hT y0 x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨fun b => D.sp.hyp_ee b c, by rw [← (VS D).herm.eq (D.sp.hypE c) y0, hy.1 c, map_zero]⟩
    | zero => simp
    | add x z _ _ hx hz => exact ⟨fun b => by rw [map_add, hx.1 b, hz.1 b, add_zero], by
        rw [map_add, hx.2, hz.2, add_zero]⟩
    | smul c x _ hx => exact ⟨fun b => by rw [map_smul, hx.1 b, smul_zero], by
        rw [map_smul, hx.2, smul_zero]⟩
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range D.sp.hypE), eichE D a y0 hy x = x := by
    intro x hx
    obtain ⟨h1, h2'⟩ := hP x hx
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, h1 a, h2', smul_zero, zero_smul, add_zero, sub_zero]
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  have hy0z : (VS D).hT y0 D.sp.zm = 0 := by
    rw [← (VS D).herm.eq D.sp.zm y0, hy.2.2, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    exact eich_isom D he h2 h3 h5 u v
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => eichL_lat D hU hea hy2 hc hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨(eichE D a y0 hy).symm v, ?_, (eichE D a y0 hy).apply_symm_apply v⟩
      rw [eichE_symm_apply]
      exact eichL_lat D hU hea (Λ.neg_mem hy2) hc hv
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
      rw [← hFe]
      exact Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    have hex : (VS D).hT (D.sp.hypE a) x = 0 := by
      have h1 : x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range F0.e)) := hx
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker] at h1
      exact h1 _ (by rw [hFe]; exact Submodule.subset_span ⟨a, rfl⟩)
    show (eichE D a y0 hy) x - x ∈ Submodule.span D.host.E (Set.range F0.e)
    rw [eichE_apply, hFe]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, hex, zero_smul, add_zero, smul_zero, add_sub_cancel_left, zero_sub]
    rw [sub_sub_cancel_left]
    apply Submodule.neg_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro b
    rw [hFe]
    exact hspan _ (Submodule.subset_span ⟨b, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [eichE_apply]
    simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, LinearMap.map_smulₛₗ₂, hzm a, hy0z, smul_zero, zero_smul, add_zero, sub_zero]

theorem eichE_pW (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (v : (VS D).V) :
    pW D (eichE D a y0 hy v) = pW D v + (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0) := by
  rw [eichE_apply]
  have hf : ∀ b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hy2 : ∀ b, (VS D).hT (D.sp.hypF b) y0 = 0 := hy.2.1
  simp only [pW, eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_sub, map_smul, hf, hy.1, hy2, hy.2.2,
    D.sp.hyp_ee, (D.sp.hyp_orthz a).1, smul_eq_mul, mul_zero, add_zero, sub_zero, zero_add, mul_ite,
    mul_one, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, add_smul, sub_smul, zero_div]
  module

theorem eichE_hTe (D : Formalism.BasicNotions.D7) (a : Fin D.R.rS) (y0 : (VS D).V) (hy : InW D y0) (a' : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE a') (eichE D a y0 hy v) = (VS D).hT (D.sp.hypE a') v := by
  rw [eichE_apply]
  simp [eichL, D.sp.hyp_ee, hy.1 a']

theorem eich_all (hN : UnipotentIntegralIsGroup) (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (y0 : Fin D.R.rS → (VS D).V)
    (hy : ∀ a, InW D (y0 a)) (hyΛ : ∀ a, y0 a ∈ Λ) :
    ∃ n ∈ N0 F0 Λ, ∀ v, pW D (n v) = pW D v + ∑ a, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) := by
  have key : ∀ s : Finset (Fin D.R.rS), ∃ n ∈ N0 F0 Λ, ∀ v,
      pW D (n v) = pW D v + ∑ a ∈ s, (VS D).hT (D.sp.hypE a) v • ((2 : D.host.E) • y0 a) ∧
      ∀ a', (VS D).hT (D.sp.hypE a') (n v) = (VS D).hT (D.sp.hypE a') v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨LinearEquiv.refl _ _, (hN D F0 Λ).1, fun v => ⟨by simp, fun a' => rfl⟩⟩
    | @insert a s ha ih =>
      obtain ⟨n, hn, hv⟩ := ih
      refine ⟨n.trans (eichE D a (y0 a) (hy a)),
        (hN D F0 Λ).2.2 n hn _ (eichE_mem D F0 Λ hF a (hy a) (hyΛ a)), fun v => ⟨?_, fun a' => ?_⟩⟩
      · rw [LinearEquiv.trans_apply, eichE_pW, (hv v).1, (hv v).2 a, Finset.sum_insert ha]
        abel
      · rw [LinearEquiv.trans_apply, eichE_hTe, (hv v).2 a']
  obtain ⟨n, hn, hv⟩ := key Finset.univ
  exact ⟨n, hn, fun v => (hv v).1⟩

end PI.UnitaryGroupMassFormula.CntFormula
