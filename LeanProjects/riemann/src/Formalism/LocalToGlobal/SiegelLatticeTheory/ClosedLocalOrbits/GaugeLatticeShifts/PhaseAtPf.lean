import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviColsPf

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section NCongS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def NCong (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, (X.B.I.fmat x - 1) *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1})) ∧
    (X.B.I.fmat x - 1) *ᵥ X.z0 ∈ Mo X.B.I X.B.g (Set.range X.e0)

theorem ncong_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hnx : NCong X x) (hny : NCong X y) :
    NCong X (x * y) := by
  obtain ⟨hx1, hx2⟩ := hnx
  obtain ⟨hy1, hy2⟩ := hny
  refine ⟨fun a => ?_, ?_⟩
  · rw [mul_id]
    refine Submodule.add_mem _ ?_ (hx1 a)
    apply SE (hx := hx) (hc := hx1)
    exact hy1 a
  · rw [mul_id]
    refine Submodule.add_mem _ ?_ hx2
    apply SR (hx := hx) (hc := hx1)
    exact hy2

theorem Z_pair_Mo {w : VA X.B.I} (hw : w ∈ X.B.I.Lf) {S : Set (VA X.B.I)}
    (hS : ∀ s ∈ S, ZMod' X.B.I X.B.g (hA X.B.I w s)) :
    ∀ v ∈ Mo X.B.I X.B.g S, ZMod' X.B.I X.B.g (hA X.B.I w v) := by
  have hmL : mL X.B.I X.B.g ≤ Qs X.B.I X.B.g w := by
    apply mL_Qs
    exact hw
  have hle : Mo X.B.I X.B.g S ≤ Qs X.B.I X.B.g w :=
    sup_le (Submodule.span_le.mpr (fun s hs => hS s hs)) hmL
  exact fun v hv => hle hv

end NCongS

section K2iff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem res_ew_one (v : TR.Pl) : TR.res v ⟨X.ew, X.ew_int⟩ = 1 := by
  have h := TR.res_ew v 1
  rw [map_one] at h
  rw [← h]
  congr 1
  exact Subtype.ext (by simp)

theorem res_of_Z_delta (v : TR.Pl) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hc : c ∈ IntAf X.B.I.F X.B.I.E) (b : Prop)
    [Decidable b] (hZ : ZMod' X.B.I X.B.g (c - if b then X.ew else 0)) :
    TR.res v ⟨c, hc⟩ = if b then 1 else 0 := by
  set y : ↥(IntAf X.B.I.F X.B.I.E) := if b then ⟨X.ew, X.ew_int⟩ else 0 with hy
  have hyc : ((y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) = if b then X.ew else 0 := by
    rw [hy]
    split_ifs <;> rfl

  have hker : ∀ w, TR.res w (⟨c, hc⟩ - y) = 0 := by
    rw [TR.res_ker]
    obtain ⟨t, ht, hct⟩ := hZ
    refine ⟨X.ew * t, (IntAf X.B.I.F X.B.I.E).mul_mem X.ew_int ht, ?_⟩
    rw [AddSubgroupClass.coe_sub, hyc]
    show X.ew * (c - (if b then X.ew else 0)) = _
    rw [hct]
    ring
  have h := hker v
  rw [map_sub, sub_eq_zero] at h
  rw [h, hy]
  split_ifs
  · exact res_ew_one TR v
  · exact map_zero _

theorem bwc_ew (x : X.B.I.Gf) (j i : Fin D.R.k) :
    hA X.B.I (X.bwd j) (X.B.I.fmat x *ᵥ X.bw i) = X.ew * hA X.B.I (X.bwd j) (X.B.I.fmat x *ᵥ X.bw i) := by
  conv_lhs => rw [X.bwd_w j]
  rw [hA_smul_left, sigA_sigA]

private theorem leviM_apply_of_le_of_mem_K2 {x : X.B.I.Gf} (hk : x ∈ X.K2) (v : TR.Pl) :
    ∀ i j : Fin D.R.k, j ≤ i → leviM TR x v i j = if i = j then 1 else 0 := by
  obtain ⟨_, _, _, hc3⟩ := hk
  obtain ⟨_, _, hbe, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences (X := X)
  intro i j hji
  have hZ : ZMod' X.B.I X.B.g
      (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) - if i = j then X.ew else 0) := by
    have e : X.B.I.fmat x *ᵥ X.bw j = X.bw j + (X.B.I.fmat x - 1) *ᵥ X.bw j := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e, hA_add_right]
    have h1 := X.bw_dual i j
    have hsub : Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1} ⊆ Set.range X.e0 ∪ X.bw '' {l | l.1 < i.1} :=
      Set.union_subset_union_right _ (Set.image_mono
        (fun l (hl : l.1 < j.1) => lt_of_lt_of_le hl (Fin.le_iff_val_le_val.mp hji)))
    have hmono : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < j.1}) ≤
        Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < i.1}) := by
      apply Mo_mono
      exact hsub
    have hle : Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {l | l.1 < i.1}) ≤ Qs X.B.I X.B.g (X.bwd i) := by
      apply Mb_Q <;> first | exact fun l => (X.vectorsInLattice.2.2 l).2 | exact hbe | exact hbb
    have h2 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat x - 1) *ᵥ X.bw j)) :=
      hle (hmono (hc3 j))
    have h3 := Z_add X.B.I X.B.g h1 h2
    convert h3 using 1
    ring
  obtain ⟨t, ht, hct⟩ := hZ
  have hint : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E := by
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) =
        (if i = j then X.ew else 0) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
      rw [← hct]
      ring
    rw [e]
    refine add_mem ?_ (mul_mem (natCast_mem _ _) ht)
    split_ifs
    · exact X.ew_int
    · exact zero_mem _
  show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j)) = _
  unfold resT
  rw [dif_pos hint]
  exact res_of_Z_delta TR v hint (i = j) ⟨t, ht, hct⟩

private theorem coe_levi_eq_leviM_of_mem_K2 {x : X.B.I.Gf} (hk : x ∈ X.K2) (v : TR.Pl) :
    ((levi TR x v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) =
      leviM TR x v := by
  have hent := leviM_apply_of_le_of_mem_K2 TR hk v
  have hup : (leviM TR x v).BlockTriangular id := fun i j hij => by
    rw [hent i j hij.le, if_neg (ne_of_gt (show j < i from hij))]
  have hdet : (leviM TR x v).det = 1 := by
    rw [Matrix.det_of_upperTriangular hup]
    exact Finset.prod_eq_one (fun i _ => by rw [hent i i le_rfl, if_pos rfl])
  have hunit : IsUnit (leviM TR x v).det := by
    rw [hdet]
    exact isUnit_one
  simp only [levi, dif_pos hunit]
  rfl

theorem unitriangular_reduction_of_mem_level {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) (v : TR.Pl) :
    Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v) := by
  have hent := leviM_apply_of_le_of_mem_K2 TR hk v
  have hlevi := coe_levi_eq_leviM_of_mem_K2 TR hk v
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [hlevi, hent i i le_rfl, if_pos rfl]
  · rw [hlevi, hent i j hji.le, if_neg (ne_of_gt hji)]

theorem mem_level_of_unitriangular {x : X.B.I.Gf} (hx : Good X x) (hn : NCong X x)
    (hu : ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR x v)) : x ∈ X.K2 := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hx.1.1, hn.1, hn.2, fun i => ?_⟩
  set w := X.B.I.fmat x *ᵥ X.bw i with hwdef
  have hwL : w ∈ X.B.I.Lf := K_mv X.B.I hx.1.1 (hB i)
  have hwM := hx.1.2.2 i
  have hd := dual_coords X hwL
  have hZe : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) w) := fun a =>
    Z_pair_Mo X (hE0 a) (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · exact (X.gramIntegral a b).1
      · exact ((X.weightVectorsIntegral l).2.2 a).1) _ hwM
  have hZz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 w) :=
    Z_pair_Mo X hZ0 (by
      rintro s (⟨b, rfl⟩ | ⟨l, rfl⟩)
      · rw [hA_symm]; exact Z_sig X.B.I X.B.g ((X.formsAtZero).2 b).1
      · exact (X.weightVectorsIntegral l).1) _ hwM
  have hbw0 : ∀ j, hA X.B.I (X.bw j) w = 0 := fun j => by
    rw [hwdef, X.bw_w j, X.bw_w i, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
    have := X.ew_orth
    linear_combination (hA X.B.I (X.bw j) (X.B.I.fmat x *ᵥ X.bw i)) * this

  have hcoef : ∀ j : Fin D.R.k, i.1 ≤ j.1 →
      ZMod' X.B.I X.B.g (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) := by
    intro j hij
    have hI := hA_int X.B.I (hBd j) hwL
    have hIt : ((if j = i then 1 else 0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have hres : ∀ v, TR.res v ⟨_, sub_mem hI hIt⟩ = 0 := by
      intro v
      have hu' := hu v
      have hent : leviM TR x v j i = if j = i then 1 else 0 := by
        rw [← levi_coe TR hx]
        by_cases h : j = i
        · subst h; rw [if_pos rfl]; exact hu'.1 j
        · rw [if_neg h]; exact hu'.2 j i (lt_of_le_of_ne (Fin.le_def.2 hij) (fun e => h e.symm))
      have e : (⟨_, sub_mem hI hIt⟩ : IntAf X.B.I.F X.B.I.E) = ⟨_, hI⟩ - ⟨_, hIt⟩ := by
        apply Subtype.ext; simp
      rw [e, map_sub]
      have h1 : TR.res v ⟨_, hI⟩ = leviM TR x v j i := by
        show _ = resT TR v (hA X.B.I (X.bwd j) (X.B.I.fmat x *ᵥ X.bw i))
        rw [resT_of_mem TR v hI]
      rw [h1, hent]
      by_cases h : j = i
      · subst h
        have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 1 := by apply Subtype.ext; simp
        rw [if_pos rfl, this, map_one, sub_self]
      · have : (⟨_, hIt⟩ : IntAf X.B.I.F X.B.I.E) = 0 := by apply Subtype.ext; simp [h]
        rw [if_neg h, this, map_zero, sub_self]
    have hZ := (TR.res_ker ⟨_, sub_mem hI hIt⟩).1 hres
    have e : X.ew * (hA X.B.I (X.bwd j) w - if j = i then 1 else 0) =
        hA X.B.I (X.bwd j) w - if j = i then X.ew else 0 := by
      rw [mul_sub, ← bwc_ew x j i]
      split_ifs <;> ring
    simpa [e] using hZ

  have e1 : (X.B.I.fmat x - 1) *ᵥ X.bw i = (w - repr0 X w) +
      ((∑ a, hA X.B.I (X.f0 a) w • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) w • X.f0 a) - hA X.B.I X.z0 w • X.z0 +
        (∑ j, (hA X.B.I (X.bwd j) w - if j = i then X.ew else 0) • X.bw j) +
        (∑ j, hA X.B.I (X.bw j) w • X.bwd j)) := by
    have hbi : (∑ j, (if j = i then X.ew else 0) • X.bw j) = X.bw i := by
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact (X.bw_w i).symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hwdef]
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib, hbi]
    abel
  rw [e1]
  have spn : ∀ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s : VA X.B.I), c ∈ IntAf X.B.I.F X.B.I.E →
      s ∈ Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1} →
      c • s ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) := fun c s hc hs => by
    have : c • s = (⟨c, hc⟩ : IntAf X.B.I.F X.B.I.E) • s := rfl
    rw [this]; exact Submodule.smul_mem _ _ (sub_Mo X.B.I hs)
  refine add_mem (mL_Mo X.B.I hd) (add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · exact sum_mem fun a _ => spn _ _ (hA_int X.B.I (hF0 a) hwL) (Or.inl ⟨a, rfl⟩)
  · exact sum_mem fun a _ => mL_Mo X.B.I (Z_smul_mL X (hZe a) (hF0 a))
  · exact mL_Mo X.B.I (Z_smul_mL X hZz hZ0)
  · refine sum_mem fun j _ => ?_
    by_cases hj : j.1 < i.1
    · have hne : j ≠ i := fun h => by subst h; exact lt_irrefl _ hj
      rw [if_neg hne, sub_zero]
      exact spn _ _ (hA_int X.B.I (hBd j) hwL) (Or.inr ⟨j, hj, rfl⟩)
    · exact mL_Mo X.B.I (Z_smul_mL X (hcoef j (not_lt.1 hj)) (hB j))
  · refine sum_mem fun j _ => ?_
    rw [hbw0, zero_smul]; exact zero_mem _

end K2iff

section ChiL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem chiL_eq_psiG {x : X.B.I.Gf} (hx : Good X x) (hk : x ∈ X.K2) : chiL X x = psiG TR (levi TR x) := by
  have hK : x ∈ X.B.I.Kset := hk.1
  have hint : ∀ i j : Fin D.R.k, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw j) ∈ IntAf X.B.I.F X.B.I.E :=
    fun i j => hA_int X.B.I (X.vectorsInLattice.2.2 i).2 (K_mv X.B.I hK (X.vectorsInLattice.2.2 j).1)
  set C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := ∑ i : Fin D.R.k,
    if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0 with hC
  have hCint : C ∈ IntAf X.B.I.F X.B.I.E := by
    refine sum_mem (fun i _ => ?_)
    split_ifs
    · exact hint _ _
    · exact zero_mem _
  have hCew : C = X.ew * C := by
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with h
    · exact bwc_ew x i ⟨i.1 + 1, h⟩
    · simp

  have hsum : ∀ v, TR.res v ⟨C, hCint⟩ = ∑ i : Fin D.R.k,
      (if h : i.1 + 1 < D.R.k then TR.res v ⟨_, hint i ⟨i.1 + 1, h⟩⟩ else 0) := by
    intro v
    have e : (⟨C, hCint⟩ : ↥(IntAf X.B.I.F X.B.I.E)) = ∑ i : Fin D.R.k,
        (if h : i.1 + 1 < D.R.k then (⟨_, hint i ⟨i.1 + 1, h⟩⟩ : ↥(IntAf X.B.I.F X.B.I.E)) else 0) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      show C = _
      rw [hC]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      split_ifs <;> rfl
    rw [e, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  have hinner : ∀ (v : TR.Pl) (M : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) (i : Fin D.R.k),
      (∑ j : Fin D.R.k, if (j : ℕ) = (i : ℕ) + 1 then M i j else 0) =
        if h : i.1 + 1 < D.R.k then M i ⟨i.1 + 1, h⟩ else 0 := by
    intro v M i
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
      · simp
      · intro j _ hj
        rw [if_neg]
        intro hj'
        exact hj (Fin.ext hj')
      · simp
    · refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg]
      intro hj'
      have := j.2
      omega
  have hfac : ∀ v, Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (levi TR x v) =
      TR.psi0 v (TR.res v ⟨C, hCint⟩) := by
    intro v
    unfold Formalism.L2.SG.GGMirabolic.psiNat
    rw [if_pos (unitriangular_reduction_of_mem_level TR hx hk v)]
    unfold Formalism.L2.SG.GGMirabolic.psiU
    rw [coe_levi_eq_leviM_of_mem_K2 TR hk v, hsum v]
    congr 1
    unfold Formalism.L2.SG.GGMirabolic.superdiag
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hinner v]
    split_ifs with h
    · show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩)) = _
      exact resT_of_mem TR v (hint i ⟨i.1 + 1, h⟩)
    · rfl
  unfold psiG
  simp only [hfac]
  rw [TR.psi_eq ⟨C, hCint⟩ hCew]
  rfl

end ChiL

section PhaseAtPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0 F0') in

def AdmN : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    NCong X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt)

theorem ncong_colDiff (w : D.what₂.Word) (h h' : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w)
    (hk : ((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) :
    NCong X (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) := by
  have s := colStab X w h h' hk
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact mL_Mo X.B.I (s.1 a)
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact mL_Mo X.B.I s.2

private theorem ite_mem_K2_chiL_eq_psiG_levi {k : X.B.I.Gf} (gk : Good X k) (nk : NCong X k) :
    (if k ∈ X.K2 then chiL X k else 0) = psiG TR (levi TR k) := by
  by_cases hk2 : k ∈ X.K2
  · rw [if_pos hk2]
    exact chiL_eq_psiG TR gk hk2
  · rw [if_neg hk2]
    have hn : ¬ ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi TR k v) := fun hu => hk2 (mem_level_of_unitriangular TR gk nk hu)
    push_neg at hn
    obtain ⟨v, hv⟩ := hn
    unfold psiG
    refine (Finset.prod_eq_zero (Finset.mem_univ v) ?_).symm
    unfold Formalism.L2.SG.GGMirabolic.psiNat
    rw [if_neg hv]

theorem phaseAt_of (hL : ColLatK cs) (hL' : ColLatK cs') (hA : AdmPar F0 F0' cs cs') (hN : AdmN F0 F0' cs cs') :
    PhaseAt TR F0 F0' cs cs' := by
  unfold PhaseAt
  intro t ρ ρ' h1 h2
  have hK : Good X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt) := hA t
  have hNt : NCong X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt) :=
    hN t
  unfold kOf at hK hNt ⊢
  have lb : cs.lamOf (cs.base t.lam) = cs.lamOf ρ := by
    rw [h1]
    exact cs.base_lam _ (h1 ▸ cs.lam_mem ρ)
  have lb' : cs'.lamOf (cs'.base t.lam') = cs'.lamOf ρ' := by
    rw [h2]
    exact cs'.base_lam _ (h2 ▸ cs'.lam_mem ρ')
  have gA := colGood X u _ _ (hL _ _ lb) (hL _ _ lb.symm)
  have gB := colGood X u' _ _ (hL' _ _ lb') (hL' _ _ lb'.symm)
  have gAi : Good X (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) := by
    have g := good_inv _ gA
    rwa [_root_.mul_inv_rev, inv_inv] at g
  have nAi := ncong_colDiff u (cs.h ρ) (cs.h (cs.base t.lam)) (hL _ _ lb.symm)
  have nB := ncong_colDiff u' (cs'.h (cs'.base t.lam')) (cs'.h ρ') (hL' _ _ lb')
  have e : ((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * ((cs'.h ρ' : X.B.I.Gf) * X.xu u') =
      (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) *
        (((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 *
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    group
  have gk := good_mul _ (good_mul _ gAi hK) gB
  have nk := ncong_mul X (good_mul _ gAi hK).1.1 (ncong_mul X gAi.1.1 nAi hNt) nB
  rw [e]
  exact ite_mem_K2_chiL_eq_psiG_levi TR gk nk

end PhaseAtPf

end Formalism.L2.SG.NormCut
