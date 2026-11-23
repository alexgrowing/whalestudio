import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.UnGrpHaarProbExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

noncomputable section

open Finset Matrix MeasureTheory Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def kdC (ε : Fin n → Bool) : Bool → ℕ
  | true => pOf ε
  | false => qOf ε

lemma kdC_card (ε : Fin n → Bool) (s : Bool) : (univ.filter fun a => ε a = s).card = kdC ε s := by
  cases s <;> rfl

def kdE (ε : Fin n → Bool) (s : Bool) : Fin (kdC ε s) ↪o Fin n :=
  (univ.filter fun a => ε a = s).orderEmbOfFin (kdC_card ε s)

lemma ε_kdE (ε : Fin n → Bool) (s : Bool) (i : Fin (kdC ε s)) : ε (kdE ε s i) = s := by
  have h := (univ.filter fun a => ε a = s).orderEmbOfFin_mem (kdC_card ε s) i
  exact (Finset.mem_filter.1 h).2

lemma kdE_surj (ε : Fin n → Bool) (a : Fin n) : ∃ i, kdE ε (ε a) i = a := by
  have ha : a ∈ (univ.filter fun b => ε b = ε a) := by simp
  have := Finset.range_orderEmbOfFin (univ.filter fun b => ε b = ε a) (kdC_card ε (ε a))
  have hr : a ∈ Set.range ((univ.filter fun b => ε b = ε a).orderEmbOfFin (kdC_card ε (ε a))) := by
    rw [this]; exact ha
  exact hr

def kdSig (ε : Fin n → Bool) : (Σ s : Bool, Fin (kdC ε s)) ≃ Fin n :=
  Equiv.ofBijective (fun x => kdE ε x.1 x.2) (by
    constructor
    · rintro ⟨s, i⟩ ⟨s', j⟩ h
      have hs : s = s' := by
        have h1 := ε_kdE ε s i
        have h2 := ε_kdE ε s' j
        simp only at h
        rw [h] at h1
        rw [← h1, h2]
      subst hs
      simp only at h
      rw [(kdE ε s).injective h]
    · intro a
      obtain ⟨i, hi⟩ := kdE_surj ε a
      exact ⟨⟨ε a, i⟩, hi⟩)

lemma kdSig_apply (ε : Fin n → Bool) (s : Bool) (i : Fin (kdC ε s)) : kdSig ε ⟨s, i⟩ = kdE ε s i := rfl

def kdD (ε : Fin n → Bool) :
    (∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (kdSig ε)).toRingEquiv.toRingHom.comp
    (Matrix.blockDiagonal'RingHom (fun s => Fin (kdC ε s)) ℂ)

lemma kdD_apply (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ)
    (x y : Σ s : Bool, Fin (kdC ε s)) :
    kdD ε v (kdSig ε x) (kdSig ε y) = blockDiagonal' v x y := by
  simp [kdD, Matrix.reindex_apply]

lemma continuous_kdD (ε : Fin n → Bool) : Continuous (kdD ε) := by
  show Continuous fun v : (∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) =>
    Matrix.reindex (kdSig ε) (kdSig ε) (blockDiagonal' v)
  exact (continuous_id.matrix_blockDiagonal').matrix_reindex _ _

lemma kdD_injective (ε : Fin n → Bool) : Function.Injective (kdD ε) := by
  intro v w h
  funext s
  ext i j
  have := congrFun (congrFun h (kdSig ε ⟨s, i⟩)) (kdSig ε ⟨s, j⟩)
  rwa [kdD_apply, kdD_apply, blockDiagonal'_apply_eq, blockDiagonal'_apply_eq] at this

lemma kd_commJ_iff (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    M * Jm ε = Jm ε * M ↔ ∀ a b, ε a ≠ ε b → M a b = 0 := by
  unfold Jm
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [mul_diagonal, diagonal_mul] at h1
    have hne : (if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1) ≠ 0 := by
      revert hab
      cases ε a <;> cases ε b <;> norm_num
    have h2 : M a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
      rw [mul_sub, h1, mul_comm, sub_self]
    exact (mul_eq_zero.1 h2).resolve_right hne
  · intro h
    ext a b
    rw [mul_diagonal, diagonal_mul]
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]

lemma kdD_commJ (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) :
    kdD ε v * Jm ε = Jm ε * kdD ε v := by
  rw [kd_commJ_iff]
  intro a b hab
  obtain ⟨⟨s, i⟩, rfl⟩ := (kdSig ε).surjective a
  obtain ⟨⟨s', j⟩, rfl⟩ := (kdSig ε).surjective b
  rw [kdD_apply]
  refine blockDiagonal'_apply_ne _ _ _ ?_
  rw [kdSig_apply, kdSig_apply, ε_kdE ε s i, ε_kdE ε s' j] at hab
  exact hab

def kdR (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (s : Bool) :
    Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ :=
  Matrix.of fun i j => X (kdE ε s i) (kdE ε s j)

lemma eq_kdD {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) :
    X = kdD ε (kdR ε X) := by
  ext a b
  obtain ⟨⟨s, i⟩, rfl⟩ := (kdSig ε).surjective a
  obtain ⟨⟨s', j⟩, rfl⟩ := (kdSig ε).surjective b
  rw [kdD_apply]
  by_cases h : s = s'
  · subst h
    rw [blockDiagonal'_apply_eq]; rfl
  · rw [blockDiagonal'_apply_ne _ _ _ h]
    exact (kd_commJ_iff ε X).1 hX _ _ (by rw [kdSig_apply, kdSig_apply, ε_kdE ε s i, ε_kdE ε s' j]; exact h)

lemma kdD_conjTranspose (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) :
    (kdD ε v)ᴴ = kdD ε (fun s => (v s)ᴴ) := by
  ext a b
  obtain ⟨⟨s, i⟩, rfl⟩ := (kdSig ε).surjective a
  obtain ⟨⟨s', j⟩, rfl⟩ := (kdSig ε).surjective b
  rw [conjTranspose_apply, kdD_apply, kdD_apply]
  by_cases h : s = s'
  · subst h
    rw [blockDiagonal'_apply_eq, blockDiagonal'_apply_eq, conjTranspose_apply]
  · rw [blockDiagonal'_apply_ne _ _ _ h, blockDiagonal'_apply_ne _ _ _ (Ne.symm h), star_zero]

lemma kdD_Kset (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ)
    (hv : ∀ s, v s * (v s)ᴴ = 1) : kdD ε v ∈ Kset ε := by
  refine ⟨?_, kdD_commJ ε v⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, kdD_conjTranspose, ← map_mul]
  have : (v * fun s => (v s)ᴴ) = 1 := funext hv
  rw [this, map_one]

lemma exp_kdD (ε : Fin n → Bool) (v : ∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) :
    NormedSpace.exp (kdD ε v) = kdD ε (fun s => NormedSpace.exp (v s)) := by
  let _ : ∀ s : Bool, NormedRing (Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedRing
  let _ : ∀ s : Bool, NormedAlgebra ℂ (Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) :=
    fun _ => Matrix.linftyOpNormedAlgebra
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hv : NormedSpace.exp v = fun s => NormedSpace.exp (v s) := by
    funext s
    exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ)
      (Pi.evalRingHom (fun s : Bool => Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ) s)
      (continuous_apply s) v
      ((NormedSpace.expSeries_radius_eq_top ℂ
        (∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ)).symm ▸ edist_lt_top _ _)
  rw [← hv]
  exact (NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (kdD ε) (continuous_kdD ε) v
    ((NormedSpace.expSeries_radius_eq_top ℂ
      (∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ)).symm ▸ edist_lt_top _ _)).symm

lemma kd_Jm_true (k : ℕ) : Jm (fun _ : Fin k => true) = 1 := by simp [Jm]

lemma kd_un_unitary {N : ℕ} (u : UNgrp N) : toM u * (toM u)ᴴ = 1 := by
  have h : (toM u)ᴴ * Jm (fun _ : Fin N => true) * toM u = Jm (fun _ : Fin N => true) := u.2
  rw [kd_Jm_true, Matrix.mul_one] at h
  exact mul_eq_one_comm.1 h

def kdMkU {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (h : A * Aᴴ = 1) : UNgrp N :=
  ⟨⟨A, Aᴴ, h, mul_eq_one_comm.1 h⟩, by
    show Aᴴ * Jm (fun _ : Fin N => true) * A = Jm (fun _ : Fin N => true)
    rw [kd_Jm_true, Matrix.mul_one]; exact mul_eq_one_comm.1 h⟩

lemma kd_toM_inj {ε : Fin n → Bool} {g h : UJ ε} (e : toM g = toM h) : g = h := Subtype.ext (Units.ext e)

lemma kd_KG_ext {ε : Fin n → Bool} {g h : KG ε} (e : toMK g = toMK h) : g = h :=
  Subtype.ext (kd_toM_inj e)

def kdMkK (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩, by
      show gᴴ * Jm ε * g = Jm ε
      have h1 : gᴴ * g = 1 := by
        rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hg.1
      rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]⟩, hg⟩

def kdPair (ε : Fin n → Bool) (A : Matrix (Fin (pOf ε)) (Fin (pOf ε)) ℂ)
    (B : Matrix (Fin (qOf ε)) (Fin (qOf ε)) ℂ) : ∀ s : Bool, Matrix (Fin (kdC ε s)) (Fin (kdC ε s)) ℂ
  | true => A
  | false => B

lemma kdPair_mul (ε : Fin n → Bool) (A A' : Matrix (Fin (pOf ε)) (Fin (pOf ε)) ℂ)
    (B B' : Matrix (Fin (qOf ε)) (Fin (qOf ε)) ℂ) :
    kdPair ε (A * A') (B * B') = kdPair ε A B * kdPair ε A' B' := by
  funext s; cases s <;> rfl

lemma kdPair_one (ε : Fin n → Bool) : kdPair ε 1 1 = 1 := by
  funext s; cases s <;> rfl

lemma kdPsi_mem (ε : Fin n → Bool) (x : UNgrp (pOf ε) × UNgrp (qOf ε)) :
    kdD ε (kdPair ε (toM x.1) (toM x.2)) ∈ Kset ε :=
  kdD_Kset ε _ (by intro s; cases s; exacts [kd_un_unitary x.2, kd_un_unitary x.1])

def kdPsi (ε : Fin n → Bool) : UNgrp (pOf ε) × UNgrp (qOf ε) →* KG ε where
  toFun x := kdMkK ε (kdPsi_mem ε x)
  map_one' := by
    apply kd_KG_ext
    show kdD ε (kdPair ε 1 1) = 1
    rw [kdPair_one, map_one]
  map_mul' x y := by
    apply kd_KG_ext
    show kdD ε (kdPair ε (toM x.1 * toM y.1) (toM x.2 * toM y.2)) =
      kdD ε (kdPair ε (toM x.1) (toM x.2)) * kdD ε (kdPair ε (toM y.1) (toM y.2))
    rw [kdPair_mul, map_mul]

lemma toMK_kdPsi (ε : Fin n → Bool) (x : UNgrp (pOf ε) × UNgrp (qOf ε)) :
    toMK (kdPsi ε x) = kdD ε (kdPair ε (toM x.1) (toM x.2)) := rfl

lemma continuous_kdPsi (ε : Fin n → Bool) : Continuous (kdPsi ε) := by
  have hP : Continuous fun x : UNgrp (pOf ε) × UNgrp (qOf ε) => kdPair ε (toM x.1) (toM x.2) := by
    refine continuous_pi fun s => ?_
    cases s
    · exact (continuous_toM _).comp continuous_snd
    · exact (continuous_toM _).comp continuous_fst
  have hM : Continuous fun x : UNgrp (pOf ε) × UNgrp (qOf ε) => kdD ε (kdPair ε (toM x.1) (toM x.2)) :=
    (continuous_kdD ε).comp hP
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact Units.continuous_iff.mpr ⟨hM, continuous_star.comp hM⟩

lemma kdPsi_injective (ε : Fin n → Bool) : Function.Injective (kdPsi ε) := by
  intro x y h
  have h1 : kdPair ε (toM x.1) (toM x.2) = kdPair ε (toM y.1) (toM y.2) :=
    kdD_injective ε (by rw [← toMK_kdPsi, ← toMK_kdPsi, h])
  exact Prod.ext (kd_toM_inj (congrFun h1 true)) (kd_toM_inj (congrFun h1 false))

lemma kdPsi_surjective (ε : Fin n → Bool) : Function.Surjective (kdPsi ε) := by
  intro k
  have hk : toMK k ∈ Kset ε := k.2
  set X := toMK k with hXdef
  have hX : X = kdD ε (kdR ε X) := eq_kdD hk.2
  have hu : X * Xᴴ = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  have hv : (kdR ε X * fun s => (kdR ε X s)ᴴ) = 1 := by
    apply kdD_injective ε
    rw [map_mul, ← kdD_conjTranspose, ← hX, hu, map_one]
  refine ⟨(kdMkU (kdR ε X true) (congrFun hv true), kdMkU (kdR ε X false) (congrFun hv false)), ?_⟩
  apply kd_KG_ext
  rw [toMK_kdPsi]
  conv_rhs => rw [← hXdef, hX]
  congr 1
  funext s; cases s <;> rfl

def kdHomeo (ε : Fin n → Bool) : (UNgrp (pOf ε) × UNgrp (qOf ε)) ≃ₜ KG ε :=
  have := unGrp_compactSpace (pOf ε)
  have := unGrp_compactSpace (qOf ε)
  (continuous_kdPsi ε).homeoOfEquivCompactToT2 (f := Equiv.ofBijective (kdPsi ε)
    ⟨kdPsi_injective ε, kdPsi_surjective ε⟩)

theorem kd_dk_eq_map (ε : Fin n → Bool) (μp : Measure (UNgrp (pOf ε))) [μp.IsHaarMeasure]
    [IsProbabilityMeasure μp] (μq : Measure (UNgrp (qOf ε))) [μq.IsHaarMeasure] [IsProbabilityMeasure μq] :
    dk ε = (μp.prod μq).map (kdPsi ε) := by
  have := unGrp_compactSpace (pOf ε)
  have := unGrp_compactSpace (qOf ε)
  have := compactSpace_KG ε
  have : Measure.IsHaarMeasure ((μp.prod μq).map (kdPsi ε)) :=
    Measure.isHaarMeasure_map _ (kdPsi ε) (continuous_kdPsi ε) (kdPsi_surjective ε)
      (by rw [Filter.cocompact_eq_bot]; exact Filter.tendsto_bot)
  have : IsProbabilityMeasure ((μp.prod μq).map (kdPsi ε)) :=
    Measure.isProbabilityMeasure_map (continuous_kdPsi ε).aemeasurable
  have h0 : muK ε Set.univ ≠ 0 := (isOpen_univ.measure_pos (muK ε) Set.univ_nonempty).ne'
  have htop : muK ε Set.univ ≠ ⊤ := measure_ne_top _ _
  have : Measure.IsHaarMeasure (dk ε) := Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
  have : IsProbabilityMeasure (dk ε) := ⟨by
    simp only [dk, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 htop⟩
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end ReciprocityTheory.ChartRestriction.DS
