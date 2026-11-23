import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty

noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants
  Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.Pf.AmpWinLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

def eT (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : Formalism.REAL.UJ (X.B.I.ε v) → Mt D.R.k D.R.rS :=
  fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ)

def muNl (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  (muNB D θ).comap (eT C τ v)

def muHl (u : D.what₂.Word) (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) :=
  (C.muW u τ).comap (eT C τ v)

def Mb (u : D.what₂.Word) (τ : D.what₂.Tau) : Measure (Mt D.R.k D.R.rS) :=
  ((muNB D θ).prod (C.muW u τ)).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS))

theorem eT_emb (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) : MeasurableEmbedding (eT C τ v) :=
  (Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε v) (C.isT τ).2.1).measurableEmbedding

theorem eT_mul (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) (a b : Formalism.REAL.UJ (X.B.I.ε v)) :
    eT C τ v (a * b) = Matrix.of.symm (Matrix.of (eT C τ v a) * Matrix.of (eT C τ v b)) := by
  unfold eT Formalism.L2.SG.RealObj.trG
  simp only [Equiv.apply_symm_apply]
  congr 1
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  have key : ∀ A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ,
      C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) = C.Qi τ * (A * B) * C.Q τ := by
    intro A B
    calc C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) = C.Qi τ * A * (C.Q τ * C.Qi τ) * B * C.Q τ := by
          simp only [Matrix.mul_assoc]
      _ = C.Qi τ * (A * B) * C.Q τ := by
          rw [hQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [key]
  congr 2

theorem eT_lmul (τ : D.what₂.Tau) (v : InfinitePlace X.B.I.F) (s : Formalism.REAL.UJ (X.B.I.ε v)) :
    eT C τ v ∘ (fun x => s * x) = lmulM (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s) ∘ eT C τ v := by
  funext x
  simp only [Function.comp]
  rw [eT_mul]
  first
  | rfl
  | (unfold lmulM eT; simp only [Equiv.apply_symm_apply])
  | (unfold lmulM; exact (rfl : (0 : ℕ) = 0))

end Defs

section Place

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau)

theorem uh_sub_range {x : Mt D.R.k D.R.rS} (hx : Matrix.of x ∈ UH (Hpk D.R.k D.R.rS)) :
    x ∈ Set.range (eT C τ (vOf X τ)) := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  set ε := X.B.I.ε (vOf X τ)
  set M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ := Matrix.of x with hMdef
  have hM : Mᴴ * Hpk D.R.k D.R.rS * M = Hpk D.R.k D.R.rS := hx
  set g := C.Q τ * M * C.Qi τ with hgdef
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hg : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := by
    calc gᴴ * Formalism.REAL.Jm ε * g =
          (C.Qi τ)ᴴ * (Mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm ε * C.Q τ) * M) * C.Qi τ := by
          simp only [hgdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm ε * (C.Q τ * C.Qi τ) := by
          rw [h3, hM, ← h3]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hg' : gᴴ * (Formalism.REAL.Jm ε * g) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact hg
  have hinv : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hg', hJJ]
  let U : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ :=
    ⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_eq_one_comm.1 hinv, hinv⟩
  refine ⟨⟨U, hg⟩, ?_⟩
  have hback : C.Qi τ * g * C.Q τ = M := by
    simp only [hgdef, ← Matrix.mul_assoc]
    rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  unfold eT Formalism.L2.SG.RealObj.trG
  show Matrix.of.symm (C.Qi τ * g * C.Q τ) = x
  rw [hback]
  rfl

theorem muNB_haar (hθ : 0 < θ) : Formalism.MainNotions.S.IsHaarOn (Nset D.R.k D.R.rS) (muNB D θ) :=
  Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ)

theorem muNB_haarB (hθ : 0 < θ) : Formalism.FourierDecayAlt.B.IsHaarOn (Nset D.R.k D.R.rS) (muNB D θ) :=
  Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ))

theorem map_muNl (hθ : 0 < θ) : (muNl C τ (vOf X τ)).map (eT C τ (vOf X τ)) = muNB D θ := by
  unfold muNl
  rw [(eT_emb C τ (vOf X τ)).map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have h3 := (muNB_haar (D := D) hθ).2.2.1
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h3
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hN
  obtain ⟨hU, -⟩ := hN
  exact hx (uh_sub_range C τ hU)

theorem map_muHl : (muHl C u τ (vOf X τ)).map (eT C τ (vOf X τ)) = C.muW u τ := by
  unfold muHl
  rw [(eT_emb C τ (vOf X τ)).map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have h3 := (C.muW_haar u τ).2.2.1
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h3
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hW
  obtain ⟨hU, -⟩ := hW
  exact hx (uh_sub_range C τ hU)

theorem sf_muNl (hθ : 0 < θ) : SigmaFinite (muNl C τ (vOf X τ)) := by
  refine SigmaFinite.of_map _ (eT_emb C τ (vOf X τ)).measurable.aemeasurable ?_
  rw [map_muNl C τ hθ]
  exact (muNB_haar (D := D) hθ).1

theorem sf_muHl : SigmaFinite (muHl C u τ (vOf X τ)) := by
  haveI : IsFiniteMeasure (C.muW u τ) := ⟨by rw [C.muW_one u τ]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (muHl C u τ (vOf X τ)) := ⟨by
    unfold muHl
    rw [(eT_emb C τ (vOf X τ)).comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top _ _)⟩
  infer_instance

theorem nDict (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (eT C τ (vOf X τ) γ) ∈ Nset D.R.k D.R.rS ↔ γ ∈ Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ) := by
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (frS_ne D)
  have hzB := (Formalism.L2.SG.Pf.zTr C u τ).1
  constructor
  · intro hm
    have := Formalism.L2.SG.Pf.EquivPf.inN_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) hzB hm
    show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat γ)
    have e : C.Q τ * Matrix.of (eT C τ (vOf X τ) γ) * C.Qi τ = uMat γ := by
      show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [← e]; exact this
  · intro hN
    exact Formalism.L2.SG.Pf.EquivPf.nset_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) γ.2 hN

theorem hDict (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (eT C τ (vOf X τ) γ) ∈ UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) ↔
      γ ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u (vOf X τ) := by
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (frS_ne D)
  have hd : ∀ a : Fin D.R.rS, (star (frS D ^ (D.R.rS - (a : ℕ))))⁻¹ ≠ 0 := fun a => by
    rw [Ne, inv_eq_zero, star_eq_zero]; exact hc a
  rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]
  have e : C.Q τ * Matrix.of (eT C τ (vOf X τ) γ) * C.Qi τ = uMat γ := by
    show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  constructor
  · intro hh
    have := Formalism.L2.SG.Pf.EquivPf.fix_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ hc hd
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) hh
    rw [e] at this
    exact this
  · rintro ⟨hhe, hhf, hhz⟩
    exact Formalism.L2.SG.Pf.EquivPf.uw_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) γ.2 hhe hhf hhz

theorem invOn_muNl : QPK.InvOn (muNl C τ (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) := by
  have he := eT_emb C τ (vOf X τ)
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  obtain ⟨hsf, hne, hcon, hinv⟩ := muNB_haar (D := D) hθ
  have hmap := map_muNl C τ hθ
  refine ⟨sf_muNl C τ hθ, fun h0 => hne (by rw [← hmap, h0, Measure.map_zero]), ?_, ?_⟩
  · rw [muNl, he.comap_apply]
    refine measure_mono_null ?_ hcon
    rintro _ ⟨γ, hγ, rfl⟩
    exact fun hm => hγ ((nDict C u τ γ).1 hm)
  · intro s hs
    rw [← he.comap_map ((muNl C τ (vOf X τ)).map (fun x => s * x)),
      Measure.map_map he.measurable (measurable_const_mul s), eT_lmul,
      ← Measure.map_map (Formalism.L2.SG.Pf.WFL.measurable_lmulM _) he.measurable, hmap]
    have hs' : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s ∈ Nset D.R.k D.R.rS := (nDict C u τ s).2 hs
    rw [hinv _ hs']
    rfl

theorem invOn_muHl : QPK.InvOn (muHl C u τ (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hloc X u (vOf X τ)) := by
  have he := eT_emb C τ (vOf X τ)
  obtain ⟨hsf, hne, hcon, hinv⟩ := C.muW_haar u τ
  have hmap := map_muHl C u τ
  refine ⟨sf_muHl C u τ, fun h0 => hne (by rw [← hmap, h0, Measure.map_zero]), ?_, ?_⟩
  · rw [muHl, he.comap_apply]
    refine measure_mono_null ?_ hcon
    rintro _ ⟨γ, hγ, rfl⟩
    exact fun hm => hγ ((hDict C u τ γ).1 hm)
  · intro s hs
    rw [← he.comap_map ((muHl C u τ (vOf X τ)).map (fun x => s * x)),
      Measure.map_map he.measurable (measurable_const_mul s), eT_lmul,
      ← Measure.map_map (Formalism.L2.SG.Pf.WFL.measurable_lmulM _) he.measurable, hmap]
    have hs' : Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) s ∈ UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) :=
      (hDict C u τ s).2 hs
    rw [hinv _ hs']
    rfl

theorem map_mulMap :
    (QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))).map (eT C τ (vOf X τ)) = Mb C u τ := by
  have he := eT_emb C τ (vOf X τ)
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  have := sf_muNl C τ hθ
  have := sf_muHl C u τ
  have hF : Measurable fun p : Mt D.R.k D.R.rS × Mt D.R.k D.R.rS =>
      (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS) := Formalism.L2.SG.Pf.Choice.measurable_mulF
  have hcomm : eT C τ (vOf X τ) ∘ (fun p : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) × Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => p.1 * p.2) =
      (fun p : Mt D.R.k D.R.rS × Mt D.R.k D.R.rS => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt D.R.k D.R.rS)) ∘
        Prod.map (eT C τ (vOf X τ)) (eT C τ (vOf X τ)) := by
    funext p
    exact eT_mul C τ (vOf X τ) p.1 p.2
  rw [QPK.mulMap, Measure.map_map he.measurable measurable_mul, hcomm,
    ← Measure.map_map hF (he.measurable.prodMap he.measurable),
    ← Measure.map_prod_map _ _ he.measurable he.measurable, map_muNl C τ hθ, map_muHl C u τ]
  rfl

theorem invOn_mulMap : QPK.InvOn (QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ)))
    (QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ))) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  obtain ⟨μS, hμS, hmap⟩ := Formalism.L2.SG.Pf.BaseOf.muS_loc (n_eq' X) (X.B.I.ε (vOf X τ)) h1 h2 hg hz hT
    (C.muW_haar u τ) (C.muW_one u τ) (muNB_haarB (D := D) (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ))
  have he := eT_emb C τ (vOf X τ)
  have hmap' : μS.map (eT C τ (vOf X τ)) = Mb C u τ := hmap
  have heq : QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ)) = μS := by
    rw [← he.comap_map (QPK.mulMap _ _), ← he.comap_map μS, map_mulMap, hmap']
  have hset : {γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) | Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ ∈
      Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)} =
      QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ)) := by
    ext γ
    rw [Set.mem_setOf_eq, Formalism.L2.SG.Pf.LocF.local_dictionary_all D X θ C u τ γ, Formalism.L2.SG.Pf.WuDec.NHloc_eq]
  rw [heq, ← hset]
  exact hμS

theorem bruhat_mulMap : ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧
    ∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1 := by
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩ := Formalism.L2.SG.Pf.WuDec.place_facts X u (vOf X τ)
  obtain ⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩ := QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition
    QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
    (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ)) hNc hHc hNg hHg hnorm hunim
  have hK := QPK.prodSet_isClosed hNc hHc
  have hKg := QPK.prodSet_isGrp hNg hHg hnorm
  obtain ⟨c, hc0, hct, hμS⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) _ hK hKg _ _
    (invOn_mulMap C u τ) hM
  refine ⟨fun x => c⁻¹ * β x, measurable_const.mul hβm, fun x => ?_⟩
  rw [hμS, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one,
    smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]

end Place

section Ident

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau)

theorem loc_id {β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞} (hβm : Measurable β)
    (hβ1 : ∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) :
    ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = l2SG (C.nuS u τ) (wT C u τ) := by
  set e := eT C τ (vOf X τ) with he_def
  have he : MeasurableEmbedding e := eT_emb C τ (vOf X τ)
  have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  set g : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞ := fun y => β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 with hg_def
  have hgm : Measurable g := hβm.mul ((X.Wloc_cont u (vOf X τ)).enorm.measurable.pow_const 2)
  set f : Mt D.R.k D.R.rS → ℝ≥0∞ := Function.extend e g 0 with hf_def
  have hfm : Measurable f := he.measurable_extend hgm measurable_const
  have hfe : ∀ γ, f (e γ) = g γ := fun γ => he.injective.extend_apply g 0 γ

  have h1 : ∫⁻ y, g y ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = ∫⁻ x, f x ∂(muGB X (C.Q τ) (C.Qi τ) τ) := by
    have : muGB X (C.Q τ) (C.Qi τ) τ = (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map e := rfl
    rw [this, he.lintegral_map]
    exact lintegral_congr fun γ => (hfe γ).symm

  have h2 := C.nuS_q u τ f hfm

  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) (Formalism.L2.SG.Pf.LocF.muS_haar C u τ)
    (C.nuS_q u τ)
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hMS : Formalism.MainNotions.S.muS (C.muW u τ) (muNB D θ) = (QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))).map e := by
    rw [map_mulMap C u τ]
    exact (Formalism.L2.SG.Pf.BaseOf.muS_swap hz hT (C.muW_haar u τ) (muNB_haarB (D := D) hθ)).symm
  have hSc : ∀ᵐ σ ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))),
      σ ∈ QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u (vOf X τ)) (Formalism.L2.SG.Pf.WuDec.Hfix X u (vOf X τ)) :=
    mem_ae_iff.mpr (invOn_mulMap C u τ).2.2.1
  have h3 : ∀ᵐ x ∂(C.nuS u τ), ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(Formalism.MainNotions.S.muS (C.muW u τ) (muNB D θ)) =
      ‖wT C u τ (Matrix.of x)‖ₑ ^ 2 := by
    filter_upwards [hae] with x hx
    obtain ⟨γx, rfl⟩ := uh_sub_range C τ hx
    rw [hMS, he.lintegral_map]
    have hin : ∀ᵐ σ ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))),
        f (fun i j => (Matrix.of (e σ) * Matrix.of (e γx)) i j) = β (σ * γx) * ‖X.Wloc u (vOf X τ) γx‖ₑ ^ 2 := by
      filter_upwards [hSc] with σ hσ
      have e1 : (fun i j => (Matrix.of (e σ) * Matrix.of (e γx)) i j : Mt D.R.k D.R.rS) = e (σ * γx) := by
        rw [he_def, eT_mul]; rfl
      rw [e1, hfe]
      obtain ⟨m, hm, h, hh, rfl⟩ := hσ
      have hh' : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u (vOf X τ) := by rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]; exact hh
      have hs : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ) :=
        Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X u _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X u _ hm)
          (Formalism.L2.SG.Pf.WuDec.Hloc_sub X u _ hh')
      show β (m * h * γx) * ‖X.Wloc u (vOf X τ) (m * h * γx)‖ₑ ^ 2 = _
      rw [← enorm_norm (X.Wloc u (vOf X τ) (m * h * γx)), Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u _ hs, enorm_norm]
    rw [lintegral_congr_ae hin, lintegral_mul_const _ (show Measurable (fun a => β (a * γx)) from hβm.comp (measurable_mul_const γx)), hβ1 γx, one_mul]
    have hw : wT C u τ (Matrix.of (e γx)) = X.Wloc u (vOf X τ) γx := Formalism.L2.SG.Pf.WuBL.wT_at C u τ γx
    rw [hw]
  rw [h1, h2, lintegral_congr_ae h3]
  unfold l2SG
  rfl

theorem l2SG_phiOf_eq_l2SG_wT (hLF : LocFactor C) (hB : WuBessel C) :
    l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  have hHG := Formalism.L2.SG.Pf.haarTr C τ
  have hq := C.nuS_q u τ
  have hy := C.y_mem τ
  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT hHG hSH hq
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT (Formalism.L2.SG.Pf.colsTypeTr C u τ)
  have hinv : ∀ s ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ UH (Hpk D.R.k D.R.rS),
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
    rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, Formalism.L2.SG.Pf.WuBL.norm_psi, one_mul, hπ.2.1 h0 hh0]
  have heq := Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm D.R.k D.R.rS _ hz hT _ _ _ hHG hSH hq _ (wT C u τ) hWc
    (Formalism.L2.SG.Pf.WuBL.wT_off C u τ) hinv (C.y τ) hy
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hphi : l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) := by
    unfold l2SG
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [Formalism.L2.SG.Pf.GoodS.phi_eq C hB u τ _ hx]
  rw [hphi, heq]

theorem loc_main (hLF : LocFactor C) (hB : WuBessel C) :
    ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        l2SG (C.nuS u τ) (phiOf hB u τ) := by
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  exact ⟨β, hβm, hβ1, (loc_id C u τ hβm hβ1).trans (l2SG_phiOf_eq_l2SG_wT C u τ hLF hB).symm⟩

end Ident

end Formalism.L2.SG.Pf.AmpWinLoc
