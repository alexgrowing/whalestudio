import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeightStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LowerBlockHecke

theorem sum_translate {G : Type} [Group G] (J : Subgroup G) (g₀ : G) (R : Finset G) (hRJ : ∀ y ∈ R, y ∈ J)
    (hR : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g₀)⁻¹ * (j * g₀) ∈ J) (χ : G → ℂ)
    (hmul : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (hne : ∀ a ∈ J, χ a ≠ 0)
    (hconj : ∀ m ∈ J, g₀⁻¹ * m * g₀ ∈ J → χ (g₀⁻¹ * m * g₀) = χ m)
    (Φ : G → ℂ) (hΦ : ∀ x, ∀ k ∈ J, Φ (x * k) = χ k * Φ x) {y₀ : G} (hy₀ : y₀ ∈ J) :
    ∑ y ∈ R, (χ y)⁻¹ * Φ (y₀ * y * g₀) = χ y₀ * ∑ y ∈ R, (χ y)⁻¹ * Φ (y * g₀) := by
  classical
  let s : G → G → G := fun a y => if h : a * y ∈ J then (hR _ h).exists.choose else y
  have hs : ∀ a ∈ J, ∀ y ∈ R, s a y ∈ R ∧ (s a y * g₀)⁻¹ * (a * y * g₀) ∈ J := by
    intro a ha y hy
    have h : a * y ∈ J := J.mul_mem ha (hRJ y hy)
    have e : s a y = (hR _ h).exists.choose := dif_pos h
    rw [e]
    exact (hR _ h).exists.choose_spec
  have huniq : ∀ a ∈ J, ∀ y ∈ R, ∀ z ∈ R, (z * g₀)⁻¹ * (a * y * g₀) ∈ J → s a y = z := by
    intro a ha y hy z hz hzJ
    exact (hR _ (J.mul_mem ha (hRJ y hy))).unique (hs a ha y hy) ⟨hz, hzJ⟩
  have hinv : ∀ y ∈ R, s y₀⁻¹ (s y₀ y) = y := by
    intro y hy
    obtain ⟨hm, hK⟩ := hs y₀ hy₀ y hy
    apply huniq _ (J.inv_mem hy₀) _ hm _ hy
    have e : (y * g₀)⁻¹ * (y₀⁻¹ * s y₀ y * g₀) = ((s y₀ y * g₀)⁻¹ * (y₀ * y * g₀))⁻¹ := by group
    rw [e]
    exact J.inv_mem hK
  have hinv' : ∀ y ∈ R, s y₀ (s y₀⁻¹ y) = y := by
    intro y hy
    obtain ⟨hm, hK⟩ := hs y₀⁻¹ (J.inv_mem hy₀) y hy
    apply huniq _ hy₀ _ hm _ hy
    have e : (y * g₀)⁻¹ * (y₀ * s y₀⁻¹ y * g₀) = ((s y₀⁻¹ y * g₀)⁻¹ * (y₀⁻¹ * y * g₀))⁻¹ := by group
    rw [e]
    exact J.inv_mem hK
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (s y₀) (s y₀⁻¹) (fun y hy => (hs y₀ hy₀ y hy).1)
    (fun y hy => (hs _ (J.inv_mem hy₀) y hy).1) hinv hinv' ?_
  intro y hy
  obtain ⟨hm, hK⟩ := hs y₀ hy₀ y hy
  set y' := s y₀ y
  set k := (y' * g₀)⁻¹ * (y₀ * y * g₀)
  have hyJ := hRJ y hy
  have hy'J := hRJ y' hm
  have hmJ : y'⁻¹ * (y₀ * y) ∈ J := J.mul_mem (J.inv_mem hy'J) (J.mul_mem hy₀ hyJ)
  have ek : k = g₀⁻¹ * (y'⁻¹ * (y₀ * y)) * g₀ := by simp only [k]; group
  have hχk : χ k = χ (y'⁻¹ * (y₀ * y)) := by rw [ek]; exact hconj _ hmJ (ek ▸ hK)
  have e1 : y₀ * y * g₀ = y' * g₀ * k := by simp only [k]; group
  have e2 : χ y₀ * χ y = χ y' * χ (y'⁻¹ * (y₀ * y)) := by
    rw [← hmul _ hy₀ _ hyJ, ← hmul _ hy'J _ hmJ, mul_inv_cancel_left]
  rw [e1, hΦ _ _ hK, hχk]
  have hy0 := hne y hyJ
  have hy'0 := hne y' hy'J
  have e3 : χ (y'⁻¹ * (y₀ * y)) = χ y₀ * χ y * (χ y')⁻¹ := by
    rw [e2, mul_comm (χ y'), mul_assoc, mul_inv_cancel₀ hy'0, mul_one]
  rw [e3]
  field_simp

end GlobalTheory.LowerBlockHecke

namespace GlobalTheory.LowerBlockHecke

open ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.ZonalCellDecomposition

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem det_lower_ne {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 := by
  obtain ⟨h, hh, rfl⟩ := hj
  intro h0
  have e1 : (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k) h).1.toBlocks₂₂ =
      (algebraMap 𝒪[k] k).mapMatrix h.1.toBlocks₂₂ := rfl
  rw [e1, ← RingHom.map_det] at h0
  have h1 : h.1.toBlocks₂₂.det = 0 := Subtype.ext h0
  set u := GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]) h with hu
  have h21 : u.1.toBlocks₂₁ = 0 := by
    ext i j
    exact hh (i := .inr i) (j := .inl j) (show false < true by decide)
  have h22 : u.1.toBlocks₂₂.det = 0 := by
    have : u.1.toBlocks₂₂ = (IsLocalRing.residue 𝒪[k]).mapMatrix h.1.toBlocks₂₂ := rfl
    rw [this, ← RingHom.map_det, h1, map_zero]
  have := u.det_ne_zero
  rw [← fromBlocks_toBlocks u.1, h21, det_fromBlocks_zero₂₁, h22, mul_zero] at this
  exact this rfl

theorem det_lower_conj_mtor (ϖ : kˣ) (e : D → ℤ) (m : GL (A ⊕ D) k) :
    ((mtor ϖ e)⁻¹ * m * mtor ϖ e : GL (A ⊕ D) k).1.toBlocks₂₂.det = m.1.toBlocks₂₂.det := by
  set c : A ⊕ D → kˣ := fun i => ϖ ^ (Sum.elim (0 : A → ℤ) e i) with hc
  have ht : mtor (A := A) ϖ e = diagT k (A ⊕ D) c := rfl
  have hti : (mtor (A := A) ϖ e)⁻¹ = diagT k (A ⊕ D) c⁻¹ := by rw [ht, map_inv]
  have hb : ((mtor ϖ e)⁻¹ * m * mtor ϖ e : GL (A ⊕ D) k).1.toBlocks₂₂ =
      diagonal (fun i => ((c (.inr i))⁻¹ : kˣ) : D → k) * m.1.toBlocks₂₂ * diagonal (fun i => (c (.inr i) : k)) := by
    rw [hti, ht, Units.val_mul, Units.val_mul, val_diagT, val_diagT]
    ext i j
    simp only [toBlocks₂₂, of_apply, diagonal_mul, mul_diagonal, Pi.inv_apply]
  rw [hb, det_mul, det_mul, det_diagonal, det_diagonal, mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp

end GlobalTheory.LowerBlockHecke

namespace GlobalTheory.LowerBlockHecke

open GlobalTheory.ZonalCellDecomposition

set_option maxHeartbeats 2000000 in

theorem hecke_level : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ (ξl : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v))) (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ), GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ F : GA D s.V → ℂ, (∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, F (g * κ) = Lev.levChi s.V s.β s.L κ * F g) → ∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR F hF κ hκ g
  obtain ⟨-, -, -, -, hch⟩ := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw j hj s hs PP hPP v φ hφ
  obtain ⟨⟨eq, hemb, -⟩, hlev, hchi⟩ := hch ι hι
  have hchi' := hchi ξl hξ
  set J := parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) with hJ
  set g₀ : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) := mtor ϖ e with hg₀
  set χ : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → ℂ := fun x => Lev.levChi s.V s.β s.L (ι x) with hχ

  set k0 := gAt s.V (.inl v) κ with hk0def
  have hk0 : k0 ∈ Lev.levG s.V s.β s.L := by
    obtain ⟨hr, hL, hfl⟩ := hs
    have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
    have hP : s.L.P.H = ⊥ := by rw [hL]; rfl
    obtain ⟨-, hS, hl⟩ := (LevLoc.mem_lev_iff s.V.gram s.β s.L hP _).1 hκ.2
    have hkS := LevLoc.finE_gAt_mem_St hfr κ v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr κ).1 hS v)
    refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC s.V v _, ?_⟩
    refine (LevLoc.mem_lev_iff s.V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA s.V _, hkS, fun PP' => ?_⟩
    by_cases e' : PP'.under (𝓞 D.host.F) = v
    · subst e'
      rw [← LevLoc.red_local hfr κ hS PP']
      exact hl PP'
    · rw [GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β _ PP' hkS (GlobalTheory.AdelicU.proj_emb_ne _ _ e' _)]
      exact LevLoc.locOK_one _ _
  set y₀ := eq.symm (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ) with hy₀def
  have hy0 : ι y₀ = k0 := by
    rw [hemb, hy₀def, eq.apply_symm_apply]
    rfl
  have hy0J : y₀ ∈ J := (hlev y₀).1 (hy0 ▸ hk0)
  set κ' := k0⁻¹ * κ with hκ'def
  have hκ' : κ' ∈ Lev.levG s.V s.β s.L := mul_mem (inv_mem hk0) hκ
  have hκeq : κ = k0 * κ' := by rw [hκ'def, mul_inv_cancel_left]
  have hpκ' : GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ' = 1 := by
    rw [hκ'def, map_mul, map_inv]
    show (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v
      (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ)))⁻¹ *
        GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ = 1
    rw [GlobalTheory.AdelicU.proj_emb_self, inv_mul_cancel]
  have hcomm : ∀ x, ι x * κ' = κ' * ι x := fun x => by
    rw [hemb]
    exact (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig s.V.gram (eq x) hpκ').eq

  have hmul : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b := fun a ha b hb => by
    simp only [hχ, map_mul]
    exact GlobalTheory.ChainOnto.LevelFacts.levChi_mul ((hlev a).2 ha) ((hlev b).2 hb)
  have hne : ∀ a ∈ J, χ a ≠ 0 := fun a ha => by
    simp only [hχ]
    rw [hchi' a ha (Units.mk0 _ (det_lower_ne ha)) rfl]
    exact Units.ne_zero _
  have hconj : ∀ m ∈ J, g₀⁻¹ * m * g₀ ∈ J → χ (g₀⁻¹ * m * g₀) = χ m := fun m hm hm' => by
    simp only [hχ]
    rw [hchi' _ hm' (Units.mk0 _ (det_lower_ne hm')) rfl, hchi' m hm (Units.mk0 _ (det_lower_ne hm)) rfl]
    have : Units.mk0 _ (det_lower_ne hm') = Units.mk0 _ (det_lower_ne hm) :=
      Units.ext (det_lower_conj_mtor ϖ e m)
    rw [this]
  have hΦ : ∀ x, ∀ k ∈ J, F (g * ι (x * k)) = χ k * F (g * ι x) := fun x k hk => by
    rw [map_mul, ← mul_assoc]
    exact hF _ ((hlev k).2 hk) _
  have hxi : ∀ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) = (χ y)⁻¹ := fun y hy => by
    simp only [hχ]
    rw [hchi' y (hR.1 y hy).1 (d y) (hR.1 y hy).2]
    simp
  have hterm : ∀ y, F (g * κ * ι (y * g₀)) = Lev.levChi s.V s.β s.L κ' * F (g * ι (y₀ * y * g₀)) := fun y => by
    have e1 : g * κ * ι (y * g₀) = g * ι (y₀ * y * g₀) * κ' := by
      rw [hκeq, mul_assoc y₀ y g₀, map_mul ι y₀, hy0]
      simp only [mul_assoc]
      rw [hcomm]
    rw [e1, hF κ' hκ']
  have key := sum_translate J g₀ R (fun y hy => (hR.1 y hy).1) hR.2 χ hmul hne hconj (fun x => F (g * ι x)) hΦ hy0J
  calc ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * g₀))
      = Lev.levChi s.V s.β s.L κ' * ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y₀ * y * g₀)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hxi y hy, hterm y]
        ring
    _ = Lev.levChi s.V s.β s.L κ' * (χ y₀ * ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y * g₀))) := by rw [key]
    _ = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * g₀)) := by
        have h1 : Lev.levChi s.V s.β s.L κ = χ y₀ * Lev.levChi s.V s.β s.L κ' := by
          rw [hκeq, GlobalTheory.ChainOnto.LevelFacts.levChi_mul hk0 hκ']
          simp only [hχ, hy0]
        have h2 : ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * g₀)) = ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y * g₀)) :=
          Finset.sum_congr rfl fun y hy => by rw [hxi y hy]
        rw [h1, h2]
        ring

end GlobalTheory.LowerBlockHecke

end
