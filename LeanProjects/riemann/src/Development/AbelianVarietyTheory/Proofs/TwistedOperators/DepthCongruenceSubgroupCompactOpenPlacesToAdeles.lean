import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasColOfChoice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NonemptyOffDatOfTrueD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PlaceLevelCosets

variable {D : D7}

theorem mem_GinfC_of_off (V : HSp D) (S : GlobalTheory.FinPl.Pl D → Prop) {g : GA D V} (h1 : g ∈ grpOff V S)
    (h2 : g ∈ grpOff V (fun v => ¬ S v)) : g ∈ GinfC V := by
  have h3 : g ∈ grpOff V (fun _ => True) := by
    refine GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.2 fun i j => ?_
    have a := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h1 i j
    have b := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h2 i j
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf] at a b ⊢
    intro w
    by_cases hw : S w.1
    · exact a ⟨w.1, hw⟩
    · exact b ⟨w.1, hw⟩
  exact GlobalTheory.FinPl.OffInh.mem_GinfC_of_all (fun _ => trivial) h3

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem mem_lev_of_inK {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node)
    (hΛ : Submodule.IsLattice D.host.E (G.Λ X)) {κ : GA D (G.V X)}
    (hκ : InK (G.V X) (G.Λ X) (fun v => v ∉ G.pl.S0) κ) : κ ∈ lev G X := by
  classical
  have hfg : (G.Λ X).FG := Submodule.IsLattice.fg (A := D.host.E)
  obtain ⟨hGf, hpr⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff (G.V X) _ κ).1 hκ.1
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E (G.V X).rank (G.Λ X) hΛ
  have hS : Lev.finE (G.V X) κ ∈ Formalism.L2.DIV.St β :=
    (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (G.V X) β (G.Λ X) hβ κ).2
      (GlobalTheory.AdelicU.mem_levelOpen.1 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK (G.V X) (G.Λ X) hfg _ hκ))
  refine ⟨hGf, ?_⟩
  show Lev.finE (G.V X) κ ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  rw [← GlobalTheory.ColMeas.princ_eq_congLev D.sp.cm (G.V X).gram hβ G.modul]
  refine ⟨GlobalTheory.LevSplit.finE_mem_UA (G.V X) κ, ?_⟩
  obtain ⟨y, hy⟩ := hS
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, hy, fun a b => ?_⟩

  have hE : ∀ c d, ((Lev.finE (G.V X) κ).1 - 1) c d = toEAf D ((Formalism.L2.Theta.mt (G.V X) κ - 1) c d) := by
    intro c d
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
    congr 1
    by_cases h : c = d
    · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero]
  have hW : ∀ w ∈ G.pl.W0, ((Lev.finE (G.V X) κ).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    have h1 := (GlobalTheory.FinPl.KOpen.proj_eq_one_iff (G.V X) v κ).1 (hpr v (not_not.2 hv))
    refine Matrix.ext fun c d => ?_
    rw [Matrix.map_apply, hE, Matrix.zero_apply]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt v _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero v _ (h1 c d)) _ (G.pl.under_w hv)
  have hconj : (Lev.finE (G.V X) κ).1 = β.1 * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 * (β⁻¹).1 := by
    rw [← hy]; rfl
  have hY := GlobalTheory.LevRedTriv.conj_sub_one β _ _ hconj
  refine (GlobalTheory.FunObj.Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
  have hM : ((Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    rw [hY, Matrix.map_mul, Matrix.map_mul, hW w hw, Matrix.mul_zero, Matrix.zero_mul]
  have e0 : GlobalTheory.StdFrames.cpt w (((y.1 - 1) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 0 := by
    rw [GlobalTheory.LevRedTriv.coe_sub_one_apply]
    exact congrFun (congrFun hM a) b
  rw [e0, map_zero]
  exact zero_le'

theorem idAt_le_idOff_compl (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D (fun v => ¬ P v) ≤ idOff D P := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, not_not.2 w.2⟩

theorem idAt_le_idOff_compl' (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D P ≤ idOff D (fun v => ¬ P v) := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, w.2⟩

end GlobalTheory.PlaceLevelCosets

open GlobalTheory.PlaceLevelCosets GlobalTheory.FinPl.PlacesAdeles in

theorem GlobalTheory.PlaceLevelCosets.levCoset_of_places : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → (lev G (.grid i 0) ≤ GfC _ ∧ IsCompact (lev G (.grid i 0) : Set (GA D (G.V (.grid i 0)))) ∧ IsOpen (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0))))) ∧ ∀ (R : Subgroup (GA D (G.V (.grid i 0)))) h, (∀ v ∉ G.pl.S0, ∀ h₁ ∈ grpAt _ (· = v), ∀ h₂ ∈ grpOff _ (· = v), h = h₁ * h₂ → CosetAt _ R (G.Λ (.grid i 0)) v h₁) → (∀ h₁ ∈ grpAt _ (fun v => v ∈ G.pl.S0), ∀ h₂ ∈ grpOff _ (fun v => v ∈ G.pl.S0), h = h₁ * h₂ → ∃ r ∈ R, r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid i 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ h₁ = r * k) → ∃ r ∈ R, ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid i 0), h = r * a * k := by
  intro D _ T L μ0 hL sc G W M _ i hi
  have hV := node_isV G hL (X := .grid i 0) ⟨hi, Nat.zero_le _⟩
  have hlat : Submodule.IsLattice D.host.E (G.Λ (.grid i 0)) := hV.sd.1
  have hoc := congLev_open_compact (G.V (.grid i 0)) hlat (G.pl.modul_ne_bot sc)
  refine ⟨⟨inf_le_left, hoc.2, ?_⟩, ?_⟩
  · have e : (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0)))) =
        Subtype.val ⁻¹' ((((congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul).comap
          (Lev.finE (G.V (.grid i 0))) : Subgroup (GA D (G.V (.grid i 0)))) : Set (GA D (G.V (.grid i 0))))) := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hoc.1.preimage continuous_subtype_val
  · intro R h hA hB
    have hsd : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := hV.sd
    have hoff : ∀ v, (fun v => v ∉ G.pl.S0) v → ∃ hv ∈ grpAt (G.V (.grid i 0)) (· = v), ∃ h' ∈ grpOff (G.V (.grid i 0)) (· = v),
        h = hv * h' ∧ ∃ r ∈ R, r ∈ grpAt (G.V (.grid i 0)) (· = v) ∧ ∃ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ ∧
          hv = r * κ := by
      intro v hv
      obtain ⟨x, hx, y, hy, e⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 (G.V (.grid i 0))).1 h
      exact ⟨x, hx, y, hy, e, hA v hv x hx y hy e⟩
    obtain ⟨r₁, hr₁, hr₁P, g, hg, κ₁, hκ₁, e₁⟩ :=
      GlobalTheory.FinPl.placesToAdeles_all D (G.V (.grid i 0)) (G.Λ (.grid i 0)) (fun v => v ∉ G.pl.S0) hsd R h hoff
    obtain ⟨hdec, hcomm, -, -⟩ := (GlobalTheory.FinPl.localComponents D (fun v => v ∈ G.pl.S0)).2 (G.V (.grid i 0))
    obtain ⟨g₁, hg₁, g₂, hg₂, eg⟩ := hdec g
    have hin : ∀ x ∈ grpAt (G.V (.grid i 0)) (fun v => v ∉ G.pl.S0), x ∈ grpOff (G.V (.grid i 0)) (fun v => v ∈ G.pl.S0) :=
      fun x hx => congGrp_mono (idAt_le_idOff_compl (fun v => v ∈ G.pl.S0)) hx
    have hr₁off := hin r₁ hr₁P
    have hκ₁off := hin κ₁ hκ₁.1
    have hg₁off : g₁ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) :=
      congGrp_mono (idAt_le_idOff_compl' (fun v => v ∈ G.pl.S0)) hg₁
    have hg₂off : g₂ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) := by
      have : g₂ = g₁⁻¹ * g := by rw [eg]; group
      rw [this]
      exact mul_mem (inv_mem hg₁off) hg
    have c1 : r₁ * g₁ = g₁ * r₁ := (hcomm g₁ hg₁ r₁ hr₁off).symm
    have eh : h = g₁ * (r₁ * g₂ * κ₁) := by
      rw [e₁, eg, ← mul_assoc, ← mul_assoc, ← mul_assoc, c1]
    obtain ⟨r₀, hr₀, -, k₀, hk₀, hk₀S, ek⟩ := hB g₁ hg₁ _ (mul_mem (mul_mem hr₁off hg₂) hκ₁off) eh
    have c2 : k₀ * r₁ = r₁ * k₀ := hcomm k₀ hk₀S r₁ hr₁off
    have c3 : k₀ * g₂ = g₂ * k₀ := hcomm k₀ hk₀S g₂ hg₂
    refine ⟨r₀ * r₁, R.mul_mem hr₀ hr₁, g₂, mem_GinfC_of_off _ _ hg₂ hg₂off, k₀ * κ₁,
      mul_mem hk₀ (mem_lev_of_inK G _ hlat hκ₁), ?_⟩
    calc h = g₁ * (r₁ * g₂ * κ₁) := eh
      _ = r₀ * (k₀ * r₁) * g₂ * κ₁ := by rw [ek]; simp only [mul_assoc]
      _ = r₀ * r₁ * (k₀ * g₂) * κ₁ := by rw [c2]; simp only [mul_assoc]
      _ = r₀ * r₁ * g₂ * (k₀ * κ₁) := by rw [c3]; simp only [mul_assoc]
