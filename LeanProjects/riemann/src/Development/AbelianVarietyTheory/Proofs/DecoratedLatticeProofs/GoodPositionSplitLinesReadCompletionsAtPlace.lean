import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocCongr

variable {D : D7}

theorem mul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) ∈ latA S L P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem latA_le_of_latV_le {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P ≤ latV S L' P) :
    latA S L P ≤ latA S L' P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
  have hz : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) ∈ latV S L P :=
    AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
  have hm := mul_mem_latA (L := L') ha (h hz)
  have key : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
      fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [SetLike.mem_coe, key]
  exact hm

theorem latA_congr {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P = latV S L' P) :
    latA S L P = latA S L' P :=
  le_antisymm (latA_le_of_latV_le h.le) (latA_le_of_latV_le h.ge)

theorem latO_congr {S T : HSp D} {LS LS' : Lat S} {LT LT' : Lat T} (hS : IsSelfDualC S LS) (hS' : IsSelfDualC S LS')
    (hT : IsSelfDualC T LT) (hT' : IsSelfDualC T LT') {P : Pl D → Prop} (eS : latV S LS P = latV S LS' P)
    (eT : latV T LT P = latV T LT' P) :
    latO S T (LS : Set _) (LT : Set _) P = latO S T (LS' : Set _) (LT' : Set _) P := by
  ext u
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS' LT' hS' hT', eS,
    latA_congr eT]

theorem monoAt_congr {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {L₀ L₀' : Lat S₀} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (e₀ : latV S₀ L₀ (· = v) = latV S₀ L₀' (· = v)) (H : MonoAt d L L₀ v) :
    MonoAt d L' L₀' v := by
  unfold MonoAt at H ⊢
  rw [← e, ← e₀]
  exact H

theorem orthAt_congr {S A B : HSp D} {o : OrthDec S A B} {L L' : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : OrthAt o L LA LB v) : OrthAt o L' LA LB v := by
  unfold OrthAt at H ⊢
  rw [← e]
  exact H

theorem primAt_congr {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : PrimAt ψ d L v) : PrimAt ψ d L' v := by
  unfold PrimAt at H ⊢
  rw [← e]
  exact H

theorem colsAt_congr {V V₀ W : HSp D} {ρ : ℕ} {d : HypDec V V₀ ρ} {x : Mx D W.rank ρ} {LV LV' : Lat V} {LW LW' : Lat W}
    {v : Pl D} (e : latV V LV (· = v) = latV V LV' (· = v)) (eW : latV W LW (· = v) = latV W LW' (· = v))
    (H : ColsAt d x LV LW v) : ColsAt d x LV' LW' v := by
  unfold ColsAt at H ⊢
  rw [← e, ← latA_congr eW]
  exact H

end GlobalTheory.LocCongr

namespace GlobalTheory.LocCongr

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem goodBF_congr {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} {LV LV' : Lat B.V} {LV₀ LV₀' : Lat B.V₀} {LW LW' : Lat J.W}
    {LW₀ : Lat J.W₀} {v : Pl D} (sV : IsSelfDualC B.V LV') (sV₀ : IsSelfDualC B.V₀ LV₀') (sW : IsSelfDualC J.W LW')
    (eV : latV B.V LV (· = v) = latV B.V LV' (· = v)) (eV₀ : latV B.V₀ LV₀ (· = v) = latV B.V₀ LV₀' (· = v))
    (eW : latV J.W LW (· = v) = latV J.W LW' (· = v)) (H : GoodBF ψ B J LV LV₀ LW LW₀ v) :
    GoodBF ψ B J LV' LV₀' LW' LW₀ v where
  tame := H.tame
  sdV := sV
  sdV₀ := sV₀
  sdW := sW
  sdW₀ := H.sdW₀
  monoV := monoAt_congr eV eV₀ H.monoV
  monoW := monoAt_congr eW rfl H.monoW
  prim := primAt_congr eV H.prim
  cols := colsAt_congr eV eW H.cols
  last := by
    rw [← latO_congr H.sdV₀ sV₀ H.sdW sW eV₀ eW]
    exact H.last

theorem adaptFB_congr {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} {LV LV' : Lat J.W} {LV₀ : Lat J.W₀}
    {LW LW' : Lat B.V} {LW₀ LW₀' : Lat B.V₀} {v : Pl D} (sV : IsSelfDualC J.W LV') (sW : IsSelfDualC B.V LW')
    (sW₀ : IsSelfDualC B.V₀ LW₀') (eV : latV J.W LV (· = v) = latV J.W LV' (· = v))
    (eW : latV B.V LW (· = v) = latV B.V LW' (· = v)) (eW₀ : latV B.V₀ LW₀ (· = v) = latV B.V₀ LW₀' (· = v))
    (H : AdaptFB ψ J B LV LV₀ LW LW₀ v) : AdaptFB ψ J B LV' LV₀ LW' LW₀' v where
  tame := H.tame
  sdV := sV
  sdV₀ := H.sdV₀
  sdW := sW
  sdW₀ := sW₀
  monoV := monoAt_congr eV rfl H.monoV
  monoW := monoAt_congr eW eW₀ H.monoW
  prim := primAt_congr eV H.prim
  cols := colsAt_congr eV eW H.cols

theorem goodAt_splitAt_congr : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀)
    (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧
      latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) →
    (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) →
    (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
      (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  intro D c v k _ _ _ _ ι o N M x hN hM
  refine ⟨fun hg => ⟨fun j ρ h => ?_, fun j σ h => ?_⟩, fun hs => ⟨fun j ρ h => ?_, fun j h => ?_⟩⟩
  · have h0 := hN j (by omega)
    have h1 := hN (j + 1) (by omega)
    exact goodBF_congr h0.2.1 (hM j ρ h).2.1 h1.2.1 h0.2.2.symm (hM j ρ h).2.2.symm h1.2.2.symm (hg.bf j ρ h)
  · have h1 := hN (j + 1) (by omega)
    have h2 := hN (j + 1 + 1) (by omega)
    exact adaptFB_congr h1.2.1 h2.2.1 (hM (j + 1 + 1) σ (idx_step h)).2.1 h1.2.2.symm h2.2.2.symm
      (hM (j + 1 + 1) σ (idx_step h)).2.2.symm (hg.fb j σ h)
  · obtain ⟨LL, hLL, hO⟩ := hs.core j ρ h
    exact ⟨LL, hLL, orthAt_congr (hM j ρ h).2.2.symm hO⟩
  · obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := hs.top j h
    exact ⟨LL, LZ, h1, h2, orthAt_congr (hM j 0 h).2.2.symm h3, h4, h5⟩

end GlobalTheory.LocCongr
