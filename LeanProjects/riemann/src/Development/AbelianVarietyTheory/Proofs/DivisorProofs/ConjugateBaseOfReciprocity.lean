import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRatioRealizationSameStatement

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

theorem baseLat_le
    (hinj : ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (ν : ℂ), ν ≠ 0 → Function.Injective (rdAt p w j hρ ν))
    (hgen : ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h →
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hunit : ∀ (ρ ρ' : Setup D.ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
      RealPin p.R p.cG ρ → ρ.LevelOf D.nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
      IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν → IsNorm p.R p.v₀ (ρ'.B (ex.nch.twI w) j (ex.nch.sd w)) ν' →
      RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
      ∀ s h P, ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h P → P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h →
        ∀ f f', rdAt p w j hρ ν f = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P →
          rdAt p w j hρ' ν' f' = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P →
          ∃ u : FractionRing (D.ntw.O (ex.nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f)
    (ρ ρ' : Setup D.ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ) (hp : RealPin p.R p.cG ρ) (hL : ρ.LevelOf D.nexp) (hp' : RealPin p.R p.cG ρ')
    (hS : SameBut ρ ρ') (hN : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν)
    (hN' : IsNorm p.R p.v₀ (ρ'.B (ex.nch.twI w) j (ex.nch.sd w)) ν')
    (hR : RatBase (rdAt p w j hρ ν)) (hR' : RatBase (rdAt p w j hρ' ν')) :
    baseLat p w j hρ ν ≤ baseLat p w j hρ' ν' := by
  have hbad := hS.2.2.1
  have hB := hS.2.2.2.1
  have hom := hS.2.2.2.2
  have hth : ∀ h P, ρ'.theta (ex.nch.twI w) j (ex.nch.sd w) h P = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := by
    intro h P
    simp only [Setup.theta, hB, hom]
  have hlat : ∀ O h, ρ'.lat (ex.nch.twI w) j (ex.nch.sd w) O h = ρ.lat (ex.nch.twI w) j (ex.nch.sd w) O h := by
    intro O h
    simp only [Setup.lat, hB]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨s, h, P, hd, hf⟩, rfl⟩
  have key : ∀ Q ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
      (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)),
      ∃ g, rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q ∧
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g) ∈ baseLat p w j hρ' ν' := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      have hd1 : ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q :=
        ⟨hd.split, hd.off, hd.fin, hd.supp, lat_mono ρ _ j _ (smallInt_le hρ _ _) h hQ⟩
      have hd2 : ρ'.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q :=
        ⟨hd.split, by rw [hbad]; exact hd.off, hd.fin, hd.supp,
          lat_mono ρ' _ j _ (smallInt_le hρ' _ _) h (by rw [hlat]; exact hQ)⟩
      obtain ⟨g, hg⟩ := hR s h Q hd1
      obtain ⟨g', hg'⟩ := hR' s h Q hd2
      rw [hth] at hg'
      obtain ⟨u, ⟨n, hn, hu⟩, hgu⟩ := hunit ρ ρ' hρ hρ' ν ν' hp hL hp' hS hN hN' hR hR' s h Q hd1 hQ g g' hg hg'
      obtain ⟨o, ho⟩ := exists_inv_of_root u n hn hu
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [zero_pow hn] at hu
        exact zero_ne_one hu
      have hgo : g = o • g' := by
        rw [← algebraMap_smul (FractionRing (D.ntw.O (ex.nch.twI w))) o g', ho, hgu, smul_smul, inv_mul_cancel₀ hu0, one_smul]
      refine ⟨g, hg, ?_⟩
      rw [hgo, TensorProduct.tmul_smul]
      refine Submodule.smul_of_tower_mem _ o (Submodule.subset_span ⟨g', ⟨s, h, Q, hd2, ?_⟩, rfl⟩)
      rw [hg', hth]
    | zero =>
      refine ⟨0, ?_, by rw [TensorProduct.tmul_zero]; exact zero_mem _⟩
      rw [map_zero]
      exact (map_zero _).symm
    | add Q1 Q2 _ _ h1 h2 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨g2, e2, m2⟩ := h2
      refine ⟨g1 + g2, ?_, by rw [TensorProduct.tmul_add]; exact add_mem m1 m2⟩
      rw [map_add, e1, e2]
      exact (map_add _ _ _).symm
    | smul a Q _ h1 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨o, ho⟩ := a.2
      refine ⟨o • g1, ?_, by rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ o m1⟩
      rw [rd_smul, e1]
      change _ = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).theta (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) h ((a : ℂ) • Q)
      rw [map_smul, ← ho]
  obtain ⟨g, hg, hm⟩ := key P (hgen ρ hρ hp h P hd.mem)
  have : f = g := hinj ρ hρ ν hN.1 (hf.trans hg.symm)
  rw [this]
  exact hm

end Point

def SeriesUnitL : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ ρ' : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  IsNorm p.R p.v₀ (ρ'.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
  RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ f f', rdAt p w j hρ ν f = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      rdAt p w j hρ' ν' f' = ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P →
      ∃ u : FractionRing ((Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f

theorem conjBase_of_steps (hI : ReadInj) (hG : LatSmallGen) (hU : SeriesUnitL) : ConjBase := by
  unfold ConjBase ReadInj LatSmallGen SeriesUnitL AtTw AtPts at *
  refine ((Formalism.MainNotions.Closed.and hI hG).and hU).imp fun Fm CH _ h => ?_
  obtain ⟨x0, hx0⟩ := (h.1.1.and h.1.2).and h.2
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ ρ' hρ hρ' ν ν' hpin hS hN hR hF => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := hx0 x hx hle i p hp
  have hL : ρ.LevelOf (Fm.D x i).nexp := levelOf_of_sameBut hm.2.2 hρ' hρ hF.1.1 hpin hS.symm hF.2.2.2
  exact le_antisymm
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ ρ' hρ hρ' ν ν' hpin hL hF.1.1 hS hN hF.2.1 hR.1 hF.2.2.1.1)
    (baseLat_le p w j (a1 hm w hw j) (a2 hm w hw j) (a3 hm w hw j) ρ' ρ hρ' hρ ν' ν hF.1.1 hF.2.2.2 hpin hS.symm hF.2.1 hN hF.2.2.1.1 hR.1)

theorem conjBase_of : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → ConjBase := fun h1 h2 h3 h4 =>
  conjBase_of_steps readInj GlobalTheory.T.LatticeSmallGeneration (GlobalTheory.T.norm_ratio_realization_same h1 h2 h3 h4)

end GlobalTheory.BigOn.Exp
