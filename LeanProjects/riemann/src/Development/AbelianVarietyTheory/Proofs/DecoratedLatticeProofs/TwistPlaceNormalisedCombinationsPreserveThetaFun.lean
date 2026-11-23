import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.ThetaPin

variable {D : D7}

theorem isFinComb_of_half {S T : HSp D} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (c : WO S T →₀ ℂ)
    (hc : ∀ u ∈ c.support, IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) : IsFinComb c := by
  intro u hu
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    obtain ⟨α, rfl, -, -⟩ := hε
    show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hc u hu i j, map_mul, h0, zero_mul]

theorem aconv_support {G : Type} [AddMonoid G] (P : AddSubmonoid G) :
    ∀ (l : List (G →₀ ℂ)), (∀ e ∈ l, ∀ g ∈ e.support, g ∈ P) → ∀ g ∈ (aconv l).support, g ∈ P
  | [], _, g, hg => by
    have : g = 0 := by
      simpa [aconv] using Finsupp.support_single_subset hg
    rw [this]; exact P.zero_mem
  | e :: l, hl, g, hg => by
    classical
    have ih := aconv_support P l (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    have he := hl e List.mem_cons_self
    change g ∈ (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).support at hg
    obtain ⟨x, hx, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    obtain ⟨y, hy, hg⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hg)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
    exact P.add_mem (he x hx) (ih y hy)

def finSub (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | u.map (infPart D) = 0}
  zero_mem' := by ext i j; simp
  add_mem' {a b} ha hb := by
    change Matrix.map a (infPart D) = 0 at ha
    change Matrix.map b (infPart D) = 0 at hb
    change Matrix.map (a + b) (infPart D) = 0
    rw [Matrix.map_add (infPart D) (fun x y => RingHom.map_add (infPart D) x y) a b, ha, hb, add_zero]

theorem isFinComb_aconv {S T : HSp D} (l : List (WO S T →₀ ℂ)) (hl : ∀ e ∈ l, IsFinComb e) : IsFinComb (aconv l) :=
  aconv_support (finSub S T) l hl

theorem isFinComb_cast {c : Comm D} {a b : ℕ} (e : a = b) (x : WO (c.V (a + 1)) c.T →₀ ℂ) (hx : IsFinComb x) :
    IsFinComb (e ▸ x : WO (c.V (b + 1)) c.T →₀ ℂ) := by
  subst e; exact hx

end GlobalTheory.QPl.ThetaPin

open GlobalTheory.QPl.ThetaPin in
theorem GlobalTheory.QPl.pins_keep_theta : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) Ψ₁) ∧ IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQT j h) Ψ₂) := by
  intro D c v t w F hc hP j h Ψ₁ Ψ₂ h1 h2
  have hs : ∀ i, (F.Q i).s = j := fun i => by have := (F.Q i).hs; omega
  refine ⟨?_, ?_⟩
  · rw [hP.eQ j (by omega)]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h1 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := ((F.Q i).eL_at j 0 (by have := hs i; omega)).1
    exact isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu
  · rw [hP.eQT j h]
    refine (GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 _ _ h2 ?_ hc.std
    refine isFinComb_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    obtain ⟨ε, hε, hsum⟩ := (F.Q i).q.above
    have hat := (F.Q i).eLT_at.1
    unfold QAt.eT
    exact isFinComb_cast _ _ (isFinComb_of_half hε _ fun u hu => hsum ▸ hat u hu)
