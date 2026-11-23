import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open Matrix

namespace GlobalTheory.RatSplitLat

theorem colLat_fg {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem colLat_span {K : Type} [Field K] [NumberField K] {n : ℕ} (B : GL (Fin n) K) :
    Submodule.span K ((colLat B : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤ := by
  unfold colLat
  rw [Submodule.span_span_of_tower]
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j •
      (fun a : Fin n => (B : Matrix (Fin n) (Fin n) K) a j) := by
    funext a
    have := congrFun (show (B : Matrix (Fin n) (Fin n) K) *ᵥ (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) a
    conv_lhs => rw [← this]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem stab_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (H : AddSubgroup (Fin n → GlobalTheory.AdLat.RA F E)) (k : GL (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h1 : ∀ z ∈ H, ∃ w ∈ H, k.1 *ᵥ z - z = N • w) (h2 : ∀ z ∈ H, (k⁻¹).1 *ᵥ z ∈ H) (y : Fin n → GlobalTheory.AdLat.RA F E) :
    y ∈ H ↔ k.1 *ᵥ y ∈ H := by
  constructor
  · intro hy
    obtain ⟨w, hw, e⟩ := h1 y hy
    rw [show k.1 *ᵥ y = (k.1 *ᵥ y - y) + y by abel, e]
    exact H.add_mem (H.nsmul_mem hw N) hy
  · intro hy
    have := h2 _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

set_option maxHeartbeats 1000000 in

theorem exists_rat_split_lat : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  intro D V B N hN g
  obtain ⟨-, -, -, -, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, hki⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (GlobalTheory.Member.cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (GlobalTheory.UnRep.Space.finrank_two D) (colLat B) (colLat_fg B) (colLat_span B) (finHom V g.1) N
    (GlobalTheory.UnRep.Space.isUnA_finHom V g.1) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [GlobalTheory.UnRep.Space.herm_neg_eq, GlobalTheory.UnRep.Space.herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g.1 = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨g * ⟨k, hk'⟩⁻¹ * ⟨h, hh⟩⁻¹, ⟨h, hh⟩, ⟨k, hk'⟩, ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, ?_⟩, ?_, ?_, by rw [inv_mul_cancel_right, inv_mul_cancel_right]⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, e]
    rw [mul_inv_cancel_right, mul_inv_cancel_right]
  · change GlobalTheory.UnRep.SuppSplit _ N (finHom V h).1
    rw [eh]
    exact hs
  · intro v
    have key := GlobalTheory.StdFrames.hatL_of_hat (F := D.host.F) (colLat B) (colLat B) k'.1
      (stab_iff _ k' N hk hki) v
    have hm : (Formalism.IndefR.Lev.finE V k).1 =
        k'.1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [← ek]; rfl
    refine key.trans (iff_of_eq ?_)
    exact congrArg (fun M => M *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) hm.symm

end GlobalTheory.RatSplitLat
