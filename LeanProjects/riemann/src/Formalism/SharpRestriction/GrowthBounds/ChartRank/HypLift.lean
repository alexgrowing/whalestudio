import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypFormsCl
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LiMap

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLift

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def trN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) →ₗ[ℂ]
      (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) where
  toFun h := fun z => (detF (cTw D i) z)⁻¹ * h (foTrR (embT D) γ0 z)
  map_add' h h' := by funext z; simp only [Pi.add_apply]; ring
  map_smul' a h := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem trN_inj (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    LinearMap.ker (trN D i hi γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun h hh => ?_
  funext z
  have h1 := congrFun hh (foTrR (embT D) γ0⁻¹ z)
  have h2 : foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z) = z := by
    rw [← foTrR_mul, mul_inv_cancel, foTrR_one]
  change (detF (cTw D i) _)⁻¹ * h (foTrR (embT D) γ0 (foTrR (embT D) γ0⁻¹ z)) = 0 at h1
  rw [h2] at h1
  exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero (detF_ne _ _))

def phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) :
    XR (Hc S β).P ℂ →ₗ[ℂ] (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
  (trN D i hi γ0).comp
    (evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B))

theorem ker_phiC (S : StepIn M i hi G) (β : S.Ch) (γ0 : GL (Fin (D.R.N i)) D.host.E) : LinearMap.ker (phiC S β γ0) = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 fun Q hQ => ?_
  have h1 : evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q = 0 :=
    LinearMap.ker_eq_bot'.1 (trN_inj D i hi γ0) _ hQ
  exact evInj_pf (J := gramN D i hi) (embT D) (Hc S β) (S.loc β) S.pos Q h1

def VtupDesc (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  ∀ β (Q : YR (Hc S β) D.what₂.LL), MvPolynomial.map e Q ∈ (Hc S β).P.Vtup → MvPolynomial.map D.what₂.embLL Q ∈ VtupR (Hc S β).P ℂ

def EvValLe (S : StepIn M i hi G) (β : S.Ch) : Prop :=
  ∀ Q ∈ VtupR (Hc S β).P ℂ,
    evC (Hc S β).P (S.loc β).rk S.pos (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B) Q ∈
      Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i)

def CmpInvOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (phiC S β γ0 (MvPolynomial.map D.what₂.embLL Q))

theorem phiC_mem_ValC (S : StepIn M i hi G) (β : S.Ch) (hV : EvValLe S β) (γ0 : GL (Fin (D.R.N i)) D.host.E)
    {Q : XR (Hc S β).P ℂ} (hQ : Q ∈ VtupR (Hc S β).P ℂ) :
    phiC S β γ0 Q ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (lamTG M i) := by
  have h1 := foValC_tr (M.lam i) (Formalism.L2.Forms.atInf (embT D) γ0.1) (foInf_unit (embT D) γ0) (hV Q hQ)
  have h2 := (mem_ValC_shW (D.R.N_pos i) (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) (M.lam i) (cTw D i) 1 one_ne_zero
    (phiC S β γ0 Q)).2
  refine h2 ?_
  convert h1 using 1
  funext z
  change 1 * detF (cTw D i) z * ((detF (cTw D i) z)⁻¹ * _) = _
  rw [one_mul, ← mul_assoc, mul_inv_cancel₀ (detF_ne _ _), one_mul]
  rfl

theorem cmpLiftOf_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hD : VtupDesc S e) (hV : ∀ β, EvValLe S β)
    (hI : CmpInvOf S e) : CmpLiftOf S e := by
  intro hS H X β rep hok c
  obtain ⟨g, γ0, κ0, hγ0, hL, hpt⟩ := hok c
  let Y := YInv (Hc S β) e (rep c).1 (rep c).2
  let Φ : Y →+ (Formalism.L2.Forms.Frames (Formalism.L2.Forms.gramC (gramN D i hi) (embT D)) → ℂ) :=
    (phiC S β γ0).toAddMonoidHom.comp ((MvPolynomial.map D.what₂.embLL).toAddMonoidHom.comp Y.subtype.toAddMonoidHom)
  refine ⟨Φ, fun Q => ⟨?_, ?_⟩, fun k Q hQ => ?_⟩
  · exact phiC_mem_ValC S β (hV β) γ0 (hD β Q.1 Q.2.1)
  · exact hI hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q.1 Q.2
  · have a : LinearIndependent D.what₂.LL (fun j => (Q j : YR (Hc S β) D.what₂.LL)) :=
      hQ.map' Y.subtype (Submodule.ker_subtype _)
    have b := Formalism.MainNotions.G.SymmetricFormBlocks.li_map D.what₂.embLL _ a
    exact b.map' (phiC S β γ0) (ker_phiC S β γ0)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLift
