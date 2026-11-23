import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore

theorem mulPow_mulVar {K : Type} [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ}
    (h : j + (a + 1) = l) (h' : (j + 1) + a = l) (α : MonoDeg (Fin G.D) a) (i : Fin G.D) (m : G.Sec j) :
    mulPow G s h (MonoDeg.mulVar i α) m = mulPow G s h' α (G.mulW j (s i) m) := by
  rw [G.mulW_apply]
  unfold mulPow
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, monoVal_mulVar, mul_comm (secGer _ _ _ _ _), mul_assoc]

theorem filMono_of_kerRes : KerRes → FilMono := by
  intro H K _ _ G hnef hbig s hs a
  induction a with
  | zero =>
    intro j l h _ f hf
    obtain rfl : j = l := h
    have : Subsingleton (MonoDeg (Fin G.D) 0) := ⟨fun α β => Subtype.ext
      (((Finsupp.degree_eq_zero_iff _).1 α.2).trans ((Finsupp.degree_eq_zero_iff _).1 β.2).symm)⟩
    refine ⟨fun _ => f, fun _ => hf.1, ?_⟩
    rw [Fintype.sum_subsingleton _ (⟨0, rfl⟩ : MonoDeg (Fin G.D) 0)]
    exact (mulMono_zero _ _ _ _ _ f).symm
  | succ a ih =>
    classical
    intro j l h hj f hf
    have h' : (j + 1) + a = l := by omega
    have hfa : f ∈ Fil (G.ideal s) a (G.global l) := Fil_anti (Nat.le_succ a) hf
    obtain ⟨m, hm, e⟩ := ih (j + 1) l h' (by omega) f hfa
    have h0 : hs.sym h' (G.global l) ⟨f, hfa⟩ = 0 := (sym_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _).2 hf
    have h1 : hs.sym h' (G.global l) ⟨f, hfa⟩ = fun α => hs.res (j + 1) (m α) :=
      sym_sum _ _ _ _ _ _ _ _ _ _ m _ e
    have hv : ∀ α, m α ∈ Fil (G.ideal s) 1 (G.global (j + 1)) := fun α =>
      ⟨hm α, (Res_eq_zero_iff _ _ _ _ _ _ _ _ _ _).1 (congrFun (h1.symm.trans h0) α)⟩
    choose m' hm' e' using fun α => H K G hnef hbig s hs j (by omega) (m α) (hv α)
    refine ⟨fun γ => ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
      m' p.1 p.2, fun γ => sum_mem fun p _ => hm' _ _, ?_⟩
    have key : ∀ γ : MonoDeg (Fin G.D) (a + 1), mulPow G s h γ
        (∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ), m' p.1 p.2) =
        ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
          mulPow G s h' p.1 (G.mulW j (s p.2) (m' p.1 p.2)) := fun γ => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Finset.mem_filter.1 hp).2, mulPow_mulVar G s h h']
    rw [Finset.sum_congr rfl fun γ _ => key γ, Finset.sum_fiberwise, Fintype.sum_prod_type, e]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [e' α, map_sum]

end GlobalTheory.HSCore
