import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical

noncomputable section

namespace GlobalTheory.RootWeight

theorem wtOf_rootLetter {D : D7} (O : Setup D) (la : D.what₂.Tau → Fin O.N → ℤ) (x : DV.Rt D.what₂.Tau O.N) :
    (GlobalTheory.AllWt.wtOf O.S.Dw (O.S.wt O.L la) 0).1
                 ((GlobalTheory.RootSum.rootLetter O.S x).1, ((GlobalTheory.RootSum.rootLetter O.S x).2 : ℕ)) =
      (if (x.2 : ℕ) < O.S.Dw.p then 1 else -1 : ℤ) * la x.1 x.2 := by
  rw [GlobalTheory.RootSum.rootLetter_key]
  have hr := O.S.rank_eq
  have hx := x.2.2
  by_cases h : (x.2 : ℕ) < O.S.Dw.p
  · rw [if_pos h, if_pos h]
    have e := GlobalTheory.AllWt.wtOf_big (O.S.wt O.L la) 0 (O.L.ψ x.1) x.2 h
    rw [O.L.ψ_val] at e
    rw [e]
    simp [GlobalTheory.ShFam.Sig.wt]
  · rw [if_neg h, if_neg h]
    have hi : O.S.Dw.p + O.S.Dw.q - 1 - (x.2 : ℕ) < O.S.Dw.q := by omega
    have e := GlobalTheory.AllWt.wtOf_small (O.S.wt O.L la) 0 (O.L.ψ x.1) _ hi
    rw [O.L.ψ_val] at e
    rw [e]
    simp only [GlobalTheory.ShFam.Sig.wt, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply, sub_zero]
    have : (Fin.cast O.S.rank_eq ⟨O.S.Dw.p + (O.S.Dw.q - 1 - (O.S.Dw.p + O.S.Dw.q - 1 - (x.2 : ℕ))), by omega⟩ : Fin O.N)
        = x.2 := Fin.ext (by simp only [Fin.coe_cast]; omega)
    rw [this]
    ring

theorem sum_neg_smul_divOf_ex_eq_Lw : ∀ {D : D7} (O : Setup D) (c : O.s.Comp) (la : D.what₂.Tau → Fin O.N → ℤ),
    ∑ x : DV.Rt D.what₂.Tau O.N, (-la x.1 x.2) • GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x) = O.s.Lw O.L O.Φ c la := by
  intro D O c la
  have hR : O.s.Lw O.L O.Φ c la = -∑ l : GlobalTheory.ShFam.Pad.Letter O.S.Dw,
      (GlobalTheory.AllWt.wtOf O.S.Dw (O.S.wt O.L la) 0).1 (l.1, (l.2 : ℕ)) • (O.Φ.C c).gr l.1 l.2 := rfl
  rw [hR, ← Fintype.sum_bijective (GlobalTheory.RootSum.rootLetter O.S) (GlobalTheory.RootSum.rootLetter_bijective O.S)
    (fun x => (GlobalTheory.AllWt.wtOf O.S.Dw (O.S.wt O.L la) 0).1
        ((GlobalTheory.RootSum.rootLetter O.S x).1, ((GlobalTheory.RootSum.rootLetter O.S x).2 : ℕ)) •
      (O.Φ.C c).gr (GlobalTheory.RootSum.rootLetter O.S x).1 (GlobalTheory.RootSum.rootLetter O.S x).2)
    (fun l : GlobalTheory.ShFam.Pad.Letter O.S.Dw =>
      (GlobalTheory.AllWt.wtOf O.S.Dw (O.S.wt O.L la) 0).1 (l.1, (l.2 : ℕ)) • (O.Φ.C c).gr l.1 l.2) (fun _ => rfl),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hL : GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x) = _ := GlobalTheory.RootSum.divOf_root O.S O.Φ c x
  rw [hL, wtOf_rootLetter, smul_smul, ← neg_smul]
  congr 1
  ring

end GlobalTheory.RootWeight
