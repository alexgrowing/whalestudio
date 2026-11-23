import Mathlib
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
open MvPolynomial

noncomputable section
namespace GlobalTheory.FockMinorFunctional
open Formalism.L2.DIV

theorem map_int_eq_map_rat {σ K : Type} [Field K] [CharZero K] (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom K) f = map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f) := by
  have e : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := RingHom.ext_int _ _
  rw [map_map, e]

theorem nablaX_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    WeylLatticeDuality.nablaX N nu J = Formalism.BasicNotions.KM.nablaX N nu J := by
  unfold WeylLatticeDuality.nablaX Formalism.BasicNotions.KM.nablaX
  rfl

theorem colProd_map {K : Type} [Field K] [CharZero K] (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N)
    (J : ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) :
    GlobalTheory.WeylMinorDual.colProd K N Y hY J =
      map (algebraMap ℚ K) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) := by
  rw [← map_int_eq_map_rat]
  unfold GlobalTheory.WeylMinorDual.colProd
  rw [fk_map_bidet]

theorem aeval_map_nablaX {K Lt : Type} [Field K] [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : ∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N) :
    aeval (R := K) (fun v : Lt × ℕ × Fin N =>
        if h : v.2.1 < N then (X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin N)) : Pol K Lt N) else 0)
      (map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J)) =
      ten fun s => GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s) := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap, nablaX_eq]
  exact GlobalTheory.WeylMinorDual.aeval_nablaX N nu hY J

theorem fock_functional_nablaX : ∀ (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (g : Lt → MvPolynomial (Fin N × Fin N) ℤ),
    ∃ Ψ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      ∀ J : (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N),
        Ψ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
          ∏ s, ((Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) (g s))
            (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N (nu s) (hY s) (J s))) : ℚ) : ℂ_[p]) := by
  intro p _ Lt _ _ N nu hY g
  let ρ : Lt × ℕ × Fin N → Pol ℂ_[p] Lt N := fun v =>
    if h : v.2.1 < N then X (v.1, v.2.2, (⟨v.2.1, h⟩ : Fin N)) else 0
  let G : Pol ℂ_[p] Lt N := ten fun s => map (Int.castRingHom ℂ_[p]) (g s)
  refine ⟨(fockBL G).comp (aeval ρ).toLinearMap, fun J => ?_⟩
  have h1 : aeval ρ (map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J)) =
      ten fun s => GlobalTheory.WeylMinorDual.colProd ℂ_[p] N (nu s) (hY s) (J s) := by
    exact aeval_map_nablaX N nu hY J
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, h1, fockBL_apply, GlobalTheory.WeylMinorDual.fockB_ten]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_int_eq_map_rat, colProd_map, GlobalTheory.WeylMinorDual.fockB_map]
end GlobalTheory.FockMinorFunctional
