import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StatementsBasicOpen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.StatementsUnbranched
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.BasicOpenSteps
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

theorem IrreducibleBasicOpenConnected.fin (hU : UnbranchedPartConnected.Statement) (n : ℕ)
    (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin n) ℂ) (hW : W.IsPrime) (hg : g ∉ W) :
    IsPreconnected (ComplexSets.zeroSet W \ {x : Fin n → ℂ | eval x g = 0}) := by
  obtain ⟨d, hd⟩ := IrreducibleBasicOpenConnected.exists_dim hW
  obtain ⟨A, hA⟩ := ComplexSets.LinearNoetherNormalization.proof n d W hd
  obtain ⟨P, hP, hconn⟩ := hU n d W A hW hd hA
  obtain ⟨Q, hQ, hQg⟩ := IrreducibleBasicOpenConnected.exists_base_vanishing hW hA hg
  refine (hconn Q hQ).subset_closure ?_ ?_
  · rintro x ⟨hxW, hx⟩
    refine ⟨hxW, fun hgx => hx ?_⟩
    rw [map_mul, hQg x hxW hgx, mul_zero]
  · exact fun x hx =>
      IrreducibleBasicOpenConnected.zeroSet_subset_closure hW hA (mul_ne_zero hP hQ) hx.1

theorem IrreducibleBasicOpenConnected.proof (hU : UnbranchedPartConnected.Statement) :
    IrreducibleBasicOpenConnected.Statement := by
  intro σ _ W g hW hg
  obtain ⟨e⟩ : Nonempty (σ ≃ Fin (Fintype.card σ)) := ⟨Fintype.equivFin σ⟩
  set φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin (Fintype.card σ)) ℂ := renameEquiv ℂ e with hφ
  have hev : ∀ (y : Fin (Fintype.card σ) → ℂ) (p : MvPolynomial σ ℂ), eval y (φ p) = eval (y ∘ e) p :=
    fun y p => eval_rename (⇑e) y p
  have hcomp : ∀ x : σ → ℂ, (x ∘ e.symm) ∘ e = x := fun x => by funext i; simp
  have hW' : (W.map φ).IsPrime := Ideal.map_isPrime_of_equiv φ
  have hg' : φ g ∉ W.map φ := by
    rw [Ideal.mem_map_of_equiv]
    rintro ⟨p, hp, hpg⟩
    exact hg (φ.injective hpg ▸ hp)
  have heq : zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0} =
      (fun y : Fin (Fintype.card σ) → ℂ => y ∘ e) ''
        (ComplexSets.zeroSet (W.map φ) \ {x | eval x (φ g) = 0}) := by
    ext x
    constructor
    · rintro ⟨hxW, hxg⟩
      refine ⟨x ∘ e.symm, ⟨fun q hq => ?_, fun h => hxg ?_⟩, hcomp x⟩
      · obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_of_equiv φ q).mp hq
        rw [hev, hcomp]
        exact mem_zeroLocus_iff.mp hxW p hp
      · show eval x g = 0
        rw [← hcomp x, ← hev]
        exact h
    · rintro ⟨y, ⟨hyW, hyg⟩, rfl⟩
      refine ⟨mem_zeroLocus_iff.mpr fun p hp => ?_, fun h => hyg ?_⟩
      · show eval (y ∘ e) p = 0
        rw [← hev]
        exact hyW _ (Ideal.mem_map_of_mem φ hp)
      · show eval y (φ g) = 0
        rw [hev]
        exact h
  rw [heq]
  exact (IrreducibleBasicOpenConnected.fin hU _ (W.map φ) (φ g) hW' hg').image _
    (continuous_pi fun i => continuous_apply (e i)).continuousOn

end GroundTheory.Heights₂.Heights.HilbertSamuel
