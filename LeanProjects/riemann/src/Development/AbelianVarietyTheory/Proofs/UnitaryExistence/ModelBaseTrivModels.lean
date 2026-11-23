import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OpenRowsFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ModelFamilies

noncomputable section

namespace GlobalTheory.PeriodRowsCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem isTypeFn_letters (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := fun τ => by
    have hval : relab c σ τ (H.rt : E) = σ ⟨τ (H.rt : E), c.conj τ _⟩ := rfl
    rw [hval]
    refine ⟨fun h => congrArg Subtype.val (σ.injective (h.trans hσ0.symm)), fun h => ?_⟩
    exact (congrArg σ (Subtype.ext h)).trans hσ0
  intro τ
  obtain ⟨τ₀, rfl⟩ := Finite.injective_iff_surjective.1 hinj τ
  have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
    have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
      Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
    have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    rw [Nat.card_congr (e1.trans (e2.trans (Equiv.sigmaSubtype τ₀))), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    exact if_pos ((hrel τ₀).1 h)
  · rw [hcard]
    exact if_neg (fun h' => h ((hrel τ₀).2 h'))

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e} {r : ℕ}

def modelsEquiv (F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e) (r : ℕ) :
    Rows.ModelsOf F r ≃ GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.ModelsOf F r where
  toFun M := ⟨M.X, M.φ⟩
  invFun M := ⟨M.X, M.φ⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem modelsEquiv_φ (M : Rows.ModelsOf F r) : (modelsEquiv F r M).φ = M.φ := rfl

def trivChar (X : Data E r) : Data E r :=
  { X with
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (one_mul 1).symm
    χ_add := fun _ _ _ _ => (one_mul 1).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩ }

def trivModels (M : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.ModelsOf F r) : Rows.ModelsOf F r :=
  ⟨fun k => trivChar (M.X k), M.φ⟩

end GlobalTheory.PeriodRowsCompare
