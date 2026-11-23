import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

open NumberField in

theorem _root_.GlobalTheory.FlagDim.card_pairs_lt (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  have e : {p : Fin n × Fin n // p.1 < p.2} ≃ (j : Fin n) × Fin j :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2, q.2.2.trans q.1.2⟩, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

open NumberField in

theorem _root_.GlobalTheory.FlagDim.dim_add_card_flagVar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), Dw.dim + Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have hcard : Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = ∑ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 := by
    show Nat.card ((τ : E →+* ℂ) × {p : Fin (Dw.mult τ) × Fin (Dw.mult τ) // p.1 < p.2}) = _
    rw [Nat.card_sigma]
    simp only [_root_.GlobalTheory.FlagDim.card_pairs_lt]
  have hdim : Dw.dim = Module.finrank ℚ E / 2 * Dw.p * Dw.q := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim; rfl
  have hall : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := Embeddings.card E ℂ
  have hcm : (Finset.univ.filter fun τ : E →+* ℂ => τ H.rt = H.rt0).card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, _root_.GlobalTheory.PeriodCoord.card_cmType]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ : E →+* ℂ => τ H.rt = H.rt0)
  obtain ⟨k, hk⟩ : Even (Module.finrank ℚ E) := by
    rw [IsTotallyComplex.finrank]; exact even_two_mul _
  rw [Finset.card_univ, hall] at hsplit
  have hk2 : Module.finrank ℚ E / 2 = k := by omega
  have hnot : (Finset.univ.filter fun τ : E →+* ℂ => ¬ τ H.rt = H.rt0).card = k := by omega
  have hterm : ∀ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 =
      if τ H.rt = H.rt0 then Dw.p * (Dw.p - 1) / 2 else Dw.q * (Dw.q - 1) / 2 := by
    intro τ; unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult; split_ifs <;> rfl
  rw [hcard, hdim, Finset.sum_congr rfl (fun τ _ => hterm τ), Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hcm, hnot, hk2]
  ring

end GlobalTheory.FlagDim
