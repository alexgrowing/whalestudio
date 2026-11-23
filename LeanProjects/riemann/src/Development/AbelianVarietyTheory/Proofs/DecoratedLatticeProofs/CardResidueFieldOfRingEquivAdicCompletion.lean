import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard

open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory.LocalResidue

theorem card_residue_of_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → Nat.card 𝓀[k] = Ideal.absNorm v.asIdeal := by
  intro F _ _ v k _ _ _ _ φ hφ
  let ψ : 𝒪[k] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun a => ⟨φ a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((hφ a).2 a.2)⟩
      invFun := fun b => ⟨φ.symm b, (hφ _).1 (by
        rw [RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (φ.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (φ.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : k) (b : k))
      map_add' := fun a b => Subtype.ext (map_add φ (a : k) (b : k)) }
  have e := IsLocalRing.ResidueField.mapEquiv ψ
  have hF : ∀ s : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  have hc := GlobalTheory.SplitUnif.card_residueField v (algebraMap F (v.adicCompletion F)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  rw [Nat.card_congr e.toEquiv, hc]

end GlobalTheory.LocalResidue
