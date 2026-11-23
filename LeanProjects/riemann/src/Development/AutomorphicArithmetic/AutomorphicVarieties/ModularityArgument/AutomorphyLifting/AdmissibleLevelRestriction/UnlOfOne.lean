import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SplitIrr

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.GalN.V
open UpperTheory.V UpperTheory.V.Z.Win
open scoped Pointwise

namespace UpperTheory.V.Z.Win.A4

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private def conjDec (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) :
    ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem conjDec_coe (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) (u : ↥(Dec (F := F) B)) :
    ((conjDec A B γ h u : ↥(Dec (F := F) A)) : G F Ω) = γ⁻¹ * u * γ := rfl

private theorem conjDec_surj (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) (s : ↥(Dec (F := F) A)) :
    ∃ u, conjDec A B γ h u = s := by
  refine ⟨⟨γ * s * γ⁻¹, ?_⟩, ?_⟩
  · rw [mem_Dec, ← h, mul_smul, mul_smul, inv_smul_smul, mem_Dec.1 s.2]
  · apply Subtype.ext
    rw [conjDec_coe]
    simp [mul_assoc]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (f : Γ →* C) (γ s : Γ) :
    f (γ⁻¹ * s * γ) = f s := by
  rw [map_mul, map_mul, map_inv, mul_comm (f γ)⁻¹ (f s), inv_mul_cancel_right]

private theorem flag_conj {r : G F Ω →* GL (Fin n) (Qbar l)} {A B : ValuationSubring Ω} {γ : G F Ω} (h : γ • A = B)
    {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : IsFlagOn r (Dec (F := F) A) κ) :
    IsFlagOn r (Dec (F := F) B) fun i => (κ i).comp (conjDec A B γ h) := by
  obtain ⟨g, hg⟩ := hκ
  refine ⟨g * r γ⁻¹, fun u => ?_⟩
  have key : g * r γ⁻¹ * r ↑u * (g * r γ⁻¹)⁻¹ = g * r ↑(conjDec A B γ h u) * g⁻¹ := by
    rw [conjDec_coe, map_mul, map_mul, map_inv]
    group
  rw [key]
  exact hg (conjDec A B γ h u)

end UpperTheory.V.Z.Win.A4

open UpperTheory.V.Z.Win.A4 in
theorem UpperTheory.V.Z.Win.A4.unlOfOne :
    UnlOfOne := by
  intro F Ω _ _ _ _ _ l _ n r v A hA κ hκ hne B hB
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  refine ⟨fun i => (κ i).comp (conjDec A B γ hγ), flag_conj hγ hκ, fun i j e => hne i j ?_⟩
  refine MonoidHom.ext fun s => ?_
  obtain ⟨u, rfl⟩ := conjDec_surj A B γ hγ s
  have e1 := DFunLike.congr_fun e u
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at e1 ⊢
  rw [e1, conjDec_coe, char_conj]
