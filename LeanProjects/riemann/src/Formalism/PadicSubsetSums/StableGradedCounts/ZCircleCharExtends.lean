import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

namespace Formalism.IrreducibleCountingLemmas.Z

theorem circle_pow_surjective {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Circle => a ^ n) := by
  intro z
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  refine ⟨Circle.exp (θ / n), ?_⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  show Circle.exp (θ / n) ^ n = Circle.exp θ
  rw [← Circle.exp_zsmul, zsmul_eq_mul, mul_div_cancel₀ _ hn']

theorem circle_character_extends : CircleCharExtends := by
  intro A _ H χ
  have : DivisibleBy (Additive Circle) ℤ :=
    divisibleByOfSMulRightSurj (Additive Circle) ℤ fun {n} hn a => by
      obtain ⟨b, hb⟩ := circle_pow_surjective hn a.toMul
      exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) (fun a b hab => by
      have : (a.toMul : A) = (b.toMul : A) := congrArg Additive.toMul hab
      exact congrArg Additive.ofMul (Subtype.ext this))
    (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm ψ, fun h => ?_⟩
  have := DFunLike.congr_fun hψ (Additive.ofMul h)
  exact congrArg Additive.toMul this

end Formalism.IrreducibleCountingLemmas.Z
