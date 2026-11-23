import Mathlib

open NumberField NumberField.IsCMField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

section Residue

variable {K : Type*} [Field K] [NumberField K]

noncomputable abbrev locAt (P : Ideal (𝓞 K)) [P.IsMaximal] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors

noncomputable def residueHom (P : Ideal (𝓞 K)) [P.IsMaximal] : locAt P →+* 𝓞 K ⧸ P :=
  IsLocalization.lift (M := P.primeCompl) (g := Ideal.Quotient.mk P) (fun y => by
    let _ := Ideal.Quotient.field P
    exact isUnit_iff_ne_zero.mpr (fun h => y.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)))

noncomputable def residueUnit (P : Ideal (𝓞 K)) [P.IsMaximal] : (locAt P)ˣ →* (𝓞 K ⧸ P)ˣ :=
  Units.map (residueHom P).toMonoidHom

def IsResidue (P : Ideal (𝓞 K)) (x : K) (r : 𝓞 K ⧸ P) : Prop :=
  ∃ a b : 𝓞 K, b ∉ P ∧ x * (b : K) = (a : K) ∧
    r * Ideal.Quotient.mk P b = Ideal.Quotient.mk P a

example (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (a : 𝓞 K) :
    IsResidue P (a : K) (Ideal.Quotient.mk P a) :=
  ⟨a, 1, (Ideal.ne_top_iff_one P).mp hP.ne_top, by simp, by simp⟩

end Residue

section CM

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

abbrev IdealGroup := (FractionalIdeal (𝓞 K)⁰ K)ˣ

noncomputable def fromBase : Subgroup (IdealGroup K) :=
  (Units.map (FractionalIdeal.extendedHom K (𝓞 K) :
    FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K) →+*
      FractionalIdeal (𝓞 K)⁰ K).toMonoidHom).range

variable {K}

noncomputable def conjPrime (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  v.comap (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
    (ringOfIntegersComplexConj K).surjective

noncomputable def primeTo (v : HeightOneSpectrum (𝓞 K)) : Subgroup (IdealGroup K) where
  carrier := {I | FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 ∧
    FractionalIdeal.count K (conjPrime v) (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' := by simp [FractionalIdeal.count_one]
  mul_mem' := by
    rintro I J ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Set.mem_ofPred_eq, Units.val_mul]
    rw [FractionalIdeal.count_mul K _ I.ne_zero J.ne_zero,
      FractionalIdeal.count_mul K _ I.ne_zero J.ne_zero, h1, h2, h3, h4]
    simp
  inv_mem' := by
    rintro I ⟨h1, h2⟩
    simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val]
    rw [FractionalIdeal.count_inv, FractionalIdeal.count_inv, h1, h2]
    simp

def IsDecomp {ι : Type*} [Fintype ι] (h : ℕ) (aa : ι → IdealGroup K) (A : IdealGroup K)
    (α : Kˣ) : Prop :=
  ∃ n : ι → ℤ, ∃ b ∈ fromBase K, A ^ h = (∏ i, aa i ^ n i) * toPrincipalIdeal (𝓞 K) K α * b

variable (K) in

structure MinusBasis (l : ℕ) (ι : Type*) [Fintype ι] where
  h : ℕ
  h_coprime : h.Coprime l
  aa : ι → IdealGroup K
  o : ι → ℕ
  o_pow : ∀ i, ∃ k, o i = l ^ k
  al : ι → Kˣ
  rel : ∀ i, ∃ b ∈ fromBase K, aa i ^ o i = toPrincipalIdeal (𝓞 K) K (al i) * b
  span : ∀ A : IdealGroup K, ∃ α, IsDecomp h aa A α
  indep : ∀ (n : ι → ℤ) (α : Kˣ), ∀ b ∈ fromBase K,
    ∏ i, aa i ^ n i = toPrincipalIdeal (𝓞 K) K α * b → ∀ i, (o i : ℤ) ∣ n i

def IsDel {l : ℕ} {ι : Type*} [Fintype ι] (B : MinusBasis K l ι) (v : HeightOneSpectrum (𝓞 K))
    {N : ℕ} (om : (𝓞 K ⧸ v.asIdeal)ˣ →* Multiplicative (ZMod N))
    (del : primeTo v →* Multiplicative (ZMod N)) : Prop :=
  ∀ (A : primeTo v) (α : Kˣ), IsDecomp B.h B.aa (A : IdealGroup K) α →
    ∀ u : (locAt v.asIdeal)ˣ, ((u : locAt v.asIdeal) : K) = (α : K) / complexConj K (α : K) →
      del A ^ B.h = om (residueUnit v.asIdeal u)

end CM

end KStar.IdealValuations
