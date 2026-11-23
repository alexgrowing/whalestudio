import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.FSurj

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem rF_surj : ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K]
    {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u)
    {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)],
    (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) →
    RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh →
    Function.Surjective (algebraMap Bh (FractionRing x.A)) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hcomp hker z
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors x.A) z
  obtain ⟨a', rfl⟩ := (f_surj P).1 a
  obtain ⟨b', hb'⟩ := (f_surj P).1 (b : x.A)
  have hu : IsUnit (algebraMap B Bh b') := by
    by_contra hn
    have hm : algebraMap B Bh b' ∈ maximalIdeal Bh := (mem_maximalIdeal _).2 hn
    rw [← hker, RingHom.mem_ker, hcomp, hb'] at hm
    exact nonZeroDivisors.coe_ne_zero b
      ((IsFractionRing.injective x.A (FractionRing x.A)) (hm.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ := hu
  refine ⟨algebraMap B Bh a' * ↑v⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hb', ← hcomp, ← hv, ← map_mul, mul_assoc,
    Units.inv_mul, mul_one, hcomp]

end UpperTheory.V.Pa
