import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SqrtFlip
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SelfAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.ConjEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PrimCj

noncomputable section

namespace UpperTheory.V.Z.Sym.Unl

theorem goodHalf : GoodHalf := by
  intro k N _ hk χ hχ g hg p hp hpN α β hs hm
  obtain ⟨σ, hσ⟩ := sqrtFlip p hp
  obtain ⟨g', hg'⟩ := conjEig k N χ g hg σ
  have hu : IsUnit ((p : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  have h1 : ‖χ (p : ZMod N)‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one χ hu.unit
    simpa using this
  have e : cj σ χ (p : ZMod N) = σ (χ (p : ZMod N)) := rfl
  have h2 : ‖σ (χ (p : ZMod N))‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one (cj σ χ) hu.unit
    rw [IsUnit.unit_spec, e] at this
    exact this
  have a1 := selfAdj k N hk χ hχ g p hp hpN
  have a2 := selfAdj k N hk (cj σ χ) (primCj N χ σ hχ) g' p hp hpN
  rw [hg' p hp.one_lt.le, e] at a2
  exact halfAlg p (k - 1) (g.a p) (χ (p : ZMod N)) α β σ hp.two_le h1 h2 hσ a1 a2 hs hm

end UpperTheory.V.Z.Sym.Unl
