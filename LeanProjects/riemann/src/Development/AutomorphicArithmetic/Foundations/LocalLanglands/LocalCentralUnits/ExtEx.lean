import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlaceStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx

open NumberField IsDedekindDomain

theorem UpperTheory.Zero.LLC.extEx :
    UpperTheory.Zero.LLC.ExtEx := by
  intro E Ω _ _ _ _ _ A w h g _ i hi n hn
  obtain ⟨E', fE, nE, _, aE, aΩ, tE, cE, w', h', hg, unr, card, _, _⟩ :=
    GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots E Ω g A w h i hi n hn
  obtain ⟨a', ha', _⟩ := UpperTheory.Zero.LLC.artEx E' Ω A w' h'
  haveI : w'.asIdeal.IsMaximal := w'.isMaximal
  letI : Field (𝓞 E' ⧸ w'.asIdeal) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E' ⧸ w'.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : Nat.Prime g)]
    rw [← map_natCast (Ideal.Quotient.mk w'.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  letI : Algebra (ZMod g) (𝓞 E' ⧸ w'.asIdeal) := ZMod.algebra _ g
  exact ⟨UpperTheory.Zero.LLC.Ext.mk E' w' h' unr card a' ha' (𝓞 E' ⧸ w'.asIdeal)
    (Ideal.Quotient.mk w'.asIdeal) Ideal.Quotient.mk_surjective (Ideal.mk_ker)⟩
