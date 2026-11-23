import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardClDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.levelRk :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n r : ℕ), 2 ≤ n → Nat.card (ClassGroup (𝓞 (Fn F Ω l n)) ⧸ (powMonoidHom l : ClassGroup (𝓞 (Fn F Ω l n)) →* ClassGroup (𝓞 (Fn F Ω l n))).range) ≤ l ^ r → XRk l 1 (Un F Ω l n) r := by
  intro F Ω _ _ _ _ _ l _ n r hn hc
  haveI := (fnCyc F Ω l n).1
  have htop : galOf F F Ω = ⊤ := by
    refine eq_top_iff.2 fun σ _ => ?_
    intro x
    exact σ.commutes x
  have hU : Un F Ω l n = galOf F (Fn F Ω l n) Ω := by
    unfold Un
    rw [galOfCyc F Ω l n F (Fn F Ω l n), htop]
  have hmap := pullOnto F Ω (Fn F Ω l n) (Un F Ω l n) hU.le 1 (ZMod l) (ZMod l) one_ne_zero hU.ge
    (Or.inl ((fnCyc F Ω l n).2.2 hn))
  obtain ⟨hfin, hcard⟩ := cardClDual (Fn F Ω l n) l 1
  unfold XRk CardLe
  rw [← hmap]
  have hsurj := LinearMap.submoduleMap_surjective (clPull (Fn F Ω l n) hU.le (ZMod l) (ZMod l)) (ClDual (Fn F Ω l n) 1 (ZMod l) (ZMod l))
  exact ⟨Finite.of_surjective _ hsurj, (Nat.card_le_card_of_surjective _ hsurj).trans (hcard.trans hc)⟩
