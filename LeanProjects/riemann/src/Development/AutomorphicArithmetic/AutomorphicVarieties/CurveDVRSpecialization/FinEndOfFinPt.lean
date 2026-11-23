import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.V.Pr.finEnd_of_finPt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    FinPt O Φ 3 → FinEnd l η Ψ σ g₁ B := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ hok hl hσ hF
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  have hidx : (Base.galOf ℚ L Ω).index = Module.finrank ℚ L := (Base.galEmbTop ℚ L Ω).2.2
  refine ⟨Base.galOf ℚ L Ω, ⟨by rw [hidx]; exact Module.finrank_pos.ne'⟩, ?_⟩
  intro A _ _ _ h0 r hr g hg _
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  let f : ResidueField O →+* A := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O A) h0
  have hf : ∀ a : O, f (residue O a) = algebraMap O A a := fun a => rfl
  letI : Algebra (ResidueField O) A := f.toAlgebra
  haveI : IsScalarTower O (ResidueField O) A := IsScalarTower.of_algebraMap_eq fun a => (hf a).symm
  obtain ⟨ρ, h1, h2, h3⟩ := exists_nrep3 k hok hl hσ r hr
  have hpow : ∀ (s : G ℚ Ω) (n : ℤ), algebraMap O A ((Ψ s ^ n : Oˣ) : O) =
      f ((barChar O Ψ s ^ n : (ResidueField O)ˣ) : ResidueField O) := by
    intro s n
    rw [← hf]
    congr 1
    exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ s) n)
  have key := hF A ρ h1 (by
    intro v i g hg h
    apply Units.ext
    rw [h3 v i g hg, UnitaryThreeInertia.psi, hpow]
    rw [k.j_loc, k.psi] at h
    rw [h]; simp)
  obtain ⟨s, rfl⟩ : ∃ s, Base.galEmb ℚ L Ω s = g := (Base.range_galEmb ℚ L Ω).ge hg
  rw [← h2, key]
  have : ((r0 η Ψ (Base.galEmb ℚ L Ω s)).mat).map (algebraMap O A) = Matrix.diagonal fun i =>
      algebraMap O A ((Ψ (Base.galEmb ℚ L Ω s) ^ wt1 i : Oˣ) : O) := by
    rw [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _)]
  rw [this, Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hpow]
  have h5 : Φ.Ψ (k.p0 s) = barChar O Ψ (Base.galEmb ℚ L Ω s) := k.psi _
  have h6 : Fr.w 3 i = wt1 i := by fin_cases i <;> rfl
  rw [h5, h6]
  rfl
