import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

theorem UpperTheory.V.FW.sinMap :
    ∀ (k A B ι : Type) [CommRing k] [AddCommGroup A] [AddCommGroup B] [Fintype ι] [DecidableEq ι] (φ : A →+ B) (η : ι → A) (N : ℕ) (P : ℕ → k), AddMonoidAlgebra.mapDomainRingHom k φ (sinE η N P) = sinE (fun i => φ (η i)) N P := by
  intro k A B ι _ _ _ _ _ φ η N P
  unfold sinE
  simp only [map_sum, map_mul, map_prod, map_sub, map_one, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, map_nsmul]
