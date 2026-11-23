import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LcountNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SignLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem inv_norm {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K} (L : IsLoc O Δ)
    {c : K} {d m : EL Δ τ} (h : IsDat c d m) : ∀ t ∈ NE τ, ∀ x : Kˣ,
    lcount O c d (((t * x : Kˣ) : K) • m) = lcount O c d ((x : K) • m) := fun t ht x => by
  rw [Units.val_mul, mul_smul]
  exact lcountNorm O K Δ τ L c d _ (datSmul K Δ τ c d m h x) t ht

theorem UpperTheory.V.Z.Sym.Loc.kapMove : UpperTheory.V.Z.Sym.Loc.KapMove := by
  intro O K _ _ _ _ _ Δ τ L hr c hc z hz lam lam' hn hn' htr htr'
  have h2 : (2 + τ : K) ≠ 0 := by
    intro h0
    apply hr
    have : τ = -2 := by linear_combination h0
    rw [this]
    norm_num
  obtain ⟨ul, hul⟩ : IsUnit lam :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by rw [hn]; exact h2.isUnit)
  have hβ : QuadraticAlgebra.norm (lam' * ((ul⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ)) = 1 := by
    have e : QuadraticAlgebra.norm (ul : Lsq K Δ) *
        QuadraticAlgebra.norm ((ul⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hul, hn] at e
    rw [map_mul, hn', e]
  obtain ⟨y, hy⟩ := h90L O K Δ L _ hβ
  have hl' : lam' = lam * star (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := by
    rw [hy, ← hul]
    have e1 : (ul : Lsq K Δ) * ((ul⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = 1 := Units.mul_inv ul
    have e2 : (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) = 1 := Units.mul_inv y
    linear_combination (-lam' * ((y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ))) * e1 + (-lam') * e2
  set Y : (EL Δ τ)ˣ := Units.map (algebraMap (Lsq K Δ) (EL Δ τ)).toMonoidHom y with hYdef
  have hsig : ∀ a : Lsq K Δ, sigL (algebraMap (Lsq K Δ) (EL Δ τ) a) =
      algebraMap (Lsq K Δ) (EL Δ τ) (star a) := by
    intro a
    ext <;> simp [sigL]
  have hstar : ∀ a : Lsq K Δ, star (algebraMap (Lsq K Δ) (EL Δ τ) a) =
      algebraMap (Lsq K Δ) (EL Δ τ) a := by
    intro a
    ext <;> simp
  have hYc : (Y : EL Δ τ) = algebraMap (Lsq K Δ) (EL Δ τ) y := rfl
  have hYi : ((Y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) =
      algebraMap (Lsq K Δ) (EL Δ τ) ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) := rfl
  have hA : dLam lam z * sigL (Y : EL Δ τ) * ((Y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = dLam lam' z := by
    rw [hYc, hYi, hsig, hl']
    simp only [dLam, Algebra.smul_def, map_mul]
    ring
  set g : Kˣ := Units.map (QuadraticAlgebra.norm : Lsq K Δ →* K) y with hgdef
  have hB : ∀ x : Kˣ, ((x : K) • (1 : EL Δ τ)) * ↑Y * star (sigL (Y : EL Δ τ)) =
      ((x * g : Kˣ) : K) • (1 : EL Δ τ) := by
    intro x
    rw [hYc, hsig, hstar, mul_assoc, ← map_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    rw [Units.val_mul, mul_smul]
    have hgc : ((g : Kˣ) : K) = QuadraticAlgebra.norm (y : Lsq K Δ) := rfl
    rw [hgc, smul_one_mul]
    congr 1
    rw [Algebra.smul_def, mul_one]
    exact (IsScalarTower.algebraMap_apply K (Lsq K Δ) (EL Δ τ) _).symm
  have hD' := datLam K Δ τ c hr hc lam' hn' z hz
  have hf : ∀ t ∈ NE τ, ∀ x : Kˣ,
      (fun x : Kˣ => lcount O c (dLam lam' z) ((x : K) • (1 : EL Δ τ))) (t * x) =
      (fun x : Kˣ => lcount O c (dLam lam' z) ((x : K) • (1 : EL Δ τ))) x :=
    fun t ht x => inv_norm L hD' t ht x
  have hss := (sumShift O K Δ τ L hr (fun x : Kˣ => lcount O c (dLam lam' z) ((x : K) • (1 : EL Δ τ))) hf g).2.1
  have hk : kapSum O c (dLam lam z) 1 = hs (τ ^ 2 - 4) (QuadraticAlgebra.norm (y : Lsq K Δ)) *
      kapSum O c (dLam lam' z) 1 := by
    unfold kapSum
    rw [← show ((g : Kˣ) : K) = QuadraticAlgebra.norm (y : Lsq K Δ) from rfl, ← hss]
    refine finsum_congr (fun t => ?_)
    congr 1
    rw [(datIso O K Δ τ c (dLam lam z) (((Quotient.out t : Kˣ) : K) • 1) Y).1, hA, hB]
  have hε : eps τ lam' = hs (τ ^ 2 - 4) (QuadraticAlgebra.norm (y : Lsq K Δ)) * eps τ lam := by
    have htr'' := htr'
    rw [hl'] at htr'' ⊢
    exact signLaw O K Δ τ L hr lam y hn htr htr''
  rw [hk, hε]
  ring
