import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.NotEvenIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompactTorusUnitsEqTopOfNonsplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EvenValuationNormCompactUnitsOfSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FinsumQuotientNormsOfNonsplit

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.pStable :
    UpperTheory.V.Z.Sym.Loc.PStable := by
  intro O K _ _ _ _ _ Δ τ L hr j χ hj hχ a ha
  haveI := L.frac
  have hnω : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha, QuadraticAlgebra.norm_def]
    simp
  have hR : gOrb O j χ a = ((PS.Fv O τ).ncard : ℂ) := by
    rw [gLat O K Δ τ L hr j χ hj hχ a 1 1 (by rw [hnω]; simp), ← PS.vcount_eq L hr]
    simp [ha]
  rw [hR]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    exact hπ.ne_zero
  set p : Kˣ := Units.mk0 _ hp0 with hpdef
  have hpv : ((p : Kˣ) : K) = algebraMap O K π := rfl
  have hpe : ¬ EvenVal O ((p : Kˣ) : K) := by
    rw [hpv]
    exact PS.not_even_irr L hπ
  have hfv : ∀ t : Kˣ, (PS.Fv O τ).ncard = (PS.Gs O τ (↑t) 1).ncard + (PS.Gs O τ (↑(t * p)) 1).ncard :=
    fun t => PS.fv_card L hr t p hpe
  by_cases hD : IsSquare (τ ^ 2 - 4)
  · have hI := UpperTheory.evenValuation_norm_compactUnits_of_split O K Δ τ L hr hD
    have hall : ∀ x : Kˣ, x ∈ NE τ := fun x =>
      (hsNE O K Δ τ L hr x).2 ((hsLaw O K Δ L).2.2.2 (τ ^ 2 - 4) x hr hD)
    obtain ⟨r, hrr⟩ := hD
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hr
      rw [hrr, mul_zero]
    have h2 : (2 : K) ≠ 0 := by
      have h := L.two.map (algebraMap O K)
      rw [map_ofNat] at h
      exact h.ne_zero
    set β : K := (τ - r) / 2 with hβdef
    set u : K := (((p : Kˣ) : K) - 1) / r with hudef
    have hb : β ^ 2 - τ * β + 1 = 0 := by
      rw [hβdef]
      field_simp
      linear_combination (-1 : K) * hrr
    have hτβ : τ - 2 * β = r := by
      rw [hβdef]
      field_simp
      ring
    have hru : r * u = ((p : Kˣ) : K) - 1 := by
      rw [hudef]
      field_simp
    set w : Etau K τ := ⟨1 - β * u, u⟩ with hwdef
    have hw : QuadraticAlgebra.norm w = ((p : Kˣ) : K) := by
      rw [QuadraticAlgebra.norm_def, hwdef]
      simp only
      linear_combination u ^ 2 * hb + u * hτβ + hru
    obtain ⟨y0, hy0⟩ : IsUnit w :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.2 (by rw [hw]; exact p.isUnit)
    have hy0n : QuadraticAlgebra.norm (y0 : Etau K τ) = ((p : Kˣ) : K) := by rw [hy0, hw]
    have hy0u : PS.nU y0 = p := Units.ext (by rw [PS.nU_val, hy0n])
    have hy0C : y0 ∉ Cint O τ := by
      intro h
      have := hI.1 y0 h
      rw [hy0n] at this
      exact hpe this
    have hpc : ∀ t : Kˣ, pcount O τ ↑t = ((PS.Fv O τ).ncard : ℂ) := by
      intro t
      have c1 : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = y0 * c * z ^ 2 := by
        intro y
        have hyne : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := by
          rw [← PS.nU_val]
          exact Units.ne_zero _
        rcases PS.even_or L hyne hp0 hpe with he | he
        · obtain ⟨z, c, hc, hyc⟩ := hI.2 y he
          exact ⟨z, c, hc, Or.inl (by rw [one_mul, hyc])⟩
        · have e : QuadraticAlgebra.norm ((y * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
              QuadraticAlgebra.norm (y : Etau K τ) / ((p : Kˣ) : K) := by
            rw [← PS.nU_val, map_mul, map_inv, hy0u, Units.val_mul, Units.val_inv_eq_inv_val,
              PS.nU_val, div_eq_mul_inv]
          obtain ⟨z, c, hc, hyc⟩ := hI.2 (y * y0⁻¹) (e ▸ he)
          refine ⟨z, c, hc, Or.inr ?_⟩
          rw [mul_assoc, ← hyc, mul_comm, inv_mul_cancel_right]
      have c2 : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * y0⁻¹ ∈ Cint O τ → z ∈ Cint O τ := by
        intro z hz
        exfalso
        have hE := hI.1 _ hz
        have hzn : ((PS.nU z : Kˣ) : K) ≠ 0 := Units.ne_zero _
        have e : QuadraticAlgebra.norm ((z ^ 2 * 1 * y0⁻¹ : (Etau K τ)ˣ) : Etau K τ) =
            ((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K) := by
          rw [← PS.nU_val, map_mul, map_mul, map_pow, map_one, mul_one, map_inv, hy0u, Units.val_mul,
            Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, div_eq_mul_inv]
        rw [e] at hE
        have hsq : EvenVal O (((PS.nU z : Kˣ) : K) ^ 2) := ⟨1, (PS.nU z : K), hzn, by simp⟩
        apply hpe
        have := PS.even_mul hsq (PS.even_inv hE)
        have hp' : ((PS.nU z : Kˣ) : K) ^ 2 * (((PS.nU z : Kˣ) : K) ^ 2 / ((p : Kˣ) : K))⁻¹ =
            ((p : Kˣ) : K) := by
          field_simp
        rwa [hp'] at this
      rw [PS.pcount_eq L hr t 1 y0 c1 c2]
      have hdisj : Disjoint (PS.Gs O τ (↑t) 1) (PS.Gs O τ (↑t) y0) := by
        rw [Set.disjoint_left]
        rintro S ⟨-, c, hc, hg⟩ ⟨-, c', hc', hg'⟩
        have hu := PS.gen_uniq hg hg'
        apply hy0C
        have e : y0 = (1 * c) * ((1 * c)⁻¹ * (y0 * c')) * c'⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (by rw [one_mul]; exact hc) hu) (inv_mem hc')
      rw [Set.ncard_union_eq hdisj (PS.gs_fin L hr t 1) (PS.gs_fin L hr t y0), PS.gs_ncard ((t : Kˣ) : K) y0,
        hy0u, hfv t, Units.val_mul]
    rw [finsum_eq_single _ (QuotientGroup.mk 1 : Kˣ ⧸ NE τ), hpc]
    intro t ht
    exfalso
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    exact ht (QuotientGroup.eq.2 (hall _))
  · have hC := UpperTheory.compactTorusUnits_eq_top_of_nonsplit O K Δ τ L hr hD
    have hpc : ∀ (t : Kˣ) (b : (Etau K τ)ˣ), pcount O τ ↑t = ((PS.Gs O τ (↑t) b).ncard : ℂ) := by
      intro t b
      rw [PS.pcount_eq L hr t b b (fun y => ⟨1, b⁻¹ * y, by rw [hC]; trivial, Or.inl (by group)⟩)
        (fun z _ => by rw [hC]; trivial), Set.union_self]
    have hinv : ∀ t ∈ NE τ, ∀ x : Kˣ, pcount O τ ↑(t * x) = pcount O τ ↑x := by
      rintro t ⟨b, rfl⟩ x
      rw [hpc x b, PS.gs_ncard, hpc _ 1, Units.val_mul, mul_comm]
      rfl
    obtain ⟨⟨g0, hg0⟩, hsum⟩ := UpperTheory.finsum_quotient_norms_of_nonsplit O K Δ τ L hr hD
    have e : ∀ t : Kˣ, ((PS.Fv O τ).ncard : ℂ) = pcount O τ ↑t + pcount O τ ↑(t * p) := by
      intro t
      rw [hfv t, Nat.cast_add, hpc t 1, hpc (t * p) 1]
    by_cases hpN : p ∈ NE τ
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑g0 :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv g0 hg0
      rw [hS]
      have e1 := e 1
      have e2 := e g0
      rw [mul_comm, hinv p hpN] at e1 e2
      linear_combination (-1 / 2 : ℂ) * e1 + (-1 / 2 : ℂ) * e2
    · have hS : ∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ↑(Quotient.out t) = pcount O τ ↑(1 : Kˣ) + pcount O τ ↑p :=
        hsum (fun x : Kˣ => pcount O τ ↑x) hinv p hpN
      rw [hS, e 1, one_mul]
