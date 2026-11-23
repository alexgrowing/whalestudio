import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLengthStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalSameDoubleCosetSumsZonalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSums
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets

noncomputable section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

namespace GlobalTheory.UnramDoublingProof

section Cells

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_cell {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) :
    ∃ e : {e : Fin N → ℤ // Antitone e}, g ∈ cell k (Fin N) ϖ e := by
  have h := iUnion_cell (k := k) (N := N) hϖ
  exact Set.mem_iUnion.1 (h ▸ Set.mem_univ g)

def cellLen {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) : ℕ :=
  (∑ i, |(exists_cell hϖ g).choose.1 i|).toNat

theorem cellLen_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin N → ℤ) (he : Antitone e)
    (g : GL (Fin N) k) (hg : g ∈ cell k (Fin N) ϖ e) : cellLen hϖ g = (∑ i, |e i|).toNat := by
  have h := (exists_cell hϖ g).choose_spec
  have h' : (exists_cell hϖ g).choose = ⟨e, he⟩ := by
    by_contra hne
    exact Set.disjoint_left.1 (pairwise_disjoint_cell hϖ hne) h hg
  simp only [cellLen, h']

theorem sphSection_eq_pow {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : ℂ)
    (g : GL (Fin N) k) :
    sphSection k (Fin N) s (io k (Fin N) (g, 1)) =
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s))) ^ cellLen hϖ g := by
  obtain ⟨⟨e, he⟩, hg⟩ := exists_cell hϖ g
  rw [cellLen_eq hϖ e he g hg]
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [sphSection_io_biinv s _ hx hy, sphSection_torusElt hϖ, Fintype.card_fin, ← Complex.cpow_nat_mul]
  have h0 : 0 ≤ ∑ i, |e i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hc : (((∑ i, |e i|).toNat : ℕ) : ℂ) = ((∑ i, |e i| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [hc]
  congr 1
  ring

theorem isCommensurated_KO {N : ℕ} : Formalism.UG.IsCommensurated (KO k (Fin N)) := by
  intro x
  have hmo : IsOpen (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
      Set (GL (Fin N) k)) := by
    have hset : (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) = (fun y => x⁻¹ * y * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) := by
      ext y
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [mul_assoc] using hz
      · intro h
        exact ⟨_, h, by group⟩
    rw [hset]
    exact SplitFlip.isOpen_KO.preimage (by fun_prop)
  have : CompactSpace (KO k (Fin N)) := isCompact_iff_compactSpace.mp SplitFlip.isCompact_KO
  have hso : IsOpen ((((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N)) :
      Subgroup (KO k (Fin N))) : Set (KO k (Fin N))) := by
    rw [Subgroup.coe_subgroupOf]
    exact hmo.preimage continuous_subtype_val
  have : Finite ((KO k (Fin N)) ⧸ ((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N))) :=
    Subgroup.quotient_finite_of_isOpen _ hso
  exact Subgroup.index_ne_zero_of_finite

end Cells

section Factors

theorem factor_one {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (n - 1 - (i : ℕ)) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hc : ((n - 1 - (i : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℕ) := by
    have := i.2
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, hc,
    mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

theorem qpow_mul_inv_mul_qpow_eq {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (i : ℕ) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a⁻¹ * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, mul_inv,
    ← Complex.cpow_neg, mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

theorem prod_one_sub_eq_invNormFactor {q n : ℕ} (hq : 0 < q) (s : ℂ) :
    ∏ i : Fin n, (1 - (q : ℂ) ^ (i : ℕ) * ((q : ℂ) ^ (-((n : ℂ) / 2 + s))) ^ 2) = invNormFactor q n s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  unfold invNormFactor
  refine Finset.prod_bij' (fun i _ => n - (i : ℕ))
    (fun j hj => ⟨n - j, by have := Finset.mem_Icc.1 hj; omega⟩) (fun i _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun i _ => ?_) (fun j hj => ?_) (fun i _ => ?_)
  · have := i.2
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · have := i.2
    exact Fin.ext (by simp only; omega)
  · have := Finset.mem_Icc.1 hj
    simp only
    omega
  · rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, Nat.cast_sub i.2.le]
    congr 2
    push_cast
    ring

end Factors

theorem unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL := by
  intro k _ _ _ _ _ n _ _ μ _ hμ V _ _ π α hπ ω hω
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x h0, hx⟩
  have hq1 : 1 < resCard k := one_lt_resCard k
  have hq : 0 < resCard k := zero_lt_one.trans hq1
  have hqR : (1 : ℝ) < resCard k := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < resCard k := zero_lt_one.trans hqR
  obtain ⟨φ, hφ, hsum⟩ := GlobalTheory.T.exists_borel_spherical_same_double_coset_sums_zonal k n V π α hπ ω hω
  obtain ⟨δ, hδ, hmain⟩ := GlobalTheory.T.hasSum_sphericalFunction_doublingLength k n _ φ hφ
    (fun i => mul_ne_zero (α i).ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hqR0 _).ne'))
    ϖ hϖ (cellLen hϖ) (cellLen_eq hϖ)
  refine ⟨-Real.logb (resCard k) δ - n / 2, fun s hs => ?_⟩
  have hX : ‖(resCard k : ℂ) ^ (-((n : ℂ) / 2 + s))‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos hq]
    refine (Real.rpow_lt_rpow_of_exponent_lt hqR (?_ : _ < Real.logb (resCard k) δ)).trans_eq
      (Real.rpow_logb hqR0 hqR.ne' hδ)
    have : (-((n : ℂ) / 2 + s)).re = -((n : ℝ) / 2 + s.re) := by simp
    rw [this]
    linarith
  have h1 := hmain _ hX
  simp only [← sphSection_eq_pow hϖ s, factor_one hq, qpow_mul_inv_mul_qpow_eq hq, prod_one_sub_eq_invNormFactor hq] at h1
  have h2 := GlobalTheory.InertZeta.dosetSwap (GL (Fin n) k) (KO k (Fin n)) isCommensurated_KO
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1))) ω φ _
    (fun a b g => sphSection_io_biinv s g a.2 b.2) (fun a b g => zonal_biinv hω g a.2 b.2) hsum h1
  have h3 := GlobalTheory.InertZeta.cosetIntegral_holds (GL (Fin n) k) μ (KO k (Fin n)) SplitFlip.isOpen_KO hμ
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g) _ (fun g y hy => by
      have e1 := sphSection_io_biinv s g (one_mem (KO k (Fin n))) hy
      have e2 := zonal_biinv hω g (one_mem (KO k (Fin n))) hy
      rw [one_mul] at e1 e2
      simp only [e1, e2]) h2
  refine ⟨h3.1, h3.2.trans ?_⟩
  simp only [lFactor, Pi.inv_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.UnramDoublingProof
