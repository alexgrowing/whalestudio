import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockEndMinorsOfCell
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ideal

variable {D : D7}

abbrev dI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

theorem star_F (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c :=
  (NumberField.IsCMField.complexConj D.host.E).commutes c

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨⟨star (o : D.host.E), o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩

theorem star_mem_pow (n : ℕ) (y : 𝓞 D.host.E) (hy : y ∈ dI D ^ n) :
    ∃ y' ∈ dI D ^ n, (y' : D.host.E) = star (y : D.host.E) := by
  rw [← Ideal.map_pow] at hy ⊢
  have hy' : y ∈ Submodule.span (𝓞 D.host.E)
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) '' ((differentIdeal ℤ (𝓞 D.host.F) ^ n : Ideal (𝓞 D.host.F)) : Set (𝓞 D.host.F))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c, Ideal.mem_map_of_mem _ hc, ?_⟩
    have e : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (c : D.host.F) := rfl
    rw [e, star_F]
  | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', Ideal.add_mem _ hx' hy', ?_⟩
    rw [show ((x' + y' : 𝓞 D.host.E) : D.host.E) = (x' : D.host.E) + (y' : D.host.E) from rfl,
      show ((x + y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) + (y : D.host.E) from rfl, ex, ey, star_add]
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := star_int a
    refine ⟨a' * x', Ideal.mul_mem_left _ _ hx', ?_⟩
    rw [smul_eq_mul, show ((a' * x' : 𝓞 D.host.E) : D.host.E) = (a' : D.host.E) * (x' : D.host.E) from rfl,
      show ((a * x : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * (x : D.host.E) from rfl, ea, ex, star_mul, mul_comm]

theorem dI_ne_bot (n : ℕ) : dI D ^ n ≠ ⊥ := by
  have h : dI D ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
  rw [← Ideal.zero_eq_bot] at h ⊢
  exact pow_ne_zero n h

theorem mem_inv_coe {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) (x : D.host.E) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (y : D.host.E) := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hy))
    exact ⟨o, ho⟩
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨o, ho⟩ := h y hy
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩

theorem star_mem_inv (n : ℕ) {x : D.host.E}
    (hx : x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹) :
    star x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [mem_inv_coe (dI_ne_bot n)] at hx ⊢
  intro y hy
  obtain ⟨y', hy', ey⟩ := star_mem_pow n y hy
  obtain ⟨o, ho⟩ := hx y' hy'
  obtain ⟨o', eo⟩ := star_int o
  refine ⟨o', ?_⟩
  rw [eo, ho, ey, star_mul, star_star, mul_comm]

end Ideal

section Entry

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem hT_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (m n : ℕ)
    (v v' : (VS D).V) (hv : ∀ x ∈ (((dI D ^ m : Ideal (𝓞 D.host.E)) : FI))⁻¹, x • v ∈ Λ)
    (hv' : ∀ y ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FI))⁻¹, y • v' ∈ Λ) :
    ∃ o ∈ dI D ^ (m + n), (o : D.host.E) = (VS D).hT v v' := by
  set Z := (VS D).hT v v' with hZ
  set A : FI := (((dI D ^ m : Ideal (𝓞 D.host.E)) : FI))⁻¹
  set B : FI := (((dI D ^ n : Ideal (𝓞 D.host.E)) : FI))⁻¹
  have hJ : (((dI D ^ (m + n) : Ideal (𝓞 D.host.E)) : FI)) = (A * B)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv, ← FractionalIdeal.coeIdeal_mul, ← pow_add]
  have hAB0 : A * B ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_) <;>
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero] <;> exact dI_ne_bot _
  have hmem : Z ∈ (A * B)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hAB0]
    intro w hw
    refine FractionalIdeal.mul_induction_on hw ?_ ?_
    · intro a ha b hb
      have ha' : star a ∈ A := star_mem_inv m ha
      obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hv _ ha') (hv' _ hb)
      refine (FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩
      show (c : D.host.E) = _
      rw [hc, LinearMap.map_smulₛₗ₂, LinearMap.map_smulₛₗ, RingHom.id_apply, starRingEnd_apply, star_star,
        smul_eq_mul, smul_eq_mul, hZ]
      ring
    · intro x y hx hy
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
  rw [← hJ] at hmem
  obtain ⟨o, ho, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  exact ⟨o, ho, e⟩

theorem det_mem {q : ℕ} (M : Matrix (Fin q) (Fin q) (𝓞 D.host.E)) (m : Fin q → ℕ)
    (hM : ∀ i j, M i j ∈ dI D ^ (m i + m j)) : M.det ∈ dI D ^ (2 * ∑ i, m i) := by
  rw [Matrix.det_apply]
  refine Ideal.sum_mem _ fun σ _ => ?_
  have h := Ideal.prod_mem_prod (s := Finset.univ) (I := fun i => dI D ^ (m (σ i) + m i))
    (x := fun i => M (σ i) i) (fun i _ => hM (σ i) i)
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, Equiv.sum_comp σ m, ← two_mul] at h
  rw [Units.smul_def]
  exact zsmul_mem h _

theorem two_sum_sub (r : ℕ) : ∀ q : ℕ, q ≤ r + 1 → 2 * ∑ i : Fin q, (r - (i : ℕ)) = q * (2 * r + 1 - q)
  | 0, _ => by simp
  | q + 1, hq => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_add, two_sum_sub r q (by omega)]
    have h1 : q ≤ r := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
    have e1 : 2 * (q + d) + 1 - q = q + 2 * d + 1 := by omega
    have e2 : 2 * (q + d) + 1 - (q + 1) = q + 2 * d := by omega
    have e3 : q + d - q = d := by omega
    rw [e1, e2, e3]
    ring

end Entry

section Norm

variable {D : D7}

theorem discr_sq : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 :=
  D.host.der.discr_sq

theorem absNorm_dI : ((Ideal.absNorm (dI D) : ℕ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := by
  have h := Formalism.MainNotions.BridgeLemma.szf_normDD D discr_sq
  unfold Formalism.MainNotions.BridgeLemma.SzfNormDD Formalism.MainNotions.S.ddE at h
  rw [FractionalIdeal.coeIdeal_absNorm] at h
  exact_mod_cast h

theorem rd_pos : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _

theorem prod_sq_ge (n : ℕ) (o : 𝓞 D.host.E) (ho : o ∈ dI D ^ n) (h0 : (o : D.host.E) ≠ 0) :
    (D.host.rdE ^ D.R.f) ^ (2 * n) ≤ ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm (o : D.host.E)
  have h2 : ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ w.mult =
      ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 :=
    Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← h2, h1, ← Algebra.coe_norm_int]
  have ho0 : o ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hspan : Ideal.span {o} ≤ dI D ^ n := (Ideal.span_singleton_le_iff_mem _).2 ho
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  rw [Ideal.absNorm_span_singleton, map_pow] at hdvd
  have hne : (Algebra.norm ℤ o).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]; exact Algebra.norm_ne_zero_iff.2 ho0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have hle' : ((Ideal.absNorm (dI D) ^ n : ℕ) : ℝ) ≤ ((Algebra.norm ℤ o).natAbs : ℝ) := by exact_mod_cast hle
  rw [Nat.cast_pow, absNorm_dI, ← pow_mul] at hle'
  have e : (((Algebra.norm ℤ o).natAbs : ℕ) : ℝ) = ((|((Algebra.norm ℤ o : ℤ) : ℚ)| : ℚ) : ℝ) := by
    simp [Nat.cast_natAbs, Rat.cast_abs]
  rw [← e]
  exact hle'

end Norm

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality
