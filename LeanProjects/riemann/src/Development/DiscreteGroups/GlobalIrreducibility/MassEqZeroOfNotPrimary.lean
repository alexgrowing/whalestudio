import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzKFour

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {F : Type} [Field F] [Finite F]

theorem aC_mod {n : ℕ} (θ : AlgebraicClosure F →* ℂ) (h : AlgebraicClosure F → ℂ) (l : ℕ) :
    aC n θ h (l % (Nat.card F ^ n - 1)) = aC n θ h l := by
  unfold aC
  congr 1
  refine finsum_mem_congr rfl fun β hβ => ?_
  have e := theta_pow_N θ hβ
  conv_rhs => rw [← Nat.mod_add_div l (Nat.card F ^ n - 1), pow_add, pow_mul, e, one_pow, mul_one]

theorem aC_frob {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ) (ψ : F → ℂ) (k i : ℕ) :
    aC n θ (hT n ψ) (k * Nat.card F ^ i) = aC n θ (hT n ψ) k := by
  unfold aC
  congr 1
  obtain ⟨f, hf⟩ := exists_algHom_pow_card_pow (F := F) i
  have hmaps : Set.MapsTo (fun β : AlgebraicClosure F => β ^ Nat.card F ^ i) (tor F n) (tor F n) :=
    fun β hβ => pow_mem_tor hβ _
  have hinj : Set.InjOn (fun β : AlgebraicClosure F => β ^ Nat.card F ^ i) (tor F n) := by
    intro x _ y _ hxy
    have : f x = f y := by rw [hf, hf]; exact hxy
    exact f.toRingHom.injective this
  have hbij := ((tor_finite (F := F) hn).injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
  refine finsum_mem_eq_of_bijOn (fun β : AlgebraicClosure F => β ^ Nat.card F ^ i) hbij fun β _ => ?_
  rw [hT_pow_card, map_pow, mul_comm k, pow_mul]

theorem sum_filter_aC {n : ℕ} (hn : 0 < n) (θ : AlgebraicClosure F →* ℂ) (ψ : F → ℂ) (k : ℕ) :
    ∑ l ∈ Finset.range (Nat.card F ^ n - 1), star (aC n θ (hT n ψ) l) *
      (((Finset.range n).filter fun i => k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1]).card : ℂ) =
      (n : ℂ) * star (aC n θ (hT n ψ) k) := by
  classical
  have hN := N_pos (F := F) hn
  simp_rw [Finset.natCast_card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ i ∈ Finset.range n, ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
      star (aC n θ (hT n ψ) l) * (if k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] then (1 : ℂ) else 0) =
      star (aC n θ (hT n ψ) k) := by
    intro i _
    have e2 : ∀ l ∈ Finset.range (Nat.card F ^ n - 1),
        star (aC n θ (hT n ψ) l) * (if k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] then (1 : ℂ) else 0) =
        if (k * Nat.card F ^ i) % (Nat.card F ^ n - 1) = l then star (aC n θ (hT n ψ) l) else 0 := by
      intro l hl
      have hl' : l % (Nat.card F ^ n - 1) = l := Nat.mod_eq_of_lt (Finset.mem_range.1 hl)
      by_cases hc : (k * Nat.card F ^ i) % (Nat.card F ^ n - 1) = l
      · rw [if_pos hc, if_pos (show k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] by
          unfold Nat.ModEq; rw [hl', hc]), mul_one]
      · rw [if_neg hc, if_neg (show ¬ k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1] by
          unfold Nat.ModEq; rw [hl']; exact hc), mul_zero]
    rw [Finset.sum_congr rfl e2, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 (Nat.mod_lt _ hN)),
      aC_mod, aC_frob hn]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem mass_eq_zero_of_not_primary (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hn : 0 < Module.finrank F V) (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (P : F[X])
    (hP : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) :
    mass (psi (rootSum θ k) V) P = 0 := by
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
  have hcl : IsClassFn (psi (rootSum θ k) V) := fun e g => GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F _ V V e g
  unfold mass
  refine finsum_mem_of_eqOn_zero fun g hg => ?_
  have hg' : LinearMap.charpoly g = P := hg
  exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V _ hcl (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hadd) hn g (by rw [hg']; exact hP)

def polys (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] : Finset F[X] := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  exact (Set.finite_range (fun g : Module.End F V => LinearMap.charpoly g)).toFinset.filter
    (fun P => P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0})

theorem mem_polys {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {P : F[X]} :
    P ∈ polys (F := F) V ↔ (∃ g : Module.End F V, LinearMap.charpoly g = P) ∧
      P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} := by
  unfold polys
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_range]

theorem finsum_mass_eq (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ : Module.End F V → ℂ) (X : F[X] → ℂ) :
    ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0}, mass φ P * X P =
      ∑ P ∈ polys (F := F) V, mass φ P * X P := by
  rw [finsum_mem_def]
  rw [finsum_eq_sum_of_support_subset _ (s := polys (F := F) V) ?_]
  · refine Finset.sum_congr rfl fun P hP => ?_
    rw [Set.indicator_of_mem (mem_polys.1 hP).2]
  · intro P hP
    rw [Function.mem_support] at hP
    rw [Finset.mem_coe, mem_polys]
    by_cases hS : P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0}
    · refine ⟨?_, hS⟩
      by_contra hc
      apply hP
      rw [Set.indicator_of_mem hS]
      have hm : mass φ P = 0 := by
        unfold mass
        exact finsum_mem_of_eqOn_zero fun g hg => absurd ⟨g, hg⟩ hc
      rw [hm, zero_mul]
    · exact absurd (Set.indicator_of_notMem hS _) hP

theorem ipGL_psi_trace (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hn : 0 < Module.finrank F V) (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (k : ℕ) (ψ : F → ℂ) :
    ipGL (psi (rootSum θ k) V) (fun x => ψ (-(LinearMap.charpoly x).nextCoeff)) =
      glCard F (Module.finrank F V) * star (aC (Module.finrank F V) θ (hT (Module.finrank F V) ψ) k) := by
  classical
  have hl : ∀ l, ∑ P ∈ polys (F := F) V, mass (psi (rootSum θ k) V) P * star (rootSum θ l P) =
      glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter fun i =>
        k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ Module.finrank F V - 1]).card : ℂ) := by
    intro l
    rw [← finsum_mass_eq, ← ipGL_charpoly_eq_finsum_mass F V _ (rootSum θ l)]
    exact GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn k l
  rw [ipGL_charpoly_eq_finsum_mass F V _ (fun P => ψ (-P.nextCoeff)), finsum_mass_eq]
  set n := Module.finrank F V with hndef
  set φ := psi (rootSum θ k) V with hφ
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key : ∀ P ∈ polys (F := F) V,
      mass φ P * star (ψ (-P.nextCoeff)) = (n : ℂ)⁻¹ * ∑ l ∈ Finset.range (Nat.card F ^ n - 1),
        star (aC n θ (hT n ψ) l) * (mass φ P * star (rootSum θ l P)) := by
    intro P hP
    obtain ⟨hPm, hPd, hP0⟩ := (mem_polys.1 hP).2
    by_cases hpr : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
    · obtain ⟨f, m, hf, hirr, hm, hPf⟩ := hpr
      have e := expand_primary hn θ hθ ψ P f m hf hirr hm hPf hPd hP0
      have e' : ψ (-P.nextCoeff) = (n : ℂ)⁻¹ *
          ∑ l ∈ Finset.range (Nat.card F ^ n - 1), aC n θ (hT n ψ) l * rootSum θ l P := by
        rw [← e]; field_simp
      rw [e', star_mul', star_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_mul', star_inv₀, star_natCast]; ring
    · rw [mass_eq_zero_of_not_primary V hn θ k P hpr]; simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [hl]
  have e2 : ∀ l ∈ Finset.range (Nat.card F ^ n - 1), star (aC n θ (hT n ψ) l) * (glCard F n *
      (((Finset.range n).filter fun i => k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1]).card : ℂ)) =
      glCard F n * (star (aC n θ (hT n ψ) l) *
      (((Finset.range n).filter fun i => k * Nat.card F ^ i ≡ l [MOD Nat.card F ^ n - 1]).card : ℂ)) :=
    fun l _ => by ring
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, sum_filter_aC hn θ ψ k]
  field_simp

end DiscreteGroups.sglob.DzType.Kon
