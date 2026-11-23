import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Across2
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.InfCyc

open UpperTheory.V.Z.Win.Dn
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.HV UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.GalN.V
open scoped Pointwise

namespace UpperTheory.V.Z.Win.Dn.PotentialDiagonalRankTwo

section Abstract

variable {Γ k : Type} [Group Γ] [Field k]

private theorem low_zero {t m m' : Matrix (Fin 2) (Fin 2) k} (ht : t 1 0 = 0) (hm' : m' 1 0 = 0)
    (h00 : m' 0 0 = t 0 0) (hne : t 0 0 ≠ t 1 1) (e : t * m = m * m') : m 1 0 = 0 := by
  have h := congrFun (congrFun e 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ht, hm', h00, zero_mul, mul_zero, zero_add, add_zero] at h
  have h2 : (t 1 1 - t 0 0) * m 1 0 = 0 := by
    rw [sub_mul, h, mul_comm, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3).symm hne
  · exact h3

private def diagChar (ρ : Γ →* GL (Fin 2) k) (D : Subgroup Γ)
    (h0 : ∀ d : ↥D, (ρ d : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (i : Fin 2) : ↥D →* kˣ :=
  MonoidHom.toHomUnits
    { toFun := fun d => (ρ d : Matrix (Fin 2) (Fin 2) k) i i
      map_one' := by simp
      map_mul' := fun x y => by
        have hx := h0 x
        have hy := h0 y
        rw [Subgroup.coe_mul, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
        fin_cases i
        · simp [hy]
        · simp [hx] }

private theorem diagChar_val (ρ : Γ →* GL (Fin 2) k) (D : Subgroup Γ)
    (h0 : ∀ d : ↥D, (ρ d : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (i : Fin 2) (d : ↥D) :
    ((diagChar ρ D h0 i d : kˣ) : k) = (ρ d : Matrix (Fin 2) (Fin 2) k) i i := rfl

private theorem flag_core (r : Γ →* GL (Fin 2) k) (α : Fin 2 → Γ →* kˣ) {N₀ N D : Subgroup Γ} (g : Γ)
    (hg : ∀ h ∈ N, g⁻¹ * h * g ∈ N₀)
    (hfl : IsFlagOn r N₀ fun i => (α i).comp N₀.subtype)
    (hD : ∀ d ∈ D, ∀ h ∈ N, d⁻¹ * h * d ∈ N)
    {s : Γ} (hs : s ∈ N) (hab : α 0 s ≠ α 1 s) :
    ∃ κ : Fin 2 → ↥D →* kˣ, IsFlagOn r D κ ∧ ∀ (i : Fin 2) (d : ↥D), (d : Γ) ∈ N → κ i d = α i d := by
  obtain ⟨P, hP⟩ := hfl
  let Q : GL (Fin 2) k := P * (r g)⁻¹
  let ρ : Γ →* GL (Fin 2) k := (MulAut.conj Q).toMonoidHom.comp r
  have hρ : ∀ x, ρ x = Q * r x * Q⁻¹ := fun _ => rfl
  have hconj : ∀ (χ : Γ →* kˣ) (x y : Γ), χ (y⁻¹ * x * y) = χ x := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm (χ y)⁻¹, mul_assoc, mul_comm _ (χ y)]
    simp
  have hN : ∀ h (hh : h ∈ N), (ρ h : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧
      ∀ i, (ρ h : Matrix (Fin 2) (Fin 2) k) i i = (α i h : k) := fun h hh => by
    have e : ρ h = P * r (g⁻¹ * h * g) * P⁻¹ := by
      rw [hρ]
      simp only [Q, map_mul, map_inv]
      group
    obtain ⟨h1, h2⟩ := hP ⟨_, hg h hh⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [e]
      exact h1 1 0 (by decide)
    · rw [e]
      refine (h2 i).trans ?_
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [hconj]
  have h0 : ∀ d : ↥D, (ρ d : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := fun d => by
    have hd : (d : Γ)⁻¹ * s * d ∈ N := hD d d.2 s hs
    refine low_zero (t := (ρ s : Matrix (Fin 2) (Fin 2) k)) (m' := (ρ ((d : Γ)⁻¹ * s * d) : Matrix (Fin 2) (Fin 2) k))
      (hN s hs).1 (hN _ hd).1 ?_ ?_ ?_
    · rw [(hN _ hd).2 0, (hN s hs).2 0, hconj]
    · rw [(hN s hs).2 0, (hN s hs).2 1]
      exact fun e => hab (Units.ext e)
    · rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
      congr 2
      group
  refine ⟨diagChar ρ D h0, ⟨Q, fun u => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i d hd => ?_⟩
  · have hi : i = 1 := by omega
    have hj : j = 0 := by omega
    subst hi hj
    exact h0 u
  · rfl
  · apply Units.ext
    rw [diagChar_val]
    exact (hN d hd).2 i

end Abstract

private theorem ne_one_zpow {C : Type} [Group C] {x : C} (h : ¬ IsOfFinOrder x) {z : ℤ} (hz : z ≠ 0) : x ^ z ≠ 1 :=
  fun e => h (isOfFinOrder_iff_zpow_eq_one.2 ⟨z, hz, e⟩)

private theorem place_eq {l : ℕ} [hl : Fact l.Prime] {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).2 (Nat.prime_iff_prime_int.1 hl.out)
  have hq : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hm : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    hq.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  refine HeightOneSpectrum.ext ?_
  rw [← hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv),
    ← hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)]

end UpperTheory.V.Z.Win.Dn.PotentialDiagonalRankTwo

open UpperTheory.V.Z.Win.Dn.PotentialDiagonalRankTwo in
theorem UpperTheory.V.Z.Win.Dn.potTwo_of :
    PotTwo := by
  intro Ω _ _ _ l _ e he W B hB H hHo hHn hfl v hv A hA
  have hBv : IsPlaceOver (F := ℚ) B v := by
    obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places ℚ Ω l B
    obtain ⟨v', hv'⟩ := h1 fun h => (h2 h).2 hB
    have h4 : ((l : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal := (h3 v' hv').1 hB
    rw [← place_eq h4 hv]
    exact hv'
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) hBv hA
  have hAl : (g • B).valuation (l : Ω) < 1 := ((UpperTheory.V.Two.ineConj ℚ Ω g).2.1 B l).2 hB
  obtain ⟨s, hs, hinf⟩ := UpperTheory.V.Keep.infCyc ℚ Ω l (g • B) hAl H hHo
  have he0 : (e : ℤ) ≠ 0 := by omega
  have hab : ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] 0)) s ≠ ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] 1)) s := by
    intro h
    refine ne_one_zpow hinf (z := 2 * (e : ℤ)) (by omega) ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.zpow_apply] at h
    rw [two_mul, zpow_add]
    nth_rewrite 1 [h]
    simp
  obtain ⟨κ, hκ, hval⟩ := flag_core (N₀ := H ⊓ Ine (F := ℚ) B) (N := H ⊓ Ine (F := ℚ) (g • B)) (D := Dec (F := ℚ) (g • B)) W
    (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) g
    (fun h hh => ⟨hHn.conj_mem' h hh.1 g, (UpperTheory.V.Two.ineConj ℚ Ω g).1 B h hh.2⟩) hfl
    (fun d hd h hh => ⟨hHn.conj_mem' h hh.1 d,
      (UpperTheory.V.Two.ineConj ℚ Ω d).1 (g • B) h (by rw [mem_Dec.1 hd]; exact hh.2)⟩) hs hab
  refine ⟨κ, hκ, fun i j m hm heq => ?_⟩
  have hsD : s ∈ Dec (F := ℚ) (g • B) := hs.2.1
  have h1 := DFunLike.congr_fun heq ⟨s, hsD⟩
  simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
  rw [hval i ⟨s, hsD⟩ hs, hval j ⟨s, hsD⟩ hs] at h1
  simp only [MonoidHom.zpow_apply] at h1
  have hz : ((m : ℤ) * (![(e : ℤ), -(e : ℤ)] i - ![(e : ℤ), -(e : ℤ)] j - 1)) ≠ 0 := by
    refine mul_ne_zero (by omega) ?_
    fin_cases i <;> fin_cases j <;> simp <;> omega
  refine ne_one_zpow hinf hz ?_
  have h2 : (cycBar ℚ Ω l s) ^ ((m : ℤ) * ![(e : ℤ), -(e : ℤ)] i) =
      (cycBar ℚ Ω l s) ^ ((m : ℤ) * (![(e : ℤ), -(e : ℤ)] j + 1)) := by
    rw [mul_comm (m : ℤ), mul_comm (m : ℤ), zpow_mul, zpow_mul, zpow_add_one, zpow_natCast, zpow_natCast]
    exact h1
  rw [show (m : ℤ) * (![(e : ℤ), -(e : ℤ)] i - ![(e : ℤ), -(e : ℤ)] j - 1) =
      (m : ℤ) * ![(e : ℤ), -(e : ℤ)] i - (m : ℤ) * (![(e : ℤ), -(e : ℤ)] j + 1) by ring, zpow_sub, h2]
  simp
