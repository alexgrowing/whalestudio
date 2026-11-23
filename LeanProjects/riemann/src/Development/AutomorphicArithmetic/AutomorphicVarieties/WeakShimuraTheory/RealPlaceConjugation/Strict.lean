import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem exists_natCard_eq_pow_and_separating_zmod_forms (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod l) M]
    [Finite M] : ∃ (d : ℕ) (c : Fin d → M →+ ZMod l), Nat.card M = l ^ d ∧
      ∀ x y : M, (∀ i, c i x = c i y) → x = y := by
  refine ⟨Module.finrank (ZMod l) M,
    fun i => ((Module.finBasis (ZMod l) M).coord i).toAddMonoidHom, ?_, ?_⟩
  · letI : Fintype M := Fintype.ofFinite M
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  · intro x y h
    apply (Module.finBasis (ZMod l) M).ext_elem
    intro i
    simpa [Module.Basis.coord_apply] using h i

private theorem eq_zero_of_nsmul_eq_zero_of_coprime_torsion (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M]
    (htor : ∀ m : M, l • m = 0) (n : ℕ) (hn : ¬ l ∣ n) (x : M) (hx : n • x = 0) : x = 0 := by
  have hcop : Nat.Coprime n l :=
    Nat.coprime_comm.mp ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr hn)
  have h := Nat.gcd_eq_gcd_ab n l
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  calc x = (1 : ℤ) • x := (one_zsmul x).symm
    _ = ((n : ℤ) * Nat.gcdA n l + (l : ℤ) * Nat.gcdB n l) • x := by rw [h]
    _ = Nat.gcdA n l • (n • x) + Nat.gcdB n l • (l • x) := by
      rw [add_smul, mul_comm (n : ℤ), mul_comm (l : ℤ), mul_smul, mul_smul, natCast_zsmul,
        natCast_zsmul]
    _ = 0 := by rw [hx, htor, smul_zero, smul_zero, add_zero]

theorem UpperTheory.V.Ws.card_cocycles_vanishing_on_inertia_le_pow :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M], (∀ m : M, l • m = 0) → ∀ (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (r : ℕ), ¬ l ∣ K.index → (∀ g ∈ K, ∀ m, ρ g m = m) → XRk l 1 K r → CardLe (cocOff ρ (ineOff F Ω 1 ∩ K)) (Nat.card M ^ (r + 1)) := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ htor ρ K r hdvd hK hX
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hidx : K.index ≠ 0 := fun h => hdvd (h ▸ dvd_zero l)
  haveI : K.FiniteIndex := ⟨hidx⟩
  letI : Fintype (G F Ω ⧸ K) := Fintype.ofFinite _
  have hn : ¬ l ∣ Fintype.card (G F Ω ⧸ K) := by
    rw [← Nat.card_eq_fintype_card]
    exact hdvd
  have key : ∀ w : G F Ω → M, (∀ g h, w (g * h) = w g + ρ g (w h)) → (∀ k ∈ K, w k = 0) →
      (∑ q : G F Ω ⧸ K, w q.out) = 0 → w = 0 := by
    intro w hw hwK hS
    funext h
    show w h = 0
    have e1 : ∀ q : G F Ω ⧸ K, w (h * q.out) = w (h • q).out := by
      intro q
      have hq : ((h * q.out : G F Ω) : G F Ω ⧸ K) = h • q := by
        show ((h • q.out : G F Ω) : G F Ω ⧸ K) = h • q
        rw [← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
      have hk : (h * q.out)⁻¹ * (h • q).out ∈ K :=
        QuotientGroup.eq.mp (hq.trans (QuotientGroup.out_eq' _).symm)
      have := hw (h * q.out) ((h * q.out)⁻¹ * (h • q).out)
      rw [mul_inv_cancel_left, hwK _ hk, map_zero, add_zero] at this
      exact this.symm
    have hsum : ∑ q : G F Ω ⧸ K, w (h * q.out) = ∑ q : G F Ω ⧸ K, w q.out := by
      rw [Finset.sum_congr rfl (fun q _ => e1 q)]
      exact Equiv.sum_comp (MulAction.toPerm h) (fun q : G F Ω ⧸ K => w q.out)
    have hexp : ∑ q : G F Ω ⧸ K, w (h * q.out) =
        Fintype.card (G F Ω ⧸ K) • w h + ρ h (∑ q : G F Ω ⧸ K, w q.out) := by
      simp only [hw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
    rw [hsum, hS, map_zero, add_zero] at hexp
    exact eq_zero_of_nsmul_eq_zero_of_coprime_torsion l M htor _ hn (w h) hexp.symm
  obtain ⟨hXfin, hXcard⟩ := hX
  obtain ⟨d, c, hM, hc⟩ := @exists_natCard_eq_pow_and_separating_zmod_forms l _ M _ (AddCommGroup.zmodModule htor) _
  have mem : ∀ z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))),
      IsLocallyConstant z.1 ∧ (∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h)) ∧
        ∀ g ∈ ineOff F Ω 1 ∩ (K : Set (G F Ω)), z.1 g = 0 := fun z => z.2
  have hone : ∀ A : ValuationSubring Ω, ¬ A.valuation ((1 : ℕ) : Ω) < 1 := by
    intro A
    simp
  have coordMem : ∀ (z : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))) (i : Fin d),
      (fun u : K => c i (z.1 u)) ∈ UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l) := by
    intro z i
    obtain ⟨hlc, hcoc, hvan⟩ := mem z
    have hφ : IsLocallyConstant (fun u : K => c i (z.1 u)) ∧
        (∀ a e : K, c i (z.1 ↑(a * e)) = c i (z.1 a) + c i (z.1 e)) ∧
        (∀ (A : ValuationSubring Ω) (u : K), (u : G F Ω) ∈ Ine A → c i (z.1 u) = 0) ∧
        ∀ (A : ValuationSubring Ω), A.valuation ((1 : ℕ) : Ω) < 1 → ∀ u : K, (u : G F Ω) ∈ Dec A →
          c i (z.1 u) = 0 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (hlc.comp_continuous continuous_subtype_val).comp (fun m => c i m)
      · intro a e
        rw [Subgroup.coe_mul, hcoc, hK a a.2, map_add]
      · intro A u hu
        have hin : (u : G F Ω) ∈ ineOff F Ω 1 := by
          show ∃ A, _
          exact ⟨A, hone A, hu⟩
        rw [hvan u ⟨hin, u.2⟩, map_zero]
      · intro A hA
        exact absurd hA (hone A)
    exact hφ
  let Φ : ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω)))) →
      (Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M :=
    fun z => (fun i => ⟨_, coordMem z i⟩, ∑ q : G F Ω ⧸ K, z.1 q.out)
  have hinj : Function.Injective Φ := by
    intro z z' hzz
    have h2 : (∑ q : G F Ω ⧸ K, z.1 q.out) = ∑ q : G F Ω ⧸ K, z'.1 q.out :=
      congrArg Prod.snd hzz
    have hKeq : ∀ k ∈ K, z.1 k = z'.1 k := by
      intro k hk
      exact hc _ _ (fun i => congrArg (fun p => (p.1 i).1 ⟨k, hk⟩) hzz)
    obtain ⟨_, hcoc, -⟩ := mem z
    obtain ⟨_, hcoc', -⟩ := mem z'
    have hw := key (fun g => z.1 g - z'.1 g)
      (by
        intro g h
        simp only [hcoc, hcoc', map_sub]
        abel)
      (by
        intro k hk
        simp [hKeq k hk])
      (by simp only [Finset.sum_sub_distrib, h2, sub_self])
    apply Subtype.ext
    funext g
    exact sub_eq_zero.mp (congrFun hw g)
  haveI : Finite ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) := hXfin
  refine (show Finite _ ∧ Nat.card _ ≤ _ from ⟨Finite.of_injective Φ hinj, ?_⟩)
  calc Nat.card ↥(cocOff ρ (ineOff F Ω 1 ∩ (K : Set (G F Ω))))
      ≤ Nat.card ((Fin d → ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l))) × M) :=
        Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card ↥(UpperTheory.V.Kum.XDual (F := F) (Ω := Ω) 1 K (ZMod l) (ZMod l)) ^ d * Nat.card M := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    _ ≤ (l ^ r) ^ d * Nat.card M :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hXcard _)
    _ = Nat.card M ^ (r + 1) := by
        rw [hM]
        ring
