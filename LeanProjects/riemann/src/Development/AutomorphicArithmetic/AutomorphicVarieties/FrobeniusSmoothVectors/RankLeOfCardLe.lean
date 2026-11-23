import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HthPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HlayPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardClDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.MuIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.GalCharBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem rank_le_of_cardLe (l : ℕ) [hl : Fact l.Prime] (P : Type) [AddCommGroup P] [Module (ZMod l) P] (r : ℕ)
    (h : Two.CardLe P (l ^ r)) : Module.rank (ZMod l) P ≤ r := by
  obtain ⟨hfin, hcard⟩ := h
  haveI := hfin
  haveI : Module.Finite (ZMod l) P := Module.Finite.of_finite
  rw [← Module.finrank_eq_rank]
  have hc : Nat.card P = l ^ Module.finrank (ZMod l) P := by
    haveI := Fintype.ofFinite P
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  rw [hc] at hcard
  have hle := (Nat.pow_le_pow_iff_right hl.out.one_lt).mp hcard
  exact_mod_cast hle

private theorem lev_rk {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2)
    (V : Subgroup (G ℚ Ω)) (ho : IsOpen (V : Set (G ℚ Ω))) (hab : commutator (G ℚ Ω) ≤ V) (hμ : V ≤ (cycMod ℚ Ω l 1).ker) :
    ∃ r : ℕ, ∀ n, GC.clRk l (V ⊓ (cycMod ℚ Ω l n).ker) ≤ r := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  let H : ClosedSubgroup (G ℚ Ω) := ⟨V, Subgroup.isClosed_of_isOpen V ho⟩
  let E := IntermediateField.fixedField V
  have hEV : E.fixingSubgroup = V := InfiniteGalois.fixingSubgroup_fixedField H
  have hnorm : V.Normal := by
    constructor
    intro v hv g
    have hc : g * v * g⁻¹ * v⁻¹ ∈ V := hab (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top v))
    have := V.mul_mem hc hv
    simpa using this
  haveI hfd : FiniteDimensional ℚ E := by
    rw [← InfiniteGalois.isOpen_iff_finite, hEV]
    exact ho
  have hG := (InfiniteGalois.normal_iff_isGalois E).mp (hEV ▸ hnorm)
  have hquot : ∀ a b : G ℚ Ω ⧸ V, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hc : y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ ∈ V :=
          hab (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        simpa [mul_assoc] using hc
  haveI : H.Normal := hnorm
  have hc2 : ∀ x y : @AlgEquiv ℚ E E _ _ _ (IntermediateField.algebra' E) (IntermediateField.algebra' E),
      x * y = y * x := fun x y =>
    (InfiniteGalois.normalAutEquivQuotient H).symm.injective (by rw [map_mul, map_mul, hquot])
  have hA : (IntermediateField.algebra' E : Algebra ℚ E) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  rw [hA] at hc2 hG
  haveI hAb : IsAbelianGalois ℚ E := @IsAbelianGalois.mk _ _ _ _ _ hG ⟨⟨hc2⟩⟩
  haveI : NumberField E := NumberField.mk
  have hgal : galOf ℚ E Ω = V := by
    rw [← hEV]
    ext σ
    rfl
  have hker : ∀ n, (cycMod ℚ Ω l n).ker = (Two.galChar Ω (l ^ n)).ker := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
    have h := (Two.levChar Ω l n ⊤).1
    rw [levU, KStar.TotallyRealRoots.princ, MonoidHom.comap_ker, top_inf_eq, top_inf_eq] at h
    exact h
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  have hζ : ∃ ζ : E, IsPrimitiveRoot ζ l := by
    haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
    have h1 : ∃ ζ : E, IsPrimitiveRoot ζ (l ^ 1) := by
      rw [Two.muIff Ω E (l ^ 1), hgal, ← hker 1]
      exact hμ
    simpa using h1
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  obtain ⟨r, hr⟩ := FW.main l E (by rw [if_neg h2]; exact hζ)
  refine ⟨r, fun n => ?_⟩
  let K' := Kum.Fn E Ω l n
  obtain ⟨hcyc, -, -⟩ := Kum.fnCyc E Ω l n
  haveI := hcyc
  haveI : NumberField K' := IsCyclotomicExtension.numberField {l ^ n} E K'
  have hgal' : galOf ℚ K' Ω = V ⊓ (cycMod ℚ Ω l n).ker := by
    rw [Kum.galOfCyc ℚ Ω l n E K', hgal, levU, KStar.TotallyRealRoots.princ, MonoidHom.comap_ker]
    rfl
  haveI : Module.IsTorsionFree K' Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have h2z : ∀ m : ZMod l, 2 • m = 0 → m = 0 := by
    intro m hm
    have h2u : (2 : ZMod l) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).mp h')
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hm
    exact (mul_eq_zero.mp hm).resolve_left h2u
  have hmap := Kum.pullOnto ℚ Ω K' (V ⊓ (cycMod ℚ Ω l n).ker) (le_of_eq hgal'.symm) 1 (ZMod l) (ZMod l)
    one_ne_zero (le_of_eq hgal') (Or.inr h2z)
  show Module.rank (ZMod l) (Kum.XDual 1 (V ⊓ (cycMod ℚ Ω l n).ker) (ZMod l) (ZMod l)) ≤ r
  rw [← hmap]
  have hc := Two.cardClDual K' l 1
  calc _ ≤ _ := rank_map_le _ _
    _ ≤ r := rank_le_of_cardLe l _ r ⟨hc.1, hc.2.trans (hr n K')⟩

private theorem kills_open {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {C : Type} [Group C] (N : ℕ) (hN : N ≠ 0)
    (χ : G ℚ Ω →* C) (h : Af.KillsMu N χ) : IsOpen (χ.ker : Set (G ℚ Ω)) := by
  classical
  let S : Finset Ω := (Polynomial.nthRoots N (1 : Ω)).toFinset
  have hS : ∀ ζ : Ω, ζ ^ N = 1 → ζ ∈ (S : Set Ω) := by
    intro ζ hζ
    simp only [S, Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)).mpr hζ
  have hint : ∀ x ∈ (S : Set Ω), IsIntegral ℚ x := by
    intro x hx
    simp only [S, Finset.mem_coe, Multiset.mem_toFinset] at hx
    have hx' := (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)).mp hx
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero hN)
    rw [hx']
    exact isIntegral_one
  let E := IntermediateField.adjoin ℚ (S : Set Ω)
  haveI : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin hint
  have hle : E.fixingSubgroup ≤ χ.ker := by
    intro s hs
    rw [MonoidHom.mem_ker]
    apply h
    intro ζ hζ
    have hm : ζ ∈ E := IntermediateField.subset_adjoin ℚ _ (hS ζ hζ)
    exact (IntermediateField.mem_fixingSubgroup_iff E s).mp hs ζ hm
  exact Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen E)

theorem UpperTheory.V.Fr.b0 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (H₀ : Subgroup (G ℚ Ω)) (w : ℕ), FrobeniusSplitPrimeDatum η M H₀ → FrobeniusWitnessPrime l η Ψ M w → ∃ C₀ : ℕ, ∀ m, GC.clRk l (Upl l Hb H₀ w m ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker) ≤ C₀ := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG H₀ w h0 hW
  obtain ⟨a, hηk, hΨk⟩ := hG.cyc
  have hMa : M ^ a ≠ 0 := pow_ne_zero _ hG.M_ne
  have hth' := hth Ω l w hW.prime hW.one
  have hk1 : Af.KillsMu l (cycMod ℚ Ω l 1) := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    intro s hs
    apply Units.ext
    rw [Units.val_one]
    show PadicInt.toZModPow 1 (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) : ℤ_[l]) = 1
    rw [cyclotomicCharacter.toZModPow]
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    have htn : (t : Ω) ^ (l ^ 1) = 1 := by
      rw [mem_rootsOfUnity] at ht
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    change s (t : Ω) = (t : Ω) ^ (1 : ZMod (l ^ 1)).val
    have h1 : l ^ 1 ≠ 1 := by
      rw [pow_one]
      exact (Fact.out : l.Prime).one_lt.ne'
    rw [ZMod.val_one'' h1, pow_one]
    exact hs t (by simpa using htn)
  have hηo := kills_open (M ^ a) hMa η hηk
  have hΨo := kills_open (M ^ a) hMa (barChar O Ψ) hΨk
  have h1o := kills_open l (Fact.out : l.Prime).ne_zero _ hk1
  have hc0 : commutator (G ℚ Ω) ≤ H₀ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def]
    simp only [Subgroup.mul_mem_iff_of_index_two h0.idx, inv_mem_iff]
    tauto
  set V := H₀ ⊓ Hth Ω l w ⊓ Hb ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker with hV
  have hVo : IsOpen (V : Set (G ℚ Ω)) := by
    simp only [hV, Subgroup.coe_inf]
    exact ((((h0.isOpen.inter hth'.1).inter hG.Hb_open).inter hηo).inter hΨo).inter h1o
  have hVc : commutator (G ℚ Ω) ≤ V :=
    le_inf (le_inf (le_inf (le_inf (le_inf hc0 hth'.2.1) hG.Hb_ab) (Abelianization.commutator_subset_ker _))
      (Abelianization.commutator_subset_ker _)) (Abelianization.commutator_subset_ker _)
  obtain ⟨r, hr⟩ := lev_rk l hG.odd V hVo hVc inf_le_right
  refine ⟨r, fun m => ?_⟩
  have heq : Upl l Hb H₀ w m ⊓ η.ker ⊓ (barChar O Ψ).ker ⊓ (cycMod ℚ Ω l 1).ker =
      V ⊓ (cycMod ℚ Ω l (m + 1)).ker := by
    rw [← (hlay Ω l m hG.odd).2.2.2.1]
    ext s
    simp only [hV, Upl, Subgroup.mem_inf]
    tauto
  rw [heq]
  exact hr (m + 1)
