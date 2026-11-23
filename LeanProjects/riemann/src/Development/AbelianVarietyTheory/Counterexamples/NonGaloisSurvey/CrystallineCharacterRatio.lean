import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCyclotomic

noncomputable section

namespace GlobalTheory.Survey.CrystallineCharacterRatio

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module TensorProduct
  GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]

end Abstract

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω]

theorem chi_eq_cyc (P : LocPrime l) (j : Ω →+* Om l) (σ : Formalism.ConjugateSelfDual.G E Ω) (g : GQ l)
    (h : ∀ x, g (j x) = j (σ x)) :
    ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  set c : ℤ_[l] := ((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc

  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (c : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ' : IsPrimitiveRoot (j ζ) (l ^ m) := hζ.map_of_injective j.injective
    have hσζ : σ ζ = ζ ^ (PadicInt.toZModPow m c).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G E Ω) Ω σ) ζ hζ.pow_eq_one
    obtain ⟨a, ha1, ha2⟩ := P.χQ_cyc g m (j ζ) hζ'.pow_eq_one
    have hne : j ζ ≠ 0 := hζ'.ne_zero (pow_ne_zero _ hl.ne_zero)
    have hpow : (j ζ) ^ a = (j ζ) ^ (PadicInt.toZModPow m c).val := by
      rw [← ha2, h, hσζ, map_pow]
    have hdvd : ((l ^ m : ℕ) : ℤ) ∣ (a : ℤ) - ((PadicInt.toZModPow m c).val : ℤ) := by
      rw [← hζ'.zpow_eq_one_iff_dvd, zpow_sub₀ hne, zpow_natCast, zpow_natCast, hpow,
        div_self (pow_ne_zero _ hne)]
    have h2 : ‖((a : ℚ_[l]) - (((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - ((PadicInt.toZModPow m c).val : ℤ)) m).mpr
        (by exact_mod_cast hdvd)
      exact_mod_cast this
    have h3 : ‖((((PadicInt.toZModPow m c).val : ℕ) : ℤ_[l]) - c)‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_natCast, ZMod.natCast_zmod_val, sub_self]
    have h3' : ‖((((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]) - (c : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_def] at h3
      exact_mod_cast h3
    have hsplit : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (c : ℚ_[l]) =
        (((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) +
          (((a : ℚ_[l]) - (((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l])) +
            ((((PadicInt.toZModPow m c).val : ℕ) : ℚ_[l]) - (c : ℚ_[l]))) := by ring
    rw [hsplit]
    refine (Padic.nonarchimedean _ _).trans (max_le ha1 ((Padic.nonarchimedean _ _).trans (max_le h2 h3')))
  refine sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_))
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hl1
  refine (key m).trans ?_
  rw [zpow_neg, zpow_natCast, ← inv_pow, zero_add]
  exact hm.le

end Bridge

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem locChi_eps (g : Br.G D.nbr i w hw) :
    ((Br.locChi D.nbr i w hw (epsU D.nd i) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        (((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hχ := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw g

  have hc := chi_eq_cyc (D.loc (D.nd.l i)) (D.nbr i w hw).j
    ((ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype ((D.nbr i w hw).e.symm g)) _ (fun x => by
      have := (D.nbr i w hw).e_comm ((D.nbr i w hw).e.symm g) x
      rw [MulEquiv.apply_symm_apply] at this
      exact this)
  unfold Br.locChi Br.chiG Br.PD
  rw [hχ, hc]
  unfold epsU Glob.epsO LocBridge.toLL decS Br.ι
  simp only [RingHom.comp_apply, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  erw [(D.nbr i w hw).eO_alg]
  rfl

end GlobalTheory.Survey.CrystallineCharacterRatio
