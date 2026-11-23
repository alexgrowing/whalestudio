import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum Formalism.IndefR.Mult
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.InertLoc

open Formalism.UG (intL IsUnramInv UJ GLint cT bc)

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem mem_intL {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem odd_of_v_two (h : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) : Odd q := by
  obtain ⟨-, -, -, -, -, hq, hc⟩ := h
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hV
  have hc' : Nat.card (IsLocalRing.ResidueField V.valuationSubring) = q ^ 2 := hc
  haveI : Finite (IsLocalRing.ResidueField V.valuationSubring) :=
    Nat.finite_of_card_ne_zero (by rw [hc']; positivity)
  letI := Fintype.ofFinite (IsLocalRing.ResidueField V.valuationSubring)
  by_contra hodd
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hodd
  have h1 : ringChar (IsLocalRing.ResidueField V.valuationSubring) = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hc', hk, ← two_mul, mul_pow]
    omega
  have h3 : ((2 : ℕ) : IsLocalRing.ResidueField V.valuationSubring) = 0 := (ringChar.spec _ 2).2 (by rw [h1])
  rw [← map_natCast (IsLocalRing.residue V.valuationSubring), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff] at h3
  exact absurd h2 (ne_of_lt h3)

theorem exists_delta_psi (h : IsUnramInv ϖ σ q) (h2 : Valued.v (2 : L) = 1) (θ : AddChar L ℂ) (hθ : ∀ z, θ (σ z) * θ z = 1)
    (hc : ∀ z, (∀ u ∈ intL L, θ (z * u) = 1) ↔ z ∈ intL L) :
    ∃ (δ : L) (ψ : AddChar L ℂ), (Valued.v δ = 1 ∧ σ δ = -δ) ∧ (∀ a ∈ intL L, σ a = a → ψ a = 1) ∧
      (∃ a ∈ intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) ∧ ∀ t, ψ ((δ * t + σ (δ * t)) / 2) = θ (2⁻¹ * t) := by
  obtain ⟨hσσ, hσv, hϖ, hϖv, ⟨x, -, hx⟩, -⟩ := h
  set δ := σ x - x with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσσ, neg_sub]
  have h20 : (2 : L) ≠ 0 := fun e => by rw [e, map_zero] at h2; exact zero_ne_one h2
  have hδ0 : δ ≠ 0 := fun e => by rw [e, map_zero] at hx; exact zero_ne_one hx
  have key : ∀ t, θ (2⁻¹ * (t - σ t)) = θ t := fun t => by
    have e1 : t = 2⁻¹ * (t - σ t) + (σ (2⁻¹ * t) + 2⁻¹ * t) := by
      rw [map_mul, map_inv₀, map_ofNat]; field_simp; ring
    conv_rhs => rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hθ, mul_one]
  refine ⟨δ, θ.mulShift (2 * δ)⁻¹, ⟨hx, hσδ⟩, fun a ha _ => ?_, ?_, fun t => ?_⟩
  · rw [AddChar.mulShift_apply]
    exact (hc _).2 (mem_intL.2 (by rw [map_inv₀, map_mul, h2, hx, mul_one, inv_one])) a ha
  · have h1 : ϖ⁻¹ ∉ intL L := by
      rw [mem_intL, map_inv₀, hϖv]
      decide
    rw [← hc] at h1
    push Not at h1
    obtain ⟨u, hu, hu'⟩ := h1
    refine ⟨δ * (u - σ u), mul_mem (mem_intL.2 hx.le) (sub_mem hu (mem_intL.2 ((hσv u).trans_le hu))), ?_, ?_⟩
    · rw [map_mul, hσδ, map_sub, hσσ]; ring
    · rw [← key (ϖ⁻¹ * u), σ.map_mul, map_inv₀ σ, hϖ] at hu'
      rw [AddChar.mulShift_apply]
      convert hu' using 2
      field_simp
  · rw [AddChar.mulShift_apply, ← key (2⁻¹ * t), σ.map_mul, hσδ, σ.map_mul, map_inv₀ σ, map_ofNat]
    congr 1
    field_simp
    ring

end Local

section CM

open GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus GlobalTheory.InertDoubleCoset

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_chart_cm (hc : CMData (maximalRealSubfield E) E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    {e : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (he : IsIdemOf E v e)
    (hin : Formalism.UG.IsInertAt (maximalRealSubfield E) E v P) :
    ∃ (ϖ : P.adicCompletion E) (σ : P.adicCompletion E →+* P.adicCompletion E) (q : ℕ)
      (π : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* P.adicCompletion E), IsUnramInv ϖ σ q ∧
      (Function.Surjective π ∧ (∀ a, π a = 0 ↔ e * a = 0) ∧
        (∀ x : E, π (inclR (AF (maximalRealSubfield E)) x) = algebraMap E _ x) ∧
        (∀ z, π (sigR (AF (maximalRealSubfield E)) hc.sig z) = σ (π z)) ∧
        ∀ a, finP _ E (e * a) ∈ intA (maximalRealSubfield E) E ↔ π a ∈ intL _) ∧
      ∀ V : HSpace E, ∃ (β : GL (Fin V.rank) (P.adicCompletion E))
        (ι : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) →* HA (AF (maximalRealSubfield E)) hc.sig V.gram),
        (cT σ β.1 * V.gram.map (algebraMap E _) * β.1 = 1 ∧
          ∀ y : Fin V.rank → AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E,
            (fun i => finP _ E (e * y i)) ∈ lamHat (maximalRealSubfield E) V ↔
              ∀ i, ((β⁻¹).1 *ᵥ fun k => π (y k)) i ∈ intL _) ∧
        (∀ g, Supp hc V e (ι g)) ∧
        (∀ g, (HA.mat (AF (maximalRealSubfield E)) hc.sig V.gram (ι g)).1.map π = β.1 * g.1.1 * (β⁻¹).1) ∧
        (∀ x, Supp hc V e x → ∃ g, ι g = x) ∧
        ∀ g, (IsFin hc V (ι g) ∧ Stab hc V (ι g)) ↔ g.1 ∈ GLint (Fin V.rank) (intL _) := by
  have hur := unramified hc
  obtain ⟨σ, ϖ, hσE, hU⟩ := GlobalTheory.FixedPrime.exists_isUnramInv v P hin
  obtain ⟨ψ, hψE, hψσ, hψO⟩ := GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion E v P hin σ hσE hU.2.1
  let ψ' : LocAlg v →+* P.adicCompletion E := ψ
  have hO : ∀ z, z ∈ ordAt E v ↔ ψ' z ∈ intL _ := fun z => (mem_ordAt_iff v z).trans (hψO z)
  let π : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* P.adicCompletion E :=
    ψ'.comp ((evF E v).comp (finP _ E))
  have hπ : ∀ a, π a = ψ (evF E v (finP _ E a)) := fun a => rfl
  have hev : ∀ a, evF E v (finP _ E (e * a)) = evF E v (finP _ E a) := fun a => by
    rw [map_mul, map_mul, he.2.1, one_mul]
  have hew : ∀ a w, w ≠ v → evF E w (finP _ E (e * a)) = 0 := fun a w hw => by
    rw [map_mul, map_mul, he.2.2 w hw, zero_mul]
  refine ⟨ϖ, σ, _, π, hU, ⟨fun z => ?_, fun a => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_, fun z => ?_, fun a => ?_⟩, fun V => ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, finP _ E a = sgT E v (ψ.symm z) :=
      Algebra.TensorProduct.map_surjective _ _ (fun b => ⟨pairA _ 0 b, rfl⟩) Function.surjective_id _
    exact ⟨a, by rw [hπ, ha, evF_sgT_self, ψ.apply_symm_apply]⟩
  · refine GlobalTheory.LatVac.tensor_prod_eq_zero (F := maximalRealSubfield E) (A := Ainf (maximalRealSubfield E))
      (B := Af (maximalRealSubfield E)) _ ?_ ?_
    · show infP _ E (e * a) = 0
      rw [map_mul, he.1, zero_mul]
    · show finP _ E (e * a) = 0
      refine evF_ext fun w => ?_
      rw [map_zero]
      by_cases hw : w = v
      · subst hw
        rw [hev]
        exact ψ.injective (h.trans ψ.map_zero.symm)
      · exact hew a w hw
  · rw [hπ, ← hev, h, map_zero, map_zero, map_zero]
  · rw [hπ, evF_finP_incl]; exact hψE x
  · rw [hπ, hπ, ← hψσ]
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rfl
  · rw [GlobalTheory.T.mem_integralFiniteAdelesTensor_iff_localOrders]
    refine Iff.trans ⟨fun h => hev a ▸ h v, fun h w => ?_⟩ (hO _)
    by_cases hw : w = v
    · subst hw; rwa [hev]
    · rw [hew a w hw]; exact zero_mem _
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary _ E hc V v e he
  let χ : P.adicCompletion E →+* LocAlg v := ψ.symm
  have hback' : ∀ x : GL (Fin V.rank) (P.adicCompletion E), bc ψ' (bc χ x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have hback : ∀ x : GL (Fin V.rank) (LocAlg v), bc χ (bc ψ' x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.symm_apply_apply _)
  have hex : ∀ g : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)),
      ∃ k, Supp hc V e k ∧ locMat hc V v k = h * bc χ g.1 * h⁻¹ := fun g => by
    have h1 := bc_mem_UJ_one (σ' := locConj v) χ
      (fun z => ψ.injective (by
        rw [hψσ]
        exact (ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) g.2
    exact s3 _ (conj_mem_UJ _ (inv_frame _ hon) h1)
  choose ι hι1 hι2 using hex
  have hmul : ∀ k k', Supp hc V e k → Supp hc V e k' → Supp hc V e (k * k') := fun k k' hk hk' => by
    rw [s1] at hk hk' ⊢
    refine ⟨?_, fun w hw => by rw [map_mul, hk.2 w hw, hk'.2 w hw, mul_one]⟩
    exact ((bc (infP _ E)).map_mul (HA.mat _ hc.sig V.gram k) (HA.mat _ hc.sig V.gram k')).trans
      (by rw [hk.1, hk'.1, mul_one])
  refine ⟨bc ψ' h, MonoidHom.mk' ι fun g g' => s2 _ _ (hι1 _) (hmul _ _ (hι1 _) (hι1 _)) ?_, ⟨?_, fun y => ?_⟩, hι1,
    fun g => ?_, fun x hx => ?_, fun g => ?_⟩
  · rw [map_mul, hι2, hι2, hι2, Subgroup.coe_mul, map_mul]
    group
  · have := congrArg (fun m => m.map ψ') hon
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero ψ') (map_one ψ')] at this
    rw [← this]
    congr 2
    · exact Matrix.ext fun i j => (hψσ _).symm
    · exact Matrix.ext fun i j => (hψE _).symm
  · rw [mem_lamHat_iff]
    refine Iff.trans ⟨fun h => by simpa only [hev] using h v, fun h w => ?_⟩ ((hfr fun i => evF E v (finP _ E (y i))).trans
      (forall_congr' fun i => (hO _).trans ?_))
    · by_cases hw : w = v
      · subst hw; simpa only [hev] using h
      · simp only [hew _ w hw]; exact zero_mem _
    · rw [RingHom.map_mulVec, ← map_inv]; rfl
  · have := congrArg (fun m => (bc ψ' m).1) (hι2 g)
    simp only [map_mul, map_inv, hback'] at this
    exact this
  · refine ⟨⟨bc ψ' (h⁻¹ * locMat hc V v x * h), bc_mem_UJ_one (σ := locConj v) ψ' hψσ
      (conj_mem_UJ _ hon (locMat_mem hc V v x))⟩, s2 _ _ (hι1 _) hx ?_⟩
    show locMat hc V v (ι _) = _
    rw [hι2, hback]
    group
  · have h1 := (s1 _).1 (hι1 g)
    show IsFin hc V (ι g) ∧ Stab hc V (ι g) ↔ _
    rw [and_iff_right h1.1, GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ E hc V v h hfr _ h1.2, hι2, bc_mem_range_iff ψ' hO,
      show h⁻¹ * (h * bc χ g.1 * h⁻¹) * h = bc χ g.1 by group, hback']
    rfl

end CM

section Host

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev LP (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : Type := P.adicCompletion D.host.E

variable {P : HeightOneSpectrum (𝓞 D.host.E)}

def Chart (e : AE D) (σ : LP D P →+* LP D P) (π : AE D →+* LP D P) : Prop :=
  (e * e = e ∧ cA D e = e ∧ infPart D e = 0) ∧ Function.Surjective π ∧ (∀ a, π a = 0 ↔ e * a = 0) ∧
    (∀ x : D.host.E, π (incA D x) = algebraMap D.host.E (LP D P) x) ∧ (∀ z, π (cA D z) = σ (π z)) ∧
    ∀ a, finPart D (e * a) ∈ intAE D ↔ π a ∈ intL (LP D P)

def Frame (V : HSp D) (e : AE D) (σ : LP D P →+* LP D P) (π : AE D →+* LP D P) (β : GL (Fin V.rank) (LP D P)) : Prop :=
  cT σ β.1 * V.gram.map (algebraMap D.host.E (LP D P)) * β.1 = 1 ∧
    ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ LamHat V ↔
      ∀ i, ((β⁻¹).1 *ᵥ fun k => π (y k)) i ∈ intL (LP D P)

def GrpChart (V : HSp D) (e : AE D) (σ : LP D P →+* LP D P) (π : AE D →+* LP D P) (β : GL (Fin V.rank) (LP D P))
    (ι : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (LP D P)) →* GA D V) : Prop :=
  (∀ g, SuppF V e (ι g)) ∧ (∀ g, (Formalism.L2.Theta.mt V (ι g)).map π = β.1 * g.1.1 * (β⁻¹).1) ∧
    (∀ x, SuppF V e x → ∃ g, ι g = x) ∧ ∀ g, ι g ∈ KsphC V ∅ ↔ g.1 ∈ GLint (Fin V.rank) (intL (LP D P))

theorem exists_chart (hP : Formalism.DivisionValues.conjPl P = P) {e : AE D} (he : IsPrimeIdem P e e) :
    ∃ (ϖ : LP D P) (σ : LP D P →+* LP D P) (q : ℕ) (π : AE D →+* LP D P), IsUnramInv ϖ σ q ∧ Valued.v (2 : LP D P) = 1 ∧
      Chart e σ π ∧ ∀ V : HSp D, ∃ β ι, Frame V e σ π β ∧ GrpChart V e σ π β ι := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  have hP' : P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal := congrArg HeightOneSpectrum.asIdeal hP
  have hfix : ∀ x : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E x ∈ P.asIdeal ↔ x ∈ P.asIdeal := fun x => by
    conv_lhs => rw [← hP']
    exact Ideal.apply_mem_of_equiv_iff
  have h2 : Valued.v (2 : LP D P) = 1 := by
    have h : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
      Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h (Ideal.ext fun x => by
        rw [Ideal.mem_comap, ← hfix x]
        refine Eq.to_iff (congrArg (· ∈ P.asIdeal) (RingOfIntegers.ext ?_))
        exact (GlobalTheory.SplitIdem.star_eq_conj _ _).symm)
    rw [← map_ofNat (algebraMap D.host.E (LP D P)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h
  obtain ⟨i1, i2, -⟩ := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.1 P e e he
  rcases he with ⟨⟨⟨-, h3, -⟩, h4⟩, -⟩ | ⟨-, ⟨v, ε, ⟨α, rfl, a1, a2⟩, rfl⟩, hPe⟩
  · exfalso
    rw [i2, i1] at h3
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    refine (h4 x hx0).1 hx ?_
    rw [h3, zero_mul, RingHom.map_zero]
    exact zero_mem _
  have he := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2
  have hin0 := GlobalTheory.FixedPrime.isInertAt_under P fun x hx => (hfix x).1 hx
  have hin := GlobalTheory.InertDoubleCoset.inert_of_idem (E := D.host.E) he hPe (by
    by_contra hne
    push Not at hne
    have h1 : P.asIdeal ≤ P.asIdeal ^ 2 := by
      conv_lhs => rw [← show _ = P.asIdeal from hin0]
      exact Ideal.map_le_iff_le_comap.2 fun x hx => hne x _ rfl hx
    exact (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl).not_ge h1)
  obtain ⟨ϖ, σ, q, π, hU, hπ, hV⟩ := exists_chart_cm (E := D.host.E) D.sp.cm he hin
  refine ⟨ϖ, σ, q, π, hU, h2, ⟨⟨i1, i2, he.1⟩, hπ⟩, fun V => ?_⟩
  obtain ⟨β, ι, h1, h3, h4, h5, h6⟩ := hV V
  exact ⟨β, ι, h1, h3, h4, h5, fun g => (GlobalTheory.InertDoubleCoset.mem_KsphC_iff V _).trans (h6 g)⟩

end Host

end GlobalTheory.InertLoc
