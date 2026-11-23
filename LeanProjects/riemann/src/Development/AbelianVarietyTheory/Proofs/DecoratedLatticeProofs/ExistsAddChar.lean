import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.SymTieExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

theorem hom_extend {A B C : Type} [AddCommGroup A] [AddCommGroup B] [CommGroup C]
    (hC : ∀ n : ℕ, n ≠ 0 → ∀ c : C, ∃ d : C, d ^ n = c) (i : A →+ B) (hi : Function.Injective i)
    (f : A →+ Additive C) : ∃ g : B →+ Additive C, ∀ a, g (i a) = f a := by
  letI : DivisibleBy (Additive C) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨d, hd⟩ := hC n hn (Additive.toMul u)
    exact ⟨Additive.ofMul d, congrArg Additive.ofMul hd⟩
  letI : DivisibleBy (Additive C) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (Additive C)).extension_property_addMonoidHom i hi f
  exact ⟨g, fun a => DFunLike.congr_fun hg a⟩

theorem circle_roots (n : ℕ) (hn : n ≠ 0) (c : Circle) : ∃ d : Circle, d ^ n = c := by
  obtain ⟨t, ht⟩ := Circle.exp_surjective c
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact ⟨Circle.exp (t / n), by rw [← ht, ← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hn']⟩

theorem units_roots (n : ℕ) (hn : n ≠ 0) (c : ℂˣ) : ∃ d : ℂˣ, d ^ n = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) (Nat.pos_of_ne_zero hn)
  have h0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact c.ne_zero hz.symm
  exact ⟨Units.mk0 z h0, Units.ext (by simpa using hz)⟩

section Local
variable {k : Type} [Field k] [ValuativeRel k] {F : Type} [CommRing F]

theorem exists_addChar (ϖ : kˣ) (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : 𝒪[k] →+* F) (hr : Function.Surjective r)
    (h0 : ∀ x : 𝒪[k], valuation k (x : k) < 1 → r x = 0) (α : AddChar F Circle) (hα : α ≠ 1) :
    ∃ ψ : AddChar k Circle, HasConductor ψ 1 ∧ ∀ x : 𝒪[k], ψ ((x : k) / ϖ) = α (r x) := by
  let i : 𝒪[k] →+ k := (AddMonoidHom.mulRight ((ϖ : k)⁻¹)).comp (𝒪[k]).subtype.toAddMonoidHom
  have hi : Function.Injective i := fun x y h => Subtype.ext (mul_right_cancel₀ (inv_ne_zero ϖ.ne_zero) h)
  obtain ⟨g, hg⟩ := hom_extend circle_roots i hi (α.toAddMonoidHom.comp r.toAddMonoidHom)
  have hv : ∀ x : 𝒪[k], AddChar.toAddMonoidHomEquiv.symm g ((x : k) / ϖ) = α (r x) := fun x => by
    rw [div_eq_mul_inv]
    exact congrArg Additive.toMul (hg x)
  have hϖ1 : valuation k (ϖ : k) < 1 := (hϖ _).2 le_rfl
  have hp : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  refine ⟨AddChar.toAddMonoidHomEquiv.symm g, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩, hv⟩
  · by_contra hx
    rw [Units.val_one, map_one, not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hxi : valuation k x⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
    have h2 := (hϖ _).1 hxi
    have h3 : valuation k (ϖ : k)⁻¹ ≤ valuation k x := by
      rw [map_inv₀] at h2 ⊢
      exact inv_le_of_inv_le₀ (by simp [zero_lt_iff, hx0]) h2
    refine hα (AddChar.ext _ _ fun t => ?_)
    obtain ⟨z, rfl⟩ := hr t
    rw [← hv z]
    refine h _ (le_trans ?_ h3)
    rw [div_eq_mul_inv, map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 z.2)
  · have hy1 : valuation k y ≤ 1 := by simpa using hy.trans h
    have hlt : valuation k (y * ϖ) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hy1) hϖ1
    have h4 := hv ⟨y * ϖ, (Valuation.mem_integer_iff _ _).2 hlt.le⟩
    rw [h0 _ hlt, AddChar.map_zero_eq_one] at h4
    simpa using h4

theorem exists_tame (r : 𝒪[k] →+* F) (h0 : ∀ x : 𝒪[k], valuation k (x : k) < 1 → r x = 0) (χ : Fˣ →* ℂˣ) :
    ∃ μ : kˣ →* ℂˣ, IsTame μ ∧ ∀ u : (𝒪[k])ˣ, μ (Units.map (𝒪[k]).subtype.toMonoidHom u) = χ (Units.map r.toMonoidHom u) := by
  obtain ⟨g, hg⟩ := hom_extend units_roots (MonoidHom.toAdditive (Units.map (𝒪[k]).subtype.toMonoidHom))
    (Units.map_injective Subtype.val_injective) (MonoidHom.toAdditive (χ.comp (Units.map r.toMonoidHom)))
  have hv : ∀ u : (𝒪[k])ˣ, MonoidHom.toAdditive.symm g (Units.map (𝒪[k]).subtype.toMonoidHom u) =
      χ (Units.map r.toMonoidHom u) := fun u => congrArg Additive.toMul (hg (Additive.ofMul u))
  refine ⟨MonoidHom.toAdditive.symm g, fun x hx => ?_, hv⟩
  have hx1 : valuation k (x : k) = 1 := by
    have := Valuation.map_one_add_of_lt (valuation k) hx
    simpa using this
  let x' : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff _ _).2 hx1.le⟩
  have hu : IsUnit x' := by
    by_contra h
    exact absurd (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h) (by simp [x', hx1])
  have e : Units.map (𝒪[k]).subtype.toMonoidHom hu.unit = x := Units.ext rfl
  have e2 : Units.map r.toMonoidHom hu.unit = 1 := by
    refine Units.ext ?_
    have := h0 (x' - 1) hx
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this
  rw [← e, hv, e2, map_one]

end Local

section Res
variable {E k : Type} [Field E] [NumberField E]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reduction_spec (P : HeightOneSpectrum (𝓞 E)) {a : E} (h : IntAt P a) :
    ∃ r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  obtain ⟨r, s, hs, e⟩ := h
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨(Ideal.Quotient.mk P.asIdeal s)⁻¹ * Ideal.Quotient.mk P.asIdeal r, r, s, hs, e, mul_inv_cancel_left₀ hs' _⟩
  unfold redP
  rw [dif_pos hex]
  exact hex.choose_spec

theorem exists_residue (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a)
    (hd : DenseRange ι) :
    ∃ r : 𝒪[k] →+* 𝓞 E ⧸ P.asIdeal, Function.Surjective r ∧ (∀ x : 𝒪[k], r x = 0 ↔ valuation k (x : k) < 1) ∧
      ∀ a (h : ι a ∈ 𝒪[k]), r ⟨ι a, h⟩ = redP P a := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hlt : ∀ y : 𝒪[k], IsLocalRing.residue 𝒪[k] y = 0 ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  let j : 𝓞 E →+* 𝒪[k] := (ι.comp (algebraMap (𝓞 E) E)).codRestrict _ fun r =>
    (hint _).2 ⟨r, 1, h1, by simp⟩
  have hj : ∀ r, (j r : k) = ι (algebraMap (𝓞 E) E r) := fun _ => rfl
  let φ : 𝓞 E →+* 𝓀[k] := (IsLocalRing.residue 𝒪[k]).comp j
  have hker : ∀ r ∈ P.asIdeal, φ r = 0 := by
    intro r hr
    refine (hlt _).2 ?_
    by_contra hlt'
    have hv : valuation k (j r : k) = 1 :=
      le_antisymm ((Valuation.mem_integer_iff _ _).1 (j r).2) (not_lt.1 hlt')
    have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
      intro h
      rw [hj, h] at hv
      simp at hv
    obtain ⟨t, s, hs, e⟩ := (hint (algebraMap (𝓞 E) E r)⁻¹).1 (by
      rw [Valuation.mem_integer_iff, map_inv₀, map_inv₀, ← hj, hv, inv_one])
    apply hs
    have : s = t * r := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_mul, ← e, inv_mul_cancel_right₀ hr0]
    rw [this]
    exact Ideal.mul_mem_left _ _ hr
  let φ' : 𝓞 E ⧸ P.asIdeal →+* 𝓀[k] := Ideal.Quotient.lift _ φ hker
  have hφ' : ∀ r, φ' (Ideal.Quotient.mk _ r) = IsLocalRing.residue 𝒪[k] (j r) := fun _ => rfl
  have hred : ∀ a (h : ι a ∈ 𝒪[k]), φ' (redP P a) = IsLocalRing.residue 𝒪[k] ⟨ι a, h⟩ := by
    intro a h
    obtain ⟨r, s, hs, e, e'⟩ := reduction_spec P ((hint a).1 h)
    have hs' : φ' (Ideal.Quotient.mk P.asIdeal s) ≠ 0 := by
      rwa [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    apply mul_left_cancel₀ hs'
    rw [← map_mul, e', hφ', hφ', ← map_mul]
    congr 1
    apply Subtype.ext
    change ι (algebraMap (𝓞 E) E r) = ι (algebraMap (𝓞 E) E s) * ι a
    rw [← map_mul, e]
  have hsurj : Function.Surjective φ' := by
    intro t
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective t
    have hn : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨1, by simp⟩
    obtain ⟨a, ha⟩ := hd.mem_nhds hn
    have ha' : valuation k (ι a - x) < 1 := ha
    have hm : ι a ∈ 𝒪[k] := by
      have := add_mem ((Valuation.mem_integer_iff _ _).2 ha'.le) x.2
      simpa using this
    refine ⟨redP P a, ?_⟩
    rw [hred a hm, ← sub_eq_zero, ← map_sub]
    exact (hlt _).2 ha'
  let e := RingEquiv.ofBijective φ' ⟨φ'.injective, hsurj⟩
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue 𝒪[k]), e.symm.surjective.comp IsLocalRing.residue_surjective,
    fun x => ?_, fun a h => ?_⟩
  · rw [← hlt]
    exact map_eq_zero_iff _ e.symm.injective
  · change e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    exact (hred a h).symm

end Res

theorem exists_tie : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ)
    (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (ρ κ : ℕ),
    IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ψ₀ ≠ 1 → ∃ S : SymData k (2 * ρ) κ, Comparison₂ P q ι σ₀ ψ₀ χ S := by
  intro E K k _ _ _ _ _ _ _ _ P q ι ϖ σ₀ ψ₀ χ ρ κ hc hϖ hψ₀
  obtain ⟨r, hr, h0, hred⟩ := exists_residue P ι hc.int hc.dense
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  let α : AddChar (𝓞 E ⧸ P.asIdeal) Circle := AddChar.circleEquivComplex.symm (σ₀.toMonoidHom.compAddChar ψ₀)
  have hαv : ∀ t, (α t : ℂ) = σ₀ (ψ₀ t) := fun t =>
    DFunLike.congr_fun (AddChar.circleEquivComplex.apply_symm_apply (σ₀.toMonoidHom.compAddChar ψ₀)) t
  have hα : α ≠ 1 := by
    intro h
    refine hψ₀ (AddChar.ext _ _ fun t => σ₀.injective ?_)
    rw [← hαv, h]
    simp
  obtain ⟨ψ, hψ, hψv⟩ := exists_addChar ϖ hϖ r hr (fun x => (h0 x).2) α hα
  choose μ hμ hμv using fun i =>
    exists_tame r (fun x => (h0 x).2) ((Units.map σ₀.toMonoidHom).comp (χ (i - 1)))
  obtain ⟨L, hL⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel k ψ hψ ϖ hϖ ρ κ (2 * ρ + 1)
  refine ⟨SymData.mk ψ ϖ ρ L μ hμ hψ hϖ rfl hL, hc, fun a ha => ?_, fun i a u ha hu e => ?_⟩
  · have h := hψv ⟨ι a, (hc.int a).2 ha⟩
    rw [hred] at h
    change (ψ (ι (a / (q : E))) : ℂ) = _
    rw [map_div₀, ← hc.unif, ← hαv, ← h]
  · let x : 𝒪[k] := ⟨ι a, (hc.int a).2 ha⟩
    have hx : IsUnit x := by
      by_contra h
      have h1 := (h0 x).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h)
      rw [hred] at h1
      haveI := P.isPrime
      exact hu.ne_zero h1
    have e1 : Units.map (𝒪[k]).subtype.toMonoidHom hx.unit = u := Units.ext e.symm
    have e2 : Units.map r.toMonoidHom hx.unit = hu.unit := Units.ext (hred a _)
    change (μ (i + 1) u : ℂ) = _
    rw [← e1, hμv, e2, LocE.unitV, dif_pos hu]
    rfl

end GlobalTheory.SymTieExists
