import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published

namespace PoitouTate

section Local

variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  (l : ℕ) [Fact l.Prime] (r : ℕ)

abbrev muLoc (A : ValuationSubring Ω) :
    Representation (ZMod (l ^ r)) (Dec (F := F) A) (ZMod (l ^ r)) :=
  charRep ((cycMod F Ω l r).comp (Dec (F := F) A).subtype)

variable (Ω) in

abbrev InvFam : Type :=
  ∀ A : ValuationSubring Ω, H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)

variable {F l r}

def IsNormalised (ζ : Ω) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F))
    (inv : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) : Prop :=
  ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)),
    ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) →
    (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) →
    (∀ g h, χ (g * h) = χ g + χ h) →
    (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) →
    (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) →
    (∀ g h, z.1 (g, h) = κ g * χ h) →
    inv (Submodule.Quotient.mk z) = 1

def ConjCompatible (ζ : Ω) (inv : InvFam F Ω l r) : Prop :=
  ∀ (σ : Ω ≃+* Ω) (τ : F ≃+* F), (∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)) →
  ∀ c : ZMod (l ^ r), σ ζ = ζ ^ c.val →
  ∀ (A A' : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
    (∀ x, σ x ∈ A' ↔ x ∈ A) →
  ∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F l r A')),
    (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F) A'),
      (∀ x, (g' : G F Ω) (σ x) = σ ((g : G F Ω) x)) →
      (∀ x, (h' : G F Ω) (σ x) = σ ((h : G F Ω) x)) → z'.1 (g', h') = c * z.1 (g, h)) →
    inv A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)

def IsLocalInvariants (ζ : Ω) (inv : InvFam F Ω l r) : Prop :=
  (∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
    Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A)) ∧
  ConjCompatible ζ inv

end Local

section Global

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)

theorem locFam_apply_eq (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (v : S)
    (g : Dec (F := F) (Av v)) (m : ZMod (l ^ r)) :
    ((charRep μ).comp (locFam S Av v)) g m = muLoc F l r (Av v) g m := by
  have key : μ (toGS Ω _ (g : G F Ω)) = cycMod F Ω l r g := by
    rw [← hμ]
    rfl
  show charRep μ (toGS Ω _ (g : G F Ω)) m =
    charRep ((cycMod F Ω l r).comp (Dec (F := F) (Av v)).subtype) g m
  rw [charRep_apply, charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, key]

def toMuLoc (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (v : S) :
    H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] H2 (muLoc F l r (Av v)) :=
  mapH2 _ _ LinearMap.id continuous_id (locFam_apply_eq S Av μ hμ v)

theorem toMuLoc_bijective (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (v : S) :
    Function.Bijective (toMuLoc S Av μ hμ v) := by

  have hback : ∀ (g : Dec (F := F) (Av v)) (m : ZMod (l ^ r)),
      (LinearMap.id : ZMod (l ^ r) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (muLoc F l r (Av v) g m) =
        ((charRep μ).comp (locFam S Av v)) g
          ((LinearMap.id : ZMod (l ^ r) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) m) :=
    fun g m => (locFam_apply_eq S Av μ hμ v g m).symm
  refine Function.bijective_iff_has_inverse.mpr
    ⟨mapH2 _ _ LinearMap.id continuous_id hback, fun c => ?_, fun c => ?_⟩
  · exact Submodule.Quotient.induction_on _ c fun z => rfl
  · exact Submodule.Quotient.induction_on _ c fun z => rfl

def invAt (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) (inv : InvFam F Ω l r) (v : S) :
    H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r) :=
  (inv (Av v)).comp (toMuLoc S Av μ hμ v)

theorem invAt_bijective (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) {ζ : Ω} {inv : InvFam F Ω l r}
    (h : IsLocalInvariants ζ inv) (v : S) (hv : IsPlaceOver (Av v) v.1) :
    Function.Bijective (invAt S Av μ hμ inv v) := by
  rw [invAt, LinearMap.coe_comp]
  exact (h.1 (Av v) v.1 hv).1.comp (toMuLoc_bijective S Av μ hμ v)

variable (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

def loc0 : H0 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H0 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH0 ρ (locFam S Av v)

def loc1 : H1 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H1 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH1 ρ (locFam S Av v) (continuous_locFam S Av v)

def loc2 : H2 ρ →ₗ[ZMod (l ^ r)] ∀ v : S, H2 (ρ.comp (locFam S Av v)) :=
  LinearMap.pi fun v => resH2 ρ (locFam S Av v) (continuous_locFam S Av v)

def tr0 : (∀ v : S, H0 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H2 (twDual μ ρ)) :=
  ∑ v : S, (((cupH0H2TwistedDual μ ρ (locFam S Av v)).compr₂ (j v)).compl₁₂ (LinearMap.proj v)
    (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v)))

def tr1 (hρ : ContAction ρ) : (∀ v : S, H1 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H1 (twDual μ ρ)) :=
  ∑ v : S, (((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).flip.compr₂
    (j v)).compl₁₂ (LinearMap.proj v)
    (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v)))

def tr2 : (∀ v : S, H2 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
    Module.Dual (ZMod (l ^ r)) (H0 (twDual μ ρ)) :=
  ∑ v : S, (((cup20 μ ρ (locFam S Av v)).compr₂ (j v)).compl₁₂ (LinearMap.proj v)
    (resH0 (twDual μ ρ) (locFam S Av v)))

theorem poitouTateNineTerm_transgressionZero_apply (x : ∀ v : S, H0 (ρ.comp (locFam S Av v))) (y : H2 (twDual μ ρ)) :
    tr0 S Av μ j ρ x y = ∑ v : S, j v (cupH0H2TwistedDual μ ρ (locFam S Av v) (x v)
      (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y)) := by
  simp only [tr0, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.proj_apply]

theorem poitouTateNineTerm_transgressionOne_apply (hρ : ContAction ρ) (x : ∀ v : S, H1 (ρ.comp (locFam S Av v)))
    (y : H1 (twDual μ ρ)) :
    tr1 S Av μ j ρ hρ x y = ∑ v : S, j v (cupH1H1TwistedDual μ ρ (locFam S Av v)
      (hρ.comp' (continuous_locFam S Av v))
      (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) := by
  simp only [tr1, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.flip_apply, LinearMap.proj_apply]

theorem poitouTateNineTerm_transgressionTwo_apply (x : ∀ v : S, H2 (ρ.comp (locFam S Av v))) (y : H0 (twDual μ ρ)) :
    tr2 S Av μ j ρ x y = ∑ v : S, j v (cup20 μ ρ (locFam S Av v) (x v)
      (resH0 (twDual μ ρ) (locFam S Av v) y)) := by
  simp only [tr2, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
    LinearMap.proj_apply]

def NineTermExact (hρ : ContAction ρ) : Prop :=
  ∃ (δ₁ : Module.Dual (ZMod (l ^ r)) (H2 (twDual μ ρ)) →ₗ[ZMod (l ^ r)] H1 ρ)
    (δ₂ : Module.Dual (ZMod (l ^ r)) (H1 (twDual μ ρ)) →ₗ[ZMod (l ^ r)] H2 ρ),
    Function.Injective (loc0 S Av ρ) ∧
    Function.Exact (loc0 S Av ρ) (tr0 S Av μ j ρ) ∧
    Function.Exact (tr0 S Av μ j ρ) δ₁ ∧
    Function.Exact δ₁ (loc1 S Av ρ) ∧
    Function.Exact (loc1 S Av ρ) (tr1 S Av μ j ρ hρ) ∧
    Function.Exact (tr1 S Av μ j ρ hρ) δ₂ ∧
    Function.Exact δ₂ (loc2 S Av ρ) ∧
    Function.Exact (loc2 S Av ρ) (tr2 S Av μ j ρ) ∧
    Function.Surjective (tr2 S Av μ j ρ)

def ShaDual : Prop :=
  (Finite (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
    Finite (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) ∧
    Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃ₗ[ZMod (l ^ r)]
      Module.Dual (ZMod (l ^ r)) (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))) ∧
    Nat.card (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) =
      Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av))) ∧
  (Finite (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) ∧
    Finite (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
    Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃ₗ[ZMod (l ^ r)]
      Module.Dual (ZMod (l ^ r)) (Sha1 ρ (locFam S Av) (continuous_locFam S Av))) ∧
    Nat.card (Sha1 ρ (locFam S Av) (continuous_locFam S Av)) =
      Nat.card (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)))

variable {S Av μ j ρ}

theorem NineTermExact.mem_range_localization_H1_iff {hρ : ContAction ρ} (h : NineTermExact S Av μ j ρ hρ)
    (x : ∀ v : S, H1 (ρ.comp (locFam S Av v))) :
    x ∈ LinearMap.range (loc1 S Av ρ) ↔ ∀ y : H1 (twDual μ ρ),
      ∑ v : S, j v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))
        (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) = 0 := by
  obtain ⟨δ₁, δ₂, -, -, -, -, h5, -, -, -, -⟩ := h
  rw [LinearMap.mem_range, ← Set.mem_range, ← h5 x, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply, poitouTateNineTerm_transgressionOne_apply]

theorem NineTermExact.mem_range_localization_H2_iff {hρ : ContAction ρ} (h : NineTermExact S Av μ j ρ hρ)
    (x : ∀ v : S, H2 (ρ.comp (locFam S Av v))) :
    x ∈ LinearMap.range (loc2 S Av ρ) ↔ ∀ y : H0 (twDual μ ρ),
      ∑ v : S, j v (cup20 μ ρ (locFam S Av v) (x v) (resH0 (twDual μ ρ) (locFam S Av v) y)) = 0 := by
  obtain ⟨δ₁, δ₂, -, -, -, -, -, -, -, h8, -⟩ := h
  rw [LinearMap.mem_range, ← Set.mem_range, ← h8 x, LinearMap.ext_iff]
  simp only [LinearMap.zero_apply, poitouTateNineTerm_transgressionTwo_apply]

def idInv (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) :
    H0 (twDual μ (charRep μ)) :=
  ⟨TDual.mk LinearMap.id, fun g => by
    ext m
    simp only [twDual_apply, TDual.mk_apply, LinearMap.id_apply, charRep_apply, map_inv]
    rw [← mul_assoc, Units.mul_inv, one_mul]⟩

theorem NineTermExact.sum_eq_zero {hρ : ContAction (charRep μ)}
    (h : NineTermExact S Av μ j (charRep μ) hρ) (x : H2 (charRep μ)) :
    ∑ v : S, j v (resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) x) = 0 := by
  obtain ⟨δ₁, δ₂, -, -, -, -, -, -, -, h8, -⟩ := h

  have key : ∀ (v : S) (c : H2 ((charRep μ).comp (locFam S Av v))),
      cup20 μ (charRep μ) (locFam S Av v) c
        (resH0 (twDual μ (charRep μ)) (locFam S Av v) (idInv μ)) = c := by
    intro v c
    refine Submodule.Quotient.induction_on _ c fun z => ?_
    simp only [cup20, cupProductH2H0, Submodule.liftQ_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply]

    congr 1

  have hz : tr2 S Av μ j (charRep μ) (loc2 S Av (charRep μ) x) = 0 := (h8 _).2 ⟨x, rfl⟩
  have hz' := LinearMap.congr_fun hz (idInv μ)
  simp only [poitouTateNineTerm_transgressionTwo_apply, loc2, LinearMap.pi_apply, key, LinearMap.zero_apply] at hz'
  exact hz'

theorem continuous_toZModPow : Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) ?_
  rw [ContinuousAt, map_zero, nhds_discrete (ZMod (l ^ r)), Filter.tendsto_pure, Metric.eventually_nhds_iff]
  refine ⟨(l : ℝ) ^ (-(r : ℤ)), zpow_pos hl0 _, fun y hy => ?_⟩
  rw [dist_zero_right] at hy
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow y r).1 hy.le
  rw [← PadicInt.ker_toZModPow] at hmem
  exact (RingHom.mem_ker).1 hmem

omit [IsAlgClosure F Ω] in
theorem continuous_cycMod [Algebra.IsAlgebraic F Ω] : Continuous (cycMod F Ω l r) := by
  rw [cycMod, MonoidHom.coe_comp]
  exact (Continuous.units_map _ continuous_toZModPow).comp (continuous_cycZ F Ω l)

theorem contAction_charRep (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r) :
    ContAction (charRep μ) := by
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic

  have hc : Continuous μ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have hpull : (μ ∘ (QuotientGroup.mk : G F Ω → GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))) =
        cycMod F Ω l r := by
      rw [← hμ]
      rfl
    rw [hpull]
    exact continuous_cycMod
  show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × ZMod (l ^ r) =>
    charRep μ p.1 p.2
  simp only [charRep_apply]
  exact (Units.continuous_val.comp (hc.comp continuous_fst)).mul continuous_snd

theorem exists_lift_cycMod (hS : ContainsAbove S l) :
    ∃ μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
      μ.comp (toGS Ω _) = cycMod F Ω l r := by
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic

  have hker : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ (cycMod F Ω l r).ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) ?_
    · intro σ hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨v, hv, A, hA, hσA⟩ := hσ
      have hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := fun h => hv (hS v h)
      have h1 : cyc F Ω l σ = 1 := cyc_eq_one_of_mem_Ine hl hA (mem_Ine.2 hσA)
      rw [cyc_eq_map_cycZ] at h1
      have h3 := congrArg Units.val h1
      rw [Units.coe_map, Units.val_one] at h3
      have hinj : Function.Injective
          ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom) :=
        (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp fun a b h => PadicInt.ext h
      have h2 : cycZ F Ω l σ = 1 := by
        refine Units.ext (hinj ?_)
        rw [Units.val_one, map_one]
        exact h3
      rw [SetLike.mem_coe, MonoidHom.mem_ker, cycMod, MonoidHom.comp_apply, h2, map_one]
    · rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage continuous_cycMod
  refine ⟨QuotientGroup.lift _ (cycMod F Ω l r) hker, MonoidHom.ext fun σ => ?_⟩
  exact QuotientGroup.lift_mk _ hker σ

end Global

end PoitouTate

open PoitouTate in

def PoitouTateTotallyComplex : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r →
  ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
  ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      NineTermExact S Av μ (invAt S Av μ hμ inv) ρ hρ ∧ ShaDual S Av μ ρ

open PoitouTate in

theorem PoitouTateTotallyComplex.annihilators (h : PoitouTateTotallyComplex)
    (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ r)) :
    ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    (∀ x : H2 (charRep μ), ∑ v : S, invAt S Av μ hμ inv v
      (resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) x) = 0) ∧
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      (∀ x : ∀ v : S, H1 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc1 S Av ρ) ↔ ∀ y : H1 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v)
            (hρ.comp' (continuous_locFam S Av v))
            (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) = 0) ∧
      (∀ x : ∀ v : S, H2 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc2 S Av ρ) ↔ ∀ y : H0 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cup20 μ ρ (locFam S Av v) (x v)
            (resH0 (twDual μ ρ) (locFam S Av v) y)) = 0) ∧
      Finite (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
      Finite (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) ∧
      Nat.card (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) =
        Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨inv, hinv, hall⟩ := h F Ω l r hr ζ hζ
  refine ⟨inv, hinv, fun S hS Av hAv μ hμ => ⟨fun x => ?_, fun M _ _ _ _ _ ρ hρ => ?_⟩⟩
  · have hρμ := contAction_charRep hμ
    exact (hall S hS Av hAv μ hμ (ZMod (l ^ r)) (charRep μ) hρμ).1.sum_eq_zero x
  · obtain ⟨hN, hSha⟩ := hall S hS Av hAv μ hμ M ρ hρ
    exact ⟨fun x => hN.mem_range_localization_H1_iff x, fun x => hN.mem_range_localization_H2_iff x,
      hSha.1.1, hSha.1.2.1, hSha.1.2.2.2⟩

end GlobalTheory.Published
