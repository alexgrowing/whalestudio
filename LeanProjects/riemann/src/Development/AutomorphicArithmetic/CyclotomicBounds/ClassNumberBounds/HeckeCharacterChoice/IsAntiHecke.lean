import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.PrincipalIdele

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

abbrev modInt (E : Type*) [Field E] (M : ℕ) : Ideal (𝓞 E) := Ideal.span {(M : 𝓞 E)}

noncomputable def modMap {F E : Type*} [Field F] [Field E] (M : ℕ) (f : 𝓞 F →+* 𝓞 E) :
    (𝓞 F ⧸ modInt F M)ˣ →* (𝓞 E ⧸ modInt E M)ˣ :=
  Units.map (Ideal.quotientMap (I := modInt F M) (modInt E M) f (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)).toMonoidHom

variable {E : Type*} [Field E] [NumberField E]

noncomputable def placeRed {M N : ℕ} (h : N ∣ M) (φ : 𝓞 E →+* ZMod N) :
    (𝓞 E ⧸ modInt E M)ˣ →* (ZMod N)ˣ :=
  Units.map (Ideal.Quotient.lift (modInt E M) φ (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_natCast, (ZMod.natCast_eq_zero_iff M N).2 h, zero_mul])).toMonoidHom

def HasCondExp (χ : Idele E →* ℂˣ) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Prop :=
  (∀ x ∈ localUnits w, Valued.v (finComp w x - 1) ≤ WithZero.exp (-(n : ℤ)) → χ x = 1) ∧
    ∀ m : ℕ, m < n → ∃ x ∈ localUnits w,
      Valued.v (finComp w x - 1) ≤ WithZero.exp (-(m : ℤ)) ∧ χ x ≠ 1

example (w : HeightOneSpectrum (𝓞 E)) : HasCondExp 1 w 0 := ⟨fun _ _ _ => rfl, by simp⟩

noncomputable def localOrder (χ : Idele E →* ℂˣ) (w : HeightOneSpectrum (𝓞 E)) : ℕ :=
  orderOf (χ.comp (localUnits w).subtype)

section CM

variable [IsCMField E]

noncomputable def antiFin {M : ℕ} (θ : (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ) :
    (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ :=
  θ / θ.comp (modMap M (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom)

structure IsAntiHecke {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) (e : ι → ℤ)
    (χ : Idele E →* ℂˣ) : Prop where
  continuous : Continuous χ
  principal : ∀ α : Eˣ, χ (principalIdele E α) = 1
  base : χ.comp (ideleMap (maximalRealSubfield E) E) = 1
  infinite : ∀ x : Idele E, (∀ v, finComp v x = 1) →
    χ x = infType conjRatio τ e (infPart E x)

example {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) : IsAntiHecke τ 0 1 :=
  ⟨continuous_const, fun _ => rfl, rfl, fun _ _ => by simp [infType]⟩

def TorsionCond {ι : Type*} [Fintype ι] (τ : ι → E →+* ℂ) (e : ι → ℤ) {M : ℕ}
    (θ : (𝓞 E ⧸ modInt E M)ˣ →* ℂˣ) : Prop :=
  ∀ ζ : Units.torsion E, (∏ i, τ i (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E) ^ e i) *
    (θ (Ideal.torsionMapQuot (modInt E M) ζ) : ℂ) = 1

end CM

section Eta

variable (F : Type*) [Field F] [NumberField F] [Algebra F E]

variable {F} (E) in

noncomputable def etaSign (v : HeightOneSpectrum (𝓞 F)) : ℂˣ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1

variable (E) in

noncomputable def etaIdeal : IdealGroup F →* ℂˣ where
  toFun I := ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    etaSign E v ^ FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F)
  map_one' := by simp [FractionalIdeal.count_one]
  map_mul' I J := by
    have h : ∀ I : FractionalIdeal (𝓞 F)⁰ F, Function.HasFiniteMulSupport
        fun v : HeightOneSpectrum (𝓞 F) => etaSign E v ^ FractionalIdeal.count F v I := fun I =>
      (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset
        fun v hv h0 => hv (by simp [h0])
    rw [← finprod_mul_distrib (h _) (h _)]
    refine finprod_congr fun v => ?_
    rw [Units.val_mul, FractionalIdeal.count_mul F _ I.ne_zero J.ne_zero, zpow_add]

noncomputable def signInf : (InfiniteAdeleRing F)ˣ →* ℂˣ :=
  infType phase (fun φ : F →+* ℂ => φ) fun _ => 1

variable (E) in

def EtaRecip : Prop :=
  ∀ a : Fˣ, etaIdeal E F (toPrincipalIdeal (𝓞 F) F a) * signInf F (infDiag F a) = 1

variable (E) in

def IsEta (η : Idele F →* ℂˣ) : Prop :=
  IsHeckeIdele (modInt F 1) (signInf F) 1 η ∧
    HeckeCompat (modInt F 1) (signInf F) 1 η ((etaIdeal E F).comp (primeToMod _).subtype)

end Eta

end KStar.Choice
