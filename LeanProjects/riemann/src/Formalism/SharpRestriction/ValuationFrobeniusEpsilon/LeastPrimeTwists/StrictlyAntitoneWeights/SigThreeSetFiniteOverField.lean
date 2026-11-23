import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.UnitaryThreeHeightBounds
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.AntitoneWeightsLemma.LiteratureFamilyBoundOfMembers

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

theorem l_ne_zero (l : ℕ) [Fact l.Prime] : ((l : ℕ) : V.Ol l) ≠ 0 := by
  intro h
  have h1 : V.jO l ((l : ℕ) : V.Ol l) = 0 := by rw [h, map_zero]
  rw [map_natCast] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h1

instance instDVR (l : ℕ) [Fact l.Prime] : IsDiscreteValuationRing (V.Ol l) := by
  haveI : IsNoetherianRing (V.Ol l) := IsNoetherianRing.of_finite ℤ_[l] (V.Ol l)
  have hf : ¬ IsField (V.Ol l) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, V.Ol_unram l]
    intro h
    exact l_ne_zero V l (Ideal.span_singleton_eq_bot.mp h)
  refine ((IsDiscreteValuationRing.TFAE (V.Ol l) hf).out 0 4).mpr ?_
  rw [V.Ol_unram l]
  exact ⟨⟨_, rfl⟩⟩

def vL (l : ℕ) [Fact l.Prime] (x : QbarL l) : ℝ := - Real.log ‖x‖ / Real.log l

def dK (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] : ℕ := (discr K).natAbs

structure FrobAt (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (p : ℕ) where
  v : HeightOneSpectrum (𝓞 K)
  hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal
  A : ValuationSubring QbarQ
  hA : Formalism.ConjugateSelfDual.IsPlaceOver (F := K) A v
  σ : K.fixingSubgroup
  hσ : Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) (IntermediateField.fixingSubgroupEquiv K σ)
  vp : HeightOneSpectrum (𝓞 ℚ)
  hvp : ((p : ℕ) : 𝓞 ℚ) ∈ vp.asIdeal
  h : ℕ
  hq : Formalism.ConjugateSelfDual.normV v = p ^ h
  h_pos : 1 ≤ h
  h_le : h ≤ 2

namespace FrobAt
variable {K : IntermediateField ℚ QbarQ} [FiniteDimensional ℚ K] {p : ℕ} (Fr : FrobAt K p)

def q : ℕ := Formalism.ConjugateSelfDual.normV Fr.v

def φ : K.fixingSubgroup := Fr.σ⁻¹
end FrobAt

def Sig2 (M e : ℕ) : Set (V.spec ℚ 2).Rep :=
  {π | (V.spec ℚ 2).level π M ∧ (V.spec ℚ 2).wt π = fun _ => ![2 * (e : ℤ), 0]}

def IsRiAt {F : Type} [Field F] [NumberField F] [Algebra F QbarQ] {n l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ)
    (π : (V.spec F n).Rep) (ρ : Formalism.ConjugateSelfDual.G F QbarQ →* GL (Fin n) (QbarL l)) : Prop :=
  TV.GeoMatch ρ ι.toRingHom ((V.spec F n).hecke π)

def Ram3 (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l))
    (M : ℕ) : Prop :=
  (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q → (σ : GQ) ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu M →
    ρ σ = 1) ∧
  ∃ a : ℕ, ((l - 1) ∣ a ∨ l ∣ M) ∧
    V.Crys l 3 (HcrSub l a (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
      (ρ.comp (Subgroup.inclusion (inf_le_left.trans inf_le_right)))

def Ram2 (l : ℕ) [Fact l.Prime] (W : GQ →* GL (Fin 2) (QbarL l)) (M : ℕ) : Prop :=
  (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : GQ, σ ∈ V.Iq q → σ ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu M → W σ = 1) ∧
  ∃ (a : ℕ) (K' : IntermediateField ℚ QbarQ), ((l - 1) ∣ a ∨ l ∣ M) ∧ V.Iq l ≤ K'.fixingSubgroup ∧
    V.Crys l 2 (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)) (V.plc l)
      (W.comp (HcrSub l a (V.Dq l ⊓ K'.fixingSubgroup)).subtype)

def IsCSDOne {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Prop :=
  ∃ s : K ≃+* K, s ≠ RingEquiv.refl K ∧
    ∃ (τ : Ω ≃+* Ω) (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)), (∀ x, τ (τ x) = x) ∧
    ∃ J : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l), J.det ≠ 0 ∧ J.transpose = J ∧ ∀ σ : Formalism.ConjugateSelfDual.G K Ω,
      (ρ σ : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).transpose * J *
        (ρ (Formalism.ConjugateSelfDual.conjGal s τ hτ σ) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) = J

def OrdFixAt {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) (A : ValuationSubring Ω) (k : Fin n → ℤ) (M : ℕ) : Prop :=
  ∃ g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l),
    (∀ σ ∈ A.decompositionSubgroup F,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)).BlockTriangular id) ∧
    ∀ σ ∈ Formalism.ConjugateSelfDual.Inertia (F := F) A, (∀ ζ : Ω, ζ ^ M = 1 → σ ζ = ζ) → ∀ i : Fin n,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin n) (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) i i =
        ((Formalism.ConjugateSelfDual.cyc F Ω l σ : (Formalism.ConjugateSelfDual.Qbar l)ˣ) : Formalism.ConjugateSelfDual.Qbar l) ^ (k i)

def OrdFixAbove {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Formalism.ConjugateSelfDual.Qbar l)) (k : Fin n → ℤ) (M : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ A, Formalism.ConjugateSelfDual.IsPlaceOver A v → OrdFixAt ρ A k M

def Ord3 {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ QbarQ} [FiniteDimensional ℚ K]
    (ρ : K.fixingSubgroup →* GL (Fin 3) (QbarL l)) (e M : ℕ) : Prop :=
  l ≠ 2 ∧ Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ) ∧ IsCSDOne (VData.toRecRep ρ) ∧
    OrdFixAbove (VData.toRecRep ρ) ![(e : ℤ), 0, -(e : ℤ)] M

theorem strictAnti_wts {e : ℕ} (he : 1 ≤ e) : StrictAnti ![(e : ℤ), 0, -(e : ℤ)] := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

theorem wts_eq (e : ℕ) (i : Fin 3) :
    ![(e : ℤ) + 1, 1, 1 - (e : ℤ)] i = -(![(e : ℤ), 0, -(e : ℤ)] i.rev) - (-1) := by
  fin_cases i <;> simp [Fin.rev] <;> ring

def Sig3G (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Set (V.spec K 3).Rep :=
  {π | π ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K (3 * condV D) e ∧
    ∃ (l : ℕ) (_ : Fact l.Prime) (ι : QbarL l ≃+* ℂ) (χ : Chi D) (g1 : GQ) (ξ : V.S3 l e χ K g1 →+* QbarL l),
      UnitaryThreeData V l e χ K ∧ IsNormElt V l e χ K g1 ∧ UnitaryThreeFiniteness V l e χ K g1 ∧ V.IsPt3 ξ ∧
      Continuous (V.rho3 ξ) ∧ Ord3 (V.rho3 ξ) e (condV D) ∧
      IsRiAt V ι π (VData.toRecRep (twistRep (V.rho3 ξ) ((epsL l).comp K.fixingSubgroup.subtype)⁻¹)) ∧
      Ram3 V l K (V.rho3 ξ) (condV D)}

def Sig2G (M e : ℕ) : Set (V.spec ℚ 2).Rep :=
  {π | π ∈ Sig2 V M e ∧
    ∃ (l : ℕ) (_ : Fact l.Prime) (ι : QbarL l ≃+* ℂ) (W : GQ →* GL (Fin 2) (QbarL l)),
      Continuous W ∧ IsRiAt V ι π (twistRep W ((epsL l) ^ e)⁻¹) ∧ Ram2 V l W M}

abbrev Lab (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Type :=
  ↥(Sig3G V K e) ⊕ ↥(Sig2G V (condV D * dK K) e)

theorem sig_three_set_finite_over_field (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (M e : ℕ) :
    (Formalism.MainNotions.UnitaryThreeHeightBounds.Sig3 V K M e).Finite := by
  refine ((V.spec K 3).finite M (fun _ => ![(e : ℤ) + 1, 1, 1 - (e : ℤ)])).subset ?_
  rintro π ⟨-, h2, h3⟩
  exact ⟨h2, funext fun τ => funext fun i => h3 τ i⟩

theorem sig_two_set_finite (M e : ℕ) : (Sig2 V M e).Finite := (V.spec ℚ 2).finite M _

instance (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Finite (Lab V K e) :=
  haveI := ((sig_three_set_finite_over_field V K (3 * condV D) e).subset (fun _ h => h.1 : Sig3G V K e ⊆ _)).to_subtype
  haveI := ((sig_two_set_finite V (condV D * dK K) e).subset (fun _ h => h.1 : Sig2G V (condV D * dK K) e ⊆ _)).to_subtype
  inferInstance

instance (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (e : ℕ) : Fintype (Lab V K e) :=
  Fintype.ofFinite _

section Num

variable {K : IntermediateField ℚ QbarQ} [FiniteDimensional ℚ K] {p : ℕ} (e : ℕ) (χ : Chi D) (Fr : FrobAt K p)

def t3 (π : (V.spec K 3).Rep) : ℂ := ((V.spec K 3).hecke π Fr.v).roots.sum / (Fr.q : ℂ)

def t2 (π : (V.spec ℚ 2).Rep) : ℂ :=
  1 + ((Fr.q : ℂ) ^ e)⁻¹ * (((V.spec ℚ 2).hecke π Fr.vp).roots.map (· ^ Fr.h)).sum

def tt : Lab V K e → ℂ := Sum.elim (fun π => t3 V Fr π.1) (fun π => t2 V e Fr π.1)

def zetaP : ℂ := ((V.chiGQ χ (Fr.φ : GQ) : ℂˣ) : ℂ)

def EisC : ℂ := ((Fr.q : ℂ) ^ e)⁻¹ * zetaP V χ Fr + 1 + (Fr.q : ℂ) ^ e * (zetaP V χ Fr)⁻¹

def fac (τ : Lab V K e) : ℂ := (Fr.q : ℂ) ^ e * (tt V e Fr τ - EisC V e χ Fr)

def prodChi : ℂ := ∏ τ : Lab V K e, fac V e χ Fr τ

open Classical in

def NNc : ℂ := ∏ χ'' ∈ Finset.univ.filter (Formalism.MainNotions.UnitaryThreeHeightBounds.ChiConj D χ), prodChi V e χ'' Fr

end Num

section Ring

variable {V}
variable {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}

def NegNZ3 (ξ : V.S3 l e χ K g1 →+* QbarL l) : Prop := ∃ j : ℤ, j < 0 ∧ ∃ x ∈ V.S3gr l e χ K g1 j, ξ x ≠ 0

def PosNZ3 (ξ : V.S3 l e χ K g1 →+* QbarL l) : Prop := ∃ j : ℤ, 0 < j ∧ ∃ x ∈ V.S3gr l e χ K g1 j, ξ x ≠ 0

def Both3 (ξ : V.S3 l e χ K g1 →+* QbarL l) : Prop := NegNZ3 ξ ∧ PosNZ3 ξ

def SameOrbit3 (ξ ξ' : V.S3 l e χ K g1 →+* QbarL l) : Prop :=
  ∃ t : (QbarL l)ˣ, ∀ (j : ℤ), ∀ x ∈ V.S3gr l e χ K g1 j, ξ' x = (t : QbarL l) ^ j * ξ x

variable (V l e χ g1) in

def aP [FiniteDimensional ℚ K] {p : ℕ} (Fr : FrobAt K p) : V.S3 l e χ K g1 :=
  ((V.unitaryGaloisRepresentation l e χ K g1 Fr.φ : GL (Fin 3) (V.S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (V.S3 l e χ K g1)).trace -
    algebraMap (V.Ol l) (V.S3 l e χ K g1)
      (V.psi l e χ (Fr.φ : GQ) + 1 + V.psi l e χ ((Fr.φ : GQ)⁻¹))

end Ring

open Formalism.MainNotions.GradedPowerSeriesLemmas in

structure Pres (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ) where
  a : ℕ
  wt : Fin a → ℤ
  𝔓 : Ideal (PT (V.Ol l) wt)
  r : ℕ
  s : ℕ
  r' : ℕ
  s' : ℕ
  m : ℕ
  F : Fin (r + 1) → PT (V.Ol l) wt
  G : Fin s → PT (V.Ol l) wt
  E1 : Fin r' → PT (V.Ol l) wt
  E2 : Fin s' → PT (V.Ol l) wt
  Z : Fin m → PT (V.Ol l) wt
  eS : ST 𝔓 F G E1 E2 Z ≃ₐ[V.Ol l] V.S3 l e χ K g1
  eS_gr : ∀ (j : ℤ) (f : PT (V.Ol l) wt), IsHom j f → eS (mkS 𝔓 F G E1 E2 Z f) ∈ V.S3gr l e χ K g1 j
  eS_sur : ∀ (j : ℤ), ∀ x ∈ V.S3gr l e χ K g1 j, ∃ f : PT (V.Ol l) wt, IsHom j f ∧ eS (mkS 𝔓 F G E1 E2 Z f) = x
  eS_pt : ∀ (hl : l ≠ 2) (f : PT (V.Ol l) wt), V.pt3 l e χ K g1 hl (eS (mkS 𝔓 F G E1 E2 Z f)) = cc f

end Formalism.MainNotions.V.Pf.V3
