import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Reduce
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Shapiro
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ApplySubrepresentationCongr
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ToFunEqZeroOfForallIsCyclic
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_killed_c

local notation "ℚ̄" => AlgebraicClosure ℚ

section Infl

variable {G : Type} [Group G] [TopologicalSpace G] (Q : OpenSubgroup G) [(Q : Subgroup G).Normal]
  {l : ℕ} {X : Type} [AddCommGroup X] [Module (ZMod l) X]

def inflHom (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) : G →* AddMonoid.End X where
  toFun g := (ρ (QuotientGroup.mk g)).toAddMonoidHom
  map_one' := by ext x; simp only [QuotientGroup.mk_one, map_one]; rfl
  map_mul' g h := by ext x; simp only [QuotientGroup.mk_mul, map_mul]; rfl

abbrev infl (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) : Rep.{0} (ULift.{0} ℤ) G :=
  Rep.of (intRep.{0} (inflHom Q ρ))

theorem infl_apply (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) (g : G) (x : X) :
    (infl Q ρ).ρ g x = ρ (QuotientGroup.mk g) x := rfl

theorem finite_infl [Finite X] (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) :
    Finite (infl Q ρ) := ‹Finite X›

theorem isDiscreteRep_infl [IsTopologicalGroup G] (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X) :
    IsDiscreteRep (infl Q ρ) :=
  ⟨fun a => Subgroup.isOpen_mono (H₁ := (Q : Subgroup G)) (fun q hq => by
      show (infl Q ρ).ρ q a = a
      rw [infl_apply, (QuotientGroup.eq_one_iff q).2 hq, map_one]
      rfl) Q.isOpen⟩

end Infl

theorem rat_eq_one_of_padicValRat {q : ℚ} (hq : 0 < q) (h : ∀ p : ℕ, p.Prime → padicValRat p q = 0) :
    q = 1 := by
  have hval : ∀ p : ℕ, p.Prime → padicValNat p q.num.natAbs = padicValNat p q.den := by
    intro p hp
    have := h p hp
    simp only [padicValRat, padicValInt] at this
    omega
  have hn0 : q.num.natAbs ≠ 0 := by
    have := Rat.num_pos.2 hq
    omega
  have hnum : ∀ p : ℕ, p.Prime → ¬ p ∣ q.num.natAbs := by
    intro p hp hd
    haveI := Fact.mk hp
    have h1 := one_le_padicValNat_of_dvd hn0 hd
    have hd' : p ∣ q.den := by
      by_contra hnd
      rw [hval p hp, padicValNat.eq_zero_of_not_dvd hnd] at h1
      omega
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hd hd' q.reduced
  have hden : ∀ p : ℕ, p.Prime → ¬ p ∣ q.den := by
    intro p hp hd
    haveI := Fact.mk hp
    have h1 := one_le_padicValNat_of_dvd q.den_nz hd
    have hd' : p ∣ q.num.natAbs := by
      by_contra hnd
      rw [← hval p hp, padicValNat.eq_zero_of_not_dvd hnd] at h1
      omega
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hd' hd q.reduced
  have h1 : q.num.natAbs = 1 := Nat.eq_one_iff_not_exists_prime_dvd.2 hnum
  have h2 : q.den = 1 := Nat.eq_one_iff_not_exists_prime_dvd.2 hden
  have h3 : q.num = 1 := by
    have := Rat.num_pos.2 hq
    omega
  exact Rat.ext h3 h2

theorem shortExact_of_fun {k G : Type} [CommRing k] [Group G] (T : ShortComplex (Rep.{0} k G))
    (h1 : Function.Injective T.f.hom) (h2 : ∀ y, T.g.hom y = 0 → ∃ x, T.f.hom x = y)
    (h3 : Function.Surjective T.g.hom) : T.ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} k G) (ModuleCat.{0} k)),
      ShortComplex.moduleCat_exact_iff]
    exact h2
  mono_f := (Rep.mono_iff_injective _).2 h1
  epi_g := (Rep.epi_iff_surjective _).2 h3

section Artin

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Q : OpenSubgroup G)
  [(Q : Subgroup G).Normal] (l : ℕ) [Fact l.Prime]
  (χ : (A : Rep.{0} (ULift.{0} ℤ) G) → [IsDiscreteRep A] → ℚ)

def MultKilled : Prop :=
  ∀ (T : ShortComplex (Rep.{0} (ULift.{0} ℤ) G)) [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂]
    [IsDiscreteRep T.X₃] [Finite T.X₂], T.ShortExact → (∀ m : T.X₂, l • m = 0) → χ T.X₂ = χ T.X₁ * χ T.X₃

def PosKilled : Prop :=
  ∀ (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [Finite A], (∀ m : A, l • m = 0) → 0 < χ A

variable {l χ}

attribute [local instance] isDiscreteRep_infl finite_infl

theorem nsmul_eq_zero_of_zmod {X : Type} [AddCommGroup X] [Module (ZMod l) X] (x : X) : l • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod l), ZMod.natCast_self, zero_smul]

noncomputable def valFun (hmult : MultKilled l χ) (hpos : PosKilled l χ) (p : ℕ) [Fact p.Prime] :
    AdditiveFunction.{0} l (G ⧸ (Q : Subgroup G)) where
  toFun X _ _ _ ρ := padicValRat p (χ (infl Q ρ))
  additive := by
    intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hinj hfg hs
    let F : infl Q ρ₁ ⟶ infl Q ρ₂ := Rep.ofHom ⟨uliftLinearOfAddHom f.toAddMonoidHom,
      fun γ => LinearMap.ext fun x => hf.isIntertwining (QuotientGroup.mk γ) x⟩
    let Gm : infl Q ρ₂ ⟶ infl Q ρ₃ := Rep.ofHom ⟨uliftLinearOfAddHom g.toAddMonoidHom,
      fun γ => LinearMap.ext fun x => hg.isIntertwining (QuotientGroup.mk γ) x⟩
    have hzero : F ≫ Gm = 0 := by
      ext x
      exact (hfg (f x)).2 ⟨x, rfl⟩
    let T := ShortComplex.mk F Gm hzero
    have hT : T.ShortExact := shortExact_of_fun T hinj (fun y hy => (hfg y).1 hy) hs
    have hm : χ (infl Q ρ₂) = χ (infl Q ρ₁) * χ (infl Q ρ₃) :=
      @hmult T (isDiscreteRep_infl Q ρ₁) (isDiscreteRep_infl Q ρ₂) (isDiscreteRep_infl Q ρ₃)
        (finite_infl Q ρ₂) hT (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X₂) m)
    have h1 := hpos (infl Q ρ₁) (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X₁) m)
    have h3 := hpos (infl Q ρ₃) (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X₃) m)
    show padicValRat p (χ (infl Q ρ₂)) = padicValRat p (χ (infl Q ρ₁)) + padicValRat p (χ (infl Q ρ₃))
    rw [hm]
    exact padicValRat.mul h1.ne' h3.ne'

theorem eq_one_of_forall_isCyclic (hmult : MultKilled l χ) (hpos : PosKilled l χ)
    [Finite (G ⧸ (Q : Subgroup G))] {X : Type} [AddCommGroup X] [Module (ZMod l) X] [Finite X]
    (ρ : Representation (ZMod l) (G ⧸ (Q : Subgroup G)) X)
    (h : ∀ D : Subgroup (G ⧸ (Q : Subgroup G)), IsCyclic D →
      χ (infl Q (funRep ((G ⧸ (Q : Subgroup G)) ⧸ D) ρ)) = 1) :
    χ (infl Q ρ) = 1 := by
  apply rat_eq_one_of_padicValRat (hpos _ (fun m => nsmul_eq_zero_of_zmod (l := l) (X := X) m))
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  exact (valFun Q hmult hpos p).toFun_eq_zero_of_forall_isCyclic ρ (fun D hD => by
    show padicValRat p (χ (infl Q _)) = 0
    rw [h D hD]
    exact padicValRat.one)

end Artin

section GSAux

theorem exists_card_eq_pow' {ℓ : ℕ} [Fact ℓ.Prime] {X : Type*} [AddCommGroup X] [Finite X]
    (h : ∀ m : X, ℓ • m = 0) : ∃ n : ℕ, Nat.card X = ℓ ^ n := by
  have hp : IsPGroup ℓ (Multiplicative X) := fun g => ⟨1, by
    show Multiplicative.toAdd (g ^ (ℓ ^ 1)) = Multiplicative.toAdd 1
    rw [toAdd_pow, pow_one]; exact h _⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  exact ⟨n, by rw [← hn]; rfl⟩

theorem ratio_shortExact_l' (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSl : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (T : ShortComplex (Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)))
    (hT : T.ShortExact) [IsDiscreteRep T.X₁] [IsDiscreteRep T.X₂] [IsDiscreteRep T.X₃] [Finite T.X₂]
    (hl : ∃ r : ℕ, ∀ m : T.X₂, (ℓ ^ r) • m = 0) :
    haveI : Finite S := hS
    gsEulerRatio S T.X₂ ιr = gsEulerRatio S T.X₁ ιr * gsEulerRatio S T.X₃ ιr :=
  PositivityTheory.Lit1.GEN.ratio_shortExact_l ℓ K S hS hSl ιr T hT hl

theorem gs_multKilled (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSl : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion) :
    MultKilled ℓ (fun A [IsDiscreteRep A] => gsEulerRatio S A ιr) := by
  intro T _ _ _ _ hT hl
  exact ratio_shortExact_l' ℓ K S hS hSl ιr T hT ⟨1, by simpa using hl⟩

theorem gs_posKilled (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (hS : S.Finite) (hSl : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion) :
    PosKilled ℓ (fun A [IsDiscreteRep A] => gsEulerRatio S A ιr) := by
  intro A _ _ hA
  haveI : Finite S := hS
  apply gsEulerRatio_pos (S := S) (M := A) (ιr := ιr)
  intro v hv
  obtain ⟨n, hn⟩ := exists_card_eq_pow' (ℓ := ℓ) (X := A) hA
  rw [hn, Nat.cast_pow] at hv
  exact hSl v (v.isPrime.mem_of_pow_mem n hv)

set_option maxHeartbeats 1000000 in

theorem exists_field_of_cyclic (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (D : Subgroup (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))) (hD : IsCyclic D) :
    ∃ (L' : FiniteSubfield) (_ : Fact (K ≤ L'))
      (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S),
      (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = D.comap (QuotientGroup.mk' _) ∧
      (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ∧
      IsCyclic ((gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) := by
  have hUD : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) ≤ D.comap (QuotientGroup.mk' _) := fun u hu => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu]
    exact D.one_mem
  let V : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S) :=
    ⟨D.comap (QuotientGroup.mk' _), Subgroup.isOpen_mono hUD (gsOpenSubgroup S hL).isOpen⟩
  obtain ⟨L', hKL', hL', hV⟩ := exists_gsOpenSubgroup_eq (K := K) (S := S) V
  have hW : (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = D.comap (QuotientGroup.mk' _) := by
    rw [hV]
  refine ⟨L', hKL', hL', hW, fun u hu => (Subgroup.ext_iff.1 hW u).2 (hUD hu), ?_⟩
  let φ : (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) →* D := ((QuotientGroup.mk' _).comp (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype).codRestrict D (fun w => (Subgroup.ext_iff.1 hW w).1 w.2)
  have hsurj : Function.Surjective φ := by
    rintro ⟨d, hd⟩
    obtain ⟨g, hgd⟩ := QuotientGroup.mk_surjective d
    have hg : g ∈ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) := (Subgroup.ext_iff.1 hW g).2 (by
      show QuotientGroup.mk g ∈ D
      rw [hgd]
      exact hd)
    exact ⟨⟨g, hg⟩, Subtype.ext hgd⟩
  have hk : φ.ker = (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subgroupOf (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).1 h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)
  let e := (QuotientGroup.quotientMulEquivOfEq hk).symm.trans (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem finite_quot_gs (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) :
    Finite (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) := by
  haveI := finiteIndex_gsOpenSubgroup S hL
  exact Subgroup.finite_quotient_of_finiteIndex

end GSAux

end PositivityTheory.Lit1.GEN.W_killed_c
