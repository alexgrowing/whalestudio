import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.TwistDet
open scoped Pointwise

namespace GlobalTheory.ChosenPrimes

section General

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

variable (F Ω) in

def rootFix (n : ℕ) : Subgroup (G F Ω) where
  carrier := {g | ∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb ζ h => by
    show a (b ζ) = ζ
    rw [hb ζ h, ha ζ h]
  inv_mem' := fun {a} ha ζ h => by
    apply a.injective
    rw [ha ζ h]
    exact a.apply_symm_apply ζ

theorem normal_rootFix (n : ℕ) : (rootFix F Ω n).Normal where
  conj_mem a ha g ζ h := by
    have h1 : ((g⁻¹ : G F Ω) ζ) ^ n = 1 := by rw [← map_pow, h, map_one]
    show g (a ((g⁻¹ : G F Ω) ζ)) = ζ
    rw [ha _ h1]
    exact ReciprocityTheory.Gal.mul_inv_apply ζ

omit [NumberField F] in
theorem isOpen_rootFix [IsAlgClosure F Ω] {n : ℕ} (hn : n ≠ 0) : IsOpen (rootFix F Ω n : Set (G F Ω)) := by
  classical

  have hfin : ({ζ : Ω | ζ ^ n = 1}).Finite := by
    refine (Polynomial.nthRoots n (1 : Ω)).toFinset.finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)] using hζ
  have : Finite {ζ : Ω | ζ ^ n = 1} := hfin.to_subtype
  let L : IntermediateField F Ω := IntermediateField.adjoin F {ζ : Ω | ζ ^ n = 1}
  have : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)

  refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen L)
  intro g hg
  show ∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ
  intro ζ hζ
  exact (IntermediateField.mem_fixingSubgroup_iff L g).mp hg ζ (IntermediateField.subset_adjoin F _ hζ)

theorem apply_root {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {n : ℕ} (hn0 : n ≠ 0)
    (hn : ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {σ : G F Ω} {q : ℕ}
    (hσ : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) {ζ : Ω} (hζ : ζ ^ n = 1) : σ ζ = ζ ^ q := by

  have hN : ¬ A.valuation (n : Ω) < 1 := by
    simpa using ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver (A := A) hn hA 1
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A hN ?_ ?_
    (hσ ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hn0 hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem ine_le_rootFix {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {n : ℕ}
    (hn0 : n ≠ 0) (hn : ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) : Ine (F := F) A ≤ rootFix F Ω n := by
  intro τ hτ
  have hτ' := (ReciprocityTheory.Gal.mem_Ine.mp hτ).2
  show ∀ ζ : Ω, ζ ^ n = 1 → τ ζ = ζ
  intro ζ hζ

  simpa using apply_root hA hn0 hn (σ := τ) (q := 1) (fun x hx => by simpa using hτ' x hx) hζ

theorem norm_mod [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    {n : ℕ} (hn1 : 1 < n) (hn : ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {σ : G F Ω} {q : ℕ} (hσ : IsFrob A q σ)
    (h : σ ∈ rootFix F Ω n) : q % n = 1 := by
  have hn0 : n ≠ 0 := by omega
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have h1 : σ ζ = ζ ^ q := apply_root hA hn0 hn hσ.2 hζ.pow_eq_one
  have h2 : σ ζ = ζ := (show ∀ ζ : Ω, ζ ^ n = 1 → σ ζ = ζ from h) ζ hζ.pow_eq_one
  have h3 : ζ ^ q = ζ ^ 1 := by rw [← h1, h2, pow_one]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn0
  rcases Nat.eq_zero_or_pos q with hq | hq
  ·
    subst hq
    have hd : n ∣ 1 := (hζ.pow_eq_one_iff_dvd 1).mp (by rw [← h3, pow_zero])
    have := Nat.le_of_dvd one_pos hd
    omega
  · have h4 : ζ ^ (q - 1) = 1 := by
      apply mul_right_cancel₀ hζ0
      rw [← pow_succ, Nat.sub_add_cancel hq, h3, pow_one, one_mul]
    have h5 : 1 ≡ q [MOD n] := (Nat.modEq_iff_dvd' hq).mpr ((hζ.pow_eq_one_iff_dvd _).mp h4)
    rw [Nat.ModEq, Nat.mod_eq_of_lt hn1] at h5
    exact h5.symm

theorem dec_le [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    {H : Subgroup (G F Ω)} (hH : IsOpen (H : Set (G F Ω))) (hI : Ine (F := F) A ≤ H) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) (h : σ ∈ H) : Dec (F := F) A ≤ H := by

  have hcl := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  let K : Subgroup (Dec (F := F) A) := H.subgroupOf (Dec (F := F) A)
  have hKo : IsOpen (K : Set (Dec (F := F) A)) := hH.preimage continuous_subtype_val
  have hKc : IsClosed (K : Set (Dec (F := F) A)) := Subgroup.isClosed_of_isOpen K hKo
  have hle : Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A) ≤ K := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact h
    · intro x hx; exact hI hx
  have htop := Subgroup.topologicalClosure_minimal _ hle hKc
  rw [hcl] at htop
  intro x hx
  exact htop (Subgroup.mem_top (⟨x, hx⟩ : Dec (F := F) A))

theorem finite_ram [IsAlgClosure F Ω] {H : Subgroup (G F Ω)} (hH : IsOpen (H : Set (G F Ω))) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F := F) B ≤ H}.Finite := by

  let Hc : ClosedSubgroup (G F Ω) := ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  have hfix : (IntermediateField.fixedField Hc.1).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField Hc
  have : FiniteDimensional F (IntermediateField.fixedField Hc.1) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hfix]; exact hH)
  have := GlobalTheory.InertiaAlmostAll.finite_ramified F Ω (IntermediateField.fixedField Hc.1)
  rwa [hfix] at this

theorem finite_mem {n : ℕ} (hn : n ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | ((n : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h := GlobalTheory.InertiaAlmostAll.finite_mem F (c := (n : ℤ)) (by exact_mod_cast hn)
  simpa using h

end General

theorem exists_seq {α : Type} (r : α → α → Prop) (hs : ∀ a b, r a b → r b a) :
    ∀ (R : ℕ) (p : Fin R → α → Prop), (∀ a (T : Set α), T.Finite → ∃ x, p a x ∧ ∀ y, r x y → y ∉ T) →
      ∃ P : Fin R → α, (∀ a, p a (P a)) ∧ ∀ a b, r (P a) (P b) → a = b := by
  intro R
  induction R with
  | zero => intro p _; exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ R ih =>
    intro p hp

    obtain ⟨P, hP, hPr⟩ := ih (fun a => p a.castSucc) (fun a T hT => hp a.castSucc T hT)
    obtain ⟨x, hx, hxr⟩ := hp (Fin.last R) (Set.range P) (Set.finite_range P)
    refine ⟨Fin.snoc (α := fun _ => α) P x, fun a => ?_, fun a b hab => ?_⟩
    · induction a using Fin.lastCases with
      | last => simpa using hx
      | cast a => simpa using hP a
    · induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
          exact absurd ⟨b, rfl⟩ (hxr _ hab)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
          exact absurd ⟨a, rfl⟩ (hxr _ (hs _ _ hab))
        | cast b =>
          simp only [Fin.snoc_castSucc] at hab
          rw [hPr a b hab]

theorem exists_values {Γ C ι : Type} [Group Γ] [CommGroup C] [Fintype ι] (V : Subgroup Γ) (d : ι → (Γ →* C))
    (h : ∀ b c, ∃ γ ∈ V, d b γ = c ∧ ∀ b', b' ≠ b → d b' γ = 1) (t : ι → C) : ∃ γ ∈ V, ∀ b, d b γ = t b := by
  classical
  choose g hgV hg1 hg2 using h

  have key : ∀ s : Finset ι, ∃ γ ∈ V, ∀ b, d b γ = if b ∈ s then t b else 1 := by
    intro s
    refine Finset.induction_on s ⟨1, V.one_mem, fun b => by simp⟩ ?_
    intro a s ha ih
    obtain ⟨γ, hγV, hγ⟩ := ih
    refine ⟨γ * g a (t a), V.mul_mem hγV (hgV a (t a)), fun b => ?_⟩
    rw [map_mul, hγ b]
    by_cases hba : b = a
    · subst hba
      simp [ha, hg1]
    · rw [hg2 a (t a) b hba]
      simp [Finset.mem_insert, hba]
  obtain ⟨γ, hγV, hγ⟩ := key Finset.univ
  exact ⟨γ, hγV, fun b => by simpa using hγ b⟩

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

def Pick (N : NData D.R D.host D.what₂) (V : Subgroup (GE N)) (g : GE N) (T : Set (PlE D.host)) (P : PlE D.host) : Prop :=
  (∀ v, Over P v → v ∉ T ∧ v.asIdeal.inertiaDeg ℤ = 1) ∧
    ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ k : GE N, k * σ * k⁻¹ * g⁻¹ ∈ V

theorem finite_over {T : Set (PlE D.host)} (hT : T.Finite) : {P | ∃ v ∈ T, Over v P}.Finite := by

  choose c hc using fun v : PlE D.host => GlobalTheory.TwistDet.exists_isConjPl (D := D) v
  refine (hT.union (hT.image c)).subset ?_
  rintro P ⟨v, hv, h | h⟩
  · left; rw [h]; exact hv
  · right; exact ⟨v, hv, GlobalTheory.TwistDet.isConjPl_unique (hc v) h⟩

theorem exists_pick (hC : Cheb) {V : Subgroup (GE N)} (hV : IsOpen (V : Set (GE N))) (hN : V.Normal) (g : GE N)
    {T : Set (PlE D.host)} (hT : T.Finite) : ∃ P, Pick N V g T P := by
  obtain ⟨P, hPA, hdeg, -, B, hB, hBV, σ₀, hσ₀, hσ₀g⟩ :=
    hC D.host.E N.Om V hV hN g (finite_over hT).toFinset
  have hnorm : ∀ w : PlE D.host, Ideal.absNorm w.asIdeal = normV w := fun w => by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hiff := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified D.host.E).1
  refine ⟨P, ?_⟩
  unfold Pick
  refine ⟨fun w hw => ⟨?_, ?_⟩, fun σ hσ => ?_⟩
  · intro hwT
    apply hPA
    rw [Set.Finite.mem_toFinset]
    exact ⟨w, hwT, GlobalTheory.TwistDet.over_symm hw⟩
  · rcases hw with rfl | hw
    · exact hdeg
    ·
      rw [← hiff, hnorm, GlobalTheory.TwistDet.normV_conj hw, ← hnorm, hiff]
      exact hdeg
  ·
    obtain ⟨k, hk⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hB (N.plOm.2 P)
    rw [← hk] at hσ
    have h1 := GlobalTheory.TwistDet.isFrob_smul hσ k⁻¹
    rw [inv_smul_smul] at h1
    have h2 : σ₀⁻¹ * (k⁻¹ * σ * k⁻¹⁻¹) ∈ V := hBV (ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob hσ₀ h1)
    refine ⟨k⁻¹, ?_⟩
    have h3 := V.mul_mem (hN.conj_mem _ h2 σ₀) hσ₀g
    convert h3 using 1
    group

theorem exists_picks (hC : Cheb) {V : Subgroup (GE N)} (hV : IsOpen (V : Set (GE N))) (hN : V.Normal) {R : ℕ}
    (g : Fin R → GE N) {T : Set (PlE D.host)} (hT : T.Finite) :
    ∃ P : Fin R → PlE D.host, (∀ a, Pick N V (g a) T (P a)) ∧ ∀ a b, Over (P a) (P b) → a = b := by
  refine exists_seq (fun P v => Over P v) (fun a b h => GlobalTheory.TwistDet.over_symm h) R
    (fun a x => Pick N V (g a) T x) ?_
  intro a T' hT'

  obtain ⟨x, hx1, hx2⟩ := exists_pick hC hV hN (g a) (hT.union hT')
  exact ⟨x, ⟨fun w hw => ⟨fun hwT => (hx1 w hw).1 (Or.inl hwT), (hx1 w hw).2⟩, hx2⟩,
    fun y hy hyT' => (hx1 y hy).1 (Or.inr hyT')⟩

variable (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)

theorem not_mem_of_pD {v : PlE D.host} (hv : v ∈ X.pD i) (M : ℕ) :
    ((2 * X.l i ^ M : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by

  have key : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ X.l i → ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal →
      ((2 * X.l i ^ M : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    intro p hp h2 hl hpv hmem
    have hcop : Nat.Coprime p (2 * X.l i ^ M) :=
      Nat.Coprime.mul_right ((Nat.coprime_primes hp Nat.prime_two).mpr h2)
        (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp (X.lPrime i).out).mpr hl))
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hab' := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Int.cast_one] at hab'
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab']
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpv) (v.asIdeal.mul_mem_left _ hmem)
  have hv' : v ∈ ((X.pD i : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.E))) := hv
  rw [X.pD_eq i] at hv'
  have h15 := D.host.pde_mod
  by_cases h : X.l i = D.host.pde
  · rw [if_pos h] at hv'
    exact key _ D.host.pde'_prime (by omega) (fun e => D.host.pde_ne (h ▸ e).symm) hv'
  · rw [if_neg h] at hv'
    exact key _ D.host.pde_prime (by omega) (fun e => h e.symm) hv'

theorem stepAB : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw),
    StepAB X i := by
  intro hC D N X i
  unfold StepAB
  intro M hM H S d hAdm z hz U hUo hUn A R h hh
  have hl := (X.lPrime i).out
  have hn1 : 1 < 2 * X.l i ^ M := by
    have : 1 ≤ X.l i ^ M := Nat.one_le_pow _ _ hl.pos
    omega
  have hn0 : 2 * X.l i ^ M ≠ 0 := by omega
  obtain ⟨hHo, hHn, hpDH, hgood⟩ := hAdm
  have := hUn
  have := hHn
  have := normal_rootFix (F := D.host.E) (Ω := N.Om) (2 * X.l i ^ M)

  let W : Subgroup (GE N) := U ⊓ H ⊓ rootFix D.host.E N.Om (2 * X.l i ^ M)
  have hWo : IsOpen (W : Set (GE N)) := (hUo.inter hHo).inter (isOpen_rootFix hn0)
  have hWn : W.Normal := inferInstance

  obtain ⟨A0, hA0f, hA0⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  have hram := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified D.host.E).2
  let T : Set (PlE D.host) := ↑A ∪ ↑S ∪ ↑(X.S0 i) ∪ A0 ∪ {v | v.asIdeal.ramificationIdx ℤ ≠ 1} ∪
    {v | ∃ B : ValuationSubring N.Om, IsPlaceOver B v ∧ ¬ Ine (F := D.host.E) B ≤ U} ∪
    {v | ∃ B : ValuationSubring N.Om, IsPlaceOver B v ∧ ¬ Ine (F := D.host.E) B ≤ H} ∪
    {v | ((2 * X.l i ^ M : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}
  have hT : T.Finite :=
    ((((((A.finite_toSet.union S.finite_toSet).union (X.S0 i).finite_toSet).union hA0f).union hram).union
      (finite_ram hUo)).union (finite_ram hHo)).union (finite_mem hn0)
  have hTmem : ∀ w, w ∉ T → w ∉ A ∧ w ∉ S ∧ w ∉ X.S0 i ∧ w ∉ A0 ∧ w.asIdeal.ramificationIdx ℤ = 1 ∧
      (∀ B : ValuationSubring N.Om, IsPlaceOver B w → Ine (F := D.host.E) B ≤ U) ∧
      (∀ B : ValuationSubring N.Om, IsPlaceOver B w → Ine (F := D.host.E) B ≤ H) ∧
      ((2 * X.l i ^ M : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro w hw
    simp only [T, Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, not_or, not_exists, not_and,
      not_not] at hw
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hw
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

  have hgoodP : ∀ P : PlE D.host, (∀ w, Over P w → w ∉ T ∧ w.asIdeal.inertiaDeg ℤ = 1) →
      (∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → σ ∈ H ⊓ rootFix D.host.E N.Om (2 * X.l i ^ M)) →
      (∀ w, Over P w → IsSplitPl D.host w ∧ w.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E w = 1 ∧
        w ∉ X.S0 i ∧ w ∉ A ∧ normV w % (2 * X.l i ^ M) = 1) ∧ GoodChar X i M P (d P) ∧
      (∀ w, Over P w → ∀ B : ValuationSubring N.Om, IsPlaceOver B w → Ine (F := D.host.E) B ≤ U) ∧
      (∀ B : ValuationSubring N.Om, IsPlaceOver B P → Ine (F := D.host.E) B ≤ W) := by
    intro P hP hfr
    have hPT := hTmem P (hP P (Or.inl rfl)).1
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (N.plOm.2 P)
    have hσW := hfr σ hσ
    have hnorm : normV P % (2 * X.l i ^ M) = 1 := norm_mod (N.plOm.2 P) hn1 hPT.2.2.2.2.2.2.2 hσ hσW.2
    have hdec : DecV N P ≤ H := dec_le (N.plOm.2 P) hHo (hPT.2.2.2.2.2.2.1 _ (N.plOm.2 P)) hσ hσW.1
    refine ⟨fun w hw => ?_, hgood P hPT.2.1 ?_ hdec,
      fun w hw B hB => (hTmem w (hP w hw).1).2.2.2.2.2.1 B hB, fun B hB => ?_⟩
    · have hwT := hTmem w (hP w hw).1
      have hdeg := (hP w hw).2
      refine ⟨hA0 w hwT.2.2.2.1 hdeg, hdeg, hwT.2.2.2.2.1, hwT.2.2.1, hwT.1, ?_⟩
      rcases hw with rfl | hw
      · exact hnorm
      · rw [GlobalTheory.TwistDet.normV_conj hw]; exact hnorm
    · exact hA0 P hPT.2.2.2.1 (hP P (Or.inl rfl)).2
    · exact le_inf (le_inf (hPT.2.2.2.2.2.1 B hB) (hPT.2.2.2.2.2.2.1 B hB))
        (ine_le_rootFix hB hn0 hPT.2.2.2.2.2.2.2)
  have hconjmem : ∀ (K : Subgroup (GE N)), K.Normal → ∀ σ k g : GE N, k * σ * k⁻¹ * g⁻¹ ∈ K → g ∈ K → σ ∈ K := by
    intro K hK σ k g h1 h2
    have h3 : k * σ * k⁻¹ ∈ K := by simpa using K.mul_mem h1 h2
    have h4 := hK.conj_mem _ h3 k⁻¹
    simpa [mul_assoc] using h4

  have hzHR : z ∈ H ⊓ rootFix D.host.E N.Om (2 * X.l i ^ M) := by
    obtain ⟨v, hv, B, hB, hzB, -, -⟩ := hz
    exact ⟨hpDH v hv B hB hzB, ine_le_rootFix hB hn0 (not_mem_of_pD X i hv M) hzB⟩
  obtain ⟨P1, hP1, hP1d⟩ := exists_picks hC hWo hWn (fun _ : Fin R => z) hT
  have hP1good := fun a => hgoodP (P1 a) (hP1 a).1 (fun σ hσ => by
    obtain ⟨k, hk⟩ := (hP1 a).2 σ hσ
    exact hconjmem _ inferInstance σ k z ⟨hk.1.2, hk.2⟩ hzHR)

  have hsurj : ∀ (b : Fin R) (c : Multiplicative (ZMod (X.l i ^ M))),
      ∃ γ ∈ W, d (P1 b) γ = c ∧ ∀ b', b' ≠ b → d (P1 b') γ = 1 := by
    intro b c
    obtain ⟨-, hgc, -, hB⟩ := hP1good b
    obtain ⟨γ, hγI, hγc⟩ := hgc.2.2.2.2 (P1 b) (Or.inl rfl) (N.plOm.1 (P1 b)) (N.plOm.2 (P1 b)) c
    refine ⟨γ, hB _ (N.plOm.2 (P1 b)) hγI, hγc, fun b' hb' => ?_⟩
    obtain ⟨-, hgc', -, -⟩ := hP1good b'
    exact hgc'.2.2.2.1 (P1 b) (fun hov => hb' (hP1d b' b hov)) (N.plOm.1 (P1 b)) (N.plOm.2 (P1 b)) γ hγI
  choose ε hεW hε using fun a : Fin R => exists_values W (fun b => d (P1 b)) hsurj
    (fun b => Multiplicative.ofAdd (if a = b then (1 : ZMod (X.l i ^ M)) else 0) * (d (P1 b) (h a))⁻¹)
  let γ : Fin R → GE N := fun a => h a * ε a
  have hγd : ∀ a b, d (P1 b) (γ a) = Multiplicative.ofAdd (if a = b then (1 : ZMod (X.l i ^ M)) else 0) := by
    intro a b
    have h1 := hε a b
    simp only [γ]
    rw [map_mul, h1, mul_comm _ (d (P1 b) (h a))⁻¹, mul_inv_cancel_left]
  have hγHR : ∀ a, γ a ∈ H ⊓ rootFix D.host.E N.Om (2 * X.l i ^ M) := fun a =>
    (H ⊓ rootFix D.host.E N.Om (2 * X.l i ^ M)).mul_mem ⟨(hh a).1, (hh a).2⟩ ⟨(hεW a).1.2, (hεW a).2⟩

  let V2 : Subgroup (GE N) := W ⊓ ⨅ b, (d (P1 b)).ker
  have hV2o : IsOpen (V2 : Set (GE N)) := by
    have : IsOpen (⋂ b, ((d (P1 b)).ker : Set (GE N))) :=
      isOpen_iInter_of_finite (fun b => (hP1good b).2.1.1)
    show IsOpen ((W : Set (GE N)) ∩ ((⨅ b, (d (P1 b)).ker : Subgroup (GE N)) : Set (GE N)))
    rw [Subgroup.coe_iInf]
    exact hWo.inter this
  have hV2n : V2.Normal := by
    have : (⨅ b, (d (P1 b)).ker).Normal := Subgroup.normal_iInf_normal (fun b => inferInstance)
    infer_instance
  obtain ⟨P2, hP2, hP2d⟩ := exists_picks hC hV2o hV2n γ (hT.union (Set.finite_range P1))
  have hP2good := fun a => hgoodP (P2 a)
    (fun w hw => ⟨fun h' => ((hP2 a).1 w hw).1 (Or.inl h'), ((hP2 a).1 w hw).2⟩)
    (fun σ hσ => by
      obtain ⟨k, hk⟩ := (hP2 a).2 σ hσ
      exact hconjmem _ inferInstance σ k (γ a) ⟨hk.1.1.2, hk.1.2⟩ (hγHR a))
  have hall : ∀ q, (∀ w, Over (Sum.elim P1 P2 q) w → IsSplitPl D.host w ∧ w.asIdeal.inertiaDeg ℤ = 1 ∧
      Formalism.BasicNotions.eWL D.host.E w = 1 ∧ w ∉ X.S0 i ∧ w ∉ A ∧ normV w % (2 * X.l i ^ M) = 1) ∧
      GoodChar X i M (Sum.elim P1 P2 q) (d (Sum.elim P1 P2 q)) ∧
      (∀ w, Over (Sum.elim P1 P2 q) w → ∀ B : ValuationSubring N.Om, IsPlaceOver B w →
        Ine (F := D.host.E) B ≤ U) := by
    rintro (a | a)
    · exact ⟨(hP1good a).1, (hP1good a).2.1, (hP1good a).2.2.1⟩
    · exact ⟨(hP2good a).1, (hP2good a).2.1, (hP2good a).2.2.1⟩
  have hpair : ∀ q q' : Fin R ⊕ Fin R, Over (Sum.elim P1 P2 q) (Sum.elim P1 P2 q') → q = q' := by
    rintro (a | a) (b | b) hov
    · exact congrArg Sum.inl (hP1d a b hov)
    · exact absurd (Or.inr ⟨a, rfl⟩) ((hP2 b).1 (P1 a) (GlobalTheory.TwistDet.over_symm hov)).1
    · exact absurd (Or.inr ⟨b, rfl⟩) ((hP2 a).1 (P1 b) hov).1
    · exact congrArg Sum.inr (hP2d a b hov)
  have hsteps2 : ∀ a b (σ : GE N), IsFrob (N.plOm.1 (P2 a)) (normV (P2 a)) σ →
      d (P1 b) σ = Multiplicative.ofAdd (if a = b then (1 : ZMod (X.l i ^ M)) else 0) := by
    intro a b σ hσ
    obtain ⟨k, hk⟩ := (hP2 a).2 σ hσ
    have hker : d (P1 b) (k * σ * k⁻¹ * (γ a)⁻¹) = 1 := (Subgroup.mem_iInf.mp hk.2) b
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_comm (d (P1 b) k),
      mul_assoc, mul_inv_cancel, mul_one] at hker
    rw [hker, hγd]
  refine ⟨Sum.elim P1 P2, And.intro (fun q => (hall q).1) (And.intro hpair (fun q => (hall q).2.1)),
    And.intro (fun a σ hσ => ?_) (fun a b σ hσ => hsteps2 a b σ hσ), fun q w hw B hB => (hall q).2.2 w hw B hB,
    fun a => ?_⟩
  · obtain ⟨k, hk⟩ := (hP1 a).2 σ hσ
    exact ⟨k, hk.1.1⟩
  · obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (N.plOm.2 (P2 a))
    obtain ⟨k, hk⟩ := (hP2 a).2 σ hσ
    refine ⟨σ, k, hσ, ?_⟩
    have h1 : k * σ * k⁻¹ * (γ a)⁻¹ ∈ U := hk.1.1.1
    have h2 : h a * ε a * (h a)⁻¹ ∈ U := hUn.conj_mem _ (hεW a).1.1 (h a)
    convert U.mul_mem h1 h2 using 1
    simp only [γ]
    group

end GlobalTheory.ChosenPrimes
