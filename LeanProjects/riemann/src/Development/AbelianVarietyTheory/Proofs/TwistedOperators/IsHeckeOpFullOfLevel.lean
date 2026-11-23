import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteIndexDimensionCounts
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CharacterPartsGaps
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DownUpLambdaOperators
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.DimPartsOfGoodIdempotentZero
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.RowsNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K G X H E : Type} [Field K] [Group G] [Fintype G] [AddCommGroup X] [Module K X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] in

theorem mem_range_adjoint (ρ : Representation ℂ G H) (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E)
    (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖) (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y)) (g : G) {y : H}
    (hy : y ∈ LinearMap.range (LinearMap.adjoint Θ)) : ρ g y ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  rw [← LinearMap.orthogonal_ker, Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  have h1 : ρ g (ρ g⁻¹ u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : inner ℂ (ρ g (ρ g⁻¹ u)) (ρ g y) = inner ℂ (ρ g⁻¹ u) y := LinearIsometry.inner_map_map ⟨ρ g, hρ g⟩ _ _
  rw [← h1, h2]
  refine hy _ ?_
  rw [LinearMap.mem_ker] at hu ⊢
  rw [hΘ, hu, map_zero]

theorem exists_rational {σ : K →+* ℂ} (j : X →ₛₗ[σ] H) (r : Representation K G X) (ρ : Representation ℂ G H)
    (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E) (hj : ∀ g z, j (r g z) = ρ g (j z)) (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖)
    (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y))
    (hrat : LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}))
    (a b : G → K) {x u : E} (hx : x ≠ 0) (hu : Θ (LinearMap.adjoint Θ u) = x)
    (ha : ∑ g, σ (a g) • π g x = x) (hb : ∑ g, σ (b g) • π g x = x) :
    ∃ z, (∑ g, a g • r g) ((∑ g, b g • r g) z) ≠ 0 ∧
      j ((∑ g, a g • r g) ((∑ g, b g • r g) z)) ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  have hop : ∀ (c : G → K) z, j ((∑ g, c g • r g) z) = ∑ g, σ (c g) • ρ g (j z) := fun c z => by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]
  have hst : ∀ (c : G → K) z, j z ∈ LinearMap.range (LinearMap.adjoint Θ) →
      j ((∑ g, c g • r g) z) ∈ LinearMap.range (LinearMap.adjoint Θ) := fun c z hz => by
    rw [hop]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (mem_range_adjoint ρ π Θ hρ hΘ g hz)
  have hth : ∀ (c : G → K) z, Θ (j ((∑ g, c g • r g) z)) = (∑ g, σ (c g) • π g) (Θ (j z)) := fun c z => by
    rw [hop]
    simp only [map_sum, map_smul, hΘ, LinearMap.sum_apply, LinearMap.smul_apply]
  by_contra hn
  push Not at hn
  have hker : Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}) ≤
      LinearMap.ker ((∑ g, σ (a g) • π g) ∘ₗ (∑ g, σ (b g) • π g) ∘ₗ Θ) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    have h0 : (∑ g, a g • r g) ((∑ g, b g • r g) z) = 0 := by
      by_contra h0
      exact hn z h0 (hst a _ (hst b z hz))
    show (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (j z))) = 0
    rw [← hth, ← hth, h0, map_zero, map_zero]
  have h1 : (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (LinearMap.adjoint Θ u))) = 0 := hker (hrat ⟨u, rfl⟩)
  simp only [hu, LinearMap.sum_apply, LinearMap.smul_apply, hb, ha] at h1
  exact hx h1

omit [FiniteDimensional ℂ E] in

theorem sum_lvlIdem {σ : K →+* ℂ} (π : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) {x : E}
    (hx : ∀ g : P, π (g : G) x = σ ((ψ g : Kˣ) : K) • x) : ∑ g, σ ((lvlIdem P ψ).coeff g) • π g x = x := by
  classical
  have hc : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h1 : ∀ (h : G) (c : K), ∑ g, σ ((MonoidAlgebra.single h c).coeff g) • π g x = σ c • π h x := fun h c => by
    rw [Finset.sum_eq_single h]
    · simp
    · intro g _ hg
      simp [Finsupp.single_eq_of_ne hg]
    · simp
  have h2 : ∀ h : P, σ ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • π (h : G) x = (Nat.card P : ℂ)⁻¹ • x := fun h => by
    rw [hx h, smul_smul, ← map_mul, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one,
      map_inv₀, map_natCast]
  unfold lvlIdem
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [h1, h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Nat.card_eq_fintype_card, mul_inv_cancel₀ hc, one_smul]

end Abstract

section Hecke

open GlobalTheory.HeckeModel GlobalTheory.SphericalOps

variable {D : D7}

theorem realUnif (P : HeightOneSpectrum (𝓞 D.host.E)) : RealUnif (D := D) P := by
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    have := D.host.isCMField_hostE
    exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  have := P.isPrime
  have h : ¬ P.asIdeal ∣ differentIdeal (𝓞 D.host.F) (𝓞 D.host.E) :=
    not_dvd_differentIdeal_iff.2 (Algebra.unramified_iff_forall.1 hU ⟨P.asIdeal, P.isPrime⟩)
  by_contra hne
  unfold RealUnif at hne
  push Not at hne
  apply h
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hne x _ rfl hx
  have := P.isMaximal
  have : (P.asIdeal.under (𝓞 D.host.F)).IsMaximal := Ideal.IsMaximal.under _ _
  have hb : P.asIdeal.under (𝓞 D.host.F) ≠ ⊥ := Ideal.under_ne_bot _ P.ne_bot
  have := pow_sub_one_dvd_differentIdeal (𝓞 D.host.F) P.asIdeal 2 hb (Ideal.dvd_iff_le.2 hle)
  simpa using this

theorem not_mem_of_offS {P : HeightOneSpectrum (𝓞 D.host.E)} (h : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h (P.under (𝓞 D.host.F)) ((GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.mem_finS D _).2 (by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
    rwa [map_natCast]))
  exact hy (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl hx

variable {V : HSp D} {S : D.what₂.Tau → SPar} {β : GL (Fin V.rank) (Lev.EAf D)}

def AtTypePrimes (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : Prop :=
  (∃ Λ N, IsBaseFrame V β Λ N ∧ ∃ c, N ∣ (D.host.g 0 * D.host.g 1) ^ c) ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal

theorem AtTypePrimes.split {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (h : AtTypePrimes β L)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (hP : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P)
    (hp : IsPrimeIdem P e f) :
    (∀ g, SuppF V f g → (g ∈ levG V β L ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ levG V β L, SuppF V f g → levChi V β L g = 1) ∧
      ∀ k ∈ levG V β L, ∃ k₁ ∈ levG V β L, ∃ k₂ ∈ levG V β L, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  obtain ⟨Λ, N, hβ, c, a, ha⟩ := h.1
  have h0 := not_mem_of_offS hP
  refine (GlobalTheory.LevSplit.lev_split V β Λ N L hβ).2 P e f hp (fun hN => h0 ?_)
    fun PP hPP => ⟨fun e => h0 (e ▸ h.2 PP hPP), fun hc => h0 ?_⟩
  · refine P.isPrime.mem_of_pow_mem c ?_
    rw [← Nat.cast_pow, ha, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hN
  · obtain ⟨c', h1, h2⟩ := hc _ (h.2 PP hPP)
    have : c' = ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by
      rw [h2]; simp)
    rwa [this] at h1

theorem isHeckeOpFull_of_level {L L' : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (h' : AtTypePrimes β L')
    {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {A : Finset (GA D V)}
    (hA : Hecke₂ V (levS V β L) (levChi V β L) (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P d A) :
    Hecke₂ V (levS V β L') (levChi V β L') (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P d A := by
  obtain ⟨e, f, ϖ, α, hS, hp, h1, h2, hd, hJ, -, hα, hD, hR, hc⟩ := hA
  obtain ⟨k1, k2, -⟩ := h'.split hS hp
  refine ⟨e, f, ϖ, α, hS, hp, h1, h2, hd, k1, k2, hα, hD, hR, ?_⟩
  have : {k | k ∈ levS V β L' ∧ SuppF V f k} = {k | k ∈ levS V β L ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => (k1 k hk).trans (hJ k hk).symm
  rwa [this]

theorem AtTypePrimes.offAt {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (h : AtTypePrimes β L)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (hP : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P)
    (hp : IsPrimeIdem P e f) {K large₂ : Subgroup (GA D V)} (hLg : ∀ g, g ∈ large₂ ↔ SuppF V f g)
    (hK : ∀ g, g ∈ K ↔ g ∈ KsphC V ∅ ∧ SuppF V f g) : OffAt β L K large₂ := by
  obtain ⟨h1, h2, h3⟩ := h.split hP hp
  obtain ⟨hf, hcf, -⟩ := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hp
  have hc := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 f hf hcf).2.2
  refine ⟨⟨fun g hg => (hLg g).2 ((hK g).1 hg).2, fun g hg => ?_, fun k hk => ?_⟩, fun k hk => ?_⟩
  · rw [h1 g ((hLg g).1 hg), hK]
    exact ⟨fun h => ⟨h, (hLg g).1 hg⟩, fun h => h.1⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, s₁, s₂, rfl⟩ := h3 k hk
    refine ⟨k₁, (hK _).2 ⟨(h1 _ s₁).1 hk₁, s₁⟩, k₂, hk₂, rfl, fun l hl => ?_⟩
    exact (hc (1 - f) l k₂ (by rw [mul_sub, mul_one, hf, sub_self]) ((hLg l).1 hl) s₂).symm
  · have := (hK k).1 hk
    exact h2 k ((h1 k this.2).2 this.1) this.2

theorem heckeOn_mem {θ : InfFam D} {M : DSModel V S} {L L' : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    (h : AtTypePrimes β L) (h' : AtTypePrimes β L') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (a : G → ℂ)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {A : Finset (GA D V)}
    (hA : Hecke₂ V (levS V β L') (levChi V β L') (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P d A) {T : MMap M}
    (hT : T ∈ goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG a)) :
    heckeOn M A T ∈ goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG a) := by
  obtain ⟨e, f, ϖ, α, hS, hp, -, -, -, hJ, -, hα, -, -, hc⟩ := hA
  obtain ⟨hf, hcf, hfin, -⟩ := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f hp
  obtain ⟨large₂, hLg⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 f hf hcf).1
  have hK : ∀ g, g ∈ levG V β L' ⊓ large₂ ↔ g ∈ KsphC V ∅ ∧ SuppF V f g := fun g =>
    ⟨fun hg => ⟨(hJ g ((hLg g).1 hg.2)).1 hg.1, (hLg g).1 hg.2⟩, fun hg => ⟨(hJ g hg.2).2 hg.1, (hLg g).2 hg.2⟩⟩
  exact heckeOn_mem_goodPart (AtTypePrimes.offAt (L := flagL L) ⟨h.1, h.2⟩ hS hp hLg hK) (h'.offAt hS hp hLg hK)
    (fun g hg => hfin g ((hLg g).1 hg)) eG a ((hLg α).2 hα) (isDC_of_rep hLg hc) hT

theorem exists_part_ne_bot {θ : InfFam D} {M : DSModel V S} {L L' : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    (h : AtTypePrimes β L) (h' : AtTypePrimes β L') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (a : G → ℂ)
    (hpos : 0 < Module.finrank ℂ (goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG a))) :
    ∃ c, partFull θ M (levS V β L') (levChi V β L') (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) c ⊓
      goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG a) ≠ ⊥ := by
  classical
  have := Module.finite_of_finrank_pos hpos
  have := Module.nontrivial_of_finrank_pos hpos
  have hlev : ∀ T : goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG a), ∀ v,
      ∀ k ∈ (levG V β L' : Set (GA D V)), ∀ g, (T : MMap M) v (g * k) = levChi V β L' k * (T : MMap M) v g := fun T =>
    ((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ _).1 T.2.1).lev
  obtain ⟨T, hT0, hT⟩ := GlobalTheory.exists_common_eigenvector_of_commute (L := ℂ)
    (ι := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D V) //
      Hecke₂ V (levS V β L') (levChi V β L') (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) x.1 x.2.1 x.2.2})
    (V := goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG a))
    (fun i => (heckeOn M i.1.2.2).restrict fun _ hT => heckeOn_mem h h' eG a i.2 hT)
    (fun i k => LinearMap.ext fun T => Subtype.ext (MultilinearMap.ext fun v =>
      comm_heckeLin (J := levG V β L') (realUnif _) i.2 k.2 (hlev T v)))
  choose x hx using hT
  refine ⟨fun P d => if hR : ∃ R, Hecke₂ V (levS V β L') (levChi V β L') (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P d R then
    x ⟨(P, d, hR.choose), hR.choose_spec⟩ else 0, fun hb => hT0 (Subtype.ext ?_)⟩
  refine (Submodule.eq_bot_iff _).1 hb _ ⟨(mem_partFull ..).2 ⟨T.2.1, fun P d R hR v => ?_⟩, T.2⟩
  have hex : ∃ R, Hecke₂ V (levS V β L') (levChi V β L') (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D) P d R := ⟨R, hR⟩
  rw [dif_pos hex, labelUnique (J := levG V β L') realUnif P d R hex.choose hR hex.choose_spec _ (hlev T v)]
  exact congrArg (fun U : goodPart θ M (levS V β L') (levChi V β L') (gaL V β L eG a) => (U : MMap M) v)
    (hx ⟨(P, d, hex.choose), hex.choose_spec⟩)

end Hecke

section Rows

variable {D : D7}

theorem mult_le_principal {V : HSp D} {S : D.what₂.Tau → SPar} {β : GL (Fin V.rank) (Lev.EAf D)} {θ : InfFam D} {M : DSModel V S}
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) :
    Mult θ M (levS V β (withP L P)) (levChi V β (withP L P)) ≤ Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) := by
  refine Submodule.span_mono fun T hT => ⟨hT.aut, hT.cusp, fun v k hk g => ?_, hT.equiv, hT.cont⟩
  have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
  have h2 : k ∈ levS V β (withP L P) := ⟨hk.1, hk.2.1, (h1 ▸ P.H.one_mem : rTup β L (finE V k) ∈ P.H)⟩
  rw [hT.lev v k h2 g]
  unfold levChi
  rw [levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem mem_of_mem_Pg (hL : R.toLevCh.Is A.μ0) {PP : Pl D.host.E} (h : PP ∈ R.Pg) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have e : PP.under (𝓞 D.host.K) = R.C.P.pb k := hk
    rw [e]
    exact R.C.P.pb_over k
  have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← map_natCast (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))]
    exact h1
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ h2
  · exact Ideal.mul_mem_left _ _ h2

theorem atTypePrimes_rows (hL : R.toLevCh.Is A.μ0) (P : LevelP R.Pg D.R.r ℂ) : AtTypePrimes (R.βY 0) (R.dat0 P) := by
  obtain ⟨c, hc⟩ := hL.βY 0 (by have := D.R.two_le_m; omega)
  exact ⟨⟨_, _, hc, c, dvd_rfl⟩, fun PP h => h.elim (mem_of_mem_Pg R hL) fun h => absurd h (Finset.notMem_empty _)⟩

theorem atTypePrimes_lift (hL : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) :
    AtTypePrimes (R.βW i) (R.datWp i P) := by
  obtain ⟨c, hc⟩ := hL.βW i
  exact ⟨⟨_, _, hc, 0, by simp⟩, fun PP h => h.elim (mem_of_mem_Pg R hL) fun h => absurd h (Finset.notMem_empty _)⟩

theorem exists_row (hL : R.toLevCh.Is A.μ0) (hE : R.models_HE) (hM : GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.MatchAll R F) (b : Bool) (i : Fin D.R.m)
    (hW : 0 < GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.dGood R F b i) :
    ∃ (c : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.Eig D) (x : R.HE.H), x ≠ 0 ∧ R.HE.e x ∈ R.EEat (R.levR F b) ∧ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R c := by
  obtain ⟨c, hc⟩ := exists_part_ne_bot (θ := R.θ) (M := R.MW i (sg0 D A)) (atTypePrimes_lift R hL i R.triv)
    (atTypePrimes_lift R hL i (R.levL F b (sg0 D A))) R.eG (RealDat.eC (A := A) (sg0 D A)) hW
  obtain ⟨h1, h2, h3⟩ := hM.2 b i c
  have h4 : GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.EEc R (R.levR F b) c ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h3
    exact hc ((Submodule.finrank_eq_zero (S := GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.Wc' R i (R.levL F b (sg0 D A)) c)).1 h3.symm)
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 h4
  have hm : U ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
    mult_le_principal (R.dat0 R.triv) (R.levR F b) hU.2.1
  have ht : U ∈ R.EEat R.triv := ⟨hm, hU.2.2⟩
  obtain ⟨x, rfl⟩ : U ∈ LinearMap.range R.HE.e := hE.2.1 ▸ ht
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.typePlaces D = GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.finS D :=
    Finset.ext fun v => (GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.mem_typePlaces D v).trans (GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps.mem_finS D v).symm
  refine ⟨c, x, fun h0 => hU0 (by rw [h0, map_zero]), hU.2, ⟨?_, ht⟩⟩
  rw [hS]
  exact (mem_partFull ..).2 ⟨hm, fun P d B hB =>
    ((mem_partFull ..).1 hU.1).2 P d B (isHeckeOpFull_of_level (atTypePrimes_rows R hL _) hB)⟩

theorem dZ_pos {K : Type} [Field K] [NumberField K] [StarRing K] (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    {z : B.S.Forms} (h0 : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ≠ 0)
    (hZ : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ∈ Z) : 0 < B.dZ ℓ Z := by
  rw [← B.gaOp_mul, ← goodAt] at h0 hZ
  have hV : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  obtain ⟨u, hu⟩ : B.S.basis.equivFun (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
    rw [hV]
    exact ⟨B.S.basis.equivFun z, by rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun]⟩
  rw [Matrix.mulVecLin_apply] at hu
  refine Nat.pos_of_ne_zero fun h => h0 ?_
  have h1 : u ∈ B.Z0 ℓ Z := by
    rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
    exact hZ
  rw [Submodule.finrank_eq_zero.1 h, Submodule.mem_bot] at h1
  rw [h1, Matrix.mulVec_zero] at hu
  exact B.S.basis.equivFun.map_eq_zero_iff.1 hu.symm

end Rows

end GlobalTheory.RowsNonzero

end
