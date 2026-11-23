import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresDoubleCosetAdjointCommuteStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHeckeAdj

variable {D : D7}

abbrev fin (V : HSp D) : GA D V →* Bridge.Gf V := (finHom V).rangeRestrict

theorem fin_inj (V : HSp D) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V) (h : fin V g = fin V g') : g = g' := by
  have h1 : finHom V g = finHom V g' := congrArg Subtype.val h
  refine (inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V ((GfC V).mul_mem ((GfC V).inv_mem hg) hg') ?_))
  show finHom V _ = 1
  rw [map_mul, map_inv, h1, inv_mul_cancel]

theorem map_eq_one_of_supp {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) {n : ℕ} (f : R) (hf : π f = 0)
    (m : Matrix (Fin n) (Fin n) R) (h : ∀ i j, f * (m - 1) i j = (m - 1) i j) : m.map π = 1 := by
  ext i j
  have h1 := congrArg π (h i j)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, ← sub_eq_zero.1 h1.symm |>.symm]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

theorem fin_lift (V : HSp D) (x : Bridge.Gf V) : ∃ g ∈ GfC V, fin V g = x := by
  obtain ⟨x, g, rfl⟩ := x
  let f : Formalism.L2.Theta.AE D := pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)
  have hp : pairA D.host.F 0 1 * pairA D.host.F 0 1 = pairA D.host.F 0 1 :=
    Prod.ext (mul_zero (0 : Ainf D.host.F)) (mul_one (1 : Af D.host.F))
  have hff : f * f = f := by
    simp only [f, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  have hc : cA D f = f := by
    change pairA D.host.F 0 1 ⊗ₜ[D.host.F] (D.sp.cm.sig 1) = _
    rw [map_one]
  obtain ⟨g₁, g₂, h₁, h₂, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hc).2.1 g
  have a : infHom V g₁ = 1 := by
    apply Units.ext
    exact map_eq_one_of_supp (infPart D) f (TensorProduct.zero_tmul _ _) _ h₁
  have b : finHom V g₂ = 1 := by
    apply Units.ext
    refine map_eq_one_of_supp (finPart D) (1 - f) ?_ _ h₂
    rw [RingHom.map_sub, RingHom.map_one, sub_eq_zero]
    rfl
  refine ⟨g₁, a, Subtype.ext ?_⟩
  show finHom V g₁ = finHom V (g₁ * g₂)
  rw [map_mul, b, mul_one]

theorem mem_J (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {g : GA D V}
    (hg : g ∈ GfC V) : fin V g ∈ (levEnv V β L).J ↔ g ∈ levG V β (flag1L L) :=
  ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩

theorem chi_eq (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {g : GA D V}
    (h : fin V g ∈ (levEnv V β L).J) : ((levEnv V β L).χ ⟨fin V g, h⟩ : ℂ) = levChi V β (flag1L L) g := rfl

theorem isConjPl_conj (P : Formalism.L2.DIV.Pl D.host.E) : IsConjPl P (Formalism.DivisionValues.conjPl P) :=
  fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

theorem eq_conj_of_isConjPl {P P' : Formalism.L2.DIV.Pl D.host.E} (h : IsConjPl P P') : P' = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  refine ((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm
  refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
  obtain ⟨c', h1, h2⟩ := h c hc
  have : Formalism.DivisionValues.cO _ c = c' := RingOfIntegers.ext h2.symm
  show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal
  rwa [this]

theorem splitOff_conj {P : Formalism.L2.DIV.Pl D.host.E} {S : Set (Formalism.L2.DIV.Pl D.host.E)} (h : Bridge.SplitOff P S) :
    Bridge.SplitOff (Formalism.DivisionValues.conjPl P) S := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at h1 h3
  refine ⟨?_, fun hh => h3 _ hh rfl, fun Q hQ hh => h2 ?_⟩
  · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]; exact h1.symm
  · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at hh
    rwa [← HeightOneSpectrum.ext hh]

theorem off_of_splitOff {P : Formalism.L2.DIV.Pl D.host.E} {S : Set (Formalism.L2.DIV.Pl D.host.E)} (h : Bridge.SplitOff P S)
    (Q : Formalism.L2.DIV.Pl D.host.E) (hQ : Q ∈ S) : Q ≠ P ∧ ¬ IsConjPl Q P := by
  refine ⟨fun e => h.2.1 (e ▸ hQ), fun hc => h.2.2 Q hQ ?_⟩
  rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]

theorem idem_unique (V : HSp D) {P : Formalism.L2.DIV.Pl D.host.E} {e e' : Formalism.L2.Theta.AE D} (h : IsIdemAt e P)
    (h' : IsIdemAt e' P) : e' = e :=
  (((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ (Or.inl ⟨h, rfl⟩)).2.2.2.1 e' _ (Or.inl ⟨h', rfl⟩)).1

theorem idem_conj (V : HSp D) {P : Formalism.L2.DIV.Pl D.host.E} {e : Formalism.L2.Theta.AE D} (h : IsIdemAt e P) :
    IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) :=
  (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.2 P _ e h (isConjPl_conj P)

theorem suppAt_conj (V : HSp D) {P : Formalism.L2.DIV.Pl D.host.E} {e : Formalism.L2.Theta.AE D} (h : IsIdemAt e P) (g : GA D V) :
    SuppAt (cA D e) V g ↔ SuppAt e V g := by
  have h2 := idem_conj V (idem_conj V h)
  rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at h2
  unfold SuppAt
  rw [idem_unique V h h2, add_comm]

theorem supp_fin (V : HSp D) {P : Formalism.L2.DIV.Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) {g : GA D V}
    (hg : SuppAt e V g) : g ∈ GfC V :=
  ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ (Or.inl ⟨he, rfl⟩)).2.2.1 g hg

theorem idem_mul_one_sub {R : Type} [CommRing R] (f : R) (h : f * f = f) : f * (1 - f) = 0 := by
  rw [mul_sub, h, mul_one, sub_self]

theorem commute_compl (V : HSp D) (f : Formalism.L2.Theta.AE D) (hff : f * f = f) (hcf : cA D f = f) {g g' : GA D V}
    (h : SuppF V f g) (h' : SuppF V (1 - f) g') : Commute g g' :=
  ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hcf).2.2 (1 - f) g g' (idem_mul_one_sub f hff) h h'

theorem transport_local {H G : Type} [Group H] [Group G] (φ : H →* G) (N J₀ L₀ : Subgroup H) (J : Subgroup G)
    (p q : H → Prop) (K : Set H) (χ : J → ℂ) (χ₀ : H → ℂ)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hi : ∀ g g', g ∈ N → g' ∈ N → φ g = φ g' → g = g')
    (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hJN : ∀ g ∈ J₀, g ∈ N) (hL : ∀ g, g ∈ L₀ ↔ p g) (hpN : ∀ g, p g → g ∈ N)
    (hc : ∀ g g', p g → q g' → Commute g g') (hχe : ∀ g (h : φ g ∈ J), χ ⟨φ g, h⟩ = χ₀ g)
    (hK : ∀ g, p g → (g ∈ J₀ ↔ g ∈ K)) (hχ : ∀ g ∈ J₀, p g → χ₀ g = 1)
    (hsp : ∀ k ∈ J₀, ∃ k₁ ∈ J₀, ∃ k₂ ∈ J₀, p k₁ ∧ q k₂ ∧ k = k₁ * k₂)
    (hθ : ∃ θ : H → H, (∀ g, p g → p (θ g)) ∧ (∀ x y, p x → p y → θ (x * y) = θ y * θ x) ∧ (∀ x, p x → θ (θ x) = x) ∧
      (∀ k ∈ {k | k ∈ K ∧ p k}, θ k ∈ K) ∧
      ∀ g, p g → ∃ a ∈ {k | k ∈ K ∧ p k}, ∃ b ∈ {k | k ∈ K ∧ p k}, θ g = a * g * b) :
    (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L₀.map φ ∧ k = k₁ * k₂ ∧ ∀ l ∈ L₀.map φ, Commute k₂ l) ∧
      (∀ k : J, (k : G) ∈ L₀.map φ → χ k = 1) ∧
      ∃ θ : G → G, (∀ g ∈ L₀.map φ, θ g ∈ L₀.map φ) ∧ (∀ x ∈ L₀.map φ, ∀ y ∈ L₀.map φ, θ (x * y) = θ y * θ x) ∧
        (∀ x ∈ L₀.map φ, θ (θ x) = x) ∧ (∀ k ∈ J ⊓ L₀.map φ, θ k ∈ J) ∧
        ∀ g ∈ L₀.map φ, ∃ a ∈ J ⊓ L₀.map φ, ∃ b ∈ J ⊓ L₀.map φ, θ g = a * g * b := by
  have hKJ : ∀ k, k ∈ K → p k → φ k ∈ J := fun k h1 h2 => (hJ k (hpN k h2)).2 ((hK k h2).2 h1)
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, hg, rfl⟩ := hs k
    obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, rfl⟩ := hsp g ((hJ g hg).1 hk)
    refine ⟨φ k₁, (hJ _ (hJN _ h₁)).2 h₁, φ k₂, (hJ _ (hJN _ h₂)).2 h₂, ⟨k₁, (hL _).2 s₁, rfl⟩, map_mul _ _ _, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact (hc l k₂ ((hL l).1 hl) s₂).symm.map φ
  · rintro ⟨k, hk⟩ ⟨g, hg, hgk⟩
    obtain rfl : φ g = k := hgk
    have a := (hL g).1 hg
    rw [hχe, hχ g ((hJ g (hpN g a)).1 hk) a]
  · obtain ⟨θ, t1, t2, t3, t4, t5⟩ := hθ
    choose s hs1 hs2 using hs
    obtain ⟨θ', hθ'⟩ : ∃ θ' : G → G, ∀ g, p g → θ' (φ g) = φ (θ g) :=
      ⟨fun x => φ (θ (s x)), fun g hg => by simp only [hi _ _ (hs1 _) (hpN g hg) (hs2 _)]⟩
    refine ⟨θ', ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      have a := (hL g).1 hg
      exact ⟨θ g, (hL _).2 (t1 g a), (hθ' g a).symm⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      have a := (hL g).1 hg
      have b := (hL g').1 hg'
      rw [← map_mul, hθ' g a, hθ' g' b, hθ' _ ((hL _).1 (L₀.mul_mem hg hg')), t2 g g' a b, map_mul]
    · rintro _ ⟨g, hg, rfl⟩
      have a := (hL g).1 hg
      rw [hθ' g a, hθ' _ (t1 g a), t3 g a]
    · rintro _ ⟨hj, g, hg, rfl⟩
      have a := (hL g).1 hg
      rw [hθ' g a]
      exact hKJ _ (t4 g ⟨(hK g a).1 ((hJ g (hpN g a)).1 hj), a⟩) (t1 g a)
    · rintro _ ⟨g, hg, rfl⟩
      have c := (hL g).1 hg
      obtain ⟨a, ha, b, hb, h⟩ := t5 g c
      refine ⟨φ a, ⟨hKJ a ha.1 ha.2, a, (hL a).2 ha.2, rfl⟩, φ b, ⟨hKJ b hb.1 hb.2, b, (hL b).2 hb.2, rfl⟩, ?_⟩
      rw [hθ' g c, h, map_mul, map_mul]

section Level

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
  (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1)

include hβ

theorem norm_chi (k : (levEnv V β L).J) : ‖((levEnv V β L).χ k : ℂ)‖ = 1 := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨g, hg, rfl⟩ := fin_lift V k
  have h0 := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).1 g ((mem_J V β L hg).1 hk)
  obtain ⟨n, hn, h⟩ := h0
  rw [chi_eq]
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

theorem local_group (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (he : IsIdemAt e P)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P) :
    ∃ Lc : Subgroup (Bridge.Gf V), (∀ g, SuppAt e V g → fin V g ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L).J, ∃ k₁ ∈ (levEnv V β L).J, ∃ k₂ ∈ (levEnv V β L).J,
        k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l) ∧
      (∀ k : (levEnv V β L).J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L).χ k = 1) ∧
      (∃ θ : Bridge.Gf V → Bridge.Gf V, (∀ g ∈ Lc, θ g ∈ Lc) ∧ (∀ x ∈ Lc, ∀ y ∈ Lc, θ (x * y) = θ y * θ x) ∧
        (∀ x ∈ Lc, θ (θ x) = x) ∧ (∀ k ∈ (levEnv V β L).J ⊓ Lc, θ k ∈ (levEnv V β L).J) ∧
        ∀ g ∈ Lc, ∃ a ∈ (levEnv V β L).J ⊓ Lc, ∃ b ∈ (levEnv V β L).J ⊓ Lc, θ g = a * g * b) ∧
      ∀ k ∈ locPart V (KsphC V ∅) e, fin V k ∈ (levEnv V β L).J := by
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ hP
  have hff := h01.1
  have hcf := h01.2.1
  have h02 := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hff hcf).1
  refine h02.elim fun L₀ hL₀ => ?_
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have h03 := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e _ hP h1 hoff
  have hK := h03.1
  have hχ := h03.2.1
  have hsp := h03.2.2
  have hL : ∀ g, g ∈ L₀ ↔ SuppAt e V g := hL₀
  have hKJ : ∀ k ∈ locPart V (KsphC V ∅) e, fin V k ∈ (levEnv V β L).J := fun k hk =>
    (mem_J V β L (supp_fin V he hk.2)).2 ((hK k hk.2).2 hk.1)
  have h04 := (GlobalTheory.T.involution_spherical_hecke_anti V P e he).1
  have h05 := transport_local (fin V) (GfC V) (levG V β (flag1L L)) L₀ (levEnv V β L).J (SuppAt e V)
    (SuppF V (1 - (e + cA D e))) (KsphC V ∅) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L))
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L) (fun g hg => hg.1) hL (fun g => supp_fin V he)
    (fun g g' => commute_compl V _ hff hcf) (fun g => chi_eq V β L) hK hχ hsp h04
  exact ⟨L₀.map (fin V), fun g hg => ⟨g, (hL g).2 hg, rfl⟩, h05.1, fun k hk => Units.ext (h05.2.1 k hk), h05.2.2, hKJ⟩

end Level

theorem isDC_of_mem {G : Type} [Group G] {J : Subgroup G} {x y a b : G} {A : Finset G} (ha : a ∈ J) (hb : b ∈ J)
    (h : y = a * x * b) (hA : Bridge.IsDC J y A) : Bridge.IsDC J x A := by
  subst h
  refine ⟨fun c hc => ?_, fun g ⟨k₁, k₂, hg⟩ => hA.2 g ?_⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hA.1 c hc
    exact ⟨k₁ * ⟨a, ha⟩, ⟨b, hb⟩ * k₂, by simp only [Subgroup.coe_mul, mul_assoc]⟩
  · exact ⟨k₁ * ⟨a, ha⟩⁻¹, ⟨b, hb⟩⁻¹ * k₂, by rw [hg]; simp [mul_assoc]⟩

theorem dcOp_comm_of_commute {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {A B : Finset G}
    (h : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (F : G → W) :
    Bridge.dcOp A (Bridge.dcOp B F) = Bridge.dcOp B (Bridge.dcOp A F) := by
  funext g
  simp only [Bridge.dcOp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  rw [mul_assoc, mul_assoc, (h a ha b hb).eq]

theorem hecke_conj (V : HSp D) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ} {α α' : GA D V} {e : Formalism.L2.Theta.AE D}
    (he : IsIdemAt e P) (h : IsHeckeAt V P k α) (h' : IsHeckeAt V (Formalism.DivisionValues.conjPl P) k α') :
    ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α⁻¹ * b := by
  obtain ⟨e₁, ϖ, h1, h2, h3, h4⟩ := h
  obtain ⟨e₂, ϖ', h1', h2', h3', h4'⟩ := h'
  obtain rfl := idem_unique V he h1
  have hc := idem_conj V he
  obtain rfl := idem_unique V hc h1'
  have h5 := (((GlobalTheory.T.involution_spherical_hecke_anti V P e₁ he).2.2 ϖ h2 h3).2 k α h4).1
  have h6 : Formalism.DivisionValues.cO _ ϖ ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ h2
  have h7 : Formalism.DivisionValues.cO _ ϖ ∉ (Formalism.DivisionValues.conjPl P).asIdeal ^ 2 := by
    intro hh
    have : (Formalism.DivisionValues.conjPl P).asIdeal ^ 2 = (P.asIdeal ^ 2).map (Formalism.DivisionValues.cO D.host.E) := (Ideal.map_pow _ _ _).symm
    rw [this, Ideal.mem_map_of_equiv] at hh
    obtain ⟨x, hx, hx'⟩ := hh
    exact h3 ((Formalism.DivisionValues.cO D.host.E).injective hx' ▸ hx)
  obtain ⟨a, ha, b, hb, hab⟩ := (((GlobalTheory.T.involution_spherical_hecke_anti V _ _ hc).2.2 _ h6 h7).2 k α⁻¹ h5).2 ϖ' α' h2' h3' h4'
  exact ⟨a, ⟨ha.1, (suppAt_conj V he a).1 ha.2⟩, b, ⟨hb.1, (suppAt_conj V he b).1 hb.2⟩, hab⟩

theorem loc_supp (V : HSp D) {Pl0 : Type} {pl : Pl0 → Formalism.L2.DIV.Pl D.host.E} {ok : Set Pl0} {i : ok × ℕ}
    {x : Bridge.Gf V} (h : isLocEnv V pl ok i x) {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e (pl i.1)) :
    ∃ g, SuppAt e V g ∧ fin V g = x := by
  obtain ⟨e', α, h1, -, h2, h3⟩ := h
  obtain rfl := idem_unique V he h1
  exact ⟨α, h2, Subtype.ext h3.symm⟩

set_option maxHeartbeats 1600000 in

theorem side_adj_comm (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1) {Pl0 : Type}
    (pl : Pl0 → Formalism.L2.DIV.Pl D.host.E) (ok : Set Pl0) (Sp : Set (Formalism.L2.DIV.Pl D.host.E))
    (hok : ∀ P, P ∈ ok ↔ Bridge.SplitOff (pl P) Sp) (honto : ∀ PP, Bridge.SplitOff PP Sp → ∃ P, pl P = PP)
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ∈ Sp) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : GQ V →* Module.End ℂ W) (hρ : ∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u')
    {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : Formalism.L2.DIV.CSD K)
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ)
    (op : ok × ℕ → Module.End K S.Forms)
    (T : Bridge.HeckeTie (Bridge.ratF V) Pr op (fun i => 1 ≤ i.2 ∧ i.2 ≤ V.rank) (isTEnv V pl ok) (isLocEnv V pl ok))
    (h0 : ∀ P, op (P, 0) = 1 ∧ ∀ k, V.rank < k → op (P, k) = 0) :
    (∀ i, ∃ i', ∀ f g : S.Forms, S.csum (op i f : S.Cl → S.V) (g : S.Cl → S.V) =
      S.csum (f : S.Cl → S.V) (op i' g : S.Cl → S.V)) ∧ Formalism.L2.Col.PairComm op := by
  have hout : ∀ i : ok × ℕ, ¬ (1 ≤ i.2 ∧ i.2 ≤ V.rank) → op i = 1 ∨ op i = 0 := by
    rintro ⟨P, k⟩ h
    by_cases hk : k = 0
    · subst hk; exact Or.inl (h0 P).1
    · exact Or.inr ((h0 P).2 k (by simp only at h; omega))
  have key : ∀ i : ok × ℕ, 1 ≤ i.2 ∧ i.2 ≤ V.rank → ∃ i' : ok × ℕ, ∀ j : ok × ℕ, 1 ≤ j.2 ∧ j.2 ≤ V.rank →
      (∀ f g : S.Forms, S.csum (op i f : S.Cl → S.V) (g : S.Cl → S.V) =
        S.csum (f : S.Cl → S.V) (op i' g : S.Cl → S.V)) ∧ Commute (op i) (op j) := by
    intro i hi
    have hx := T.hx_ok i hi hi.2
    obtain ⟨α, hα, hxα⟩ := hx
    have hα0 := hα
    obtain ⟨e, -, he, -⟩ := hα0
    have hsp := (hok _).1 i.1.2
    obtain ⟨P', hP'⟩ := honto _ (splitOff_conj hsp)
    have hP'ok : P' ∈ ok := (hok _).2 (hP' ▸ splitOff_conj hsp)
    let i' : ok × ℕ := (⟨P', hP'ok⟩, i.2)
    have hi' : 1 ≤ i'.2 ∧ i'.2 ≤ V.rank := hi
    have hx' := T.hx_ok i' hi' hi'.2
    obtain ⟨α', hα', hxα'⟩ := hx'
    have hα'' : IsHeckeAt V (Formalism.DivisionValues.conjPl (pl i.1)) i.2 α' := hP' ▸ hα'
    have hl := local_group V β Λ L hβ (pl i.1) e he fun PP h => off_of_splitOff hsp PP (hS PP h)
    obtain ⟨Lc, l1, l2, l3, l4, l5⟩ := hl
    have hc := hecke_conj V he hα hα''
    obtain ⟨a, ha, b, hb, hab⟩ := hc
    have e1 : T.hx i = fin V α⁻¹ := Subtype.ext hxα
    have e2 : T.hx i' = fin V α'⁻¹ := Subtype.ext hxα'
    have hDC' : Bridge.IsDC (levEnv V β L).J (T.hx i)⁻¹ (T.hA i') := by
      refine isDC_of_mem (Subgroup.inv_mem _ (l5 b hb)) (Subgroup.inv_mem _ (l5 a ha)) ?_ (T.hDC i' hi')
      rw [e1, e2, hab]
      simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
    have hA : ∀ x ∈ T.hA i, ∃ g, SuppAt e V g ∧ fin V g = x := fun x hx => loc_supp V (T.hA_loc i hi x hx) he
    have hAL : ∀ x ∈ T.hA i, x ∈ Lc := fun x hx => by
      obtain ⟨g, hg, rfl⟩ := hA x hx
      exact l1 g hg
    have he' : IsIdemAt (cA D e) (pl i'.1) := by
      have := idem_conj V he
      rw [← hP'] at this
      exact this
    have hAL' : ∀ x ∈ T.hA i', x ∈ Lc := fun x hx => by
      obtain ⟨g, hg, rfl⟩ := loc_supp V (T.hA_loc i' hi' x hx) he'
      exact l1 g ((suppAt_conj V he g).1 hg)
    refine ⟨i', fun j hj => ?_⟩
    have main := GlobalTheory.T.classPres_doubleCoset_adjoint_commute (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ Pr Lc (T.hx i) (T.hA i) (T.hA i')
      (T.hA j) (op i) (op i') (op j) hρ (norm_chi V β Λ L hβ) l2 l3 hAL hAL' (T.hDC i hi) hDC' (T.op_eq i hi)
      (T.op_eq i' hi') (T.op_eq j hj)
    refine ⟨main.1, main.2 fun F hF => ?_⟩
    have hy := T.hx_ok j hj hj.2
    obtain ⟨-, ⟨e', -, he', -⟩, -⟩ := hy
    have hB : ∀ x ∈ T.hA j, ∃ g, SuppAt e' V g ∧ fin V g = x := fun x hx => loc_supp V (T.hA_loc j hj x hx) he'
    have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 _ e _ (Or.inl ⟨he, rfl⟩)
    have h02 := h01.2.2.2.2 _ e' _ (Or.inl ⟨he', rfl⟩)
    rcases h02 with h02 | h02
    · refine dcOp_comm_of_commute (fun x hx y hy => ?_) F
      obtain ⟨g, hg, rfl⟩ := hA x hx
      obtain ⟨g', hg', rfl⟩ := hB y hy
      exact (((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ h01.1 h01.2.1).2.2 _ g g' h02 hg hg').map (fin V)
    · have hBL : ∀ x ∈ T.hA j, x ∈ Lc := fun x hx => by
        obtain ⟨g, hg, rfl⟩ := hB x hx
        refine l1 g ?_
        unfold SuppAt at hg ⊢
        rw [← h02.1]
        exact hg
      refine (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (levEnv V β L).J Lc (levEnv V β L).χ (T.hx i) (T.hx j) (T.hA i)
        (T.hA j) (T.hA i') F l2 l3 l4 hAL hBL hAL' (T.hDC i hi) (T.hDC j hj) hDC' fun k h => ?_).1
      have := hF 1 h k
      rwa [map_one, map_one, one_mul, Module.End.one_apply] at this
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · by_cases hi : 1 ≤ i.2 ∧ i.2 ≤ V.rank
    · obtain ⟨i', h⟩ := key i hi
      exact ⟨i', (h i hi).1⟩
    · refine ⟨i, fun f g => ?_⟩
      rcases hout i hi with h | h
      · rw [h]; rfl
      · rw [h]; simp [Formalism.L2.DIV.CSD.csum]
  · by_cases hi : 1 ≤ i.2 ∧ i.2 ≤ V.rank
    · by_cases hj : 1 ≤ j.2 ∧ j.2 ≤ V.rank
      · obtain ⟨i', h⟩ := key i hi
        exact (h j hj).2
      · rcases hout j hj with h | h <;> rw [h]
        exacts [Commute.one_right _, Commute.zero_right _]
    · rcases hout i hi with h | h <;> rw [h]
      exacts [Commute.one_left _, Commute.zero_left _]

theorem splitOff_mono {P : Formalism.L2.DIV.Pl D.host.E} {S S' : Set (Formalism.L2.DIV.Pl D.host.E)} (hS : S ⊆ S')
    (h : Bridge.SplitOff P S') : Bridge.SplitOff P S :=
  ⟨h.1, fun hh => h.2.1 (hS hh), fun Q hQ => h.2.2 Q (hS hQ)⟩

end GlobalTheory.SplitHeckeAdj
