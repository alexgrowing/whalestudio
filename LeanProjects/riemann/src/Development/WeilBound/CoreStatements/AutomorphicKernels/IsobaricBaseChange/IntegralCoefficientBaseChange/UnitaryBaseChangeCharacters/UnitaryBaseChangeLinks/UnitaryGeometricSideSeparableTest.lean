import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.OrbitalIntegralUnitIndicatorEventuallyOneClassIm
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryConjugacySignProductStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.KappaSignMultiplicative
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryMassFormulaStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.KappaConstantMulOfCoprimeEllipticPolynomialsImpo
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariantStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolySelfReciprocal
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalPointsIntegralAlmostAllStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolyLocalRealisationStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralConjugacyAlmostAllStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.FiniteEllipticCharpolysSupportStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.MonicDivisorSignSumStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.AdelicClassCountProductStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PreStabU

section Generic

variable {G : Type} [Group G]

def cls (x : G) : TwCl (MonoidHom.id G) := Quot.mk _ x

theorem cls_eq_iff (x y : G) : cls x = cls y ↔ ∃ g, y = g⁻¹ * x * g := by
  have h : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * (MonoidHom.id G) g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  exact Quot.eq.trans h.eqvGen_iff

theorem cls_rep (c : TwCl (MonoidHom.id G)) : cls c.rep = c := Quot.out_eq c

theorem rep_cls (x : G) : ∃ g, (cls x).rep = g⁻¹ * x * g := (cls_eq_iff _ _).1 (cls_rep _).symm

theorem exists_ne_zero_of_twOrb [TopologicalSpace G] (K : Subgroup G) (δ : G) (f : G → ℂ)
    (h : twOrb (MonoidHom.id G) K δ f ≠ 0) : ∃ g, f (g⁻¹ * δ * g) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  simp only [twOrb, avg, MonoidHom.id_apply, hc, finsum_zero, mul_zero]

theorem twOrb_conj [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G} (hK : IsCompact (K : Set G))
    (hK' : IsLevel (MonoidHom.id G) K K') {f : G → ℂ} (hf : IsHecke K' f) (δ g : G) :
    twOrb (MonoidHom.id G) K (g⁻¹ * δ * g) f = twOrb (MonoidHom.id G) K δ f := by
  refine GlobalTheory.T.twistedOrbitalIntegral_twistedConj_invariant G (MonoidHom.id G) K δ g f fun x => ?_
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.1.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  have hi : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ne_zero_of_dvd_ne_zero hi (Subgroup.index_dvd_of_le fun k hk y => ?_)
  have hk' : (k : G) ∈ K' := hk
  have e : (x * ((y * k : K) : G))⁻¹ * δ * (MonoidHom.id G) (x * ((y * k : K) : G)) =
      (k : G)⁻¹ * (((x * y)⁻¹ * δ * (MonoidHom.id G) (x * y)) * k) := by
    simp only [MonoidHom.id_apply, Subgroup.coe_mul]; group
  show f _ = f _
  rw [e, (hf.2 _ (K'.inv_mem hk') _).1, (hf.2 _ hk' _).2]

end Generic

theorem finsum_subtype_if {α : Type} (p : α → Prop) [DecidablePred p] (u : α → ℂ) :
    ∑ᶠ a : Subtype p, u a.1 = ∑ᶠ a, if p a then u a else 0 := by
  rw [finsum_subtype_eq_finsum_cond]
  exact finsum_congr fun a => finsum_eq_if

theorem finsum_fibres {α β : Type} (u : α → ℂ) (q : α → β) (F : Finset β) (hu : (Function.support u).Finite)
    (hF : ∀ a, u a ≠ 0 → q a ∈ F) : ∑ᶠ a, u a = ∑ b ∈ F, ∑ᶠ a, if q a = b then u a else 0 := by
  rw [← finsum_sum_comm]
  · refine finsum_congr fun a => ?_
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hc
      exact h (hF a hc)
  · intro b _
    refine hu.subset fun a ha => ?_
    intro h0
    apply ha
    simp [h0]

theorem ne_zero_of_finprod {ι : Type} {S : Set ι} {u : ι → ℂ} (h1 : ∀ᶠ w in cofinite, u w = 1)
    (h : ∏ᶠ w ∈ S, u w ≠ 0) : ∀ w ∈ S, u w ≠ 0 := by
  intro w hw h0
  apply h
  have hf : (Function.mulSupport u).Finite := h1
  rw [finprod_mem_def]
  refine finprod_eq_zero _ w (by simp [hw, h0]) ?_
  refine hf.subset ?_
  rw [Set.mulSupport_mulIndicator]
  exact Set.inter_subset_right

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem charpoly_conj {w : Pl E} (y g : UL n w) : (g⁻¹ * y * g).1.val.charpoly = y.1.val.charpoly := by
  simpa using Matrix.charpoly_units_conj' g.1 y.1.val

theorem charpoly_conj' (y g : UE E n) : (g⁻¹ * y * g).1.val.charpoly = y.1.val.charpoly := by
  simpa using Matrix.charpoly_units_conj' g.1 y.1.val

theorem charpoly_cls {w : Pl E} (y : UL n w) : (cls y).rep.1.val.charpoly = y.1.val.charpoly := by
  obtain ⟨g, hg⟩ := rep_cls y
  rw [hg, charpoly_conj]

theorem charpoly_locPt (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1.val.charpoly = atPl w γ.1.val.charpoly := by
  rw [(GlobalTheory.T.local_points_integral_almost_all E hU n γ).1 w]
  exact Matrix.charpoly_map _ _

theorem locPt_conj (hU : Unr E) (w : Pl E) (γ g : UE E n) :
    locPt w (g⁻¹ * γ * g) = (locPt w g)⁻¹ * locPt w γ * locPt w g := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, (GlobalTheory.T.local_points_integral_almost_all E hU n _).1 w, map_mul, map_inv]

theorem atPl_separable {P : E[X]} (hP : P ∈ Ell E n) (w : Pl E) : (atPl w P).Separable := hP.2.2.1.map

theorem csr_one (w : Pl E) : IsCsr w (1 : (w.adicCompletion E)[X]) := by
  by_cases h : IsSplitAt w
  · exact Or.inl h
  · exact Or.inr (by simp [Polynomial.reverse])

theorem kapSign_conj (hU : Unr E) (hn : 1 ≤ n) {w : Pl E} (Q : (w.adicCompletion E)[X]) (y g : UL n w)
    (hy : y.1.val.charpoly.Separable) : kapSign n w Q (g⁻¹ * y * g).1 = kapSign n w Q y.1 :=
  (GlobalTheory.T.kappa_sign_multiplicative E hU n hn w 1 1 Q y g hy (by simp) isCoprime_one_left (csr_one w) (csr_one w)).2.1

abbrev LocCl (n : ℕ) (P : E[X]) (w : Pl E) : Type :=
  {c : TwCl (MonoidHom.id (UL n w)) // c.rep.1.val.charpoly = atPl w P}

def Good {P : E[X]} (w : Pl E) (c : LocCl n P w) : Prop := ∃ g : UL n w, g⁻¹ * c.1.rep * g ∈ KL n w

theorem ae_good (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    {f : ∀ w : Pl E, UL n w → ℂ} (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), (∃! c : LocCl n P w, Good w c) ∧ ∀ c : LocCl n P w,
      (twOrb (MonoidHom.id _) (KL n w) c.1.rep (f w) = if Good w c then 1 else 0) ∧
      (Good w c → ∀ Q : E[X], Q ∣ P → kapSign n w (atPl w Q) c.1.rep.1 = 1) := by
  filter_upwards [hf, GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass E hU n hn S hS P hP, (GlobalTheory.T.elliptic_charpoly_local_realisation E hU n P hP).1, GlobalTheory.T.integral_conjugacy_almost_all E hU n P hP]
    with w h1 h2 h3 h4
  refine ⟨?_, fun c => ⟨?_, fun hc Q hQ => (h2 _ c.2).2.2 _ (Polynomial.map_dvd _ hQ) hc⟩⟩
  · obtain ⟨y, hy, hyP⟩ := h3
    refine ⟨⟨cls y, (charpoly_cls y).trans hyP⟩, ?_, ?_⟩
    · obtain ⟨g, hg⟩ := rep_cls y
      refine ⟨g⁻¹, ?_⟩
      simpa [hg, mul_assoc] using hy
    · rintro c ⟨g, hg⟩
      apply Subtype.ext
      obtain ⟨h, hh⟩ := h4 _ y hg hy ((charpoly_conj _ _).trans c.2) hyP
      show c.1 = cls y
      rw [← cls_rep c.1, cls_eq_iff]
      exact ⟨g * h, by rw [hh]; group⟩
  · rw [h1]
    exact (h2 _ c.2).1

theorem kapOrb_eq (w : Pl E) {P₁ P₂ P : E[X]} (h : P₁ * P₂ = P) (f : UL n w → ℂ) :
    kapOrb n w (atPl w P₁) (atPl w P₂) f =
      ∑ᶠ c : LocCl n P w, kapSign n w (atPl w P₁) c.1.rep.1 * twOrb (MonoidHom.id _) (KL n w) c.1.rep f := by
  rw [finsum_subtype_if (fun c : TwCl (MonoidHom.id (UL n w)) => c.rep.1.val.charpoly = atPl w P)
    (fun c => kapSign n w (atPl w P₁) c.rep.1 * twOrb (MonoidHom.id _) (KL n w) c.rep f)]
  unfold kapOrb clSum
  subst h
  simp only [Set.mem_ofPred_eq, atPl, Polynomial.map_mul]

theorem kapOrb_support (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P₁ P₂ : E[X]}
    (hP : P₁ * P₂ ∈ Ell E n) {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (h : ∏ᶠ w ∈ S, kapOrb n w (atPl w P₁) (atPl w P₂) (f w) ≠ 0) :
    ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w (P₁ * P₂) := by
  intro w hw
  have h1 : ∀ᶠ w in cofinite, kapOrb n w (atPl w P₁) (atPl w P₂) (f w) = 1 := by
    filter_upwards [ae_good hU hn hS hP hf] with w hw
    obtain ⟨⟨c, hc, hc'⟩, h2⟩ := hw
    rw [kapOrb_eq w rfl, finsum_eq_single _ c]
    · rw [(h2 c).1, if_pos hc, (h2 c).2 hc _ (dvd_mul_right _ _), mul_one]
    · intro x hx
      rw [(h2 x).1, if_neg fun hg => hx (hc' x hg), mul_zero]
  have h2 := ne_zero_of_finprod h1 h w hw
  rw [kapOrb_eq w rfl] at h2
  obtain ⟨c, hc⟩ : ∃ c : LocCl n (P₁ * P₂) w, twOrb (MonoidHom.id _) (KL n w) c.1.rep (f w) ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h2
  obtain ⟨g, hg⟩ := exists_ne_zero_of_twOrb _ _ _ hc
  exact ⟨_, hg, (charpoly_conj _ _).trans c.2⟩

theorem orb_support (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {γ : UE E n}
    (hP : γ.1.val.charpoly ∈ Ell E n) {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (h : ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) ≠ 0) :
    ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w γ.1.val.charpoly := by
  intro w hw
  have h1 : ∀ᶠ w in cofinite, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w) = 1 := by
    filter_upwards [hf, GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass E hU n hn S hS _ hP, (GlobalTheory.T.local_points_integral_almost_all E hU n γ).2.1] with w h1 h2 h3
    rw [h1, (h2 _ (charpoly_locPt hU w γ)).1, if_pos ⟨1, by simpa using h3⟩]
  obtain ⟨g, hg⟩ := exists_ne_zero_of_twOrb _ _ _ (ne_zero_of_finprod h1 h w hw)
  exact ⟨_, hg, (charpoly_conj _ _).trans (charpoly_locPt hU w γ)⟩

theorem ell_of_dvd {P Q : E[X]} (hP : P ∈ Ell E n) (hQ : Q.Monic) (hQP : Q ∣ P) : Q ∈ Ell E Q.natDegree := by
  refine ⟨hQ, rfl, hP.2.2.1.of_dvd hQP, fun τ z hz => hP.2.2.2 τ z ?_⟩
  have h0 : P.map τ ≠ 0 := (hP.1.map τ).ne_zero
  exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd h0 (Polynomial.map_dvd τ hQP)) hz

theorem csr_at (hU : Unr E) {P Q : E[X]} (hP : P ∈ Ell E n) (hQ : Q.Monic) (hQP : Q ∣ P) (w : Pl E) :
    IsCsr w (atPl w Q) := by
  by_cases hs : IsSplitAt w
  · exact Or.inl hs
  right
  have hg := (GlobalTheory.T.elliptic_charpoly_self_reciprocal E Q.natDegree Q (ell_of_dvd hP hQ hQP)).2
  have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
  have hcomp : (algebraMap E (w.adicCompletion E)).comp (IsCMField.complexConj E).toRingEquiv.toRingHom =
      (cj w).comp (algebraMap E (w.adicCompletion E)) := by
    exact RingHom.ext fun x => (hc x).symm
  have h1 := congrArg (Polynomial.map (algebraMap E (w.adicCompletion E))) hg
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.reverse, ← Polynomial.reflect_map, Polynomial.map_map, hcomp,
    ← Polynomial.map_map] at h1
  have hd1 : (Q.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = ((atPl w Q).map (cj w)).natDegree := by
    rw [(hQ.map _).natDegree_map, hQ.natDegree_map, hQ.natDegree_map]
  rw [hd1] at h1
  rw [Polynomial.reverse, ← h1, atPl, Polynomial.coeff_map]
  congr 2
  exact hc _

theorem cls_conj {G : Type} [Group G] (x g : G) : cls (g⁻¹ * x * g) = cls x :=
  ((cls_eq_iff _ _).2 ⟨g⁻¹, by group⟩)

theorem isSplit_of_not_mem {S : Set (Pl E)} (hS : IsSection S) {w : Pl E} (hw : w ∉ S) : IsSplitAt w := by
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
  exact ⟨u, fun h => hw (h ▸ hu), hu'⟩

abbrev Fac (P : E[X]) : Type := {p : E[X] × E[X] // p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P}

theorem sign_mul (hU : Unr E) (hn : 1 ≤ n) {P Q₁ Q₂ : E[X]} (hP : P ∈ Ell E n) (h1 : Q₁.Monic) (h2 : Q₂.Monic)
    (h12 : Q₁ * Q₂ ∣ P) (hc : IsCoprime Q₁ Q₂) (w : Pl E) (γ : UL n w) (hγ : γ.1.val.charpoly = atPl w P) :
    kapSign n w (atPl w (Q₁ * Q₂)) γ.1 = kapSign n w (atPl w Q₁) γ.1 * kapSign n w (atPl w Q₂) γ.1 := by
  have d1 : Q₁ ∣ P := dvd_trans (dvd_mul_right _ _) h12
  have d2 : Q₂ ∣ P := dvd_trans (dvd_mul_left _ _) h12
  have hcw : IsCoprime (atPl w Q₁) (atPl w Q₂) := by
    have := hc.map (Polynomial.mapRingHom (algebraMap E (w.adicCompletion E)))
    simpa only [Polynomial.coe_mapRingHom] using this
  have hd : atPl w Q₁ * atPl w Q₂ ∣ γ.1.val.charpoly := by
    rw [hγ, atPl, atPl, atPl, ← Polynomial.map_mul]
    exact Polynomial.map_dvd _ h12
  have hs : γ.1.val.charpoly.Separable := by
    rw [hγ]
    exact atPl_separable hP w
  have key := (GlobalTheory.T.kappa_sign_multiplicative E hU n hn w (atPl w Q₁) (atPl w Q₂) 1 γ 1 hs hd hcw (csr_at hU hP h1 d1 w)
    (csr_at hU hP h2 d2 w)).1
  have e : atPl w (Q₁ * Q₂) = atPl w Q₁ * atPl w Q₂ := Polynomial.map_mul _
  rw [e]
  exact key

def locCl (hU : Unr E) {P : E[X]} (r : {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P}) (w : Pl E) :
    LocCl n P w :=
  ⟨cls (locPt w r.1.rep), (charpoly_cls _).trans ((charpoly_locPt hU w _).trans (by rw [r.2]))⟩

set_option maxHeartbeats 800000 in
theorem signs (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    (hgs : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ c : LocCl n P w, Good w c → ∀ Q : E[X], Q ∣ P →
      kapSign n w (atPl w Q) c.1.rep.1 = 1)
    (x : ∀ w, LocCl n P w) (hx : ∀ᶠ w in (cofinite : Filter (Pl E)), Good w (x w)) :
    ∑ᶠ d : Fac P, ∏ᶠ w ∈ S, kapSign n w (atPl w d.1.1) (x w).1.rep.1 =
      if ∃ r, ∀ w ∈ S, locCl hU r w = x w then 2 ^ nfac P else 0 := by
  have hsep : ∀ w : Pl E, (atPl w P).Separable := atPl_separable hP
  let σ : E[X] → ℂ := fun Q => ∏ᶠ w ∈ S, kapSign n w (atPl w Q) (x w).1.rep.1
  have hsepx : ∀ w, (x w).1.rep.1.val.charpoly.Separable := fun w => by rw [(x w).2]; exact hsep w
  have hmfin : ∀ Q : E[X], Q ∣ P → (S ∩ Function.mulSupport fun w => kapSign n w (atPl w Q) (x w).1.rep.1).Finite := by
    intro Q hQ
    have h : ∀ᶠ w in (cofinite : Filter (Pl E)), kapSign n w (atPl w Q) (x w).1.rep.1 = 1 := by
      filter_upwards [hx, hgs] with w h1 h2
      exact h2 (x w) h1 Q hQ
    exact (Filter.eventually_cofinite.1 h).subset Set.inter_subset_right
  have hmul : ∀ Q₁ Q₂ : E[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → σ (Q₁ * Q₂) = σ Q₁ * σ Q₂ := by
    intro Q₁ Q₂ h1 h2 h12 hc
    have d1 : Q₁ ∣ P := dvd_trans (dvd_mul_right _ _) h12
    have d2 : Q₂ ∣ P := dvd_trans (dvd_mul_left _ _) h12
    show ∏ᶠ w ∈ S, _ = (∏ᶠ w ∈ S, _) * ∏ᶠ w ∈ S, _
    rw [← finprod_mem_mul_distrib' (hmfin Q₁ d1) (hmfin Q₂ d2)]
    refine finprod_mem_congr rfl fun w _ => ?_
    exact sign_mul hU hn hP h1 h2 h12 hc w _ (x w).2
  have hpm : ∀ Q : E[X], Q.Monic → Q ∣ P → σ Q = 1 ∨ σ Q = -1 := by
    intro Q _ _
    refine finprod_mem_induction (fun z : ℂ => z = 1 ∨ z = -1) (Or.inl rfl) ?_ ?_
    · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
    · intro w _
      exact (GlobalTheory.T.kappa_sign_multiplicative E hU n hn w 1 1 (atPl w Q) (x w).1.rep 1 (hsepx w) (by simp) isCoprime_one_left
        (csr_one w) (csr_one w)).2.2
  have hdiv := (GlobalTheory.T.monic_divisor_sign_sum E P hP.1 hP.2.2.1 σ hmul hpm).2
  have hbij : Function.Bijective (fun d : Fac P => (⟨d.1.1, d.2.1, ⟨d.1.2, d.2.2.2.symm⟩⟩ :
      {Q : E[X] // Q.Monic ∧ Q ∣ P})) := by
    refine ⟨fun d d' h => ?_, fun Q => ?_⟩
    · have h1 : d.1.1 = d'.1.1 := congrArg Subtype.val h
      have h2 : d.1.2 = d'.1.2 := by
        have e := d.2.2.2.trans d'.2.2.2.symm
        rw [h1] at e
        exact mul_left_cancel₀ (d'.2.1.ne_zero) e
      exact Subtype.ext (Prod.ext h1 h2)
    · obtain ⟨R, hR⟩ := Q.2.2
      exact ⟨⟨(Q.1, R), Q.2.1, Q.2.1.of_mul_monic_left (hR ▸ hP.1), hR.symm⟩, rfl⟩
  have hsum : ∑ᶠ d : Fac P, ∏ᶠ w ∈ S, kapSign n w (atPl w d.1.1) (x w).1.rep.1 =
      ∑ᶠ Q : {Q : E[X] // Q.Monic ∧ Q ∣ P}, σ Q.1 :=
    finsum_comp_equiv (Equiv.ofBijective _ hbij) (f := fun Q : {Q : E[X] // Q.Monic ∧ Q ∣ P} => σ Q.1)
  have key : (∀ Q : E[X], Q.Monic → Q ∣ P → σ Q = 1) ↔ ∃ r, ∀ w ∈ S, locCl hU r w = x w := by
    constructor
    · intro hall
      let y : ∀ w, UL n w := fun w =>
        if h : Good w (x w) then h.choose⁻¹ * (x w).1.rep * h.choose else (x w).1.rep
      have hy1 : ∀ w, ∃ g, y w = g⁻¹ * (x w).1.rep * g := by
        intro w
        by_cases h : Good w (x w)
        · exact ⟨_, dif_pos h⟩
        · exact ⟨1, by rw [show y w = (x w).1.rep from dif_neg h]; group⟩
      have hyP : ∀ w, (y w).1.val.charpoly = atPl w P := by
        intro w
        obtain ⟨g, hg⟩ := hy1 w
        rw [hg, charpoly_conj, (x w).2]
      have hyK : ∀ᶠ w in (cofinite : Filter (Pl E)), y w ∈ KL n w := by
        filter_upwards [hx] with w h
        rw [show y w = _ from dif_pos h]
        exact h.choose_spec
      have hyS : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1 := by
        intro P₁ h1 h2
        rw [← hall P₁ h1 h2]
        refine finprod_mem_congr rfl fun w _ => ?_
        obtain ⟨g, hg⟩ := hy1 w
        rw [hg]
        exact kapSign_conj hU hn _ _ _ (hsepx w)
      obtain ⟨γ, hγP, hγ⟩ := (GlobalTheory.T.unitary_conjugacy_sign_product E hU n hn S hS P hP).2.2 y hyP hyK hyS
      obtain ⟨h, hh⟩ := rep_cls γ
      refine ⟨⟨cls γ, by rw [hh, charpoly_conj', hγP]⟩, fun w hw => ?_⟩
      apply Subtype.ext
      show cls (locPt w (cls γ).rep) = (x w).1
      obtain ⟨g, hg⟩ := hγ w hw
      obtain ⟨k, hk⟩ := hy1 w
      rw [hh, locPt_conj hU, cls_conj, hg, cls_conj, hk, cls_conj, cls_rep]
    · rintro ⟨r, hr⟩ Q hQ hQP
      rw [← (GlobalTheory.T.unitary_conjugacy_sign_product E hU n hn S hS P hP).2.1 r.1.rep r.2 Q hQ hQP]
      refine finprod_mem_congr rfl fun w hw => ?_
      have e : (x w).1 = cls (locPt w r.1.rep) := (congrArg Subtype.val (hr w hw)).symm
      obtain ⟨g, hg⟩ := rep_cls (locPt w r.1.rep)
      have hs' : (locPt w r.1.rep).1.val.charpoly.Separable := by
        rw [charpoly_locPt hU, r.2]
        exact hsep w
      rw [e, hg]
      exact kapSign_conj hU hn _ _ _ hs'
  rw [hsum, hdiv]
  by_cases h : ∀ Q : E[X], Q.Monic → Q ∣ P → σ Q = 1
  · rw [if_pos h, if_pos (key.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (key.2 h'))]

set_option maxHeartbeats 800000 in
theorem fixedP (hU : Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (hK' : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K')
    {f : ∀ w : Pl E, UL n w → ℂ} (hf : IsTest (KL n) K' f) :
    (Function.support fun c : TwCl (MonoidHom.id (UE E n)) => if c.rep.1.val.charpoly = P then
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w c.rep) (f w) else 0).Finite ∧
    (∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly = P then
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w c.rep) (f w) else 0) * 2 ^ nfac P =
    ∑ᶠ p : E[X] × E[X], if p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P then
      ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) else 0 := by
  have hsep : ∀ w : Pl E, (atPl w P).Separable := atPl_separable hP
  haveI : ∀ w, Finite (LocCl n P w) := fun w =>
    ((GlobalTheory.T.finite_twisted_classes_charpoly E hU n w (atPl w P) (hsep w)).2).to_subtype
  have hdivs := (GlobalTheory.T.monic_divisor_sign_sum E P hP.1 hP.2.2.1 (fun _ => 1) (fun _ _ _ _ _ _ => by simp) (fun _ _ _ => Or.inl rfl)).1
  have hP0 : P ≠ 0 := hP.1.ne_zero
  haveI : Finite (Fac P) := by
    haveI := hdivs.to_subtype
    refine Finite.of_injective (fun d : Fac P => (⟨d.1.1, d.2.1, ⟨d.1.2, d.2.2.2.symm⟩⟩ :
      {Q : E[X] | Q.Monic ∧ Q ∣ P})) fun d d' h => ?_
    have h1 : d.1.1 = d'.1.1 := congrArg Subtype.val h
    have h2 : d.1.2 = d'.1.2 := by
      have e := d.2.2.2.trans d'.2.2.2.symm
      rw [h1] at e
      exact mul_left_cancel₀ (d'.2.1.ne_zero) e
    exact Subtype.ext (Prod.ext h1 h2)
  have hKc : ∀ w, IsCompact (KL n w : Set (UL n w)) := fun w => (GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w).2.2.2.2.2.2.2.1
  have hgood := ae_good hU hn hS hP hf.2
  have E1 := GlobalTheory.T.adelic_class_count_product (Pl E) S (LocCl n P) (Fac P) {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P}
    (locCl hU) (fun w c => twOrb (MonoidHom.id _) (KL n w) c.1.rep (f w))
    (fun d w c => kapSign n w (atPl w d.1.1) c.1.rep.1) (fun w c => Good w c) (2 ^ nfac P) ?h1 ?h2 ?h3 ?h4 ?h5
  case h1 =>
    filter_upwards [hgood] with w hw
    exact ⟨hw.1, fun c => ⟨(hw.2 c).1, fun hc d => (hw.2 c).2 hc _ ⟨d.1.2, d.2.2.2.symm⟩⟩⟩
  case h2 =>
    intro w hw
    obtain ⟨y, hy⟩ := (GlobalTheory.T.elliptic_charpoly_local_realisation E hU n P hP).2 w (isSplit_of_not_mem hS hw)
    exact ⟨⟨cls y, (charpoly_cls y).trans hy⟩⟩
  case h3 =>
    intro r
    filter_upwards [(GlobalTheory.T.local_points_integral_almost_all E hU n r.1.rep).2.1] with w hw
    obtain ⟨g, hg⟩ := rep_cls (locPt w r.1.rep)
    refine ⟨g⁻¹, ?_⟩
    show g⁻¹⁻¹ * (cls (locPt w r.1.rep)).rep * g⁻¹ ∈ KL n w
    rw [hg]
    simpa [mul_assoc] using hw
  case h4 =>
    intro r r' h
    have := (GlobalTheory.T.unitary_conjugacy_sign_product E hU n hn S hS P hP).1 r.1.rep r'.1.rep r.2 r'.2 fun w hw => by
      have e := congrArg Subtype.val (h w hw)
      exact (cls_eq_iff _ _).1 e
    obtain ⟨g, hg⟩ := this
    apply Subtype.ext
    rw [← cls_rep r.1, ← cls_rep r'.1]
    exact (cls_eq_iff _ _).2 ⟨g, hg⟩
  case h5 =>
    intro x hx
    exact signs hU hn hS hP (by filter_upwards [hgood] with w hw; exact fun c hc => (hw.2 c).2 hc) x hx
  obtain ⟨Efin, Eeq⟩ := E1
  have hO : ∀ r : {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P},
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locCl hU r w).1.rep (f w) =
      ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w r.1.rep) (f w) := by
    intro r
    refine finprod_mem_congr rfl fun w _ => ?_
    obtain ⟨g, hg⟩ := rep_cls (locPt w r.1.rep)
    show twOrb _ _ (cls (locPt w r.1.rep)).rep _ = _
    rw [hg, twOrb_conj (hKc w) (hK'.1 w) (hf.1 w)]
  simp only [hO] at Efin Eeq
  have hR : ∀ u : TwCl (MonoidHom.id (UE E n)) → ℂ,
      ∑ᶠ r : {c : TwCl (MonoidHom.id (UE E n)) // c.rep.1.val.charpoly = P}, u r.1 =
      ∑ᶠ c, if c.rep.1.val.charpoly = P then u c else 0 := fun u => finsum_subtype_if _ u
  refine ⟨?_, ?_⟩
  · refine (Efin.image Subtype.val).subset fun c hc => ?_
    by_cases h : c.rep.1.val.charpoly = P
    · refine ⟨⟨c, h⟩, ?_, rfl⟩
      simpa [h] using hc
    · exact absurd (by simp [h]) hc
  · rw [← hR (fun c => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w c.rep) (f w)), Eeq]
    rw [← finsum_subtype_if (fun p : E[X] × E[X] => p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P)]
    refine finsum_congr fun d => finprod_mem_congr rfl fun w _ => ?_
    rw [kapOrb_eq w d.2.2.2]

theorem coprime_of_sep {k : Type} [Field k] {p q : k[X]} (h : (p * q).Separable) : IsCoprime p q := by
  refine isCoprime_of_dvd _ _ ?_ fun z hz _ hzp hzq => ?_
  · rintro ⟨rfl, -⟩
    rw [zero_mul] at h
    exact Polynomial.not_separable_zero h
  · exact (mem_nonunits_iff.1 hz) (h.squarefree z (mul_dvd_mul hzp hzq))

theorem fac_finite {P : E[X]} (hP : P ∈ Ell E n) :
    {p : E[X] × E[X] | p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P}.Finite := by
  have hdivs := (GlobalTheory.T.monic_divisor_sign_sum E P hP.1 hP.2.2.1 (fun _ => 1) (fun _ _ _ _ _ _ => by simp) (fun _ _ _ => Or.inl rfl)).1
  refine (hdivs.image fun Q => (Q, P /ₘ Q)).subset fun p hp => ⟨p.1, ⟨hp.1, ⟨p.2, hp.2.2.symm⟩⟩, ?_⟩
  refine Prod.ext rfl ?_
  show P /ₘ p.1 = p.2
  rw [← hp.2.2]
  exact Polynomial.mul_divByMonic_cancel_left _ hp.1

theorem geomURat_eq_geomU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)),
    IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f →
    (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
    geomURat lam (fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) = geomU S lam f := by
  intro E _ _ _ hU n hn S hS lam K' hK' f hf _
  have hFin := GlobalTheory.T.finite_elliptic_charpolys_support E hU n S hS f (fun w => (hf.1 w).1) hf.2
  let F := hFin.toFinset
  have hmemF : ∀ P, P ∈ F ↔ P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P :=
    fun P => hFin.mem_toFinset
  let orb : UE E n → ℂ := fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)

  have hL : geomURat lam orb = ∑ P ∈ F, kap P * chW lam P *
      ((∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly = P then orb c.rep else 0) * 2 ^ nfac P) := by
    have hterm : ∀ c : TwCl (MonoidHom.id (UE E n)), (if c.rep.1.val.charpoly.Separable then
        mass (MonoidHom.id _) (ratFinU E n) (finPt c.rep) * chW lam c.rep.1.val.charpoly * orb c.rep else 0) =
        if c.rep.1.val.charpoly ∈ Ell E n then kap c.rep.1.val.charpoly * 2 ^ nfac c.rep.1.val.charpoly *
          chW lam c.rep.1.val.charpoly * orb c.rep else 0 := by
      intro c
      by_cases h : c.rep.1.val.charpoly.Separable
      · have he := (GlobalTheory.T.local_points_integral_almost_all E hU n c.rep).2.2 h
        rw [if_pos h, if_pos he, GlobalTheory.T.unitary_mass_formula E hU n hn c.rep he]
      · rw [if_neg h, if_neg fun h' => h h'.2.2.1]
    have hsupp : ∀ c : TwCl (MonoidHom.id (UE E n)), (if c.rep.1.val.charpoly ∈ Ell E n then
        kap c.rep.1.val.charpoly * 2 ^ nfac c.rep.1.val.charpoly * chW lam c.rep.1.val.charpoly * orb c.rep else 0) ≠ 0 →
        c.rep.1.val.charpoly ∈ F ∧ orb c.rep ≠ 0 := by
      intro c hc
      by_cases h : c.rep.1.val.charpoly ∈ Ell E n
      · rw [if_pos h] at hc
        have ho : orb c.rep ≠ 0 := right_ne_zero_of_mul hc
        exact ⟨(hmemF _).2 ⟨h, orb_support hU hn hS h hf.2 ho⟩, ho⟩
      · rw [if_neg h] at hc
        exact absurd rfl hc
    unfold geomURat
    rw [finsum_congr hterm, finsum_fibres _ (fun c => c.rep.1.val.charpoly) F ?_ fun c hc => (hsupp c hc).1]
    · refine Finset.sum_congr rfl fun P hP => ?_
      have hPE : P ∈ Ell E n := ((hmemF P).1 hP).1
      rw [mul_comm _ ((2 : ℂ) ^ nfac P), ← mul_assoc, mul_finsum]
      refine finsum_congr fun c => ?_
      by_cases h : c.rep.1.val.charpoly = P
      · rw [if_pos h, if_pos h, h, if_pos hPE]
        ring
      · rw [if_neg h, if_neg h, mul_zero]
    · refine ((F.finite_toSet.biUnion fun P hP => (fixedP hU hn hS ((hmemF P).1 hP).1 hK' hf).1)).subset fun c hc => ?_
      obtain ⟨h1, h2⟩ := hsupp c hc
      exact Set.mem_biUnion h1 (by simp only [Function.mem_support, if_pos rfl]; exact h2)

  let A : Set (E[X] × E[X]) := {p | p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 ∈ Ell E n}
  let V : E[X] × E[X] → ℂ := fun p => if p ∈ A then kap (p.1 * p.2) * chW lam (p.1 * p.2) *
    ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) else 0
  have hVs : ∀ p, V p ≠ 0 → p.1 * p.2 ∈ F ∧ p ∈ A := by
    intro p hp
    by_cases h : p ∈ A
    · have hp' : kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) ≠ 0 := by
        simpa only [V, if_pos h] using hp
      exact ⟨(hmemF _).2 ⟨h.2.2, kapOrb_support hU hn hS h.2.2 hf.2 (right_ne_zero_of_mul hp')⟩, h⟩
    · exact absurd (by simp only [V, if_neg h]) hp
  have hVfin : (Function.support V).Finite := by
    refine (F.finite_toSet.biUnion fun P hP => fac_finite ((hmemF P).1 hP).1).subset fun p hp => ?_
    obtain ⟨h1, h2⟩ := hVs p hp
    exact Set.mem_biUnion h1 ⟨h2.1, h2.2.1, rfl⟩
  have hA : ∀ a ∈ Finset.range (n + 1), ∀ p : E[X] × E[X],
      p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2} ↔ p ∈ A ∧ p.1.natDegree = a := by
    intro a ha p
    have han : a ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
    constructor
    · rintro ⟨h1, h2, hc⟩
      have := (GlobalTheory.T.kappaConstant_mul_of_coprime_ellipticPolynomials E hU a (n - a) p.1 p.2 h1 h2 hc).2.2
      rw [Nat.add_sub_cancel' han] at this
      exact ⟨⟨h1.1, h2.1, this⟩, h1.2.1⟩
    · rintro ⟨⟨m1, m2, he⟩, hd⟩
      have hdeg : p.1.natDegree + p.2.natDegree = n := by
        rw [← he.2.1, Polynomial.natDegree_mul m1.ne_zero m2.ne_zero]
      have e1 := ell_of_dvd he m1 (dvd_mul_right _ _)
      have e2 := ell_of_dvd he m2 (dvd_mul_left _ _)
      rw [hd] at e1
      rw [show p.2.natDegree = n - a by omega] at e2
      exact ⟨e1, e2, coprime_of_sep he.2.2.1⟩
  have hR : geomU S lam f = ∑ P ∈ F, kap P * chW lam P * ∑ᶠ p : E[X] × E[X],
      if p.1.Monic ∧ p.2.Monic ∧ p.1 * p.2 = P then ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) else 0 := by
    unfold geomU
    have h1 : ∀ a ∈ Finset.range (n + 1),
        (∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2},
          kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)) =
        ∑ᶠ p : E[X] × E[X], if p.1.natDegree = a then V p else 0 := by
      intro a ha
      rw [finsum_mem_def]
      refine finsum_congr fun p => ?_
      rw [Set.indicator_apply]
      by_cases h : p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2}
      · obtain ⟨hpA, hd⟩ := (hA a ha p).1 h
        rw [if_pos h, if_pos hd]
        simp only [V, if_pos hpA]
      · rw [if_neg h]
        by_cases hd : p.1.natDegree = a
        · rw [if_pos hd]
          have hpA : p ∉ A := fun hpA => h ((hA a ha p).2 ⟨hpA, hd⟩)
          simp only [V, if_neg hpA]
        · rw [if_neg hd]
    rw [Finset.sum_congr rfl h1, ← finsum_sum_comm]
    · have h2 : ∀ p : E[X] × E[X], ∑ a ∈ Finset.range (n + 1), (if p.1.natDegree = a then V p else 0) = V p := by
        intro p
        rw [Finset.sum_ite_eq]
        split_ifs with h
        · rfl
        · by_contra hV
          obtain ⟨-, hpA⟩ := hVs p (Ne.symm hV)
          apply h
          have hdeg : p.1.natDegree + p.2.natDegree = n := by
            rw [← hpA.2.2.2.1, Polynomial.natDegree_mul hpA.1.ne_zero hpA.2.1.ne_zero]
          exact Finset.mem_range.2 (by omega)
      rw [finsum_congr h2, finsum_fibres V (fun p => p.1 * p.2) F hVfin fun p hp => (hVs p hp).1]
      refine Finset.sum_congr rfl fun P hP => ?_
      have hPE : P ∈ Ell E n := ((hmemF P).1 hP).1
      rw [mul_finsum]
      refine finsum_congr fun p => ?_
      by_cases h : p.1 * p.2 = P
      · by_cases hm : p.1.Monic ∧ p.2.Monic
        · have hpA : p ∈ A := ⟨hm.1, hm.2, h ▸ hPE⟩
          rw [if_pos h, if_pos ⟨hm.1, hm.2, h⟩]
          simp only [V, if_pos hpA, h]
        · have hpA : p ∉ A := fun hpA => hm ⟨hpA.1, hpA.2.1⟩
          rw [if_pos h, if_neg fun h' => hm ⟨h'.1, h'.2.1⟩, mul_zero]
          simp only [V, if_neg hpA]
      · rw [if_neg h, if_neg fun h' => h h'.2.2, mul_zero]
    · intro a _
      refine hVfin.subset fun p hp => ?_
      by_contra h0
      apply hp
      simp only [Function.mem_support, not_not] at h0
      simp [h0]
  rw [hR]
  show geomURat lam orb = _
  rw [hL]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [(fixedP hU hn hS ((hmemF P).1 hP).1 hK' hf).2]

end GlobalTheory.PreStabU
