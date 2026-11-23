import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSphericalUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassCountCharPolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRestrictedProductCountStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FibStable

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun x => ⟨1, by simp⟩, fun ⟨g, h⟩ => ⟨g⁻¹, by rw [h, map_inv]; group⟩,
    fun ⟨g, h⟩ ⟨k, h'⟩ => ⟨g * k, by rw [h', h, map_mul]; group⟩⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

theorem rep_cls (θ : G →* G) (y : G) : ∃ g, (cls θ y).rep = g⁻¹ * y * θ g :=
  (cls_eq_iff θ _ _).1 (cls_rep θ (cls θ y)).symm

theorem index_ne_zero [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsLevel θ K K') (f : G → ℂ) (hf : IsHecke K' f) (δ x : G) :
    (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  obtain ⟨ho, -, hθ⟩ := hK'
  have h1 : K'.subgroupOf K ≤ rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)) := by
    intro k' hk' k
    rw [Subgroup.mem_subgroupOf] at hk'
    have e : (x * ((k * k' : K) : G))⁻¹ * δ * θ (x * ((k * k' : K) : G)) =
        (k' : G)⁻¹ * ((x * k)⁻¹ * δ * θ (x * k)) * θ k' := by
      simp only [Subgroup.coe_mul, map_mul]; group
    show f _ = f _
    rw [e, (hf.2 _ (hθ _ hk') _).2, (hf.2 _ (K'.inv_mem hk') _).1]
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ho' : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := ho.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho'
  have h2 : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h0
  exact h2 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le h1))

theorem eq_single {D : Type} (B : D → ℂ) (h01 : ∀ d, B d = 0 ∨ B d = 1) (hs : ∑ᶠ d, B d = 1) :
    ∃ u, ∀ d, B d = if d = u then 1 else 0 := by
  have hfin : (Function.support B).Finite := by
    by_contra h
    rw [finsum_of_infinite_support h] at hs
    exact zero_ne_one hs
  rw [finsum_eq_sum _ hfin] at hs
  have hc : hfin.toFinset.card = 1 := by
    have : ∑ d ∈ hfin.toFinset, B d = (hfin.toFinset.card : ℂ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rcases h01 d with h | h
      · exact absurd h hd
      · simp [h]
    rw [this] at hs
    exact_mod_cast hs
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc
  refine ⟨u, fun d => ?_⟩
  split_ifs with h
  · subst h
    have : d ∈ hfin.toFinset := by rw [hu]; exact Finset.mem_singleton_self _
    rw [Set.Finite.mem_toFinset] at this
    rcases h01 d with h' | h'
    · exact absurd h' this
    · exact h'
  · by_contra hne
    have : d ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hne
    rw [hu, Finset.mem_singleton] at this
    exact h this

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def locTerm (n : ℕ) (w : Pl E) (P : E[X]) (φ : GLw n w → ℂ) (d : TwCl (thL n w)) : ℂ :=
  if (nrmL n w d.rep).val.charpoly = atPl w P then twOrb (thL n w) (GlobalTheory.LFun.KGL w n) d.rep φ else 0

theorem charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [nrmL_twConj, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

theorem stTw_eq (n : ℕ) (w : Pl E) (P : E[X]) (φ : GLw n w → ℂ) :
    stTw n w (atPl w P) φ = ∑ᶠ d, locTerm n w P φ d := by
  unfold stTw clSum locTerm
  refine finsum_congr fun d => ?_
  simp only [Set.mem_setOf_eq, Pi.one_apply, one_mul]

theorem locTerm_cls (n : ℕ) (w : Pl E) (P : E[X]) (K' : Subgroup (GLw n w))
    (hK' : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K') (φ : GLw n w → ℂ) (hφ : IsHecke K' φ) (y : GLw n w)
    (hy : (nrmL n w y).val.charpoly = atPl w P) :
    locTerm n w P φ (cls (thL n w) y) = twOrb (thL n w) (GlobalTheory.LFun.KGL w n) y φ := by
  obtain ⟨g, hg⟩ := rep_cls (thL n w) y
  unfold locTerm
  rw [hg, charpoly_twConj, if_pos hy]
  apply GlobalTheory.TwOrbConj.twOrb_twConj
  intro x
  exact index_ne_zero _ _ _ (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2 hK' φ hφ y x

end Local

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (GLw n w), IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' → ∀ φ : ∀ w : Pl E, GLw n w → ℂ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → ∀ P ∈ Ell E n, (∑ᶠ c : TwCl (thE E n), if (c.rep * thE E n c.rep).val.charpoly = P then ∏ᶠ w ∈ S, twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (locEl n w c.rep) (φ w) else 0) * (2 : ℂ) ^ nfac P = (2 : ℂ) ^ (n * Fintype.card (InfinitePlace E)) * ∏ᶠ w ∈ S, stTw n w (atPl w P) (φ w) := by
  intro E _ _ _ hU n S hS K' hK' φ hφ P hP
  obtain ⟨δ₀, hδ₀⟩ := (GlobalTheory.T.kappaConstant_mul_of_coprime_ellipticPolynomials E hU n 0 P 1 hP
    ⟨monic_one, natDegree_one, separable_one, fun τ z hz => by simp at hz⟩ isCoprime_one_right).2.1
  obtain ⟨A, hA⟩ : ∃ A : Set (TwCl (thE E n)), A = {c | (c.rep * thE E n c.rep).val.charpoly = P} := ⟨_, rfl⟩
  have hcA : ∀ c, c ∈ A ↔ (c.rep * thE E n c.rep).val.charpoly = P := fun c => by rw [hA]; rfl
  have hL : (∑ᶠ c : TwCl (thE E n), if (c.rep * thE E n c.rep).val.charpoly = P then
      ∏ᶠ w ∈ S, twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (locEl n w c.rep) (φ w) else 0) =
      ∑ᶠ c : TwCl (thE E n), if c ∈ A then
      ∏ᶠ w ∈ S, locTerm n w P (φ w) (cls (thL n w) (locEl n w c.rep)) else 0 := by
    refine finsum_congr fun c => ?_
    by_cases hc : (c.rep * thE E n c.rep).val.charpoly = P
    · rw [if_pos hc, if_pos ((hcA c).2 hc)]
      exact finprod_mem_congr rfl fun w _ => (locTerm_cls n w P (K' w) (hK'.1 w) (φ w) (hφ.1 w) _
        (by rw [ThBasic.charpoly_nrmL hU, hc])).symm
    · rw [if_neg hc, if_neg (fun h => hc ((hcA c).1 h))]
  have hR : ∏ᶠ w ∈ S, stTw n w (atPl w P) (φ w) = ∏ᶠ w ∈ S, ∑ᶠ d, locTerm n w P (φ w) d :=
    finprod_mem_congr rfl fun w _ => stTw_eq n w P (φ w)
  rw [hL, hR]
  refine GlobalTheory.T.finsum_restricted_product_count (Pl E) (TwCl (thE E n)) (fun w => TwCl (thL n w)) S (fun w => locTerm n w P (φ w))
    (fun c w => cls (thL n w) (locEl n w c.rep)) A
    (nfac P) (n * Fintype.card (InfinitePlace E)) (fun w => ⟨cls _ 1⟩) ?_ ?_ ?_ ?_
  · intro w _
    refine (GlobalTheory.BCT.ClsFin.classes_finite E hU n w (atPl w P) hP.2.2.1.map).1.subset fun d hd => ?_
    by_contra h
    exact Function.mem_support.1 hd (by unfold locTerm; exact if_neg h)
  · filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GlobalTheory.T.stable_twisted_orbital_unit_almost_all E hU n P hP] with w h1 h2 h3
    refine eq_single _ (fun d => ?_) ?_
    · try dsimp only
      unfold locTerm
      rw [h2]
      split_ifs with h
      · rw [h1 _ h]; split_ifs <;> simp
      · exact Or.inl rfl
    · try dsimp only
      rw [← stTw_eq, h2]
      exact h3
  · intro c hc
    rw [hcA] at hc
    filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GoodInt.eventually_mem_KGL c.rep,
      GoodInt.eventually_mem_KGL (c.rep * thE E n c.rep)] with w h1 h2 h3 h4
    have hy : (nrmL n w (locEl n w c.rep)).val.charpoly = atPl w P := by rw [ThBasic.charpoly_nrmL hU, hc]
    have hK : locEl n w c.rep ∈ GlobalTheory.LFun.KGL w n := by
      unfold locEl
      split_ifs
      exacts [h4, h3]
    try dsimp only
    rw [locTerm_cls n w P (K' w) (hK'.1 w) (φ w) (hφ.1 w) _ hy, h2, h1 _ hy, if_pos ⟨1, by simpa using hK⟩]
  · intro e he
    try dsimp only at he
    have hpoly : ∀ w ∈ S, (nrmL n w (e w).rep).val.charpoly = atPl w P := fun w hw => by
      by_contra h
      exact he w hw (by unfold locTerm; exact if_neg h)
    obtain ⟨y, hyS, hy1, hy2⟩ : ∃ y : ∀ w, GLw n w, (∀ w ∈ S, cls (thL n w) (y w) = e w) ∧
        (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) ∧ ∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n := by
      refine ⟨fun w => if w ∈ S then (if h : ∃ g : GLw n w, g⁻¹ * (e w).rep * thL n w g ∈ GlobalTheory.LFun.KGL w n then
          h.choose⁻¹ * (e w).rep * thL n w h.choose else (e w).rep) else locEl n w δ₀, fun w hw => ?_, fun w => ?_, ?_⟩
      · try dsimp only
        rw [if_pos hw]
        split_ifs with h
        · rw [← (cls_eq_iff (thL n w) (e w).rep _).2 ⟨h.choose, rfl⟩, cls_rep]
        · exact cls_rep _ _
      · try dsimp only
        split_ifs with hw h
        · rw [charpoly_twConj]; exact hpoly w hw
        · exact hpoly w hw
        · rw [ThBasic.charpoly_nrmL hU, hδ₀]
      · filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GoodInt.eventually_mem_KGL δ₀,
          GoodInt.eventually_mem_KGL (δ₀ * thE E n δ₀)] with w h1 h2 h3 h4
        try dsimp only
        split_ifs with hw h
        · exact h.choose_spec
        · exfalso
          have hne := he w hw
          unfold locTerm at hne
          rw [if_pos (hpoly w hw), h2, h1 _ (hpoly w hw), if_neg h] at hne
          exact hne rfl
        · unfold locEl
          split_ifs
          exacts [h4, h3]
    have hc := GlobalTheory.T.twisted_class_count_char_poly E hU n S hS P hP y hy1 hy2
    convert hc using 2
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => and_congr (hcA c) (forall₂_congr fun w hw => ?_))
    try dsimp only
    rw [← hyS w hw, eq_comm, cls_eq_iff]

end GlobalTheory.BCT.FibStable
