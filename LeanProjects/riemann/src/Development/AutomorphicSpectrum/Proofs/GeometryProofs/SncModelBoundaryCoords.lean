import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSncModelOfPatchesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.Seg

open MvPolynomial GlobalTheory.CompanionTheory.Ar.SegreChart

variable {K : Type} [Fintype K] {J : K → Type} {N : ℕ}

def segPt {R : Type} [CommMonoid R] (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → R) :
    (Σ _ : Unit, Fin (N + 1)) → R :=
  fun p => ∏ k, y ⟨k, E p.2 k⟩

def segMap (E : Fin (N + 1) ≃ ((k : K) → J k)) :
    MRing (fun _ : Unit => Fin (N + 1)) →ₐ[ℤ] MRing J :=
  aeval (segPt E fun p => (X p : MRing J))

theorem aeval_segMap {R : Type} [CommRing R] (E : Fin (N + 1) ≃ ((k : K) → J k)) (v : (Σ k, J k) → R)
    (g : MRing (fun _ : Unit => Fin (N + 1))) : aeval v (segMap E g) = aeval (segPt E v) g := by
  rw [segMap, comp_aeval_apply]
  simp only [segPt, map_prod, aeval_X]
  rfl

theorem seg_ratio {Ω : Type} [Field Ω] (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → Ω)
    (c : (k : K) → J k) (p : Σ _ : Unit, Fin (N + 1)) :
    segPt E y p / segPt E y ⟨p.1, E.symm c⟩ = segPt E (fun p => y p / y ⟨p.1, c p.1⟩) p := by
  simp only [segPt, Equiv.apply_symm_apply, Finset.prod_div_distrib]

theorem adjoin_ratios_seg {Ω : Type} [Field Ω] [Algebra ℚ Ω] (E : Fin (N + 1) ≃ ((k : K) → J k))
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) =
      Algebra.adjoin ℚ (Set.range fun p : Σ _ : Unit, Fin (N + 1) =>
        segPt E y p / segPt E y ⟨p.1, E.symm c⟩) := by
  classical
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    have h1 := seg_ratio_update y c hc k i
    refine Algebra.subset_adjoin ⟨⟨(), E.symm (Function.update c k i)⟩, ?_⟩
    simp only [segPt, Equiv.apply_symm_apply]
    exact h1
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe]
    simp only [seg_ratio]
    exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, E p.2 k⟩, rfl⟩

theorem clause_map {σ τ Ω : Type} [Field Ω] [Algebra ℚ Ω] (S : Subalgebra ℚ Ω) (v : σ → Ω) (hv : ∀ p, v p ∈ S)
    (v₁ : τ → Ω) (φ : MvPolynomial τ ℤ →ₐ[ℤ] MvPolynomial σ ℤ) (hφ : ∀ g, aeval v (φ g) = aeval v₁ g)
    (I : Ideal (MvPolynomial τ ℤ)) (q : Ideal S) :
    (∀ g ∈ I.map φ, ∀ s : S, (s : Ω) = aeval v g → s ∈ q) ↔
      ∀ g ∈ I, ∀ s : S, (s : Ω) = aeval v₁ g → s ∈ q := by
  let ev : MvPolynomial σ ℤ →ₐ[ℤ] S := aeval fun p => (⟨v p, hv p⟩ : S)
  have hev : ∀ g, ((ev g : S) : Ω) = aeval v g := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp [ev]
    | add p q hp hq => simp only [map_add, Subalgebra.coe_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, Subalgebra.coe_mul, hp]; simp [ev]
  constructor
  · exact fun h g hg s hs => h _ (Ideal.mem_map_of_mem _ hg) s (hs.trans (hφ g).symm)
  · intro h g hg s hs
    have hle : I.map φ ≤ q.comap ev :=
      Ideal.map_le_iff_le_comap.2 fun g hg => h g hg _ ((hev _).trans (hφ g))
    have e : s = ev g := Subtype.ext (hs.trans (hev g).symm)
    rw [e]
    exact hle hg

theorem isSncModel_seg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [∀ k, Fintype (J k)]
    (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → Ω) (e : ℕ)
    (bd₁ : Ideal (MRing (fun _ : Unit => Fin (N + 1)))) (h : Cmp.IsSncModel (segPt E y) e bd₁) :
    Cmp.IsSncModel y e (bd₁.map (segMap E)) := by
  intro c hc
  have h0 : ∀ k : Unit, segPt E y ⟨k, E.symm c⟩ ≠ 0 := fun k => by
    simp only [segPt, Equiv.apply_symm_apply]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨m, f, b, hf, hb, hsum, hS⟩ := h (fun _ => E.symm c) h0
  have hA := adjoin_ratios_seg E y c hc
  refine ⟨m, f, b, fun l => ?_, fun l => ?_, hsum, fun l hfl S hSeq => ?_⟩
  · rw [hA]
    exact hf l
  · rw [hA]
    exact hb l
  have hS' : S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun p : Σ _ : Unit, Fin (N + 1) =>
      segPt E y p / segPt E y ⟨p.1, E.symm c⟩)) := by
    rw [hSeq, ← Algebra.adjoin_insert_adjoin, hA, Algebra.adjoin_insert_adjoin]
  obtain ⟨hsm, z, n, hn, hli, hspan, hq⟩ := hS l hfl S hS'
  refine ⟨hsm, z, n, hn, hli, hspan, fun q hqp => ?_⟩
  have hv : ∀ p : Σ k, J k, y p / y ⟨p.1, c p.1⟩ ∈ S := fun p => by
    rw [hSeq]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  rw [← hq q hqp]
  refine clause_map S _ hv _ (segMap E) (fun g => ?_) bd₁ q
  rw [aeval_segMap]
  congr 2
  funext p
  exact (seg_ratio E y c p).symm

theorem mem_mcPts_seg (E : Fin (N + 1) ≃ ((k : K) → J k)) (bd₁ : Ideal (MRing (fun _ : Unit => Fin (N + 1))))
    (w : (Σ k, J k) → ℂ) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    w ∈ mcPts (bd₁.map (segMap E)) ↔ segPt E w ∈ mcPts bd₁ := by
  have hval : ∀ g, eval w (map (Int.castRingHom ℂ) (segMap E g)) =
      eval (segPt E w) (map (Int.castRingHom ℂ) g) := fun g => by
    rw [eval_map_int, eval_map_int, aeval_segMap]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun _ => ?_, fun g hg => ?_⟩
    · choose c hc using hw
      refine ⟨E.symm c, ?_⟩
      simp only [segPt, Equiv.apply_symm_apply]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
    · rw [← hval]
      exact h _ (Ideal.mem_map_of_mem _ hg)
  · rintro ⟨-, h⟩
    refine ⟨hw, fun f hf => ?_⟩
    have hle : bd₁.map (segMap E) ≤ RingHom.ker (aeval w : MRing J →ₐ[ℤ] ℂ) :=
      Ideal.map_le_iff_le_comap.2 fun g hg => by
        have h1 := h g hg
        rw [eval_map_int, ← aeval_segMap] at h1
        exact h1
    rw [eval_map_int]
    exact hle hf

section Val

variable {Sc : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Sc}
  {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ Sc}

theorem valAt_one (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) :=
  ⟨h, 1, map_one _, map_one _⟩

theorem valAt_mul {a b : Ω} {r t : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) : ValAt ξ z (a * b) (r * t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨-, s', rfl, rfl⟩ := hb
  exact ⟨h, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_prod {α : Type} (h : genPt ξ ⤳ centre z) (s : Finset α) (a : α → Ω) (r : α → R)
    (H : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valAt_one h
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact valAt_mul (H i (Finset.mem_insert_self i s))
      (ih fun j hj => H j (Finset.mem_insert_of_mem hj))

theorem coordsAt_seg [Nonempty K] (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ Sc) (w : (Σ k, J k) → ℂ) (h : CoordsAt ξ y z w) :
    CoordsAt ξ (segPt E y : (Σ _ : Unit, Fin (N + 1)) → Ω) z (segPt E w) := by
  obtain ⟨hb, hr⟩ := h
  refine ⟨fun _ => ?_, fun _ j hj => ?_⟩
  · choose c hc using hb
    refine ⟨E.symm c, ?_⟩
    simp only [segPt, Equiv.apply_symm_apply]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => (hc k).ne_zero)
  · have huj : ∀ k, IsUnit (w ⟨k, E j k⟩) := fun k =>
      isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 (show (∏ k, w ⟨k, E j k⟩) ≠ 0 from hj.ne_zero) k
        (Finset.mem_univ k))
    have h0 : ∀ k, y ⟨k, E j k⟩ ≠ 0 := fun k => (hr k _ (huj k)).1
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => h0 k, fun i => ?_⟩
    choose r hrv hrw using fun k => (hr k _ (huj k)).2 (E i k)
    have hgen : genPt ξ ⤳ centre z := by
      obtain ⟨k⟩ := ‹Nonempty K›
      exact (hrv k).choose
    refine ⟨∏ k, r k, ?_, ?_⟩
    · have h1 := valAt_prod hgen Finset.univ _ _ fun k _ => hrv k
      rw [Finset.prod_div_distrib] at h1
      exact h1
    · show (∏ k, w ⟨k, E i k⟩) = (∏ k, r k) * ∏ k, w ⟨k, E j k⟩
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => hrw k

end Val

theorem points_of_isEmpty [IsEmpty K] [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [CharZero Ω] {Sc : Scheme.{0}}
    {ξ : Sp Ω ⟶ Sc} (y : (Σ k, J k) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing J))
    (hs : Cmp.IsSncModel y e bd) (hB : ∀ p ∈ B, Char0 ξ p) (hP : SncPts ξ e B)
    (z : Spec (CommRingCat.of ℂ) ⟶ Sc) (w : (Σ k, J k) → ℂ) :
    w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B := by
  haveI hE : IsEmpty (Σ k, J k) := ⟨fun p => isEmptyElim p.1⟩
  let c : (k : K) → J k := fun k => isEmptyElim k
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := hs c (fun k => isEmptyElim k)
  have hr : (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) = ∅ := Set.range_eq_empty _
  rw [hr] at hf ha hS
  rw [Algebra.adjoin_empty] at hf ha
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra hall
    push_neg at hall
    simp [hall] at hsum
  obtain ⟨hsm, zz, n, hn, hli, hspan, hq⟩ := hS l hl _ rfl
  set S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ ∅) with hSdef
  have hbot : S ≤ ⊥ := by
    refine Algebra.adjoin_le ?_
    rintro _ (rfl | h)
    · obtain ⟨t, ht⟩ := Algebra.mem_bot.1 (hf l)
      exact Algebra.mem_bot.2 ⟨t⁻¹, by rw [← ht, map_inv₀]⟩
    · exact absurd h (Set.notMem_empty _)
  have hD : ∀ s : S, KaehlerDifferential.D ℚ S s = 0 := fun s => by
    obtain ⟨t, ht⟩ := Algebra.mem_bot.1 (hbot s.2)
    have e1 : s = algebraMap ℚ S t := Subtype.ext ht.symm
    rw [e1]
    exact (KaehlerDifferential.D ℚ S).map_algebraMap t
  haveI hFe : IsEmpty (Fin e) := ⟨fun i => hli.ne_zero i (hD _)⟩
  have hcl := hq ⊥ Ideal.isPrime_bot
  obtain ⟨g, hg, s, hs1, hs0⟩ : ∃ g ∈ bd, ∃ s : S, (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g ∧
      s ∉ (⊥ : Ideal S) := by
    by_contra hall
    push_neg at hall
    obtain ⟨i, -⟩ := hcl.1 hall
    exact isEmptyElim i
  constructor
  · rintro ⟨-, hz⟩
    exfalso
    have h1 := hz g hg
    rw [eq_C_of_isEmpty g] at h1 hs1
    apply hs0
    rw [Ideal.mem_bot]
    apply Subtype.ext
    simp at h1 hs1
    simp [hs1, h1]
  · rintro ⟨h, hp⟩
    exfalso
    obtain ⟨A, zA, nA, qA, hpa, hqA, hl'⟩ := hP _ (hB _ hp)
    obtain ⟨R, -, hRl, hbd⟩ := hpa.pts qA hqA
    have hR : R = regAt ξ ⟨centre z, h⟩ := Subring.ext fun a => (hRl a).trans (hl' a).symm
    obtain ⟨i, -⟩ := hbd.1 ⟨_, hp, hR.symm⟩
    exact isEmptyElim i

end GlobalTheory.CompanionTheory.Ar.GeoModel.Seg

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

open Seg in

theorem exists_isSncModel_of_sncPts : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ p ∈ B, Char0 ξ p) → SncPts ξ e B → ∃ bd : Ideal (MRing J), Cmp.IsSncModel y e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  intro Ω _ _ X ξ K _ J _ y e B hT hB hP
  obtain ⟨c₀, -⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Nonempty ((k : K) → J k) := ⟨c₀⟩
  have hcard : 0 < Nat.card ((k : K) → J k) := Nat.card_pos
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  let E : Fin (N + 1) ≃ ((k : K) → J k) := (Finite.equivFinOfCardEq hN).symm
  have hTx : CoordTie ℤ ξ (fun j : Fin (N + 1) => ∏ k, y ⟨k, E j k⟩) := CoordBase.coordTie_reindex E hT
  obtain ⟨bd₁, hs, hpt⟩ := GlobalTheory.T.exists_snc_model_of_patches Ω X ξ N _ e B hTx hB hP
  have hs' := isSncModel_seg E y e bd₁ hs
  refine ⟨bd₁.map (segMap E), hs', fun z w hw => ?_⟩
  rcases isEmpty_or_nonempty K with hK | hK
  · exact points_of_isEmpty y e B _ hs' hB hP z w
  · have hnz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hw.1 k
      exact ⟨i, hi.ne_zero⟩
    rw [mem_mcPts_seg E bd₁ w hnz]
    exact hpt z _ (coordsAt_seg E y z w hw)

end GlobalTheory.CompanionTheory.Ar.GeoModel
