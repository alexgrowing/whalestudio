import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfGlue

theorem tri {R : Type} [CommRing R] {g : ℕ} (G G' T : Matrix (Fin (g + g)) (Fin (g + g)) R) (h : G' = T.transpose * G * T)
    (hG : ∀ (i : Fin g) (k : Fin (g + g)), G (Fin.castAdd g i) k = if (i : ℕ) + k = 2 * g - 1 then 1 else 0)
    (hG' : ∀ (i : Fin g) (k : Fin (g + g)), G' (Fin.castAdd g i) k = if (i : ℕ) + k = 2 * g - 1 then 1 else 0)
    (hT : ∀ (k : Fin g) (i : Fin (g + g)), (k : ℕ) < i → T i (Fin.castAdd g k) = 0) (i : Fin g) :
    (∀ k : Fin (g + g), (i : ℕ) + k < 2 * g - 1 → T (Fin.natAdd g i.rev) k = 0) ∧
      T (Fin.castAdd g i) (Fin.castAdd g i) * T (Fin.natAdd g i.rev) (Fin.natAdd g i.rev) = 1 := by
  have key : ∀ (i : Fin g) (k : Fin (g + g)), (if (i : ℕ) + k = 2 * g - 1 then (1 : R) else 0) =
      ∑ m : Fin g, T (Fin.castAdd g m) (Fin.castAdd g i) * T (Fin.natAdd g m.rev) k := by
    intro i k
    rw [← hG', h, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_add]
    have h0 : ∑ m : Fin g, T.transpose (Fin.castAdd g i) (Fin.natAdd g m) * (G * T) (Fin.natAdd g m) k = 0 :=
      Finset.sum_eq_zero fun m _ => by
        rw [Matrix.transpose_apply, hT i _ (by simp; omega), zero_mul]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd g m.rev)]
    · rw [hG, if_pos (by simp; omega), one_mul]
    · intro n _ hn
      rw [hG, if_neg, zero_mul]
      intro e
      exact hn (Fin.ext (by simp; omega))
    · simp
  induction' hi : (i : ℕ) using Nat.strong_induction_on with n ih generalizing i
  subst hi
  have key2 : ∀ k : Fin (g + g), (i : ℕ) + k ≤ 2 * g - 1 → (if (i : ℕ) + k = 2 * g - 1 then (1 : R) else 0) =
      T (Fin.castAdd g i) (Fin.castAdd g i) * T (Fin.natAdd g i.rev) k := by
    intro k hk
    rw [key, Finset.sum_eq_single i]
    · intro m _ hm
      rcases lt_or_gt_of_ne hm with hm | hm
      · rw [(ih m hm m rfl).1 k (by have : (m : ℕ) < i := hm; omega), mul_zero]
      · rw [hT i _ (by simpa using hm), zero_mul]
    · simp
  have hu := key2 (Fin.natAdd g i.rev) (by simp; omega)
  rw [if_pos (by simp; omega)] at hu
  refine ⟨fun k hk => ?_, hu.symm⟩
  have h1 := key2 k hk.le
  rw [if_neg hk.ne] at h1
  linear_combination (T (Fin.natAdd g i.rev) k) * hu - T (Fin.natAdd g i.rev) (Fin.natAdd g i.rev) * h1

theorem val_stalk {K : Type} [Field K] (O : ValuationSubring K) {Z : Scheme.{0}} [IsIntegral Z] (yt : Sp O ⟶ Z)
    (a : Z.presheaf.stalk (yt (IsLocalRing.closedPoint O))) :
    GlobalTheory.TrueGeo.valAt (spMap O.subtype ≫ yt) (algebraMap _ Z.functionField a) =
      ((Scheme.stalkClosedPointTo yt).hom a : O) := by
  have hs : below (spMap O.subtype ≫ yt) ⤳ yt (IsLocalRing.closedPoint O) := by
    have e1 : below (spMap O.subtype ≫ yt) = yt ((spMap O.subtype) (IsLocalRing.closedPoint K)) := rfl
    rw [e1]
    exact (IsLocalRing.specializes_closedPoint _).map yt.continuous
  have e1 : algebraMap _ Z.functionField a = algebraMap _ Z.functionField ((Z.presheaf.stalkSpecializes hs).hom a) := by
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.germ_exist _ a
    have hb : below (spMap O.subtype ≫ yt) ∈ U := hs.mem_open U.isOpen hx
    rw [algebraMap_germ hx]
    have e3 := TopCat.Presheaf.germ_stalkSpecializes Z.presheaf (U := U) hx hs
    rw [← CommRingCat.comp_apply, e3, algebraMap_germ hb]
  rw [e1, SmallSec.valAt_algebraMap]
  have e2 : Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (spMap O.subtype ≫ yt) =
      Scheme.stalkClosedPointTo yt ≫ CommRingCat.ofHom O.subtype := by
    apply Spec.map_injective
    rw [← cancel_mono (Z.fromSpecStalk _)]
    simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk yt]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap O.subtype ≫ yt)
  exact congrArg (fun q => q.hom a) e2

section AbsVal

variable {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1)
include hO

theorem lt_one_iff (x : O) : w (x : K) < 1 ↔ IsLocalRing.residue O x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro h ⟨u, rfl⟩
    have e : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := congrArg Subtype.val u.mul_inv
    have h1 := congrArg w e
    rw [map_mul, map_one] at h1
    have h2 : w (((u⁻¹ : Oˣ) : O) : K) ≤ 1 := (hO _).1 (u⁻¹ : Oˣ).1.2
    nlinarith [w.nonneg ((u : O) : K), w.nonneg (((u⁻¹ : Oˣ) : O) : K)]
  · intro h
    by_contra h'
    have hx1 : w (x : K) = 1 := le_antisymm ((hO _).1 x.2) (not_lt.1 h')
    have hx0 : (x : K) ≠ 0 := fun e => by rw [e, map_zero] at hx1; exact zero_ne_one hx1
    have hi : (x : K)⁻¹ ∈ O := (hO _).2 (by rw [map_inv₀, hx1, inv_one])
    exact h ⟨⟨x, ⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem inv_close {r s : O} {t : K} (hrs : IsLocalRing.residue O r * IsLocalRing.residue O s = 1)
    (hrt : w ((r : K) - t) < 1) : w ((s : K) - t⁻¹) < 1 := by
  have ht : t ∈ O := by
    have : t = r - (r - t) := by ring
    rw [this]
    exact sub_mem r.2 ((hO _).2 hrt.le)
  lift t to O using ht
  have h1 : IsLocalRing.residue O (r - t) = 0 := (lt_one_iff w O hO (r - t)).1 hrt
  rw [map_sub, sub_eq_zero] at h1
  have h2 : ¬ w (t : K) < 1 := by
    rw [lt_one_iff w O hO t, ← h1]
    exact left_ne_zero_of_mul_eq_one hrs
  have hwt1 : w (t : K) = 1 := le_antisymm ((hO _).1 t.2) (not_lt.1 h2)
  have ht0 : (t : K) ≠ 0 := fun e => by rw [e, map_zero] at hwt1; exact zero_ne_one hwt1
  have hst : w ((s * t - 1 : O) : K) < 1 := by
    rw [lt_one_iff w O hO, map_sub, map_mul, map_one, ← h1, mul_comm, hrs, sub_self]
  have e : (s : K) - (t : K)⁻¹ = (t : K)⁻¹ * ((s * t - 1 : O) : K) := by
    push_cast
    field_simp
  rw [e, map_mul, map_inv₀, hwt1, inv_one, one_mul]
  exact hst

end AbsVal

theorem frames {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1)
    {Z : Scheme.{0}} [IsIntegral Z] (yt : Sp O ⟶ Z) (y : Sp K ⟶ Z) (hy : spMap O.subtype ≫ yt = y) {g : ℕ}
    (Ma Mb : Matrix (Fin (g + g)) (Fin (g + g)) Z.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ)
    (ha : ∀ i k, RegAt (yt (IsLocalRing.closedPoint O)) (Ma i k))
    (hb : ∀ i k, RegAt (yt (IsLocalRing.closedPoint O)) (Mb i k))
    (hd : UnitAt (yt (IsLocalRing.closedPoint O)) Ma.det)
    (hJa : ∀ (i : Fin g) (k : Fin (g + g)), w (valAt y
      ((Ma.transpose * J.map (Int.castRingHom Z.functionField) * Ma) (Fin.castAdd g i) k) -
        (if (i : ℕ) + k = 2 * g - 1 then 1 else 0)) < 1)
    (hJb : ∀ (i : Fin g) (k : Fin (g + g)), w (valAt y
      ((Mb.transpose * J.map (Int.castRingHom Z.functionField) * Mb) (Fin.castAdd g i) k) -
        (if (i : ℕ) + k = 2 * g - 1 then 1 else 0)) < 1)
    (hT : ∀ (k : Fin g) (i : Fin (g + g)), (k : ℕ) < i → w (valAt y ((Ma⁻¹ * Mb) i (Fin.castAdd g k))) < 1)
    (i : Fin g) :
    (∀ k : Fin (g + g), (i : ℕ) + k < 2 * g - 1 → w (valAt y ((Ma⁻¹ * Mb) (Fin.natAdd g i.rev) k)) < 1) ∧
      ∀ t : K, w (valAt y ((Ma⁻¹ * Mb) (Fin.castAdd g i) (Fin.castAdd g i)) - t) < 1 →
        w (valAt y ((Ma⁻¹ * Mb) (Fin.natAdd g i.rev) (Fin.natAdd g i.rev)) - t⁻¹) < 1 := by
  subst hy
  choose Sa hSa using ha
  choose Sb hSb using hb
  set φ := algebraMap (Z.presheaf.stalk (yt (IsLocalRing.closedPoint O))) Z.functionField with hφ
  set ψ : Z.presheaf.stalk (yt (IsLocalRing.closedPoint O)) →+* O := (Scheme.stalkClosedPointTo yt).hom with hψ
  obtain rfl : φ.mapMatrix (Matrix.of Sa) = Ma := Matrix.ext hSa
  obtain rfl : φ.mapMatrix (Matrix.of Sb) = Mb := Matrix.ext hSb
  generalize Matrix.of Sa = Pa at *
  generalize Matrix.of Sb = Pb at *
  have hdet : IsUnit Pa.det := by
    obtain ⟨u, hu, e⟩ := hd
    rw [← RingHom.map_det] at e
    rwa [← IsFractionRing.injective _ Z.functionField e]
  have hinv : (φ.mapMatrix Pa)⁻¹ = φ.mapMatrix Pa⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Matrix.nonsing_inv_mul Pa hdet, map_one]
  have hval : ∀ (S : Matrix (Fin (g + g)) (Fin (g + g)) (Z.presheaf.stalk (yt (IsLocalRing.closedPoint O)))) i k,
      valAt (spMap O.subtype ≫ yt) (φ.mapMatrix S i k) = (ψ (S i k) : O) := fun S i k => val_stalk O yt (S i k)
  have hform : ∀ P : Matrix (Fin (g + g)) (Fin (g + g)) (Z.presheaf.stalk (yt (IsLocalRing.closedPoint O))),
      (φ.mapMatrix P).transpose * J.map (Int.castRingHom Z.functionField) * φ.mapMatrix P =
        φ.mapMatrix (P.transpose * J.map (Int.castRingHom _) * P) := by
    intro P
    rw [map_mul, map_mul]
    congr 2
    ext i k
    simp
  rw [hform] at hJa hJb
  rw [hinv, ← map_mul] at hT ⊢
  simp only [hval] at hJa hJb hT ⊢
  set ρ := (IsLocalRing.residue O).comp ψ with hρ
  have hres : ∀ (s : Z.presheaf.stalk (yt (IsLocalRing.closedPoint O))) (q : Prop) [Decidable q],
      w ((ψ s : K) - if q then 1 else 0) < 1 → ρ s = if q then 1 else 0 := by
    intro s q _ h
    have h1 := (lt_one_iff w O hO (ψ s - if q then 1 else 0)).1 (by split_ifs at h ⊢ <;> simpa using h)
    rw [map_sub, sub_eq_zero] at h1
    rw [hρ, RingHom.comp_apply, h1]
    split_ifs <;> simp
  have H := tri (ρ.mapMatrix (Pa.transpose * J.map (Int.castRingHom _) * Pa))
    (ρ.mapMatrix (Pb.transpose * J.map (Int.castRingHom _) * Pb)) (ρ.mapMatrix (Pa⁻¹ * Pb))
    (by
      have e1 : (ρ.mapMatrix (Pa⁻¹ * Pb)).transpose = ρ.mapMatrix (Pa⁻¹ * Pb).transpose := rfl
      rw [e1, ← map_mul, ← map_mul]
      congr 1
      have e2 : Pa * (Pa⁻¹ * Pb) = Pb := Matrix.mul_nonsing_inv_cancel_left Pa Pb hdet
      calc Pb.transpose * J.map (Int.castRingHom _) * Pb
          = (Pa * (Pa⁻¹ * Pb)).transpose * J.map (Int.castRingHom _) * (Pa * (Pa⁻¹ * Pb)) := by rw [e2]
        _ = _ := by simp only [Matrix.transpose_mul Pa, Matrix.mul_assoc])
    (fun i k => hres _ _ (hJa i k)) (fun i k => hres _ _ (hJb i k))
    (fun k i hk => (lt_one_iff w O hO _).1 (hT k i hk)) i
  exact ⟨fun k hk => (lt_one_iff w O hO _).2 (H.1 k hk), fun t ht => inv_close w O hO H.2 ht⟩

theorem locFlag_of_halfFlag : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g N : ℕ} (h : N = g + g)
    (A B : Fin g → Adl C Y) (p : ℕ),
    (∀ k x, UnitAt x (genAt (B k).D x * genAt (A (Fin.rev k)).D x)) →
    (∀ k v, resP v = p → ∀ (e : Ext v) (y : AlgPt Y), (B k).lg v e y = -(A (Fin.rev k)).lg v e y +
      Real.log (e.w (GlobalTheory.TrueGeo.valAt y.1 (genAt (B k).D (below y.1) * genAt (A (Fin.rev k)).D (below y.1))))) →
    HalfFlag A p →
    LocFlag (fun i : Fin N => Sum.elim A B (finSumFinEquiv.symm (finCongr h i))) p := by
  intro F _ _ Y C g N h A B p hD hlg hA
  subst h
  obtain ⟨V, W, ι, U, M, J, c, -, hgen, hcov, hreg, hunit, hfr⟩ := hA
  have key : ∀ a (k : Fin g) (x : Y.X),
      V.φ (genAt (B k).D x) * (((c a k.rev)⁻¹ : V.G.functionFieldˣ) : V.G.functionField) =
        V.φ (genAt (B k).D x * genAt (A k.rev).D x) * (V.φ (genAt (A k.rev).D x) * c a k.rev)⁻¹ := by
    intro a k x
    have h0 : V.φ (genAt (A k.rev).D x) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    have h0' : ((c a k.rev : V.G.functionFieldˣ) : V.G.functionField) ≠ 0 := Units.ne_zero _
    rw [map_mul, Units.val_inv_eq_inv_val]
    field_simp
  refine ⟨V, W, ι, U, M, fun a i => Sum.elim (c a) (fun k => (c a k.rev)⁻¹) (finSumFinEquiv.symm i), hgen, hcov,
    hreg, ?_, ?_⟩
  · intro a i z hz
    induction i using Fin.addCases with
    | left i => simpa using hunit a i z hz
    | right k =>
      simp only [finCongr_refl, Equiv.refl_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
      rw [key]
      exact (V.unitAt_φ (hD k _)).mul (hunit a k.rev z hz).inv
  intro v hv e y hy z yt hz hyt
  have hfr' := hfr v hv e y hy z yt hz hyt
  have hpv : ((p : 𝓞 F)) ∈ v.asIdeal := by
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := (ringChar.spec _ p).2 (by rw [← hv]; rfl)
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hwp : e.w (p : AlgebraicClosure F) < 1 := by
    have h := e.w_alg (p : F)
    rw [map_natCast] at h
    rw [h, ← map_natCast (algebraMap (𝓞 F) F) p, ← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem F v _).2 hpv
  have hpO : ¬ IsUnit ((p : ℕ) : e.O) := by
    have h1 := (lt_one_iff e.w e.O e.mem_O (p : e.O)).1 (by simpa using hwp)
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
  have hpx : ¬ IsUnit ((p : ℕ) : V.X.presheaf.stalk (yt (IsLocalRing.closedPoint e.O))) := by
    intro h
    apply hpO
    have := h.map (Scheme.stalkClosedPointTo yt).hom
    rwa [map_natCast] at this
  have hPin : ∀ a', ⊤ ≤ yt ⁻¹ᵁ U a' → V.j (below z) ∈ U a' := by
    intro a' ha'
    have e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
      change (z ≫ V.j) _ = _
      rw [← hyt]; rfl
    rw [e2]; exact ha' trivial
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have hu : ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a → ∀ i, UnitAt (below z) (V.φ (genAt (A i).D (below y.1)) * c a i) := by
    intro a ha i
    have h := hunit a i (below z) (hPin a ha)
    rwa [hπ] at h
  intro a ha
  refine ⟨fun i => ?_, fun b hb i => ?_⟩
  · induction i using Fin.addCases with
    | left i => simpa using (hfr' a ha).1 i
    | right k =>
      simp only [finCongr_refl, Equiv.refl_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
      have hU2 := hu a ha k.rev
      have hu' : UnitAt (V.π (below z)) (genAt (B k).D (below y.1) * genAt (A k.rev).D (below y.1)) := by
        rw [hπ]; exact hD k _
      have n1 : e.w (valAt y.1 (genAt (B k).D (below y.1) * genAt (A k.rev).D (below y.1))) ≠ 0 :=
        (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hD k _))
      have n2 : e.w (valAt z (V.φ (genAt (A k.rev).D (below y.1)) * (c a k.rev : V.G.functionField))) ≠ 0 :=
        (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hU2)
      rw [key, SmallSec.valAt_mul (V.unitAt_φ hu').regAt hU2.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv hU2,
        V.valAt_φ z hu'.regAt, hz, map_mul, map_inv₀, Real.log_mul n1 (inv_ne_zero n2), Real.log_inv,
        ← (hfr' a ha).1, hlg k v hv]
      ring
  · have hra := hreg a _ (ha trivial) hpx
    have hrb := hreg b _ (hb trivial) hpx
    have hab := (hfr' a ha).2.2 b hb
    induction i using Fin.addCases with
    | left i =>
      refine ⟨fun k hk => ?_, by simpa using (hab i (Fin.castAdd g i)).2⟩
      have hk' : (k : ℕ) < i := hk
      have e1 : k = Fin.castAdd g ⟨k, hk'.trans i.2⟩ := Fin.ext rfl
      rw [e1]
      exact (hab _ _).1 hk'
    | right k =>
      obtain ⟨i, rfl⟩ : ∃ i : Fin g, k = i.rev := ⟨k.rev, (Fin.rev_rev k).symm⟩
      have H := frames e.w e.O e.mem_O yt _ hyt (M a) (M b) J hra.1 hrb.1 hra.2 (hfr' a ha).2.1 (hfr' b hb).2.1
        (fun k i hk => (hab k i).1 hk) i
      refine ⟨fun k hk => H.1 k ?_, ?_⟩
      · have hk' : (k : ℕ) < g + (g - (i + 1)) := hk
        have := i.2
        omega
      · simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.rev_rev]
        have hq : UnitAt (below z) ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) := by
          have hg : V.φ (genAt (A i).D (below y.1)) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
          have e1 : ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) =
              (V.φ (genAt (A i).D (below y.1)) * c a i) * (V.φ (genAt (A i).D (below y.1)) * c b i)⁻¹ := by
            rw [Units.val_div_eq_div_val]; field_simp
          rw [e1]
          exact (hu a ha i).mul (hu b hb i).inv
        have e2 : (c a i)⁻¹ / (c b i)⁻¹ = (c a i / c b i)⁻¹ := by rw [inv_div_inv, inv_div]
        rw [e2, Units.val_inv_eq_inv_val, GlobalTheory.LineNorm.Neg.valAt_inv hq]
        exact H.2 _ (hab i (Fin.castAdd g i)).2

end GlobalTheory.HalfGlue

end
