import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationCloseMatricesQuotientIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockTriangularIntegralGramUnitDetStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFrames
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TrivFlag

theorem locFrames_nonarch {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K)
    (hO : ∀ x, x ∈ O ↔ w x ≤ 1) {x y t : K} (h₁ : w (x - y) < 1) (h₂ : w (y - t) < 1) : w (x - t) < 1 := by
  have key : ∀ a b : K, w a < 1 → w b < 1 → w (a + b) < 1 := by
    intro a b ha hb
    by_cases h0 : b = 0
    · simpa [h0] using ha
    rcases le_total (w a) (w b) with hab | hab
    · have hb0 : 0 < w b := w.pos h0
      have h1 : a / b ∈ O := (hO _).2 (by rw [map_div₀]; exact (div_le_one hb0).2 hab)
      have h2 : a / b + 1 ∈ O := add_mem h1 O.one_mem
      have e : a + b = (a / b + 1) * b := by field_simp
      rw [e, map_mul]
      calc w (a / b + 1) * w b ≤ 1 * w b := mul_le_mul_of_nonneg_right ((hO _).1 h2) (w.nonneg _)
        _ = w b := one_mul _
        _ < 1 := hb
    · have ha0 : a ≠ 0 := fun h => by simp [h] at hab; exact h0 hab
      have ha0' : 0 < w a := w.pos ha0
      have h1 : b / a ∈ O := (hO _).2 (by rw [map_div₀]; exact (div_le_one ha0').2 hab)
      have h2 : 1 + b / a ∈ O := add_mem O.one_mem h1
      have e : a + b = (1 + b / a) * a := by field_simp
      rw [e, map_mul]
      calc w (1 + b / a) * w a ≤ 1 * w a := mul_le_mul_of_nonneg_right ((hO _).1 h2) (w.nonneg _)
        _ = w a := one_mul _
        _ < 1 := ha
  have e : x - t = (x - y) + (y - t) := by ring
  rw [e]; exact key _ _ h₁ h₂

theorem locFrames_congr_inv : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K), (∀ x, x ∈ O ↔ w x ≤ 1) →
    ∀ {N : ℕ} (Γa Γb Aa Ab : Matrix (Fin N) (Fin N) K), (∀ i k, w (Γa i k) ≤ 1) → (∀ i k, w (Γb i k) ≤ 1) →
    w Γa.det = 1 → (∀ i k, w (Aa i k - Γa i k) < 1) → (∀ i k, w (Ab i k - Γb i k) < 1) →
    w Aa.det = 1 ∧ ∀ i k, w ((Aa⁻¹ * Ab) i k - (Γa⁻¹ * Γb) i k) < 1 := GlobalTheory.T.valuation_close_matrices_quotient_integral

theorem locFrames_triangular : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K), (∀ x, x ∈ O ↔ w x ≤ 1) →
    ∀ {N : ℕ} (G Ba Bb : Matrix (Fin N) (Fin N) K) (d ga gb : Fin N → K), Ba.BlockTriangular id → Bb.BlockTriangular id →
    (∀ i, w (Ba i i * ga i - d i) < w (d i)) → (∀ i, w (Bb i i * gb i - d i) < w (d i)) →
    (∀ i k, w ((G * Ba) i k) ≤ 1) → (∀ i k, w ((G * Bb) i k) ≤ 1) → w (G * Ba).det = 1 → w (G * Bb).det = 1 →
    ∀ i, (∀ k, k < i → ((G * Ba)⁻¹ * (G * Bb)) i k = 0) ∧ w (((G * Ba)⁻¹ * (G * Bb)) i i - ga i / gb i) < 1 := GlobalTheory.T.block_triangular_integral_gram_unit_det

end GlobalTheory.TrivFlag

namespace GlobalTheory.TrivFlag

theorem locFlag_of_locFrames {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {N : ℕ}
    (A : Fin N → Adl C Y) (p : ℕ) (hA : LocFrames A p) : LocFlag A p := by
  obtain ⟨V, W, ι, U, M, c, hgen, hcov, hreg, hunit, hfr⟩ := hA
  refine ⟨V, W, ι, U, M, c, hgen, hcov, hreg, hunit, ?_⟩
  intro v hv e y hy z yt hz hyt
  obtain ⟨G, d, hGd⟩ := hfr v hv e y hy z yt hz hyt
  have hP : ∀ U' : V.X.Opens, yt (IsLocalRing.closedPoint e.O) ∈ U' → below (z ≫ V.j) ∈ U' := by
    intro U' hU'
    have e1 : below (z ≫ V.j) =
        yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
      rw [← hyt]; rfl
    rw [e1]
    exact ((IsLocalRing.specializes_closedPoint _).map yt.continuous).mem_open U'.isOpen hU'
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
    intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have hq' : ((p : AlgebraicClosure F)) * (q : AlgebraicClosure F) = 1 := by
      have := congrArg (fun x : e.O => (x : AlgebraicClosure F)) hq
      simpa using this
    have hwq : e.w (q : AlgebraicClosure F) ≤ 1 := (e.mem_O _).1 q.2
    have hw1 := congrArg e.w hq'
    rw [map_mul, map_one] at hw1
    nlinarith [e.w.nonneg (q : AlgebraicClosure F), e.w.nonneg (p : AlgebraicClosure F)]
  have hpx : ¬ IsUnit ((p : ℕ) : V.X.presheaf.stalk (yt (IsLocalRing.closedPoint e.O))) := by
    intro h
    apply hpO
    have := h.map (Scheme.stalkClosedPointTo yt).hom
    rwa [map_natCast] at this
  have hregP : ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a → ∀ i k, RegAt (below (z ≫ V.j)) (M a i k) := by
    intro a ha i k
    have hxa : yt (IsLocalRing.closedPoint e.O) ∈ U a := ha trivial
    obtain ⟨U', hU', b, hb⟩ := ((hreg a _ hxa hpx).1 i k).exists_fnOf
    rw [← hb]; exact regAt_fnOf (hP U' hU') _ b
  have hS : ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a → ∃ S : Matrix (Fin N) (Fin N) (V.X.presheaf.stalk (below (z ≫ V.j))),
      (algebraMap _ V.X.functionField).mapMatrix S = M a := by
    intro a ha
    choose S hS using hregP a ha
    exact ⟨S, Matrix.ext fun i k => hS i k⟩
  have hinv : ∀ {R S' : Type} [CommRing R] [CommRing S'] (f : R →+* S') (X : Matrix (Fin N) (Fin N) R),
      IsUnit X.det → (f.mapMatrix X)⁻¹ = f.mapMatrix X⁻¹ := by
    intro R S' _ _ f X hX
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Matrix.nonsing_inv_mul X hX, map_one]
  have hPin : ∀ a', ⊤ ≤ yt ⁻¹ᵁ U a' → V.j (below z) ∈ U a' := by
    intro a' ha'
    have e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
      change (z ≫ V.j) _ = _
      rw [← hyt]; rfl
    rw [e2]; exact ha' trivial
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  intro a ha
  refine ⟨(hGd a ha).1, fun b hb i => ?_⟩
  obtain ⟨-, Ba, hBa, hda, hia, hdeta, hca⟩ := hGd a ha
  obtain ⟨-, Bb, hBb, hdb, hib, hdetb, hcb⟩ := hGd b hb
  obtain ⟨Sa, hSa⟩ := hS a ha
  obtain ⟨Sb, hSb⟩ := hS b hb
  have hval : ∀ s, TrueGeo.valAt (z ≫ V.j) (algebraMap _ V.X.functionField s) =
      (Scheme.stalkClosedPointTo (z ≫ V.j)).hom s := Res.valAt_algebraMap _
  have hAa : ∀ i k, e.w (((Scheme.stalkClosedPointTo (z ≫ V.j)).hom.mapMatrix Sa) i k - (G * Ba) i k) < 1 := by
    intro i k; have h := hca i k
    rw [← hSa, RingHom.mapMatrix_apply, Matrix.map_apply, hval] at h
    exact h
  have hAb : ∀ i k, e.w (((Scheme.stalkClosedPointTo (z ≫ V.j)).hom.mapMatrix Sb) i k - (G * Bb) i k) < 1 := by
    intro i k; have h := hcb i k
    rw [← hSb, RingHom.mapMatrix_apply, Matrix.map_apply, hval] at h
    exact h
  obtain ⟨hdetA, hcong⟩ := locFrames_congr_inv e.w e.O e.mem_O (G * Ba) (G * Bb) _ _ hia hib hdeta hAa hAb
  obtain ⟨hlow, hdiag⟩ := locFrames_triangular e.w e.O e.mem_O G Ba Bb d
    (fun i => TrueGeo.valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField)))
    (fun i => TrueGeo.valAt z (V.φ (genAt (A i).D (below y.1)) * (c b i : V.G.functionField)))
    hBa hBb hda hdb hia hib hdeta hdetb i
  have hdetSa : IsUnit Sa.det := by
    have h1 : (Scheme.stalkClosedPointTo (z ≫ V.j)).hom Sa.det ≠ 0 := by
      rw [RingHom.map_det]; intro h0; rw [h0, map_zero] at hdetA; exact zero_ne_one hdetA
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (z ≫ V.j)).hom _ (Ne.isUnit h1)
  have hentry : ∀ i k, TrueGeo.valAt (z ≫ V.j) (((M a)⁻¹ * M b) i k) =
      (((Scheme.stalkClosedPointTo (z ≫ V.j)).hom.mapMatrix Sa)⁻¹ *
        (Scheme.stalkClosedPointTo (z ≫ V.j)).hom.mapMatrix Sb) i k := by
    intro i k
    rw [← hSa, ← hSb, hinv _ _ hdetSa, ← map_mul, hinv _ _ hdetSa, ← map_mul, RingHom.mapMatrix_apply,
      Matrix.map_apply, hval, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hua : UnitAt (below z) (V.φ (genAt (A i).D (below y.1)) * c a i) := by
    have h := hunit a i (below z) (hPin a ha); rwa [hπ] at h
  have hub : UnitAt (below z) (V.φ (genAt (A i).D (below y.1)) * c b i) := by
    have h := hunit b i (below z) (hPin b hb); rwa [hπ] at h
  have hquot : TrueGeo.valAt z ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) =
      TrueGeo.valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField)) /
        TrueGeo.valAt z (V.φ (genAt (A i).D (below y.1)) * (c b i : V.G.functionField)) := by
    have hg : V.φ (genAt (A i).D (below y.1)) ≠ 0 := left_ne_zero_of_mul hua.ne_zero
    have e1 : ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField) =
        (V.φ (genAt (A i).D (below y.1)) * c a i) * (V.φ (genAt (A i).D (below y.1)) * c b i)⁻¹ := by
      rw [Units.val_div_eq_div_val]; field_simp
    rw [e1, Res.valAt_mul hua.regAt hub.inv.regAt, div_eq_mul_inv]
    congr 1
    have h1 := Res.valAt_mul hub.regAt hub.inv.regAt
    rw [mul_inv_cancel₀ hub.ne_zero, Res.valAt_one] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hentry]
    have h := hcong i k
    rwa [hlow k hk, sub_zero] at h
  · rw [hentry, hquot]
    exact locFrames_nonarch e.w e.O e.mem_O (hcong i i) hdiag

end GlobalTheory.TrivFlag

end
