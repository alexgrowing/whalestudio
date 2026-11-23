import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReversedFlagLocalHeightLogFormula
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLat

theorem valAt_form {K : Type} [Field K] (O : ValuationSubring K) {Z : Scheme.{0}} [IsIntegral Z] (yt : Sp O ⟶ Z)
    (y : Sp K ⟶ Z) (hy : spMap O.subtype ≫ yt = y) {n g : ℕ} (M : Matrix (Fin n) (Fin g) Z.functionField)
    (J : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ i k, RegAt (yt (IsLocalRing.closedPoint O)) (M i k)) :
    (∀ i k, valAt y (M i k) ∈ O) ∧ ∀ i j, valAt y ((M.transpose * J.map (Int.castRingHom Z.functionField) * M) i j) =
      dotProduct (fun r => valAt y (M r i)) ((J.map (Int.castRingHom K)).mulVec fun r => valAt y (M r j)) := by
  subst hy
  choose S hS using hM
  set φ := algebraMap (Z.presheaf.stalk (yt (IsLocalRing.closedPoint O))) Z.functionField with hφ
  set ψ : Z.presheaf.stalk (yt (IsLocalRing.closedPoint O)) →+* K :=
    O.subtype.comp (Scheme.stalkClosedPointTo yt).hom with hψ
  have hval : ∀ s, valAt (spMap O.subtype ≫ yt) (φ s) = ψ s := fun s => GlobalTheory.HalfGlue.val_stalk O yt s
  refine ⟨fun i k => ?_, fun i j => ?_⟩
  · rw [← hS, hval]
    exact ((Scheme.stalkClosedPointTo yt).hom (S i k)).2
  · have e1 : (M.transpose * J.map (Int.castRingHom Z.functionField) * M) i j =
        φ (∑ r, S r i * ∑ s, (J r s : Z.presheaf.stalk (yt (IsLocalRing.closedPoint O))) * S s j) := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp only [map_sum, map_mul, map_intCast, hS, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
        eq_intCast]
    rw [e1, hval]
    simp only [map_sum, map_mul, map_intCast, ← hS, hval, dotProduct, Matrix.mulVec, Matrix.map_apply, eq_intCast]

theorem form_frame_small : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p k : ℕ), p.Prime →
    ∀ (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U0 : ι → V.X.Opens)
    (H0 : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (a : ι) (U : V.X.Opens)
    (Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField) (Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField)
    (c : Fin g → V.G.functionFieldˣ), U ≤ U0 a → FrameOn V W U (H0 a) d T A p Um Lf c → IsoAgree V W U0 H0 T J p k →
    AtTest V W p (fun _ e _ z yt => ⊤ ≤ yt ⁻¹ᵁ U → ∀ i j,
      e.w (valAt (z ≫ V.j) ((Um.transpose * J.map (Int.castRingHom V.X.functionField) * Um) i j)) ≤
        e.w (p : AlgebraicClosure F) ^ k) := by
  intro F _ _ Y C g A p k _ V W ι U0 H0 d T J a U Um Lf c hU hfr hiso v hv e y hy z yt hz hyt ha i j
  obtain ⟨-, hreg, -, hB⟩ := hfr
  obtain ⟨-, B, -, -, hB⟩ := hB v hv e y hy z yt hz hyt ha
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
    have h1 := (GlobalTheory.HalfGlue.lt_one_iff e.w e.O e.mem_O (p : e.O)).1 (by simpa using hwp)
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
  have hpx : ¬ IsUnit ((p : ℕ) : V.X.presheaf.stalk (yt (IsLocalRing.closedPoint e.O))) := by
    intro h
    apply hpO
    have := h.map (Scheme.stalkClosedPointTo yt).hom
    rwa [map_natCast] at this
  obtain ⟨h1, h2⟩ := valAt_form e.O yt (z ≫ V.j) hyt Um J fun i k => (hreg _ (ha trivial) hpx i k).1
  have hcol : ∀ l, (valMat V (H0 a) (T (below y.1)) z).mulVec (fun r => B r l) = fun r => valAt (z ≫ V.j) (Um r l) := by
    intro l
    funext r
    exact (congrFun (congrFun hB r) l).symm
  have hle : ∀ l, supN e.w ((valMat V (H0 a) (T (below y.1)) z).mulVec (fun r => B r l)) ≤ 1 := by
    intro l
    rw [hcol]
    exact supN_le e.w zero_le_one fun r => (e.mem_O _).1 (h1 r l)
  have h3 := (hiso v hv e y hy z yt hz hyt a (fun x hx => hU (ha hx))).1 _ _ (hle i) (hle j)
  rw [hcol, hcol] at h3
  rw [h2]
  exact h3

end GlobalTheory.ConstLat

end
