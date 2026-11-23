import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameChangeTri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReversedFlagLocalHeightLogFormula
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TestChange

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z]

theorem exists_lift (y : Sp K ⟶ Z) {m n : Type} {A : Matrix m n Z.functionField} (hA : ∀ i j, RegAt (below y) (A i j)) :
    ∃ S : Matrix m n (Z.presheaf.stalk (below y)), A = S.map (algebraMap _ Z.functionField) := by
  choose S hS using hA
  exact ⟨Matrix.of S, Matrix.ext fun i j => (hS i j).symm⟩

theorem map_lift (y : Sp K ⟶ Z) {m n : Type} (S : Matrix m n (Z.presheaf.stalk (below y))) :
    (S.map (algebraMap _ Z.functionField)).map (valAt y) = S.map (Scheme.stalkClosedPointTo y).hom :=
  Matrix.ext fun i j => SmallSec.valAt_algebraMap (S i j)

theorem val_mul (y : Sp K ⟶ Z) {m n o : Type} [Fintype n] {A : Matrix m n Z.functionField}
    {B : Matrix n o Z.functionField} (hA : ∀ i j, RegAt (below y) (A i j)) (hB : ∀ i j, RegAt (below y) (B i j)) :
    (∀ i j, RegAt (below y) ((A * B) i j)) ∧ (A * B).map (valAt y) = A.map (valAt y) * B.map (valAt y) := by
  obtain ⟨S, rfl⟩ := exists_lift y hA
  obtain ⟨S', rfl⟩ := exists_lift y hB
  rw [← Matrix.map_mul, map_lift, map_lift, map_lift]
  exact ⟨fun i j => ⟨(S * S') i j, rfl⟩, Matrix.map_mul⟩

theorem val_inv (y : Sp K ⟶ Z) {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n Z.functionField}
    (hA : ∀ i j, RegAt (below y) (A i j)) :
    valAt y A.det = (A.map (valAt y)).det ∧ (valAt y A.det ≠ 0 →
      (∀ i j, RegAt (below y) (A⁻¹ i j)) ∧ A⁻¹.map (valAt y) = (A.map (valAt y))⁻¹) := by
  obtain ⟨S, rfl⟩ := exists_lift y hA
  have hinv : ∀ {R S' : Type} [CommRing R] [CommRing S'] (f : R →+* S') (X : Matrix n n R),
      IsUnit X.det → (X.map f)⁻¹ = X⁻¹.map f := by
    intro R S' _ _ f X hX
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul X hX, Matrix.map_one _ (map_zero f) (map_one f)]
  have h1 : valAt y (S.map (algebraMap _ Z.functionField)).det = (Scheme.stalkClosedPointTo y).hom S.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact SmallSec.valAt_algebraMap _
  refine ⟨by rw [h1, map_lift, RingHom.map_det, RingHom.mapMatrix_apply], fun h => ?_⟩
  rw [h1] at h
  have hu : IsUnit S.det := isUnit_of_map_unit (Scheme.stalkClosedPointTo y).hom _ (Ne.isUnit h)
  rw [hinv _ _ hu, map_lift, map_lift, hinv _ _ hu]
  exact ⟨fun i j => ⟨S⁻¹ i j, rfl⟩, rfl⟩

theorem val_compl (y : Sp K ⟶ Z) {g : ℕ} {U : Matrix (Fin (g + g)) (Fin g) Z.functionField}
    {L : Matrix (Fin g) (Fin (g + g)) Z.functionField} {Ji : Matrix (Fin (g + g)) (Fin (g + g)) Z.functionField}
    (hU : ∀ i j, RegAt (below y) (U i j)) (hL : ∀ i j, RegAt (below y) (L i j)) (hJ : ∀ i j, RegAt (below y) (Ji i j)) :
    (∀ i j, RegAt (below y) (compl U L Ji i j)) ∧
      (compl U L Ji).map (valAt y) = compl (U.map (valAt y)) (L.map (valAt y)) (Ji.map (valAt y)) := by
  obtain ⟨h1, h2⟩ := val_mul y (B := L.transpose) hJ fun i j => hL j i
  refine ⟨fun i k => ?_, Matrix.ext fun i k => ?_⟩
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
    · simpa only [ConstLat.compl, Matrix.of_apply, Fin.addCases_left] using hU i l
    · simpa only [ConstLat.compl, Matrix.of_apply, Fin.addCases_right] using h1 i l.rev
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
    · simp only [ConstLat.compl, Matrix.of_apply, Fin.addCases_left, Matrix.map_apply]
    · simp only [ConstLat.compl, Matrix.of_apply, Fin.addCases_right, Matrix.map_apply]
      exact congrFun (congrFun h2 i) l.rev

theorem val_div (y : Sp K ⟶ Z) {a b : Z.functionField} (ha : UnitAt (below y) a) (hb : UnitAt (below y) b) :
    valAt y (a / b) = valAt y a / valAt y b := by
  rw [div_eq_mul_inv, SmallSec.valAt_mul ha.regAt hb.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv hb, div_eq_mul_inv]

theorem reg_of_closed (O : ValuationSubring K) (yt : Sp O ⟶ Z) (y : Sp K ⟶ Z) (hy : spMap O.subtype ≫ yt = y)
    {f : Z.functionField} (hf : RegAt (yt (IsLocalRing.closedPoint O)) f) : RegAt (below y) f ∧ valAt y f ∈ O := by
  subst hy
  constructor
  · obtain ⟨U', hU', b, hb⟩ := hf.exists_fnOf
    rw [← hb]
    exact regAt_fnOf (((IsLocalRing.specializes_closedPoint
      ((spMap O.subtype) (IsLocalRing.closedPoint K))).map yt.continuous).mem_open U'.isOpen hU') _ b
  · obtain ⟨a, rfl⟩ := hf
    rw [GlobalTheory.HalfGlue.val_stalk]
    exact ((Scheme.stalkClosedPointTo yt).hom a).2

theorem norm_of_unit (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) (yt : Sp O ⟶ Z)
    (y : Sp K ⟶ Z) (hy : spMap O.subtype ≫ yt = y) {f : Z.functionField}
    (hf : UnitAt (yt (IsLocalRing.closedPoint O)) f) : w (valAt y f) = 1 := by
  subst hy
  obtain ⟨a, ha, rfl⟩ := hf
  rw [GlobalTheory.HalfGlue.val_stalk]
  refine le_antisymm ((hO _).1 ((Scheme.stalkClosedPointTo yt).hom a).2) (not_lt.1 fun h => ?_)
  rw [GlobalTheory.HalfGlue.lt_one_iff w O hO] at h
  exact ((ha.map (Scheme.stalkClosedPointTo yt).hom).map (IsLocalRing.residue O)).ne_zero h

end Val

theorem w_le_one {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {x : F}
    (hx : IsIntegral ℤ x) : e.w (algebraMap F (AlgebraicClosure F) x) ≤ 1 := by
  have h1 : IsIntegral ℤ (algebraMap F (AlgebraicClosure F) x) := hx.algebraMap
  have h2 : IsIntegral e.O (algebraMap F (AlgebraicClosure F) x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact (e.mem_O _).1 y.2

theorem compl_le {K : Type} [Field K] (w : AbsoluteValue K ℝ) (hw : IsNonarchimedean w) {g : ℕ}
    {U : Matrix (Fin (g + g)) (Fin g) K} {L : Matrix (Fin g) (Fin (g + g)) K} {Ji : Matrix (Fin (g + g)) (Fin (g + g)) K}
    (hU : ∀ i j, w (U i j) ≤ 1) (hL : ∀ i j, w (L i j) ≤ 1) (hJ : ∀ i j, w (Ji i j) ≤ 1) (i k : Fin (g + g)) :
    w (compl U L Ji i k) ≤ 1 := by
  refine Fin.addCases (fun l => ?_) (fun l => ?_) k
  · simpa only [ConstLat.compl, Matrix.of_apply, Fin.addCases_left] using hU i l
  · simpa only [ConstLat.compl, Matrix.of_apply, Fin.addCases_right, one_mul] using
      FrameCmp.mul_le w hw Ji L.transpose zero_le_one zero_le_one hJ (fun i j => hL j i) i l.rev

theorem change_tri : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A A' : Fin g → Adl C Y) (p n k k' : ℕ),
    p.Prime → n ≠ 0 → ∀ (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U0 : ι → V.X.Opens)
    (H0 : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (d : Y.X → Fin g → Y.Fnˣ)
    (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ)
    (P Q : Matrix (Fin (g + g)) (Fin (g + g)) F) (κ : F →+* V.X.functionField),
    (∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (f : F), valAt (z ≫ V.j) (κ f) = valAt z (V.φ (algebraMap F Y.Fn f))) →
    IsUnit J.det → SecondLat J p n P Q → IsoAgree V W U0 H0 T J p k' → LineBase V d A p → LineBase V d A' p →
    ∀ (a b : ι) (Ua Ub : V.X.Opens) (Um' Um : Matrix (Fin (g + g)) (Fin g) V.X.functionField)
      (Lf' Lf : Matrix (Fin g) (Fin (g + g)) V.X.functionField) (c' c : Fin g → V.G.functionFieldˣ),
    Ua ≤ U0 a → Ub ≤ U0 b → ChartReg V (U0 a) (H0 a) T →
    FrameOn V W Ua (P.map (V.φ.comp (algebraMap F Y.Fn)) * H0 a) d T A' p Um' Lf' c' →
    FrameOn V W Ub (H0 b) d T A p Um Lf c →
    (∀ x ∈ Ua, ¬ IsUnit (p : V.X.presheaf.stalk x) →
      UnitAt x (compl Um' Lf' (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose)).det) →
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ Ua → ⊤ ≤ yt ⁻¹ᵁ Ub →
      e.w (p : AlgebraicClosure F) ^ k' / e.w (n : AlgebraicClosure F) ^ 3 ≤ e.w (p : AlgebraicClosure F) ^ k →
      ∀ i : Fin (g + g),
        (∀ j, j < i → e.w (valAt (z ≫ V.j) (((compl Um' Lf' (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ *
          (P.map κ).transpose))⁻¹ * P.map κ * compl Um Lf (J.map (Int.castRingHom V.X.functionField))⁻¹) i j)) ≤
            e.w (p : AlgebraicClosure F) ^ k) ∧
        e.w (valAt (z ≫ V.j) (((compl Um' Lf' (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ *
          (P.map κ).transpose))⁻¹ * P.map κ * compl Um Lf (J.map (Int.castRingHom V.X.functionField))⁻¹) i i) -
          valAt z ((Sum.elim c' (fun l => (c' l.rev)⁻¹) (finSumFinEquiv.symm i) /
            Sum.elim c (fun l => (c l.rev)⁻¹) (finSumFinEquiv.symm i) : V.G.functionFieldˣ) : V.G.functionField)) ≤
          e.w (p : AlgebraicClosure F) ^ k := by
  intro F _ _ Y C g A A' p n k k' hp hn V W ι U0 H0 d T J P Q κ hκ hJ hSL hiso hLA hLA' a b Ua Ub Um' Um Lf' Lf c' c
    hUa hUb hcr hfa hfb hdet v hv e y hy z yt hz hyt ha hb hle i
  have hw := isNonarchimedean_w e
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
  have hPin : ∀ U' : V.X.Opens, ⊤ ≤ yt ⁻¹ᵁ U' → V.j (below z) ∈ U' := by
    intro U' ha'
    have e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
      change (z ≫ V.j) _ = _
      rw [← hyt]; rfl
    rw [e2]; exact ha' trivial
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  set α := algebraMap F (AlgebraicClosure F) with hα
  have hc : ∀ f : F, valAt z (V.φ (algebraMap F Y.Fn f)) = α f := fun f => by
    rw [V.valAt_φ z (Var.regAt_algebraMap Y _ f), hz]
    exact OfLattice.valAt_const y.1 y.2 f
  have hκv : ∀ f : F, valAt (z ≫ V.j) (κ f) = α f := fun f => (hκ z f).trans (hc f)
  have hκr : ∀ f : F, RegAt (below (z ≫ V.j)) (κ f) := by
    intro f
    by_cases h0 : f = 0
    · rw [h0, map_zero]; exact regAt_zero _
    by_contra h
    have h1 := hκv f
    rw [TrueGeo.valAt, dif_neg h] at h1
    exact (map_ne_zero α).2 h0 h1.symm
  have hmap : ∀ M : Matrix (Fin (g + g)) (Fin (g + g)) F, (M.map κ).map (valAt (z ≫ V.j)) = M.map α :=
    fun M => Matrix.ext fun i j => hκv (M i j)
  have hJinv : ∀ (L : Type) [CommRing L], (J.map (Int.castRingHom L))⁻¹ = J⁻¹.map (Int.castRingHom L) := by
    intro L _
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J hJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hint : ∀ (L : Type) [CommRing L] (f : F →+* L) (M : Matrix (Fin (g + g)) (Fin (g + g)) ℤ),
      (M.map (Int.castRingHom F)).map f = M.map (Int.castRingHom L) := fun L _ f M => Matrix.ext fun i j => by simp
  obtain ⟨hPQ, hnint, s, hs, hsint⟩ := hSL
  set Ji := (J.map (Int.castRingHom F))⁻¹ with hJi
  have hJJ : J.map (Int.castRingHom F) * Ji = 1 := by
    rw [hJi, hJinv, ← Matrix.map_mul, Matrix.mul_nonsing_inv J hJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : (J.map (Int.castRingHom V.X.functionField))⁻¹ = Ji.map κ := by rw [hJi, hJinv, hJinv, hint]
  have e2 : P.map κ * Ji.map κ * (P.map κ).transpose = (P * Ji * P.transpose).map κ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2] at hdet ⊢
  obtain ⟨hLU', hreg', hun', hB'⟩ := hfa
  obtain ⟨hLU, hreg, hun, hB⟩ := hfb
  obtain ⟨-, B', hB't, hB'd, hB'⟩ := hB' v hv e y hy z yt hz hyt ha
  obtain ⟨-, B, hBt, hBd, hB⟩ := hB v hv e y hy z yt hz hyt hb
  have rU' := fun r l => reg_of_closed e.O yt _ hyt (hreg' _ (ha trivial) hpx r l).1
  have rL' := fun l r => reg_of_closed e.O yt _ hyt (hreg' _ (ha trivial) hpx r l).2
  have rU := fun r l => reg_of_closed e.O yt _ hyt (hreg _ (hb trivial) hpx r l).1
  have rL := fun l r => reg_of_closed e.O yt _ hyt (hreg _ (hb trivial) hpx r l).2
  obtain ⟨rM', vM'⟩ := val_compl (z ≫ V.j) (Ji := (P * Ji * P.transpose).map κ) (fun r l => (rU' r l).1)
    (fun l r => (rL' l r).1) fun i j => hκr _
  obtain ⟨rM, vM⟩ := val_compl (z ≫ V.j) (Ji := Ji.map κ) (fun r l => (rU r l).1) (fun l r => (rL l r).1)
    fun i j => hκr _
  rw [hmap] at vM vM'
  have hd1 := norm_of_unit e.w e.O e.mem_O yt _ hyt (hdet _ (ha trivial) hpx)
  obtain ⟨vd, hinv⟩ := val_inv (z ≫ V.j) rM'
  obtain ⟨rI, vI⟩ := hinv fun h => by rw [h, map_zero] at hd1; exact zero_ne_one hd1
  obtain ⟨rIP, vIP⟩ := val_mul (z ≫ V.j) (B := P.map κ) rI fun i j => hκr _
  obtain ⟨-, vX⟩ := val_mul (z ≫ V.j) rIP rM
  rw [vIP, vI, vM, vM', hmap] at vX
  rw [vd, vM'] at hd1
  have hone : ∀ m : ℕ, (1 : Matrix (Fin m) (Fin m) V.X.functionField).map (valAt (z ≫ V.j)) = 1 := fun m =>
    Matrix.map_one _ (by simpa using hκv 0) (by simpa using hκv 1)
  have hva : valMat V (P.map (V.φ.comp (algebraMap F Y.Fn)) * H0 a) (T (below y.1)) z =
      P.map α * valMat V (H0 a) (T (below y.1)) z := by
    have hr := hcr (below z) (hUa (hPin _ ha))
    rw [hπ] at hr
    rw [valMat, Matrix.mul_assoc, (val_mul z (A := P.map (V.φ.comp (algebraMap F Y.Fn)))
      (fun i j => V.regAt_φ (Var.regAt_algebraMap Y _ _)) hr).2]
    congr 1
    exact Matrix.ext fun i j => hc (P i j)
  rw [hva] at hB'
  have hun1 : ∀ (A₀ : Fin g → Adl C Y) (c₀ : Fin g → V.G.functionFieldˣ), LineBase V d A₀ p →
      (∀ l, UnitAt (below z) (V.φ (genAt (A₀ l).D (V.π (below z))) * c₀ l)) →
      ∀ l, UnitAt (below z) (V.φ (d (below y.1) l : Y.Fn) / (c₀ l : V.G.functionField)) := by
    intro A₀ c₀ h₁ h₂ l
    have h3 := (V.unitAt_φ (h₁.1 l (V.π (below z)))).mul (h₂ l).inv
    rw [hπ] at h3
    have hg : V.φ (genAt (A₀ l).D (below y.1)) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    convert h3 using 1
    rw [map_mul]
    field_simp
  have u' := hun1 A' c' hLA' fun l => hun' l _ (hPin _ ha)
  have u := hun1 A c hLA fun l => hun l _ (hPin _ hb)
  have hdφ : ∀ l, V.φ (d (below y.1) l : Y.Fn) ≠ 0 := fun l => (map_ne_zero _).2 (Units.ne_zero _)
  have hwn : 0 < e.w (n : AlgebraicClosure F) := e.w.pos (Nat.cast_ne_zero.2 hn)
  have hwZ : ∀ m : ℤ, e.w (m : AlgebraicClosure F) ≤ 1 := fun m => by
    simpa using w_le_one e (x := (m : F)) (isIntegral_algebraMap (R := ℤ) (x := m))
  have hwn' : ∀ x : F, IsIntegral ℤ ((n : F) * x) → e.w (α x) ≤ (e.w (n : AlgebraicClosure F))⁻¹ := fun x hx => by
    have h := w_le_one e hx
    rw [map_mul, map_mul, map_natCast] at h
    rw [← mul_one (_⁻¹), le_inv_mul_iff₀ hwn]
    exact h
  have hws : e.w (s : AlgebraicClosure F) = 1 := by
    refine le_antisymm (by simpa using hwZ s) (not_lt.1 fun h => ?_)
    obtain ⟨a₀, b₀, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
    have h1 : (a₀ : AlgebraicClosure F) * s + b₀ * p = 1 := by exact_mod_cast congrArg (Int.cast (R := AlgebraicClosure F)) hab
    have h2 := hw ((a₀ : AlgebraicClosure F) * s) (b₀ * p)
    rw [h1, map_one, map_mul, map_mul] at h2
    have h3 : e.w (a₀ : AlgebraicClosure F) * e.w (s : AlgebraicClosure F) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_right (hwZ a₀) (e.w.nonneg _) h
    have h4 : e.w (b₀ : AlgebraicClosure F) * e.w (p : AlgebraicClosure F) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_right (hwZ b₀) (e.w.nonneg _) hwp
    exact absurd h2 (not_le.2 (max_lt h3 h4))
  have hiso' := fun a₀ h => hiso v hv e y hy z yt hz hyt a₀ h
  have ha0 : ⊤ ≤ yt ⁻¹ᵁ U0 a := fun x hx => hUa (ha hx)
  have hb0 : ⊤ ≤ yt ⁻¹ᵁ U0 b := fun x hx => hUb (hb hx)
  have hQP : Q * P = 1 := mul_eq_one_comm.1 hPQ
  have H := FrameCmp.frame_change_tri e.w hw (Um.map (valAt (z ≫ V.j))) (Um'.map (valAt (z ≫ V.j)))
    (valMat V (H0 a) (T (below y.1)) z) (valMat V (H0 b) (T (below y.1)) z) (Lf.map (valAt (z ≫ V.j)))
    (Lf'.map (valAt (z ≫ V.j))) (J.map (Int.castRingHom _)) (Ji.map α) ((P * Ji * P.transpose).map α) (P.map α) (Q.map α)
    B B' (e.w (n : AlgebraicClosure F)) (e.w (p : AlgebraicClosure F) ^ k') hwn (by simpa using hwZ n) (by positivity)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← hint _ α, ← Matrix.map_mul, hJJ, Matrix.map_one _ (map_zero _) (map_one _)])
    (by
      have h1 : Q.transpose * J.map (Int.castRingHom F) * Q * (P * Ji * P.transpose) = 1 := by
        calc _ = Q.transpose * (J.map (Int.castRingHom F) * (Q * P) * Ji) * P.transpose := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hQP, Matrix.mul_one, hJJ, Matrix.mul_one, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
      rw [← hint _ α, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, h1,
        Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← (val_mul (z ≫ V.j) (fun l r => (rL l r).1) fun r l => (rU r l).1).2, hLU, hone])
    (by rw [← (val_mul (z ≫ V.j) (fun l r => (rL' l r).1) fun r l => (rU' r l).1).2, hLU', hone])
    hBt hB't (fun l => by rw [hBd]; exact SmallSec.valAt_ne_zero (u l))
    (fun l => by rw [hB'd]; exact SmallSec.valAt_ne_zero (u' l)) hB hB' (fun i j => hwZ _)
    (fun i j => ⟨hwn' _ (hnint i j).1, hwn' _ (hnint i j).2⟩)
    (compl_le e.w hw (fun r l => (e.mem_O _).1 (rU r l).2) (fun l r => (e.mem_O _).1 (rL l r).2) fun i j => by
      rw [hJi, hJinv, hint]; exact hwZ _)
    (compl_le e.w hw (fun r l => (e.mem_O _).1 (rU' r l).2) (fun l r => (e.mem_O _).1 (rL' l r).2) fun i j => by
      have h := w_le_one e (hsint i j).2
      rwa [map_mul, map_mul, map_natCast, hws, one_mul] at h)
    hd1 (hiso' a ha0).1 ((hiso' a ha0).2 b hb0) ((hiso' b hb0).2 a ha0) i
  rw [← vX] at H
  refine ⟨fun j hj => (H.1 j hj).trans hle, le_trans (le_of_eq ?_) (H.2.trans hle)⟩
  congr 2
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.addCases_left]
    rw [hBd, hB'd, ← val_div z (u l) (u' l), Units.val_div_eq_div_val]
    congr 1
    have := hdφ l
    field_simp
  · simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.addCases_right]
    rw [hBd, hB'd, ← val_div z (u' l.rev) (u l.rev), inv_div_inv, Units.val_div_eq_div_val]
    congr 1
    have := hdφ l.rev
    field_simp

end GlobalTheory.TestChange

end
