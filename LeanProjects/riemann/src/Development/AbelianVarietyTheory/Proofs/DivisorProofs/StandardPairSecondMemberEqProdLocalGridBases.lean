import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.StdSnd

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (unitChar IsUnitDet InId rightBlock dualCoord stdSnd)
open GlobalTheory.StdPairCone (stdB blk₁ blk₂ IsGLO)
open GlobalTheory.LFun (locChar locIdele)
open GlobalTheory.FunObj.Comparison₂ (vEq)

theorem hom_sum {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι) :
    f (∑ i ∈ s, p i) = ∑ i ∈ s, f (p i) := map_sum f p s

theorem hom_prod {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : ι → R) (s : Finset ι) :
    f (∏ i ∈ s, p i) = ∏ i ∈ s, f (p i) := map_prod f p s

variable {D : D7}

theorem cpt_idemSum {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (Q : Pl D.host.E) :
    (Q ∈ S → cpt (D := D) Q (toEAf D e) = 1) ∧ (Q ∉ S → cpt (D := D) Q (toEAf D e) = 0) := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  rw [hsum, hom_sum (toEAf D), hom_sum (cpt (D := D) Q)]
  refine ⟨fun hQ => ?_, fun hQ => ?_⟩
  · rw [Finset.sum_eq_single Q (fun P hP hPQ => (cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ)) (fun h => absurd hQ h)]
    exact (cpt_of_isIdemAt (hes Q hQ)).1
  · exact Finset.sum_eq_zero fun P hP => (cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))

theorem cpt_prod_locIdele (S : Finset (Pl D.host.E)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ) (Q : Pl D.host.E) :
    (∀ hQ : Q ∈ S, cpt (D := D) Q (toEAf D ((∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ) : AE D)) = u ⟨Q, hQ⟩) ∧
    (Q ∉ S → cpt (D := D) Q (toEAf D ((∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ) : AE D)) = 1) := by
  have hloc : ∀ (w : Pl D.host.E) (y : (Kw (D := D) w)ˣ), cpt (D := D) Q (toEAf D (locIdele D.host.F w y : AE D)) =
        (Neutral.B1.finiteSingle D.host.E w (y : Kw (D := D) w)) Q := by
    intro w y
    rw [GlobalTheory.DepthFix.cpt_eq_finAd]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)
  rw [Units.coe_prod, hom_prod (toEAf D), hom_prod (cpt (D := D) Q)]
  simp only [hloc]
  refine ⟨fun hQ => ?_, fun hQ => ?_⟩
  · rw [Finset.prod_eq_single ⟨Q, hQ⟩]
    · rw [GlobalTheory.LFun.finSingle_self]
    · intro b _ hb
      exact GlobalTheory.LFun.finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · exact Finset.prod_eq_one fun w _ => GlobalTheory.LFun.finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _

theorem infPart_prod_locIdele (S : Finset (Pl D.host.E)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ) :
    infPart D ((∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ) : AE D) = 1 := by
  rw [Units.coe_prod, hom_prod]
  exact Finset.prod_eq_one fun w _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) w.1 _

theorem prod_map_inv {ι M : Type} [Fintype ι] [CommGroup M] {K : ι → Type} [∀ i, Group (K i)] (f : ∀ i, K i →* M)
    (u : ∀ i, K i) : (∏ i, f i (u i))⁻¹ = ∏ i, f i (u i)⁻¹ := by
  simp only [map_inv, Finset.prod_inv_distrib]

theorem char_prod_inv {ι M : Type} [Fintype ι] [CommMonoid M] (ν : M →* Circle) (x : ι → M) :
    (((ν (∏ i, x i))⁻¹ : Circle) : ℂ) = ∏ i, (((Circle.toUnits (ν (x i)))⁻¹ : ℂˣ) : ℂ) := by
  rw [map_prod, ← Finset.prod_inv_distrib]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun w _ => ?_)
  rw [Units.val_inv_eq_inv_val]
  exact Circle.coe_inv _

theorem isUnitDet_prod {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    (N : Matrix (Fin k) (Fin k) (EAf D)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ)
    (hu : ∀ w : S, (u w : Kw (D := D) w.1) = cpt (D := D) w.1 N.det)
    (hv : ∀ w : S, Valued.v (u w : Kw (D := D) w.1) = 1) : IsUnitDet e N (∏ w : S, locIdele D.host.F w.1 (u w)) := by
  refine ⟨infPart_prod_locIdele S u, cpt_ext fun Q => ?_, ?_⟩
  · rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    by_cases hQ : Q ∈ S
    · rw [(cpt_prod_locIdele S u Q).1 hQ, (cpt_idemSum he Q).1 hQ, hu, sub_self, zero_add, one_mul]
    · rw [(cpt_prod_locIdele S u Q).2 hQ, (cpt_idemSum he Q).2 hQ, sub_zero, zero_mul, add_zero]
  · have e1 : (∏ w : S, locIdele D.host.F w.1 (u w) : (AE D)ˣ)⁻¹ = ∏ w : S, locIdele D.host.F w.1 (u w)⁻¹ :=
      prod_map_inv (fun w : S => locIdele D.host.F w.1) u
    rw [e1]
    refine (mem_OA_iff _).2 fun Q => ?_
    by_cases hQ : Q ∈ S
    · rw [(cpt_prod_locIdele S (fun w => (u w)⁻¹) Q).1 hQ, HeightOneSpectrum.mem_adicCompletionIntegers,
        Units.val_inv_eq_inv_val, map_inv₀, hv ⟨Q, hQ⟩, inv_one]
    · rw [(cpt_prod_locIdele S (fun w => (u w)⁻¹) Q).2 hQ]
      exact one_mem _

theorem isUnitDet_unique {e : AE D} {k : ℕ} {N : Matrix (Fin k) (Fin k) (EAf D)} {x x' : (AE D)ˣ} (h : IsUnitDet e N x)
    (h' : IsUnitDet e N x') : x = x' :=
  Units.ext (ae_ext (h.1.trans h'.1.symm) fun Q => congrArg (cpt (D := D) Q) (h.2.1.trans h'.2.1.symm))

theorem unitChar_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    (N : Matrix (Fin k) (Fin k) (EAf D)) (u : ∀ w : S, (Kw (D := D) w.1)ˣ)
    (hu : ∀ w : S, (u w : Kw (D := D) w.1) = cpt (D := D) w.1 N.det)
    (hv : ∀ w : S, Valued.v (u w : Kw (D := D) w.1) = 1) :
    unitChar ν e N = ∏ w : S, (((locChar ν w.1 (u w))⁻¹ : ℂˣ) : ℂ) := by
  have hx := isUnitDet_prod he N u hu hv
  have hex : ∃ x, IsUnitDet e N x := ⟨_, hx⟩
  unfold unitChar
  rw [dif_pos hex, isUnitDet_unique hex.choose_spec hx]
  exact char_prod_inv ν _

theorem v_det_of_isUnitDet {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {N : Matrix (Fin k) (Fin k) (EAf D)} {x : (AE D)ˣ} (hx : IsUnitDet e N x) {w : Pl D.host.E} (hw : w ∈ S)
    (hN : Valued.v (cpt (D := D) w N.det) ≤ 1) : Valued.v (cpt (D := D) w N.det) = 1 := by
  have h1 : cpt (D := D) w (toEAf D (x : AE D)) = cpt (D := D) w N.det := by
    rw [hx.2.1, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (cpt_idemSum he w).1 hw, sub_self,
      zero_add, one_mul]
  have h2 : Valued.v (cpt (D := D) w (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D))) ≤ 1 := (mem_OA_iff _).1 hx.2.2 w
  have h3 : Valued.v (cpt (D := D) w N.det) * Valued.v (cpt (D := D) w (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D))) = 1 := by
    rw [← h1, ← Valuation.map_mul, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one,
      Valuation.map_one]
  refine le_antisymm hN ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
    _ ≤ Valued.v (cpt (D := D) w N.det) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem mem_cball_pow (w : Pl D.host.E) (c : ℕ) (z : Kw (D := D) w) :
    z ∈ cball (unifAt (D := D) w ^ c) ↔ Valued.v z ≤ WithZero.exp (-(c : ℤ)) := by
  have h : Valued.v (unifAt (D := D) w : Kw (D := D) w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  refine (vEq w _ _).trans ?_
  rw [Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem mem_integer_iff (w : Pl D.host.E) (z : Kw (D := D) w) : z ∈ (ValuativeRel.valuation (Kw (D := D) w)).integer ↔ Valued.v z ≤ 1 := by
  rw [Valuation.mem_integer_iff, (vEq w).le_one_iff_le_one]

theorem inId_prod_iff (S : Finset (Pl D.host.E)) (c : Pl D.host.E → ℕ) {z : EAf D}
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    InId (∏ w ∈ S, w.asIdeal ^ c w) z ↔ ∀ w ∈ S, Valued.v (cpt (D := D) w z) ≤ WithZero.exp (-(c w : ℤ)) := by
  have h : (∏ w ∈ S, w.asIdeal ^ c w) = S.inf fun v => v.asIdeal ^ c v :=
    (HeightOneSpectrum.inf_pow_eq_prod S c id fun v _ v' _ hne => hne).symm
  have h0 : (∏ w ∈ S, w.asIdeal ^ c w) ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  generalize (∏ w ∈ S, w.asIdeal ^ c w) = I at h h0
  constructor
  · rintro ⟨h1, h2⟩ w hw
    exact GlobalTheory.FunObj.Comparison₂.v_le_of_mem_idS (s := ⟨z, h1⟩) (h.le.trans (Finset.inf_le hw)) h2
  · intro H
    exact ⟨hz, GlobalTheory.FunObj.Comparison₂.mem_idS_of_v_le (w := fun v => v) (e := c) (S := S) (s := ⟨z, hz⟩) h0 h H⟩

open Classical in

theorem std_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    (c : Pl D.host.E → ℕ) {a a' : ℕ} (Y : Matrix (Fin a') (Fin (a + a')) (EAf D)) (hY : ∀ i j, toEAf D e * Y i j = Y i j) :
    (if IsIntM Y ∧ ∀ i j, j.1 < a → InId (∏ w ∈ S, w.asIdeal ^ c w) (Y i j) then unitChar ν e (rightBlock a Y) else 0) =
      ∏ w ∈ S, stdB (locChar ν w) (unifAt (D := D) w) (c w) a a' (Y.map (cpt (D := D) w)) := by
  have hb : ∀ i j, rightBlock a Y i j = Y i (Fin.natAdd a j) := fun i j => dif_pos (Fin.natAdd a j).2
  have hdet : ∀ w, (blk₂ (Y.map (cpt (D := D) w))).det = cpt (D := D) w (rightBlock a Y).det := fun w => by
    rw [RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hb]
    rfl
  by_cases H : ∀ w ∈ S, (blk₂ (Y.map (cpt (D := D) w))).det ≠ 0 ∧ IsGLO (blk₂ (Y.map (cpt (D := D) w))) ∧
      ∀ i j, blk₁ (Y.map (cpt (D := D) w)) i j ∈ cball (unifAt (D := D) w ^ c w)
  · have hint : IsIntM Y := fun i j => (mem_OA_iff _).2 fun Q => by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      by_cases hQ : Q ∈ S
      · refine Fin.addCases (motive := fun j => Valued.v (cpt (D := D) Q (Y i j)) ≤ 1) (fun j => ?_) (fun j => ?_) j
        · refine ((mem_cball_pow Q _ _).1 ((H Q hQ).2.2 i j)).trans ?_
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]
          omega
        · exact (mem_integer_iff Q _).1 ((H Q hQ).2.1.1 i j)
      · rw [← hY, RingHom.map_mul, (cpt_idemSum he Q).2 hQ, zero_mul, Valuation.map_zero]
        exact zero_le_one
    rw [if_pos ⟨hint, fun i j hj => (inId_prod_iff S c (hint i j)).2 fun w hw =>
      (mem_cball_pow w _ _).1 ((H w hw).2.2 i ⟨j.1, hj⟩)⟩,
      unitChar_eq_prod ν he _ (fun w => Units.mk0 _ (H w.1 w.2).1) (fun w => hdet w.1)
        (fun w => (vEq w.1).eq_one_iff_eq_one.1 (H w.1 w.2).2.1.2), ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun w _ => ?_
    unfold stdB
    rw [dif_pos (H w.1 w.2)]
  · obtain ⟨w, hw⟩ := not_forall.1 H
    obtain ⟨hw, hn⟩ := Classical.not_imp.1 hw
    rw [Finset.prod_eq_zero (f := fun w => stdB (locChar ν w) (unifAt (D := D) w) (c w) a a' (Y.map (cpt (D := D) w))) hw
      (by unfold stdB; exact dif_neg hn)]
    split_ifs with hc
    · unfold unitChar
      refine dif_neg fun ⟨x, hx⟩ => hn ?_
      have hi : ∀ i j, blk₂ (Y.map (cpt (D := D) w)) i j ∈ (ValuativeRel.valuation (Kw (D := D) w)).integer := fun i j =>
        (mem_integer_iff w _).2 ((mem_OA_iff _).1 (hc.1 i _) w)
      have hd : (blk₂ (Y.map (cpt (D := D) w))).det ∈ (ValuativeRel.valuation (Kw (D := D) w)).integer := by
        rw [Matrix.det_apply']
        exact Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hi _ _)
      have h1 : Valued.v (blk₂ (Y.map (cpt (D := D) w))).det = 1 := by
        rw [mem_integer_iff, hdet] at hd
        rw [hdet]
        exact v_det_of_isUnitDet he hx hw hd
      refine ⟨fun h0 => ?_, ⟨hi, (vEq w).eq_one_iff_eq_one.2 h1⟩, fun i j => (mem_cball_pow w _ _).2 ?_⟩
      · rw [h0, Valuation.map_zero] at h1
        exact zero_ne_one h1
      · exact (inId_prod_iff S c (hc.1 i _)).1 (hc.2 i (Fin.castAdd a' j) j.2) w hw
    · rfl

open Classical in

theorem std_eq_prod' (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    (c : Pl D.host.E → ℕ) {a a' d : ℕ} (hd : d = a + a') (b b' : Pl D.host.E → ℕ) (hb : ∀ w, a = b w) (hb' : ∀ w, a' = b' w)
    (Y : Matrix (Fin a') (Fin d) (EAf D)) (hY : ∀ i j, toEAf D e * Y i j = Y i j)
    (Z : ∀ w, Matrix (Fin (b' w)) (Fin (b w + b' w)) (Kw (D := D) w))
    (hZ : ∀ w r s, ∃ r' s', r'.1 = r.1 ∧ s'.1 = s.1 ∧ Z w r s = cpt (D := D) w (Y r' s')) :
    (if IsIntM Y ∧ ∀ i j, j.1 < a → InId (∏ w ∈ S, w.asIdeal ^ c w) (Y i j) then unitChar ν e (rightBlock a Y) else 0) =
      ∏ w ∈ S, stdB (locChar ν w) (unifAt (D := D) w) (c w) (b w) (b' w) (Z w) := by
  obtain rfl : b = fun _ => a := funext fun w => (hb w).symm
  obtain rfl : b' = fun _ => a' := funext fun w => (hb' w).symm
  subst hd
  have : ∀ w, Z w = Y.map (cpt (D := D) w) := fun w => Matrix.ext fun r s => by
    obtain ⟨r', s', h1, h2, h3⟩ := hZ w r s
    rw [h3, Fin.ext h1, Fin.ext h2]
    rfl
  simp only [this]
  exact std_eq_prod ν he c Y hY

theorem change_frames {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n d : ℕ} (β β' : GL (Fin n) R) (γ γ' : GL (Fin d) R)
    (M : Matrix (Fin n) (Fin d) R) (ξ : R) (x : K) (hx : f ξ = x) (hξ : x ≠ 0) :
    (Units.map (Matrix.scalar (Fin n)).toMonoidHom (Units.mk0 x hξ) *
        ((GeneralLinearGroup.map f β')⁻¹ * GeneralLinearGroup.map f β)).val *
        ((β⁻¹).val * M * γ.val).map f * ((GeneralLinearGroup.map f γ)⁻¹ * GeneralLinearGroup.map f γ').val =
      (ξ • ((β'⁻¹).val * M * γ'.val)).map f := by
  have hl : ∀ {k : ℕ} (g : GL (Fin k) R), g.val.map f = (GeneralLinearGroup.map f g).val := fun g => rfl
  have hs : (ξ • ((β'⁻¹).val * M * γ'.val)).map f = x • ((β'⁻¹).val * M * γ'.val).map f := Matrix.ext fun r s => by
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, hx]
    rfl
  have hu : (Units.map (Matrix.scalar (Fin n)).toMonoidHom (Units.mk0 x hξ)).val = x • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.smul_one_eq_diagonal]
    rfl
  rw [hs, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hl, hl, hl, hl, map_inv, map_inv]
  generalize GeneralLinearGroup.map f β = b
  generalize GeneralLinearGroup.map f β' = b'
  generalize GeneralLinearGroup.map f γ = g
  generalize GeneralLinearGroup.map f γ' = g'
  generalize M.map f = N
  have h1 : b.val * (b⁻¹).val = 1 := b.mul_inv
  have h2 : g.val * (g⁻¹).val = 1 := g.mul_inv
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hu, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul]
  congr 1
  calc (b'⁻¹).val * b.val * ((b⁻¹).val * N * g.val) * ((g⁻¹).val * g'.val)
      = (b'⁻¹).val * (b.val * (b⁻¹).val) * N * (g.val * (g⁻¹).val) * g'.val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem locChar_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) :
    locChar (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) w = (locGrid G t w).nu i j := by
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
    mul_div_mul_right_eq_div _ _ _
  rw [e1, GlobalTheory.LFun.locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  ext x
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul,
    Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
  rfl

theorem val_colX_ordX (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)
    (s : Fin ((locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j))) :
    ((colX G t i j w).symm ((ordX G t i j w).symm s)).1 = s.1 := by
  have h : ∀ z : (locGrid G t w).Cols i j, ((colX G t i j w).symm z).1 = (finSumFinEquiv z).1 := by
    rintro (z | z)
    · rfl
    · change _ + z.1 = _ + z.1
      rw [rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩]
  rw [h]
  simp [ordX, SplitFlip.stdSplit]

theorem stdSnd_eq_prodB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j) (ε : AE D), IsIdemSum ε (locPl G t) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ε (X.ideal (locPl G) t)
        (spW G i j).rank (spW₁ G i j) (spX G i j) X.rA'.β X.rW.β = prodB B t i j ε (locSnd B t X) := by
  intro D T L sc G μ₀ hL B t i j X ε hε
  classical
  funext y
  unfold stdSnd prodB
  by_cases hy : IsHalf (cA D ε) y
  · rw [if_pos hy]
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    have w₀ : Pl D.host.E := ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    have hd : (spX G i j).rank = (spW G i j).rank + (spW₁ G i j).rank := by
      have := Fintype.card_congr ((colX G t i j w₀).trans (ordX G t i j w₀))
      rw [Fintype.card_fin, Fintype.card_fin] at this
      rw [this, rankW G t i j w₀, rankW₁ G t i j w₀]
    have key := std_eq_prod' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) hε (X.c t) hd _ _
      (rankW G t i j) (rankW₁ G t i j) (dualCoord (spW₁ G i j) (spX G i j) X.rA'.β X.rW.β y)
      (fun r s => by
        unfold dualCoord
        rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, GlobalTheory.AdjVecLocal.frMapAdj_half _ _ _ _ hy])
      (fun w => reindex (Equiv.refl _) (ordX G t i j w) ((chB B t X w).val * linB B t i j w y * (chX B t X w).val))
      (fun w r s => ⟨(finCongr (rankW₁ G t i j w)).symm r, _, rfl, val_colX_ordX t i j w s, by
        unfold chB chX linB frMapAdj dualCoord frMapAdj
        rw [GlobalTheory.StepData.reGL_val, GlobalTheory.StepData.reGL_val, Matrix.reindex_apply, Matrix.reindex_apply,
          Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
        exact congrFun (congrFun (change_frames (cpt (D := D) w) (B.β i j) X.rA'.β (frX B i j) X.rW.β _
          (eToEAf D D.host.xi0) (xiAt (D := D) w) (GlobalTheory.FunObj.Comparison₂.cpt_tmul w _) _) _) _⟩)
    refine Eq.trans ?_ (key.trans (Finset.prod_congr rfl fun w _ => ?_))
    · exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_iff_right hy) rfl rfl
    · rw [locChar_nu hL]
      rfl
  · rw [if_neg hy, if_neg fun h => hy h.1]

end GlobalTheory.TopFlip.StdSnd

end
