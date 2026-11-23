import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightScaling
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalModelModulusPropertiesOnUnits

noncomputable section
open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.RowsConc Formalism.HermitianLatticeCounting.ExpansionTerms ValuativeRel

namespace GlobalTheory.HTPlaceLeaf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem two_sum_range (r : ℕ) : ∀ q, q ≤ r + 1 → 2 * ∑ n ∈ Finset.range q, (r - n) = q * (2 * r + 1 - q) := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hq
    rw [Finset.sum_range_succ, mul_add, ih (by omega)]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show q ≤ r by omega)
    rw [show 2 * (q + k) + 1 - q = q + 2 * k + 1 by omega, show q + k - q = k by omega,
      show 2 * (q + k) + 1 - (q + 1) = q + 2 * k by omega]
    ring

theorem lead_scale_pow {R : Type*} [CommRing R] (r : ℕ) (x : R) (s : Fin (r + 1) → R)
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (q : ℕ) (hq : q ≤ r + 1) :
    leadingPrincipalMinor (Matrix.of fun a b : Fin (r + 1) => x ^ (r - a.val) * (s b * M a b) * x ^ (r - b.val)) q =
      x ^ (q * (2 * r + 1 - q)) *
        ((∏ b ∈ Finset.univ.filter (fun b : Fin (r + 1) => b.val < q), s b) * leadingPrincipalMinor M q) := by
  have hsub : (Matrix.of fun a b : Fin (r + 1) => x ^ (r - a.val) * (s b * M a b) * x ^ (r - b.val)).submatrix
      (fun i : {i : Fin (r + 1) // (i : ℕ) < q} => i.1) (fun i => i.1) =
      Matrix.diagonal (fun i : {i : Fin (r + 1) // (i : ℕ) < q} => x ^ (r - i.1.val)) *
        (M.submatrix (fun i : {i : Fin (r + 1) // (i : ℕ) < q} => i.1) (fun i => i.1) *
          Matrix.diagonal (fun i => s i.1)) *
        Matrix.diagonal (fun i : {i : Fin (r + 1) // (i : ℕ) < q} => x ^ (r - i.1.val)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hp : ∀ f : Fin (r + 1) → R, ∏ i : {i : Fin (r + 1) // (i : ℕ) < q}, f i.1 =
      ∏ b ∈ Finset.univ.filter (fun b : Fin (r + 1) => b.val < q), f b := fun f =>
    (Finset.prod_subtype _ (by simp) f).symm
  have hmap : (Finset.univ.filter (fun b : Fin (r + 1) => b.val < q)).map Fin.valEmbedding = Finset.range q := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hn; exact ⟨⟨n, by omega⟩, hn, rfl⟩
  have hS : 2 * ∑ b ∈ Finset.univ.filter (fun b : Fin (r + 1) => b.val < q), (r - b.val) = q * (2 * r + 1 - q) := by
    rw [← two_sum_range r q hq, ← hmap, Finset.sum_map]
    rfl
  unfold leadingPrincipalMinor
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  simp only [Matrix.det_diagonal]
  rw [hp (fun i => x ^ (r - i.val)), hp s, Finset.prod_pow_eq_pow_sum, ← hS, two_mul, pow_add]
  ring

theorem point_ends {K : Type} [Field K] {r : ℕ} (w : Point K (r + 1)) :
    (∀ a, endMin (toPts w) a ≠ 0) ∧ Function.Injective (endIdx (toPts w)) ∧
    (Finset.range (r + 2)).filter (fun l => 1 ≤ l ∧ leadingPrincipalMinor (ptMat w) l ≠ 0) =
      Finset.univ.image (endIdx (toPts w)) := by
  have hne : ∀ a, endMin (toPts w) a ≠ 0 := by
    intro a
    unfold endMin Formalism.HermitianLatticeCounting.ExpansionTerms.IndexedMinorEntry
    refine Finset.prod_ne_zero_iff.2 fun a' _ => mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · have : ((Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign ((toPts w).1.blocksFun a') : ℤ) : K) * ((Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign ((toPts w).1.blocksFun a') : ℤ) : K) = 1 := by
        unfold Formalism.HermitianLatticeCounting.ExpansionTerms.ParitySign
        push_cast
        rw [← mul_pow]; simp
      exact left_ne_zero_of_mul_eq_one this
    · exact (w.2.1 _ (List.get_mem _ _)).1
  have hinj : Function.Injective (endIdx (toPts w)) := by
    have hlt : ∀ a b : Fin (toPts w).1.length, a < b → endIdx (toPts w) a < endIdx (toPts w) b := by
      intro a b hab
      have h1 := (toPts w).1.monotone_sizeUpTo (show a.1 + 1 ≤ b.1 by exact hab)
      have h2 := (toPts w).1.sizeUpTo_succ' b
      have h3 := (toPts w).1.one_le_blocksFun b
      unfold endIdx; omega
    intro a b h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd h (hlt a b hab).ne
    · exact hab
    · exact absurd h (hlt b a hab).ne'
  refine ⟨hne, hinj, ?_⟩
  ext l
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hl, h1, hE⟩
    by_contra hno
    push_neg at hno
    apply hE
    rw [Formalism.MainNotions.BesselShellMomentBounds.ptMat_eq]
    refine Formalism.HermitianLatticeCounting.Final.ExpansionTerms.e4aVanish K (r + 1) _ _ l (by omega) fun p hp => ?_
    have hsz : ∀ p, (Formalism.MainNotions.BesselShellMomentBounds.toComp w).sizeUpTo p = (toPts w).1.sizeUpTo p := fun _ => rfl
    rw [hsz] at hp
    rcases Nat.lt_or_ge p ((toPts w).1.length + 1) with hpl | hpl
    · rcases Nat.eq_zero_or_pos p with h0 | hpos
      · subst h0; rw [Composition.sizeUpTo_zero] at hp; omega
      · exact hno ⟨p - 1, by omega⟩ (by
          show (toPts w).1.sizeUpTo (p - 1 + 1) = l
          rw [Nat.sub_add_cancel hpos, hp])
    · have hlen : 0 < (toPts w).1.length := (toPts w).1.length_pos_of_pos (Nat.succ_pos r)
      refine hno ⟨(toPts w).1.length - 1, by omega⟩ ?_
      show (toPts w).1.sizeUpTo ((toPts w).1.length - 1 + 1) = l
      rw [Nat.sub_add_cancel hlen, Composition.sizeUpTo_length, hp,
        Composition.sizeUpTo_ofLength_le _ _ (by omega)]
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have := (toPts w).1.sizeUpTo_le (a.1 + 1); show (toPts w).1.sizeUpTo (a.1 + 1) < r + 2; omega
    · have := (toPts w).1.sizeUpTo_succ' a
      have := (toPts w).1.one_le_blocksFun a
      show 1 ≤ (toPts w).1.sizeUpTo (a.1 + 1); omega
    · rw [← Formalism.L2.SG.NGCut.LeadingMinorIntegrality.endMin_eq]; exact hne a

theorem infinite_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

theorem modK_yP (D : D7) (Z : LocDat D) (p : PlF D) :
    (Z.M p).modK (algebraMap _ _ (Formalism.L2.SG.Pf.AtPt.yP Z p)) = (Z.M p).modK (algebraMap _ _ (Z.δ p)) := by
  obtain ⟨hmul, -, hone⟩ := GlobalTheory.ModuleUnits.modK_units (Z.M p) (Z.agree p).1
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.L2.SG.Pf.AtPt.yP Z p) =
      algebraMap _ _ (Z.δ p) * (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) := by
    unfold Formalism.L2.SG.Pf.AtPt.yP
    rw [map_mul, ← (D.s.atP p).compat, map_ratCast (algebraMap D.host.F D.host.E)]
  have hu : (D.s.atP p).ιE ((uP p : ℚ) : D.host.E) * (D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) = 1 := by
    rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [inv_mul_cancel₀ h0, map_one]
  have h1 : (Z.M p).modK ((D.s.atP p).ιE ((uP p : ℚ) : D.host.E)) = 1 := by
    refine hone _ (hO ▸ Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p) ⟨_, ?_, hu⟩
    rw [hO, map_natCast]; exact natCast_mem _ _
  have uδ : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)) := (Ne.isUnit (Z.agree p).2.1).map _
  have uu : IsUnit ((D.s.atP p).ιE ((uP p : ℚ) : D.host.E)) := IsUnit.of_mul_eq_one _ hu
  rw [e1, hmul _ _ uδ uu, h1, mul_one]

def sgnL (R : Type*) [CommRing R] (r l : ℕ) : R :=
  ∏ b ∈ Finset.univ.filter (fun b : Fin (r + 1) => b.val < l), (-1 : R) ^ (r - b.val)

theorem sgnL_sq (R : Type*) [CommRing R] (r l : ℕ) : sgnL R r l * sgnL R r l = 1 := by
  unfold sgnL
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun b _ => by rw [← mul_pow]; simp

theorem place_eq (D : D7) (Z : LocDat D) (p : PlF D) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS)
    {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (w : Point D.host.E (D.R.rS + 1)) (hZ : ZhatOM (ZhatL F F') = ptMat w)
    (hA : P.A.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame F a))
    (hB : P.B.f = fun b => frFac Z.δ p b • baseChange₂ D p (frame F' b)) (n n' : ℕ)
    (hAT : P.A.T = (n : (D.s.atP p).Fp)) (hBT : P.B.T = (n' : (D.s.atP p).Fp)) :
    (∀ l, l ≤ D.R.rS + 1 → P.Dm l = algebraMap _ _ ((Formalism.L2.SG.Pf.AtPt.yP Z p)⁻¹ ^ (l * (2 * D.R.rS + 1 - l))) *
      (D.s.atP p).ιE (sgnL D.host.E D.R.rS l * leadingPrincipalMinor (ptMat w) l)) ∧
    P.Gv = algebraMap _ _ ((Formalism.L2.SG.Pf.AtPt.yP Z p)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1))) *
      (D.s.atP p).ιE (GPt (n * n') (toPts w)) := by
  set x : (D.s.atP p).Ep := algebraMap _ _ (Formalism.L2.SG.Pf.AtPt.yP Z p)⁻¹ with hx
  have hZab : ∀ a b, ZhatL F F' a b = (-1) ^ (D.R.rS - b.val) * ptMat w a b := by
    intro a b
    have h := congrFun (congrFun hZ a) b
    simp only [ZhatOM] at h
    rw [← h, ← mul_assoc, ← mul_pow]; simp
  have hzl : (locH Z p).Zhat P.A.f P.B.f = Matrix.of fun a b : Fin (D.R.rS + 1) =>
      x ^ (D.R.rS - a.val) * ((D.s.atP p).ιE ((-1) ^ (D.R.rS - b.val)) * ((ptMat w).map (D.s.atP p).ιE) a b) * x ^ (D.R.rS - b.val) := by
    ext a b
    simp only [Loc.HermSp.Zhat, Matrix.of_apply, locH, locHerm, hA, hB, Matrix.map_apply]
    rw [Formalism.L2.SG.Pf.AtPt.localForm_smul, Z.hcj p, baseChangeAt_form Z.M p (Z.hcj p), Formalism.L2.SG.Pf.AtPt.frFac_eq,
      Formalism.L2.SG.Pf.AtPt.frFac_eq, Formalism.L2.SG.Pf.AtPt.cj_alg]
    have e : brS (VS D) (frame F' b) (frame F a) = ZhatL F F' a b := rfl
    rw [e, hZab, map_mul, hx, map_pow, map_pow]
    ring
  have hDm : ∀ l, l ≤ D.R.rS + 1 → P.Dm l = x ^ (l * (2 * D.R.rS + 1 - l)) *
      (D.s.atP p).ιE (sgnL D.host.E D.R.rS l * leadingPrincipalMinor (ptMat w) l) := by
    intro l hl
    have e1 : P.Dm l = leadingPrincipalMinor ((locH Z p).Zhat P.A.f P.B.f) l := by
      rw [← Formalism.MainNotions.BesselShellMomentBounds.leadMinorK_eq _ l hl]
      simp only [Formalism.MainNotions.S.LocNG.FPair.Dm, Loc.HermSp.Dl, dif_pos hl]
      rfl
    rw [e1, hzl, lead_scale_pow D.R.rS x _ _ l hl, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.leadingMinor_map, map_mul, sgnL, map_prod]
  refine ⟨fun l hl => by rw [hDm l hl, hx, map_pow], ?_⟩
  have hcjx : (Z.M p).L.cj x = x := by rw [hx, Z.hcj p]; exact Formalism.L2.SG.Pf.AtPt.cj_alg p _
  have hcjE : ∀ z, (Z.M p).L.cj ((D.s.atP p).ιE z) = (D.s.atP p).ιE (star z) := cj_iota (Z.hcj p)
  have hsg : ∀ l, ∃ k : ℕ, sgnL D.host.E D.R.rS l = (-1) ^ k := fun l =>
    ⟨_, Finset.prod_pow_eq_pow_sum _ _ _⟩
  have hs1 : ∀ l, sgnL D.host.E D.R.rS l * star (sgnL D.host.E D.R.rS l) = 1 := by
    intro l
    obtain ⟨k, hk⟩ := hsg l
    rw [hk, star_pow, star_neg, star_one, ← mul_pow]; simp
  have e1 : (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) = D.R.rS * (D.R.rS + 1) := by
    rw [show 2 * D.R.rS + 1 - (D.R.rS + 1) = D.R.rS by omega]; ring
  have e2 : D.R.rS * (2 * D.R.rS + 1 - D.R.rS) = D.R.rS * (D.R.rS + 1) := by
    rw [show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega]
  have hG : P.Gv = P.Dm (D.R.rS + 1) * (Z.M p).L.cj (P.Dm (D.R.rS + 1)) -
      algebraMap _ _ (P.A.T * P.B.T) * (P.Dm D.R.rS * (Z.M p).L.cj (P.Dm D.R.rS)) := rfl
  rw [hG, hDm _ le_rfl, hDm _ (Nat.le_succ _), e1, e2, ← Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dlast_eq,
    ← Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dr_eq, hAT, hBT]
  have hxa : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Formalism.L2.SG.Pf.AtPt.yP Z p)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1))) =
      x ^ (2 * D.R.rS * (D.R.rS + 1)) := by rw [hx, map_pow]
  rw [hxa]
  unfold GPt
  simp only [map_mul, map_pow, hcjx, hcjE, star_mul, map_sub, map_natCast, Nat.cast_mul]
  have h1 := hs1 (D.R.rS + 1)
  have h2 := hs1 D.R.rS
  have h1' : (D.s.atP p).ιE (sgnL D.host.E D.R.rS (D.R.rS + 1)) * (D.s.atP p).ιE (star (sgnL D.host.E D.R.rS (D.R.rS + 1))) = 1 := by
    rw [← map_mul, h1, map_one]
  have h2' : (D.s.atP p).ιE (sgnL D.host.E D.R.rS D.R.rS) * (D.s.atP p).ιE (star (sgnL D.host.E D.R.rS D.R.rS)) = 1 := by
    rw [← map_mul, h2, map_one]
  have e3 : 2 * D.R.rS * (D.R.rS + 1) = D.R.rS * (D.R.rS + 1) + D.R.rS * (D.R.rS + 1) := by ring
  rw [e3, pow_add]
  linear_combination (x ^ (D.R.rS * (D.R.rS + 1)) * x ^ (D.R.rS * (D.R.rS + 1)) *
      (D.s.atP p).ιE (DlastPt (toPts w)) * (D.s.atP p).ιE (star (DlastPt (toPts w)))) * h1' -
    (x ^ (D.R.rS * (D.R.rS + 1)) * x ^ (D.R.rS * (D.R.rS + 1)) * ((n : (D.s.atP p).Ep) * n') *
      (D.s.atP p).ιE (DrPt (toPts w)) * (D.s.atP p).ιE (star (DrPt (toPts w)))) * h2'

theorem htPlace : Formalism.L2.SG.NGHTie.HTPlace := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ Cl' Nu TS cls nml γ Fm hT => ?_⟩
  obtain ⟨w, F00, F'0, F'1, hγ, -, -, -, hZ, hloc, -, hPr, -⟩ := hT
  subst hγ
  obtain ⟨hEnd0, hInj, hEnds⟩ := point_ends w
  have hpl : ∀ p, _ := fun p => place_eq D (Formalism.L2.SG.NGLocModel.zOf Y) p (Fm.FP p) F00 F'0 w hZ (hloc p).1 (hloc p).2.1 _ _
    (hloc p).2.2.1 (hloc p).2.2.2
  have hιu : ∀ p (z : D.host.E), z ≠ 0 → IsUnit ((D.s.atP p).ιE z) := fun p z hz => (Ne.isUnit hz).map _
  have hG : GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts w) ≠ 0 := by
    haveI := infinite_places D.host.F
    obtain ⟨p, hp⟩ : ∃ p : PlF D, p ∉ Fm.P := Infinite.exists_notMem_finset Fm.P
    obtain ⟨-, y, -, hy⟩ := (hPr p hp).2.1
    intro h0
    rw [(hpl p).2, h0, map_zero, mul_zero, zero_mul] at hy
    exact zero_ne_one hy
  refine ⟨⟨hG, hEnd0⟩, fun p => ?_⟩
  obtain ⟨hDm, hGv⟩ := hpl p
  obtain ⟨hmul, -, hone⟩ := GlobalTheory.ModuleUnits.modK_units _ ((Formalism.L2.SG.NGLocModel.zOf Y).agree p).1
  have he : Formalism.L2.SG.Pf.AtPt.yP (Formalism.L2.SG.NGLocModel.zOf Y) p ≠ 0 := Formalism.L2.SG.Pf.AtPt.yP_ne _ p
  have hsu : ∀ l, IsUnit ((D.s.atP p).ιE (sgnL D.host.E D.R.rS l)) := fun l =>
    (IsUnit.of_mul_eq_one _ (sgnL_sq D.host.E D.R.rS l)).map _
  have hxu : ∀ k : ℕ, IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
      ((Formalism.L2.SG.Pf.AtPt.yP (Formalism.L2.SG.NGLocModel.zOf Y) p)⁻¹ ^ k)) := fun k =>
    (Ne.isUnit (pow_ne_zero _ (inv_ne_zero he))).map _
  have hGv0 : (Fm.FP p).Gv ≠ 0 := by
    rw [hGv]; exact ((hxu _).mul (hιu p _ hG)).ne_zero
  have hEndsP : (Fm.FP p).ends = Finset.univ.image (endIdx (toPts w)) := by
    have key : ∀ l ∈ Finset.range (D.R.rS + 2), (1 ≤ l ∧ IsUnit ((Fm.FP p).Dm l)) ↔
        (1 ≤ l ∧ leadingPrincipalMinor (ptMat w) l ≠ 0) := by
      intro l hl
      rw [Finset.mem_range] at hl
      constructor
      · rintro ⟨h1, hu⟩
        refine ⟨h1, fun h0 => ?_⟩
        rw [hDm l (by omega), h0, mul_zero, map_zero, mul_zero] at hu
        exact not_isUnit_zero hu
      · rintro ⟨h1, hne⟩
        refine ⟨h1, ?_⟩
        rw [hDm l (by omega), map_mul]
        exact (hxu _).mul ((hsu l).mul (hιu p _ hne))
    rw [← hEnds]
    unfold Formalism.MainNotions.S.LocNG.FPair.ends
    convert Finset.filter_congr key
  obtain ⟨hP1, hP2⟩ := GlobalTheory.local_height_scaling _ ((Formalism.L2.SG.NGLocModel.zOf Y).agree p).1
    (locH (Formalism.L2.SG.NGLocModel.zOf Y) p) D.R.rS (Fm.FP p) hGv0 _ he _
    (fun l => (D.s.atP p).ιE (sgnL D.host.E D.R.rS l * leadingPrincipalMinor (ptMat w) l)) hGv
    (fun l hl => hDm l (by
      rw [hEndsP, Finset.mem_image] at hl
      obtain ⟨a, -, rfl⟩ := hl
      exact (toPts w).1.sizeUpTo_le _))
  refine ⟨hP1, hP2.trans ?_⟩
  have hs1 : ∀ l, ((Formalism.L2.SG.NGLocModel.zOf Y).M p).modK ((D.s.atP p).ιE (sgnL D.host.E D.R.rS l)) = 1 := by
    intro l
    have hO : ((Formalism.L2.SG.NGLocModel.zOf Y).M p).L.O = (D.s.atP p).O :=
      ((Formalism.L2.SG.NGLocModel.zOf Y).agree p).2.2.2.1
    have hm : (D.s.atP p).ιE (sgnL D.host.E D.R.rS l) ∈ ((Formalism.L2.SG.NGLocModel.zOf Y).M p).L.O := by
      unfold sgnL
      rw [map_prod]
      refine Subring.prod_mem _ fun b _ => ?_
      rw [map_pow, map_neg, map_one]
      exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
    refine hone _ hm ⟨_, hm, ?_⟩
    rw [← map_mul, sgnL_sq, map_one]
  rw [modK_yP, hEndsP, Finset.sum_image (fun a _ b _ h => hInj h), Finset.prod_image (fun a _ b _ h => hInj h)]
  congr 3
  funext a
  have h0 := hEnd0 a
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.endMin_eq] at h0 ⊢
  rw [map_mul, hmul _ _ (hsu _) (hιu p _ h0), hs1, one_mul]

end GlobalTheory.HTPlaceLeaf
