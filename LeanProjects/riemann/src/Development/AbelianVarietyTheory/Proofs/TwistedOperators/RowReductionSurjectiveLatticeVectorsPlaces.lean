import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.RowOnto

open GlobalTheory.LiftLevel GlobalTheory.LiftDat

variable {D : D7}

theorem partAt_mem_hatA' (S T : HSp D) (I : Ideal (𝓞 D.host.E)) (L : Lt D.host.E T.rank) (w : AE D)
    (hw : finPart D w ∈ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ I ∧
      y = a ⊗ₜ[D.host.F] (x : D.host.E)})
    {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) L)) :
    partAt w u ∈ hatA S T (tens (stdL D.host.E S.rank) (I • L)) := by
  let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun u => partAt w u)
    fun x y => Matrix.ext fun i j => mul_add w (x i j) (y i j)
  have main : hatA S T (tens (stdL D.host.E S.rank) L) ≤
      (hatA S T (tens (stdL D.host.E S.rank) (I • L))).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, y, hy, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ WO S T := AddMonoidHom.mk'
      (fun z => Matrix.of fun a k => GlobalTheory.LatticeStable.liftMul D (α ⊗ₜ[D.host.F] y k a) z)
      fun z z' => Matrix.ext fun a k => (GlobalTheory.LatticeStable.liftMul D _).map_add z z'
    have hle : AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ I ∧
        y = a ⊗ₜ[D.host.F] (x : D.host.E)} ≤ (hatA S T (tens (stdL D.host.E S.rank) (I • L))).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, ho, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, (o : D.host.E) • y, ?_, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
        intro k
        have := Submodule.smul_mem_smul ho (hy k)
        exact this
      · ext a k
        change GlobalTheory.LatticeStable.liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] y k a)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul]
        simp [Matrix.smul_apply]
    have e : Ψ (Matrix.of fun a k => pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a) = Φ (finPart D w) :=
      Matrix.ext fun a k => GlobalTheory.LatticeStable.mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hu

theorem nsmul_mem_hatA' (S T : HSp D) {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ 𝔪)
    (L : Lt D.host.E T.rank) {u : WO S T} (hu : u ∈ hatA S T (tens (stdL D.host.E S.rank) L)) :
    N • u ∈ hatA S T (tens (stdL D.host.E S.rank) (𝔪 • L)) := by
  have main : hatA S T (tens (stdL D.host.E S.rank) L) ≤
      (hatA S T (tens (stdL D.host.E S.rank) (𝔪 • L))).comap (nsmulAddMonoidHom N) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, N • y, ?_, ?_⟩
    · rw [GlobalTheory.SW.TensLat.mem_tens_stdL] at hy ⊢
      intro k
      have := Submodule.smul_mem_smul hN (hy k)
      rwa [Nat.cast_smul_eq_nsmul] at this
    · ext a k
      change N • (pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (N • y k a)
      exact (map_nsmul (TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 α)) N (y k a)).symm
  exact main hu

theorem intAE_le_top' : intAE D ≤ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E,
    x ∈ (⊤ : Ideal (𝓞 D.host.E)) ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)} :=
  (AddSubgroup.closure_le _).2 (by
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, x, Submodule.mem_top, rfl⟩)

theorem adjA_add (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D)
    (x y : WO S T) : adjA S T βS βT a (x + y) = adjA S T βS βT a x + adjA S T βS βT a y := by
  unfold adjA
  rw [GlobalTheory.PlaceVec.frMapAdj_add, Matrix.mul_add, smul_add]

theorem redM_sub (PP : Formalism.L2.DIV.Pl D.host.E) {b c : ℕ} {N M : Matrix (Fin b) (Fin c) (EAf D)}
    (hN : IsIntM N) (hM : IsIntM M) : redM PP (N - M) = redM PP N - redM PP M := by
  funext i j
  have h1 : (N - M) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := sub_mem (hN i j) (hM i j)
  show (if h : (N - M) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then
      Formalism.L2.DIV.resS D.host.F PP ⟨(N - M) i j, h⟩ else 0) =
    (if h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨N i j, h⟩ else 0) -
    (if h : M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨M i j, h⟩ else 0)
  rw [dif_pos h1, dif_pos (hN i j), dif_pos (hM i j), ← (Formalism.L2.DIV.resS D.host.F PP).map_sub]
  rfl

theorem redM_congr (PP : Formalism.L2.DIV.Pl D.host.E) {b c b' c' : ℕ} (N : Matrix (Fin b) (Fin c) (EAf D))
    (N' : Matrix (Fin b') (Fin c') (EAf D)) (i i' j j') (h : N i j = N' i' j') :
    redM PP N i j = redM PP N' i' j' := by
  simp only [redM, h]

end GlobalTheory.RowOnto

namespace GlobalTheory.RowOnto

open GlobalTheory.LiftLevel GlobalTheory.LiftDat

variable {D : D7}

theorem partAt_add' {S T : HSp D} (c : AE D) (w w' : WO S T) :
    partAt c (w + w') = partAt c w + partAt c w' :=
  Matrix.ext fun i j => mul_add c (w i j) (w' i j)

theorem partAt_of_isHalf' {S T : HSp D} {c : AE D} {w : WO S T} (h : IsHalf c w) : partAt c w = w :=
  Matrix.ext fun i j => h i j

theorem fullStd' (n : ℕ) : (stdL D.host.E n).FG ∧
    Submodule.span D.host.E (stdL D.host.E n : Set (Fin n → D.host.E)) = ⊤ := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [stdL, Submodule.span_span_of_tower]
  convert (Pi.basisFun D.host.E (Fin n)).span_eq
  simp

theorem adjA_finW_row (S T : HSp D) (hS : S.gram = 1) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E)
    (i : Fin S.rank) (j : Fin T.rank) :
    adjA S T βS βT a (partAt (cA D e) (finW S T y)) i j = rowAdj T βT a e (y i) 0 j := by
  have key : ∀ w : WO S T, βS.val * frMapAdj S T βS βT w =
      ((((w : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose * T.gram.map (incA D)).map (toEAf D)) *
        βT.val := by
    intro w
    unfold frMapAdj
    rw [hS, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, βS.mul_inv, Matrix.one_mul]
  unfold adjA rowAdj
  rw [key]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply]
  rfl

end GlobalTheory.RowOnto

namespace GlobalTheory.RowOnto

open GlobalTheory.LiftLevel GlobalTheory.LiftDat

variable {D : D7}

set_option maxHeartbeats 3000000 in

theorem exists_row {S T : HSp D} (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e (Pg ∪ Q))
    (i0 : Fin S.rank) (t : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin T.rank → Formalism.L2.DIV.kP PP) :
    ∃ R : Matrix (Fin S.rank) (Fin T.rank) (EAf D), IsIntM R ∧ (∀ i j, toEAf D e * R i j = R i j) ∧
      ∀ PP ∈ Pg ∪ Q, ∀ j, redM PP R i0 j = t PP j := by
  have he2 : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, hes1, -⟩, -⟩ := he
  have hk : ∀ PP ∈ Pg ∪ Q, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes1 PP hPP)).1
  have hdel : ∀ PP ∈ Pg ∪ Q, ∀ PP' (hPP' : PP' ∈ Pg ∪ Q),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes1 PP hPP).1 (hes1 PP' hPP').1).resolve_left fun h => by
          have h' := hes1 PP' hPP'
          rw [← h] at h'
          exact hne (GlobalTheory.PlaceVec.isIdemAt_inj (hes1 PP hPP) h')
      have h4' : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) *
          ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4'
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (hes1 PP hPP)).2, one_mul] at h5
  choose c hc using fun (PP : Formalism.L2.DIV.Pl D.host.E) (j : Fin T.rank) =>
    Ideal.Quotient.mk_surjective (I := PP.asIdeal) (t PP j)
  let r0 : Fin S.rank → Fin T.rank → Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    if i = i0 then ⟨toEAf D e, hi⟩ * ∑ PP ∈ (Pg ∪ Q).attach,
      ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (c PP.1 j) else 0
  let R : Matrix (Fin S.rank) (Fin T.rank) (EAf D) := fun i j => (r0 i j : EAf D)
  have hRint : IsIntM R := fun i j => (r0 i j).2
  have hRe : ∀ i j, toEAf D e * R i j = R i j := by
    intro i j
    show toEAf D e * (r0 i j : EAf D) = (r0 i j : EAf D)
    by_cases h : i = i0
    · simp only [r0, if_pos h]
      rw [Subring.coe_mul, ← mul_assoc]
      change toEAf D e * toEAf D e * _ = toEAf D e * _
      rw [← map_mul, he2]
    · simp only [r0, if_neg h, ZeroMemClass.coe_zero, mul_zero]
  have hRred : ∀ PP ∈ Pg ∪ Q, ∀ j, redM PP R i0 j = t PP j := by
    intro PP hPP j
    show (if h : R i0 j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then
      Formalism.L2.DIV.resS D.host.F PP ⟨R i0 j, h⟩ else 0) = _
    rw [dif_pos (hRint i0 j)]
    have hr : (⟨R i0 j, hRint i0 j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = r0 i0 j := rfl
    rw [hr]
    simp only [r0, if_pos rfl]
    rw [map_mul, hres PP hPP, one_mul, map_sum]
    simp_rw [map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single ⟨PP, hPP⟩]
    · rw [hdel PP hPP PP hPP, if_pos rfl, one_mul, hc]
    · intro b' _ hb'
      rw [hdel PP hPP b'.1 b'.2, if_neg (fun h => hb' (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h
  exact ⟨R, hRint, hRe, hRred⟩

set_option maxHeartbeats 3000000 in

theorem rowReduction_surjective_over_adelicFrames {S T : HSp D} (C : Ctx S T) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e (Pg ∪ Q)) (a b : AE D) (hb : a * b = e)
    (hgen : IsGen C βS βT Pg Q e a) (h2' : liftI Pg Q ≠ ⊥) (hT : T.rank ≠ 0) (hn : T.rank ≤ S.rank)
    (t : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin T.rank → Formalism.L2.DIV.kP PP) :
    ∃ v ∈ C.X.Λ, ∀ PP ∈ Pg ∪ Q, rowRed T βT a e PP v = t PP := by
  have hS : 0 < S.rank := by omega
  have he2 : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨R, hRint, hRe, hRred⟩ := exists_row (S := S) Pg Q e he ⟨0, hS⟩ t
  obtain ⟨x, hxh, hx⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj S T βS βT he2 ((βS⁻¹).val * (toEAf D b • R))
  have hadj : adjA S T βS βT a x = R := by
    unfold adjA
    rw [hx, Matrix.mul_smul, ← Matrix.mul_assoc, βS.mul_inv, Matrix.one_mul]
    ext i j
    change toEAf D a * (toEAf D e * (toEAf D b * R i j)) = R i j
    rw [mul_left_comm, ← mul_assoc (toEAf D a), ← map_mul, hb, hRe, hRe]
  have hxA := ((hgen x hxh).1).1 (hadj ▸ hRint)
  obtain ⟨-, -, hst, -⟩ := HatLat.hatA_tens D S T C (stdL D.host.E S.rank) C.X.Λ (fullStd' S.rank)
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have hM0 : 0 < Ideal.absNorm (liftI Pg Q) := Nat.pos_of_ne_zero fun h => h2' (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨y, hy, u', hu', hxu⟩ := (hst x hxA).2 _ hM0
  have hz := nsmul_mem_hatA' S T (Ideal.absNorm_mem (liftI Pg Q)) C.X.Λ hu'
  have hc2 : cA D e * cA D e = cA D e := by rw [← map_mul, he2]
  have hcI := intAE_le_top' (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D (cA D e)) (by rw [← map_mul, hc2]))
  have hpz : partAt (cA D e) (Ideal.absNorm (liftI Pg Q) • u') ∈
      hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)) := by
    have := partAt_mem_hatA' S T ⊤ _ (cA D e) hcI hz
    rwa [Submodule.top_smul] at this
  have hpzh : IsHalf (cA D e) (partAt (cA D e) (Ideal.absNorm (liftI Pg Q) • u')) :=
    fun i j => by simp only [partAt, Matrix.map_apply, ← mul_assoc, hc2]
  obtain ⟨hzint, hzred⟩ := ((hgen _ hpzh).2).2 hpz
  have hsplit : adjA S T βS βT a (partAt (cA D e) (finW S T y)) =
      R - adjA S T βS βT a (partAt (cA D e) (Ideal.absNorm (liftI Pg Q) • u')) := by
    rw [eq_sub_iff_add_eq, ← adjA_add, ← partAt_add', ← hxu, partAt_of_isHalf' hxh, hadj]
  refine ⟨y ⟨0, hS⟩, (GlobalTheory.SW.TensLat.mem_tens_stdL _ _).1 hy ⟨0, hS⟩, fun PP hPP => funext fun j => ?_⟩
  show redM PP (rowAdj T βT a e (y ⟨0, hS⟩)) 0 j = t PP j
  rw [redM_congr PP _ (adjA S T βS βT a (partAt (cA D e) (finW S T y))) 0 ⟨0, hS⟩ j j
    (adjA_finW_row S T C.m.gS βS βT a e y ⟨0, hS⟩ j).symm, hsplit, redM_sub PP hRint hzint, hzred PP hPP,
    Matrix.sub_apply, Matrix.zero_apply, sub_zero, hRred PP hPP j]

theorem rowRed_onto : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ t : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin T.rank → Formalism.L2.DIV.kP PP, ∃ v ∈ C.X.Λ, ∀ PP ∈ Pg ∪ Q, GlobalTheory.LiftDat.rowRed T βT a e PP v = t PP := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ hab hmov hgen h1 h2' h3 h4 t
  by_cases hT : T.rank = 0
  · exact ⟨0, zero_mem _, fun PP _ => funext fun j => absurd j.2 (by omega)⟩
  obtain ⟨b, hb⟩ := hab
  exact rowReduction_surjective_over_adelicFrames C βS βT Pg Q e he a b hb hgen h2' hT hn t

end GlobalTheory.RowOnto

end
