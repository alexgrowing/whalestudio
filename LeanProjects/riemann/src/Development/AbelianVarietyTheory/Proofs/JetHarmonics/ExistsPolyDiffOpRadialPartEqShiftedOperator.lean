import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EventuallyLevelPointMemOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLTorus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylCellRange.ReflectionMultiplicationOnBigCell
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftOfSmoothComm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CellMulExp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts

namespace GlobalTheory.HatNF.TodaLift

open Matrix Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.Q Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 GlobalTheory.HatNF.CellRules

noncomputable section

theorem qminor_commute {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (x : A)
    (a b : Fin t → Fin n) (u : ℂ) (h : ∀ i j : Fin t, Commute (E (a i) (b j)) x) : Commute (qminor E a b u) x := by
  have hT : ∀ (v : ℂ) (i j : Fin t), Commute (Tm E v (a i) (b j)) x := by
    intro v i j
    unfold Tm
    refine Commute.add_left ?_ (h i j)
    split_ifs
    · exact Algebra.commutes v x
    · exact Commute.zero_left x
  unfold qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine (Int.cast_commute _ x).mul_left (Commute.list_prod_left _ _ fun y hy => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
  exact hT _ _ i

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

theorem leftEq_adjoin (z : Fin (2 * r + k + 1) → ℂ) (hD : IsOpen D)
    (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (x : LevelPointCoordinates.SB E hD) :
    ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D (((x : Module.End ℂ (VS k r 0 D E)) v : VS k r 0 D E) : Mx k r → E) := by
  obtain ⟨x, hx⟩ := x
  show ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D ((x v : VS k r 0 D E) : Mx k r → E)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hy
    intro v hv g hg n hn
    have h := (generator_action_preserved E k r z 0 D (PBG.c0 p) (PBG.c0 q) v v 0 hD v.2.1 v.2.1).2.1 hDN hv g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Qx3.glev_mul hn.2 hg.1, hDN g hg n hn⟩
    show ((Eh hD _ _ v : VS k r 0 D E) : Mx k r → E) _ = _ • ((Eh hD _ _ v : VS k r 0 D E) : Mx k r → E) _
    rw [ev_E hD _ _ v hng, ev_E hD _ _ v hg, h]
  | algebraMap c =>
    intro v hv g hg n hn
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg n hn, smul_comm]
  | add y1 y2 _ _ h1 h2 =>
    intro v hv g hg n hn
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h1 v hv g hg n hn, h2 v hv g hg n hn, smul_add]
  | mul y1 y2 _ _ h1 h2 =>
    intro v hv
    exact h1 _ (h2 v hv)

def ap (hD : IsOpen D) (J : Mx k r → E) (hS : SmoothLev k r 0 D J) (x : LevelPointCoordinates.SB E hD) : Mx k r → E :=
  (((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS) : VS k r 0 D E) : Mx k r → E)

def mn (hD : IsOpen D) (Y : ℂ) (m : ℕ) (hm : m ≤ r) : LevelPointCoordinates.SB E hD :=
  qminor (LevelPointCoordinates.EB hD) (C3.xR k r m hm) (C3.xR k r m hm) (Y + ((2 * r + k : ℕ) : ℂ) / 2)

variable {g : Mx k r} {c : Fin r → ℂ}

theorem res_ap_one (hD : IsOpen D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) :
    resG k r (Fin.last r) (ap hD J hS 1) c g = resG k r (Fin.last r) J c g := by
  unfold resG
  congr 1
  exact cut_of_mem J ⟨cell_mem hg hc, hx⟩

theorem res_ap_torus (hD : IsOpen D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (Y : ℂ) (a : Fin r) (x : LevelPointCoordinates.SB E hD) :
    resG k r (Fin.last r)
        (ap hD J hS (Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (a.val : ℂ)) (eI k r a) (eI k r a) * x)) c g =
      Y • resG k r (Fin.last r) (ap hD J hS x) c g + pOp a (fun c' => resG k r (Fin.last r) (ap hD J hS x) c' g) c := by
  have hxG : wCell k r (Fin.last r) c * g ∈ Glev k r 0 ∩ D := ⟨cell_mem hg hc, hx⟩
  rw [torus_rule (Ψ := ap hD J hS x) ((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS)).2.1 hg hc hx a]
  have e : ap hD J hS (Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (a.val : ℂ)) (eI k r a) (eI k r a) * x)
      (wCell k r (Fin.last r) c * g) =
      (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (a.val : ℂ)) • ap hD J hS x (wCell k r (Fin.last r) c * g) +
        EH k r (eI k r a) (eI k r a) (ap hD J hS x) (wCell k r (Fin.last r) c * g) := by
    have h := ev_E hD (PBG.c0 (eI k r a)) (PBG.c0 (eI k r a))
      ((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS)) hxG
    rw [PBG.position_level_zero_coord] at h
    unfold ap
    rw [← h, Tm, if_pos rfl, add_mul, ← Algebra.smul_def]
    rfl
  simp only [resG, e]
  push_cast
  module

theorem mn_zero (hD : IsOpen D) (Y : ℂ) : mn (E := E) hD Y 0 (Nat.zero_le r) = 1 := by
  simp [mn, qminor]

theorem mn_one (hD : IsOpen D) (Y : ℂ) (h : 1 ≤ r) : mn (E := E) hD Y 1 h =
    Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - (((⟨0, h⟩ : Fin r).val : ℕ) : ℂ)) (eI k r ⟨0, h⟩) (eI k r ⟨0, h⟩) *
      mn hD Y 0 (Nat.zero_le r) := by
  rw [mn_zero, mul_one]
  simp [mn, qminor, C3.xR]
  rfl

theorem res_mn_succ {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hD : IsOpen D)
    (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J)
    (hL : LeftEq k r z 0 D J) (hR : RightEq k r z' 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (Y : ℂ) (m : ℕ) (hm : m + 2 ≤ r) :
    resG k r (Fin.last r) (ap hD J hS (mn hD Y (m + 2) hm)) c g =
      Y • resG k r (Fin.last r) (ap hD J hS (mn hD Y (m + 1) (by omega))) c g +
        pOp ⟨m + 1, by omega⟩ (fun c' => resG k r (Fin.last r) (ap hD J hS (mn hD Y (m + 1) (by omega))) c' g) c -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • resG k r (Fin.last r) (ap hD J hS (mn hD Y m (by omega))) c g := by
  have hxG : wCell k r (Fin.last r) c * g ∈ Glev k r 0 ∩ D := ⟨cell_mem hg hc, hx⟩
  have hN : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Nlev k r 0 := fun n hn => ⟨hn, SingleEntryHermitianProducts.glev0 hn.1⟩
  have hRr : ∀ g ∈ Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → EH k r p q J g = C3.dpsiP k r z' p q • J g :=
    fun g hg p q hpq => rule_of_eq E k r z' J g hz' (fun n hn => hR g hg n (hN n hn)) p q hpq
  let La' : LevelPointCoordinates.SB E hD →ₗ[ℂ] E :=
    (PBG.La hD J hS (wCell k r (Fin.last r) c * g)).comp (LevelPointCoordinates.SB E hD).val.toLinearMap
  have hLa' : ∀ x, La' x = ap hD J hS x (wCell k r (Fin.last r) c * g) := fun x => rfl
  have hRR : C3.RightRuleFn k r z' (LevelPointCoordinates.EB hD) La' := fun x p q hpq =>
    PBG.La_rule hD z' J hS hRr _ x.1 p q hpq
  have hvK : LeftEq k r z 0 D (PBG.vK hD J hS : Mx k r → E) := by
    intro g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Qx3.glev_mul hn.2 hg.1, hDN g hg n hn⟩
    show cut k r 0 D J _ = _ • cut k r 0 D J g
    rw [cut_of_mem J hng, cut_of_mem J hg, hL g hg n hn]
  have hLL : C3.LeftRuleBig k r c (LevelPointCoordinates.EB hD) La' := by
    intro x a b hab
    rw [hLa', hLa', ← left_rule hz hg hc (ap hD J hS x)
      (fun n hn => leftEq_adjoin z hD hDN x _ hvK _ hxG n (hN n hn)) hab]
    have h := ev_E hD (PBG.c0 (eI k r a)) (PBG.c0 (eI k r b))
      ((x : Module.End ℂ (VS k r 0 D E)) (PBG.vK hD J hS)) hxG
    rw [PBG.position_level_zero_coord, PBG.position_level_zero_coord] at h
    exact h
  have hch := chain_first_identity (LevelPointCoordinates.SB E hD) E k r z' c (LevelPointCoordinates.EB hD) La' (LevelPointCoordinates.EB_gl hD) hc hRR hLL m hm
    (Y + ((2 * r + k : ℕ) : ℂ) / 2)
  have hcomm : Commute (mn (E := E) hD Y (m + 1) (by omega))
      (Tm (LevelPointCoordinates.EB hD) (Y + ((2 * r + k : ℕ) : ℂ) / 2 - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩)
        (eI k r ⟨m + 1, by omega⟩)) := by
    unfold Tm
    rw [if_pos rfl]
    refine Commute.add_right (Algebra.commutes _ _).symm (qminor_commute _ _ _ _ _ fun i j => ?_)
    have hi := i.isLt
    have hj := j.isLt
    have h := LevelPointCoordinates.EB_gl (E := E) hD (C3.xR k r (m + 1) (by omega) i) (C3.xR k r (m + 1) (by omega) j)
      (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)
    rw [if_neg (by simp only [C3.xR, Fin.ext_iff, eI_val, Fin.val_castLE]; omega),
      if_neg (by simp only [C3.xR, Fin.ext_iff, eI_val, Fin.val_castLE]; omega), sub_zero, sub_eq_zero] at h
    exact h
  rw [← res_ap_torus hD hS hg hc hx Y ⟨m + 1, by omega⟩, ← hcomm.eq]
  simp only [resG, ← hLa']
  rw [smul_comm (c _ / c _), ← smul_sub]
  congr 1

theorem res_AAop (hD : IsOpen D) {J : Mx k r → E} (hS : SmoothLev k r 0 D J) (hg : g ∈ Glev k r (Fin.last r))
    (hc : c ∈ OmX r) (hx : wCell k r (Fin.last r) c * g ∈ D) (Y : ℂ) :
    resG k r (Fin.last r) (C3.AAop k r r le_rfl (Y + ((2 * r + k : ℕ) : ℂ) / 2) J) c g =
      (∏ a, c a) • resG k r (Fin.last r) (ap hD J hS (mn hD Y r le_rfl)) c g := by
  have hxG : wCell k r (Fin.last r) c * g ∈ Glev k r 0 ∩ D := ⟨cell_mem hg hc, hx⟩
  have hxi : ∀ a p, PBG.xi0 (wCell k r (Fin.last r) c * g) a p = if eI k r a = p then c a else 0 := by
    intro a p
    rw [← row_es hg]
    simp [PBG.xi0, herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Qx3.hpk_row_e]
  simp only [resG]
  rw [smul_comm (∏ a, c a), ← PBG.La_AAx hD J hS _ hxG,
    SignAntidiagonal.AAx_head k r _ _ r le_rfl (Matrix.diagonal c) _ ?_ ?_, map_smul, Matrix.det_diagonal]
  · congr 2
    unfold ap mn
    have := PBN.MC.map_qminor (LevelPointCoordinates.SB E hD).val (LevelPointCoordinates.EB hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (Y + ((2 * r + k : ℕ) : ℂ) / 2)
    show _ = (((LevelPointCoordinates.SB E hD).val _ (PBG.vK hD J hS) : VS k r 0 D E) : Mx k r → E) _
    rw [this]
    rfl
  · intro a p ha hp
    rw [hxi, if_neg]
    rintro rfl
    rw [eI_val] at hp; omega
  · intro a b
    rw [hxi, Matrix.diagonal_apply]
    simp [C3.xR, Fin.ext_iff, eI_val]

theorem isPolyDeg_pluecker (κ : ℕ) (hκ : r ≤ κ) (b : Fin r → Fin (2 * r + k + 1)) :
    U.IsPolyDeg κ fun g : B.Mat k r => (Matrix.of fun a l : Fin r =>
      herm (Hpk k r) (g *ᵥ bvec (b l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det := by
  refine ⟨(Matrix.of fun a l : Fin r => MvPolynomial.X (Sum.inl (esI k r a, b l))).det, ?_, fun g => ?_⟩
  · rw [Matrix.det_apply]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
    refine (MvPolynomial.totalDegree_smul_le _ _).trans ((MvPolynomial.totalDegree_finset_prod _ _).trans ?_)
    simpa [MvPolynomial.totalDegree_X] using hκ
  · rw [RingHom.map_det]
    refine congrArg Matrix.det ?_
    ext a l
    simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Qx3.hpk_row_e]

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem exists_polyOp_AAop (k r o κ : ℕ) (ho : r ≤ o) (hκ : r ≤ κ) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, CutMP.PolyOp o κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r,
      ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F →
        B.opApply Θ F g = C3.AAop k r r le_rfl u F g := by
  classical
  obtain ⟨Θ, hΘ, he⟩ := GlobalTheory.HatNF.MinorPoly.minor_polyOp Wp Wq k r r κ (Fin r → Fin (2 * r + k + 1)) (fun _ => C3.xR k r r le_rfl)
    (fun b => b) u (fun b g => if StrictMono b then (Matrix.of fun a l : Fin r =>
      herm (Hpk k r) (g *ᵥ bvec (b l)) (bvec (eI k r (Fin.castLE le_rfl a)))).det else 0) (fun b => by
      by_cases hb : StrictMono b
      · simp only [if_pos hb]; exact isPolyDeg_pluecker κ hκ b
      · simp only [if_neg hb]; exact ⟨0, by simp, fun g => by simp⟩)
  refine ⟨Θ, fun T hT => ⟨(hΘ T hT).1.trans ho, (hΘ T hT).2⟩, fun F g hg V hV hgV hF => ?_⟩
  rw [he F g hg V hV hgV hF]
  unfold C3.AAop
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rfl
  · rw [zero_smul]

variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

omit [FiniteDimensional ℂ Wp] in
theorem pref_succ (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Y : ℂ) (n : ℕ) (hn : n < r) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r) :
    ((JCx2.rma_pref L Y (n + 1) 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
        Y • ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g +
          pOp ⟨n, hn⟩ (fun c' => ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c -
          c ⟨n, hn⟩ • ((JCx2.rma_pref L Y n 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g ∧
      ((JCx2.rma_pref L Y (n + 1) 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
        (c ⟨n, hn⟩)⁻¹ • ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  have key : ∀ a : Fin 2, ((JCx2.rma_pref L Y (n + 1) a 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) =
      TL k ⟨n, hn⟩ Y a 0 ((JCx2.rma_pref L Y n 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) +
        TL k ⟨n, hn⟩ Y a 1 ((JCx2.rma_pref L Y n 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) := by
    intro a
    rw [← JCx2.rma_T_fst X L hL, ← JCx2.rma_T_fst X L hL, JCx2.rma_pref, dif_pos hn, Matrix.mul_apply,
      Fin.sum_univ_two]
    rfl
  rw [key, key]
  simp [TL, crd, Tmat, cOp, ciOp, sub_eq_add_neg]

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem prod_c_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (c : Fin r → ℂ) (g : Mx k r) (l : List (Fin r)) (Ψ : RadSp k r z z' π π') :
    (((l.map L.c).prod).1 Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = (l.map c).prod • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_smul]; rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_smul, ← ih, hL.2.2.1 a]
    show (X.op a 1 (((l.map L.c).prod).1 Ψ) : Fn k r (Wq →L[ℂ] Wp)) c g = _
    rw [X.op_apply]
    rfl

omit [FiniteDimensional ℂ Wp] in

theorem ahat_apply (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π')
    (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (hL : IsActualLevel X L) (Y : ℂ)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' 0 (OmPlus k r z z')) (Φ : RadSp k r z z' π π')
    (hΦ : ∀ x ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) J x.1 x.2) :
    ∀ x ∈ DomR k r z z', ((L.Ahat Y).1 Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
      resG k r (Fin.last r) (C3.AAop k r r le_rfl (Y + ((2 * r + k : ℕ) : ℂ) / 2) J) x.1 x.2 := by
  rintro ⟨c₀, g⟩ ⟨hc₀, hg, hG⟩
  have hDom := JCx2.rma_isDom_omPlus hz hz'
  have hD := hDom.1
  have hx : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g ∈ OmPlus k r z z' :=
    fun c hc => P5.Rad.wCell_mem_omPlus hz hz' hc hg hG
  have hDN : ∀ g ∈ Glev k r 0 ∩ OmPlus k r z z', ∀ n ∈ Nlev k r 0, n * g ∈ OmPlus k r z z' := by
    intro g hg n hn
    have h1 : (1 : Mx k r) ∈ Nlev k r 0 := ⟨(nSubgroup k r).1, Qx3.glev_one 0⟩
    have := hDom.2 g hg (1 * n) ⟨1, BigCellZetaMinors.one_uw z, n, hn, rfl⟩ (1 * 1) ⟨1, BigCellZetaMinors.one_uw z', 1, h1, rfl⟩
    simpa using this
  have hp : ∀ (l : Fin r) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)), (∀ c ∈ OmX r, f₁ c = f₂ c) →
      ∀ c ∈ OmX r, pOp l f₁ c = pOp l f₂ c := by
    intro l f₁ f₂ h c hc
    simp only [pOp, wirt, (JCx2.rma_eq_nhds hc h).fderiv_eq]
  have h0 : ∀ c ∈ OmX r, ((JCx2.rma_pref L Y 0 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y 0 (Nat.zero_le r))) c g := by
    intro c hc
    rw [mn_zero, res_ap_one hD hJ.1 hg hc (hx c hc), ← hΦ (c, g) ⟨hc, hg, hG⟩, JCx2.rma_pref, Matrix.one_apply_eq]
    rfl
  have key : ∀ (m : ℕ) (hm : m + 1 ≤ r), (∀ c ∈ OmX r, ((JCx2.rma_pref L Y m 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y m (by omega))) c g) ∧
      ∀ c ∈ OmX r, ((JCx2.rma_pref L Y (m + 1) 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y (m + 1) hm)) c g := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨h0, fun c hc => ?_⟩
      rw [(pref_succ X L hL Y 0 hm Φ c g).1, hp _ _ _ h0 c hc, h0 c hc]
      have e : ((JCx2.rma_pref L Y 0 1 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := by
        rw [JCx2.rma_pref, Matrix.one_apply_ne (by decide)]
        rfl
      rw [e, smul_zero, sub_zero, ← res_ap_torus hD hJ.1 hg hc (hx c hc) Y ⟨0, hm⟩, ← mn_one]
    | succ m ih =>
      intro hm
      obtain ⟨i1, i2⟩ := ih (by omega)
      refine ⟨i2, fun c hc => ?_⟩
      rw [(pref_succ X L hL Y (m + 1) hm Φ c g).1, (pref_succ X L hL Y m (by omega) Φ c g).2, hp _ _ _ i2 c hc,
        i2 c hc, i1 c hc, res_mn_succ hz hz' hD hDN hJ.1 hJ.2.1 hJ.2.2.1 hg hc (hx c hc) Y m hm, smul_smul,
        div_eq_mul_inv]
  have hr : ((JCx2.rma_pref L Y r 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c₀ g =
      resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y r le_rfl)) c₀ g := by
    have : ∀ (m : ℕ) (hm : m ≤ r), ((JCx2.rma_pref L Y m 0 0).1 Φ : Fn k r (Wq →L[ℂ] Wp)) c₀ g =
        resG k r (Fin.last r) (ap hD J hJ.1 (mn hD Y m hm)) c₀ g := by
      intro m hm
      cases m with
      | zero => exact h0 c₀ hc₀
      | succ m => exact (key m hm).2 c₀ hc₀
    exact this r le_rfl
  show ((L.Dr).1 ((L.Tprod Y 0 0).1 Φ) : Fn k r (Wq →L[ℂ] Wp)) c₀ g = _
  rw [res_AAop hD hJ.1 hg hc₀ (hx c₀ hc₀), ← hr, TLB.rma_pref_take, ← TLB.tprod_take_all, R.LevelData.Dr,
    List.ofFn_eq_map, prod_c_apply X L hL, ← List.ofFn_eq_map, List.prod_ofFn]

end ops

end

end GlobalTheory.HatNF.TodaLift

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem polyLift_ahat : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahat y) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d _ hNF y
  obtain ⟨Θ, hΘ, he⟩ := TodaLift.exists_polyOp_AAop (Wp := Wp) (Wq := Wq) P.k P.r (2 * P.r + P.k + 1)
    (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (by omega) (by nlinarith [Nat.zero_le P.r, Nat.zero_le P.k])
    ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2)
  refine SmoothLift.polyLift_of_smooth_comm P Bs _ _ Θ _ hΘ (fun p hp f hf g hg => ?_) (fun J hJ Φ hΦ x hx => ?_)
  · rw [he _ g hg.1 Set.univ isOpen_univ trivial (by simpa using Formalism.FourierDecayAlt.P.B5.ckOn_rho Bs hp hf),
      ← (Formalism.FourierDecayAlt.P.PBG.rho_AA Bs hf P.r le_rfl _ 0 hp hg.1).1]
    simp only [B.rho]
    rw [he f _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg.1) Set.univ isOpen_univ trivial (by simpa using hf)]
  · rw [TodaLift.ahat_apply Bs.z_mem Bs.z'_mem X d.L hNF.1 y hJ Φ hΦ x hx]
    simp only [Q.resG]
    rw [he J _ (Formalism.FourierDecayAlt.P.TLB.wCell_gv Bs hx) (Q.OmPlus P.k P.r Bs.z Bs.z')
      (Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus Bs.z_mem Bs.z'_mem).1
      (Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hx.1 hx.2.1 hx.2.2) ?_]
    intro g₀ hg₀
    obtain ⟨U, F, a, b, c, e⟩ := hJ.1 g₀ ⟨Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.glev0 hg₀.1, hg₀.2⟩
    exact ⟨U, F, a, b, c, fun w hw hwG => e w hw (Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts.glev0 hwG)⟩

end GlobalTheory.HatNF
