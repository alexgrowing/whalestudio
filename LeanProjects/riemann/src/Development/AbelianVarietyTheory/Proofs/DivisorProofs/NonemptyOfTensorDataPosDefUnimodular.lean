import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarisedStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.PowLim.Rosati

open GlobalTheory.CechPic GlobalTheory.Mum.RosatiTens

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}
  {pr : Fin r → (D'.P.A ⟶ Q.B)}

def pairQ (Q : Data R) (pr : Fin r → (D'.P.A ⟶ Q.B)) (M : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) : Pic X.left :=
  ∑ i, ∑ j, M i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j)

theorem cls_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) : cls D'.P.L D'.P.isLB = ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (pr i) (pr j) := by
  have hC := LB.isLB_linComb Q.M.isLB (tensφ pr) (tensε W)
  refine ((cls_eq_iff D'.P.isLB hC).2 ⟨w, hw⟩).trans ?_
  rw [cls_linComb Q.M.isLB, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, lam, mul_smul, ← smul_add]
  congr 1
  simp
  abel

theorem pull_pow {W : Matrix (Fin r) (Fin r) ℤ} (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)))
    (hw : w.IsGen) {X : Over (Spec (CommRingCat.of R))} (h : X ⟶ D'.P.A) :
    pull h.left (cls D'.P.L D'.P.isLB) = pairQ Q pr W h h := by
  rw [cls_pow w hw, pairQ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pull_lam]

theorem pairQ_mul (hpr : ∀ i, IsMonHom (pr i)) (W : Matrix (Fin r) (Fin r) ℤ) {X : Over (Spec (CommRingCat.of R))}
    (u v : X ⟶ D'.P.A) :
    pairQ Q pr W (u * v) (u * v) = pairQ Q pr W u u + pairQ Q pr W v v + pairQ Q pr (W + W.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ pr i = u ≫ pr i * v ≫ pr i := fun i => by
    haveI := hpr i
    exact MonObj.mul_comp _ _ _
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have e : ∑ i, ∑ j, W i j • lam (cls Q.M.L Q.M.isLB) (v ≫ pr i) (u ≫ pr j) =
      ∑ i, ∑ j, W.transpose i j • lam (cls Q.M.L Q.M.isLB) (u ≫ pr i) (v ≫ pr j) := by
    rw [Finset.sum_comm]
    simp only [Matrix.transpose_apply, lam_comm _ (v ≫ _)]
  simp only [pairQ, hm, lam_mul_left Q.M.isLB hΘ, lam_mul_right Q.M.isLB hΘ, smul_add, Finset.sum_add_distrib,
    Matrix.add_apply, add_smul]
  rw [e]
  abel

theorem comp_act_pr' (hl : IsLimit (Fan.mk D'.P.A pr)) {X : Over (Spec (CommRingCat.of R))} (u : X ⟶ D'.P.A)
    (m : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    (u ≫ PowLim.act pr hl m) ≫ pr i = ∏ k, (u ≫ pr k) ^ m i k := by
  rw [Category.assoc, PowLim.act_pr]
  exact (map_prod (pre (Z := Q.B) u) _ _).trans (Finset.prod_congr rfl fun k _ => map_zpow (pre (Z := Q.B) u) _ _)

theorem pairQ_act_left (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M (u ≫ PowLim.act pr hl m) v = pairQ Q pr (m.transpose * M) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_left Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairQ_act_right (hl : IsLimit (Fan.mk D'.P.A pr)) (M m : Matrix (Fin r) (Fin r) ℤ)
    {X : Over (Spec (CommRingCat.of R))} (u v : X ⟶ D'.P.A) :
    pairQ Q pr M u (v ≫ PowLim.act pr hl m) = pairQ Q pr (M * m) u v := by
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  simp only [pairQ, comp_act_pr', lam_prod_right Q.M.isLB hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem rosatiAdj_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (h : IsUnit (W + W.transpose).det) (pr : Fin r → (D'.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.P.A pr))
    (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ i, IsMonHom (pr i)) → w.IsGen →
    ∀ a : TensO (symUnitOf W h), RosatiAdj D'.P.A D'.P.L (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a))) := by
  intro R _ _ Q D' r W h pr hl w hpr hw a
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb D'.P.isLB _ _)).1 ?_⟩
  rw [cls_linComb D'.P.isLB]
  let f := PowLim.act pr hl (TensO.mat _ a)
  let g := PowLim.act pr hl (TensO.mat _ (star a))
  let H : Fin 6 → (D'.P.A ⊗ D'.P.A ⟶ D'.P.A) := ![fst _ _ ≫ f * snd _ _, fst _ _ ≫ f, snd _ _,
    fst _ _ * snd _ _ ≫ g, fst _ _, snd _ _ ≫ g]
  have hH : rosatiφ D'.P.A f g = fun k => (H k).left := by
    funext k
    fin_cases k <;> simp [rosatiφ, H, padd, Hom.mul_def]
  have key : ∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB) = 0 := by
    simp only [hH, pull_pow w hw]
    simp only [Fin.sum_univ_six, H, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    rw [pairQ_mul hpr, pairQ_mul hpr]
    rw [pairQ_act_left hl (W + W.transpose) (TensO.mat _ a) (fst _ _) (snd _ _),
      pairQ_act_right hl (W + W.transpose) (TensO.mat _ (star a)) (fst _ _) (snd _ _), symUnit_mul_star]
    simp only [one_smul, neg_smul]
    abel
  calc ∑ k, rosatiε k • pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι ≫ rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)
      = pull (((D'.P.A ⊗ D'.P.A).hom ⁻¹ᵁ ⊤).ι)
          (∑ k, rosatiε k • pull (rosatiφ D'.P.A f g k) (cls D'.P.L D'.P.isLB)) := by
        simp only [pull_comp, map_sum, map_zsmul]
    _ = 0 := by rw [key, map_zero]

end GlobalTheory.Mum.PowLim.Rosati

theorem GlobalTheory.Mum.PFactor.nonempty_of_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
  {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → 1 ≤ r →
  ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) →
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    Nonempty (PFactor Q D'.toPre) := by
  intro R _ _ _ hR Q D' r W hpos hdet hr pr xe w hpr hlim hc hw hpsi
  let hl := hlim.some
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := PowLim.mod xe s
  obtain ⟨w', hw', htau⟩ := GlobalTheory.T.mumfordIso_periods_factor_tensor_polarised R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := PowLim.factor_latt xe s i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := PowLim.mod xe s
    o := { onB := { act := fun a => PowLim.act pr hl (TensO.mat s a)
                    hom := fun a => PowLim.act_isMonHom pr hl hpr _
                    map_one := PowLim.act_one pr hl
                    map_mul := fun a b => PowLim.act_mul pr hl _ _
                    map_add := fun a b => PowLim.act_add pr hl hpr _ _
                    rosati := GlobalTheory.Mum.PowLim.Rosati.rosatiAdj_pow R Q D'.toPre W hdet pr hl w hpr hw }
           c_lin := PowLim.c_smul Q D'.toPre pr hl xe hc s
           tau_bal := GlobalTheory.T.tensorData_periods_balanced_integralMatrices R hR Q D' W hdet hpos pr hl xe w hpr hc hw hpsi }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := PowLim.inc pr hl i₀
    pr := pr i₀
    xi := PowLim.xi xe i₀
    xp := PowLim.xp xe i₀
    w := w'
    idem := TensO.idem_mul_idem s i₀
    inc_hom := PowLim.inc_isMonHom pr hl hpr i₀
    pr_hom := hpr i₀
    inc_pr := PowLim.inc_pr_self pr hl i₀
    pr_inc := PowLim.pr_inc pr hl i₀
    xp_xi := hxx
    xi_xp := hxe
    c_xi := PowLim.c_xi Q D'.toPre pr hl xe hc i₀
    inj := hinj
    onto := honto
    w_gen := hw'
    tau := htau
    alg := PowLim.alg_idem_binv s i₀ hp }⟩
