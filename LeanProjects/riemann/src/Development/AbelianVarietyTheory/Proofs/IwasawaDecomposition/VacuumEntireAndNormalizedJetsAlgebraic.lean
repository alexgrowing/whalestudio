import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOThZeroTriv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefInTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaTorsionTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAtZeroReindexEqTaylorCoefficient

noncomputable section

namespace GlobalTheory.Mem.Col2.JetAlgebraic

section Germs

open Formalism.MainNotions.TaylorLogMetric GlobalTheory.ThetaAlgebraic Formalism.L2.Th1.H

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type}

inductive Cl (S : Set (V → ℂ)) : (V → ℂ) → Prop
  | const (c : ℂ) (hc : c ∈ Qbar) : Cl S (fun _ => c)
  | base (F : V → ℂ) (hF : F ∈ S) : Cl S F
  | add (F G : V → ℂ) (hF : Cl S F) (hG : Cl S G) : Cl S (fun z => F z + G z)
  | mul (F G : V → ℂ) (hF : Cl S F) (hG : Cl S G) : Cl S (fun z => F z * G z)

variable {S : Set (V → ℂ)} {v : ι → V}

theorem Cl.contDiff (hS : ∀ F ∈ S, ContDiff ℂ ⊤ F) {G : V → ℂ} (h : Cl S G) : ContDiff ℂ ⊤ G := by
  induction h with
  | const c _ => exact contDiff_const
  | base F hF => exact hS F hF
  | add F G _ _ hF hG => exact hF.add hG
  | mul F G _ _ hF hG => exact hF.mul hG

theorem Cl.val_mem (hS : ∀ F ∈ S, F 0 ∈ Qbar) {G : V → ℂ} (h : Cl S G) : G 0 ∈ Qbar := by
  induction h with
  | const c hc => exact hc
  | base F hF => exact hS F hF
  | add F G _ _ hF hG => exact add_mem hF hG
  | mul F G _ _ hF hG => exact mul_mem hF hG

theorem Cl.deriv (hS : ∀ F ∈ S, ContDiff ℂ ⊤ F) (hD : ∀ F ∈ S, ∀ k, (fun y => fderiv ℂ F y (v k)) ∈ S) {G : V → ℂ} (h : Cl S G)
    (k : ι) : Cl S (fun y => fderiv ℂ G y (v k)) := by
  have hd : ∀ {F}, Cl S F → Differentiable ℂ F := fun hF => (hF.contDiff hS).differentiable (by simp)
  induction h with
  | const c hc => simpa using Cl.const (S := S) 0 (zero_mem _)
  | base F hF => exact Cl.base _ (hD F hF k)
  | add F G hF hG iF iG =>
    have e : (fun y => fderiv ℂ (fun z => F z + G z) y (v k)) =
        fun y => fderiv ℂ F y (v k) + fderiv ℂ G y (v k) := by
      funext y
      rw [fderiv_fun_add (hd hF y) (hd hG y)]
      simp
    rw [e]
    exact Cl.add _ _ iF iG
  | mul F G hF hG iF iG =>
    have e : (fun y => fderiv ℂ (fun z => F z * G z) y (v k)) =
        fun y => F y * fderiv ℂ G y (v k) + G y * fderiv ℂ F y (v k) := by
      funext y
      rw [fderiv_fun_mul (hd hF y) (hd hG y)]
      simp
    rw [e]
    exact Cl.add _ _ (Cl.mul _ _ hF iG) (Cl.mul _ _ hG iF)

theorem Cl.iterated_mem (hS : ∀ F ∈ S, ContDiff ℂ ⊤ F) (h0 : ∀ F ∈ S, F 0 ∈ Qbar)
    (hD : ∀ F ∈ S, ∀ k, (fun y => fderiv ℂ F y (v k)) ∈ S) (n : ℕ) : ∀ {G : V → ℂ}, Cl S G → ∀ κ : Fin n → ι,
    iteratedFDeriv ℂ n G 0 (fun i => v (κ i)) ∈ Qbar := by
  induction n with
  | zero => intro G h κ; simpa using h.val_mem h0
  | succ n ih =>
    intro G h κ
    rw [iteratedFDeriv_succ_apply_right,
      ← iteratedFDeriv_clm_apply_const_apply (n := n) ((h.contDiff hS).fderiv_right le_top) le_rfl]
    exact ih (h.deriv hS hD (κ (Fin.last n))) (fun i => κ i.castSucc)

theorem Cl.prod {α : Type} (s : Finset α) (F : α → V → ℂ) (h : ∀ a ∈ s, Cl S (F a)) :
    Cl S (fun z => ∏ a ∈ s, F a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cl.const (S := S) 1 (one_mem _)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact Cl.mul _ _ (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

def AV (n : Type) : Type := {w : n → ℂ // ∀ i, w i ∈ Qbar}

variable {n : Type} [Fintype n]

def sl (a : Fin 4) : (Fin 4 × n → ℂ) →L[ℂ] (n → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a, i)

theorem step4 (f : Fin 4 → (n → ℂ) → ℂ) (hf : ∀ a, Differentiable ℂ (f a))
    (h : Gen (Subtype.val : AV (Fin 4 × n) → _) fun z => ∏ a, f a (sl a z)) (a : Fin 4) (u : AV n) :
    Gen (Subtype.val : AV (Fin 4 × n) → _) fun z => ∏ b, Function.update f a (fun y => fderiv ℂ (f a) y u.1) b (sl b z) := by
  let w : AV (Fin 4 × n) := ⟨fun k => if k.1 = a then u.1 k.2 else 0, fun k => by
    dsimp only
    split_ifs
    exacts [u.2 _, zero_mem _]⟩
  have hw : ∀ b, sl b w.1 = if b = a then u.1 else 0 := fun b => by
    funext i
    change (if b = a then u.1 i else 0) = _
    split_ifs <;> rfl
  convert h.deriv w using 1
  funext y
  have hd : ∀ b ∈ Finset.univ, HasFDerivAt (fun z => f b (sl b z)) ((fderiv ℂ (f b) (sl b y)).comp (sl b)) y := fun b _ =>
    (hf b _).hasFDerivAt.comp y (sl b).hasFDerivAt
  rw [(HasFDerivAt.finsetProd hd).fderiv, _root_.sum_apply, Finset.sum_eq_single a]
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Function.update_self, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, hw, if_pos rfl, smul_eq_mul, mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
  · intro b _ hb
    simp [hw, hb]
  · simp

def Root4 (f : (n → ℂ) → ℂ) : Prop :=
  ContDiff ℂ ⊤ f ∧ Gen (Subtype.val : AV (Fin 4 × n) → _) fun z => ∏ a : Fin 4, f (sl a z)

theorem Root4.val_mem {f : (n → ℂ) → ℂ} (h : Root4 f) : f 0 ∈ Qbar := by
  have := h.2.val_mem
  simp only [map_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num) (mem_algebraicClosure_iff.1 this))

theorem Root4.deriv {f : (n → ℂ) → ℂ} (h : Root4 f) (u : AV n) : Root4 fun y => fderiv ℂ f y u.1 := by
  have h1 : ContDiff ℂ ⊤ fun y => fderiv ℂ f y u.1 := (h.1.fderiv_right le_top).clm_apply contDiff_const
  refine ⟨h1, ?_⟩
  set g := fun y => fderiv ℂ f y u.1 with hg
  have key : ∀ s : Finset (Fin 4), Gen (Subtype.val : AV (Fin 4 × n) → _) fun z => ∏ a, (if a ∈ s then g else f) (sl a z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h.2
    | insert a s ha ih =>
      have := step4 (fun a => if a ∈ s then g else f) (fun b => by
        split_ifs
        exacts [h1.differentiable (by simp), h.1.differentiable (by simp)]) ih a u
      convert this using 4 with z b
      by_cases hb : b = a
      · subst hb; simp [ha, hg]
      · simp [hb]
  simpa using key Finset.univ

theorem alg_of_span {κ : Type} (s : κ → n → ℂ) (hs : ∀ k i, s k i ∈ Qbar) (hsp : Submodule.span ℂ (Set.range s) = ⊤)
    (l : (n → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ k, l (s k) ∈ Qbar) (w : AV n) : l w.1 ∈ Qbar := by
  obtain ⟨pr, hpr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hp : ∀ a : Qbar, pr (a : ℂ) = a := fun a => LinearMap.congr_fun hpr a
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (hsp ▸ Submodule.mem_top : w.1 ∈ Submodule.span ℂ (Set.range s))
  have e : w.1 = ∑ k ∈ c.support, (pr (c k) : ℂ) • s k := by
    funext i
    have h1 : (pr (w.1 i) : ℂ) = w.1 i := congrArg Subtype.val (hp ⟨_, w.2 i⟩)
    rw [← h1, ← hc, Finsupp.sum, Finset.sum_apply, Finset.sum_apply, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (c k • s k) i = (⟨_, hs k i⟩ : Qbar) • c k := mul_comm _ _
    rw [this, map_smul]
    exact mul_comm _ _
  rw [e, map_sum]
  exact sum_mem fun k _ => by rw [map_smul]; exact mul_mem (pr (c k)).2 (hl k)

end Germs

section Vacuum

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.ThetaAlgebraic Formalism.L2.Th1 GlobalTheory.Mem.Col2 Classical

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem kappa_mem : B.kappa ∈ Qbar := by
  have hrt : ∀ q : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt q ∈ Qbar := by
    intro q
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := 2 * classNumber D.host.K)
      (Nat.mul_pos two_pos (Nat.pos_of_ne_zero (classNumber_ne_zero _))) (mem_algebraicClosure_iff.1 ?_))
    rw [B.kc.rt_pow q.1 q.2.1 q.2.2]
    exact div_mem (hom_mem _ _) (hom_mem _ _)
  exact finprod_induction (fun x => x ∈ Qbar) (one_mem _) (fun x y hx hy => mul_mem hx hy) fun q => zpow_mem (hrt q) _

theorem opU_form1 (x : ℂ) (G : ℂ → ℂ) : H.opU (ThetaVec.form1 B.L) x G = U1 (lamOf D cc δ) x G := by
  rw [← ThetaVec.opU_eq]
  funext z
  have hA : area (lamOf D cc δ) = F.area B.L := WeilVac.areaOK B
  simp only [F.opU, U1, F.herm, hA]
  congr 2
  ring

theorem thetaZero_periodLattice_eq (t : ℂ) : F.th0 B.L t = GL3Theta.th0 (lamOf D cc δ) t := by
  funext z
  rw [ThetaVec.thetaZero_periodLattice_eq, opU_form1, GL3Theta.th0, GlobalTheory.OddTheta.sgStar_eq B.L _ fun z => (GlobalTheory.FourthRootStd.mem_iff B z).symm]

theorem heisenbergOp_standardVacuum_prod {n : Type} [Fintype n] [DecidableEq n] (x z : n → ℂ) :
    H.opU (H.stdH B.L n) x (H.F0 B.L B.ω₀ n) z =
      ∏ i, U1 (lamOf D cc δ) (x i) (GL3Theta.th0 (lamOf D cc δ) (B.ω₀ / 2)) (z i) := by
  simp only [← opU_form1 B, ← thetaZero_periodLattice_eq B, H.opU, H.F0, H.prodFn, ThetaVec.stdH_apply, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib, Complex.exp_sum, ← Finset.prod_mul_distrib, Pi.add_apply]

theorem thetaVector_fourthPower_algebraicGerm (hC : Crv D cc δ) : Root4 B.thMM := by
  have hS := GlobalTheory.FourthRootStd.stdOK B hC.1 hC.2
  obtain ⟨⟨h1, h2⟩, -⟩ := WeilVac.thMM_spec B hS
  refine ⟨h1.1.contDiff, ?_⟩
  have hG : admG1 D := (GlobalTheory.InducedType.induced_type D).1
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC).1
  have hσ : Differentiable ℂ (sgStar (lamOf D cc δ)) := (GlobalTheory.OddTheta.sgStar_laws _ hlat).1.1
  have hth := GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt (lamOf D cc δ) hlat
    (fun x hx => ⟨differentiable_U1 _ _ hσ, (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hC).1 x hx⟩) (B.ω₀ / 2)
    (fun h => hS.half ((GlobalTheory.FourthRootStd.mem_iff B _).2 h)) B.t0.1
  obtain ⟨N, hN, hup⟩ := GlobalTheory.FourthRootStd.up B
  change Gen _ (H.tens4 B.thMM)
  rw [h2]
  have hfin : Finite _ := Nat.finite_of_card_ne_zero hS.idx₁
  have := Fintype.ofFinite (↥(H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (H.pow4 B.lamM)) ⧸
    (H.stdLat B.L (Fin 4 × D.what₂.Tau)).addSubgroupOf (H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (H.pow4 B.lamM)))
  refine Gen.mul _ _ (Gen.const _ (kappa_mem B)) ?_
  unfold H.kernel4 H.inter
  simp only [finsum_eq_sum_of_fintype, heisenbergOp_standardVacuum_prod]
  refine Gen.mul _ _ (Gen.const _ (inv_mem (sqrt_nat_mem _))) (Gen.sum _ _ fun q _ => Gen.mul _ _ (Gen.const _ ?_) (Gen.prod _ _ fun k _ => ?_))
  · rcases hS.betaSemi.1 _ (Quotient.out q).2 with h | h
    · exact h ▸ one_mem _
    · exact h ▸ neg_mem (one_mem _)
  · have hx := hth (((Quotient.out q).1 : Fin 4 × D.what₂.Tau → ℂ) k) ⟨N, hN, by
      have := (ThetaVec.mem_stdLat B.L).1 (hup _ (Quotient.out q).2) k
      rw [← GlobalTheory.FourthRootStd.mem_iff B]
      simpa using this⟩
    refine Gen.lin _ hx.1.1 (iteratedDeriv_mem hx.1.2)
      (LinearMap.toContinuousLinearMap ((LinearMap.proj k).comp B.gC.toLinearMap)) fun w => ?_
    refine alg_of_span (GlobalTheory.FourthRootStd.emb4 D) (fun y i => hom_mem _ _) (GlobalTheory.FourthRootStd.span_range_emb4_eq_top D)
      ((LinearMap.proj k).comp B.gC.toLinearMap) (fun y => ?_) w
    change B.gC (fun w => embT D w.2 (y w.1)) k ∈ Qbar
    rw [B.gC_spec]
    exact hom_mem _ _

def col (D : D7) {N N' : ℕ} (i : Fin N') (j : Fin N) : VC D N N' →L[ℂ] (D.what₂.Tau → ℂ) :=
  ContinuousLinearMap.pi fun τ => (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D.what₂.Tau => Fin N' → Fin N → ℂ) τ))

theorem thZero_coefIn (hC : Crv D cc δ) (N N' : ℕ) : CoefIn D (B.thZero N N') Qbar := by
  let S : Set (VC D N N' → ℂ) := {G | ∃ i j f, Root4 f ∧ G = fun z => f (col D i j z)}
  have hcl : Cl S (B.thZero N N') := by
    change Cl S fun z => ∏ i, ∏ j, B.thMM (col D i j z)
    refine Cl.prod _ (fun i z => ∏ j, B.thMM (col D i j z)) fun i _ => ?_
    refine Cl.prod _ (fun j z => B.thMM (col D i j z)) fun j _ => Cl.base _ ?_
    exact ⟨i, j, _, thetaVector_fourthPower_algebraicGerm B hC, rfl⟩
  intro α
  refine div_mem (Cl.iterated_mem (v := coordV D) ?_ ?_ ?_ _ hcl _) (prod_mem fun k _ => natCast_mem _ _)
  · rintro _ ⟨i, j, f, hf, rfl⟩
    exact hf.1.comp (col D i j).contDiff
  · rintro _ ⟨i, j, f, hf, rfl⟩
    simpa using hf.val_mem
  · rintro _ ⟨i, j, f, hf, rfl⟩ k
    refine ⟨i, j, _, hf.deriv ⟨col D i j (coordV D k), fun τ => ?_⟩, ?_⟩
    · change coordV D k τ i j ∈ Qbar
      unfold coordV
      split_ifs
      exacts [one_mem _, zero_mem _]
    · funext y
      have := ((hf.1.differentiable (by simp) _).hasFDerivAt.comp y (col D i j).hasFDerivAt).fderiv
      rw [show (fun z => f (col D i j z)) = f ∘ col D i j from rfl, this]
      rfl

variable {N N' : ℕ}

def TA (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (G : VC D N N' → ℂ) : Prop :=
  Differentiable ℂ G ∧ ∀ x ∈ sat (La D (tor0 D cc δ) (stdL D N) (stdL D N')), CoefIn D (U D (tor0 D cc δ) x G) Qbar

theorem differentiable_U (T : Tor D) (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) : Differentiable ℂ (U D T x G) := by
  unfold U Hf
  fun_prop

theorem TA.comb {α : Type} (s : Finset α) (c : α → ℂ) (F : α → VC D N N' → ℂ) (hc : ∀ a, c a ∈ Qbar) (h : ∀ a, TA cc δ (F a)) :
    TA cc δ fun z => ∑ a ∈ s, c a * F a z := by
  refine ⟨?_, fun x hx β => ?_⟩
  · have := fun a => (h a).1
    fun_prop
  · have e : U D (tor0 D cc δ) x (fun z => ∑ a ∈ s, c a * F a z) = fun z => ∑ a ∈ s, c a * U D (tor0 D cc δ) x (F a) z := by
      funext z; simp only [U, Finset.sum_mul, mul_assoc]
    rw [e, GlobalTheory.AlgTranslate.taylor_sum D s c _ fun a => differentiable_U _ _ (h a).1]
    exact sum_mem fun a _ => mul_mem (hc a) ((h a).2 x hx β)

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := GlobalTheory.FourthRootStd.stdL_isSD D N

theorem TA.transl (hC : Crv D cc δ) {G : VC D N N' → ℂ} (h : TA cc δ G) {t : VC D N N'}
    (ht : t ∈ sat (La D (tor0 D cc δ) (stdL D N) (stdL D N'))) : TA cc δ (U D (tor0 D cc δ) t G) := by
  refine ⟨differentiable_U _ _ h.1, fun x hx β => ?_⟩
  obtain ⟨q, hq⟩ := ((GlobalTheory.RationalPoints.rational_points D cc δ hC N N' _ _ (sd_std D N) (sd_std D N')).2 x t hx ht).1
  rw [show U D (tor0 D cc δ) x (U D (tor0 D cc δ) t G) = _ from funext (U_U (tor0 D cc δ) x t G), hq,
    GlobalTheory.ThetaConj.taylor_mul D _ (differentiable_U _ _ h.1)]
  refine mul_mem ?_ (h.2 _ (add_mem hx ht) β)
  simpa using exp_rat_mem (-q)

theorem la_le_sat (hC : Crv D cc δ) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') : La D (tor0 D cc δ) L L' ≤ sat (La D (tor0 D cc δ) (stdL D N) (stdL D N')) := by
  intro x hx
  have hK : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨L, L', hL, hL', rfl⟩
  obtain ⟨A, rfl⟩ := GlobalTheory.ThetaInter.klat_rat (GlobalTheory.InducedType.induced_type D).1.1 hK hx
  exact (GlobalTheory.RationalPoints.rational_points D cc δ hC N N' _ _ (sd_std D N) (sd_std D N')).1 A

theorem TA.iop (hC : Crv D cc δ) {G : VC D N N' → ℂ} (h : TA cc δ G) (A₁ A₂ : AddSubgroup (VC D N N'))
    (hA : A₂ ≤ sat (La D (tor0 D cc δ) (stdL D N) (stdL D N'))) : TA cc δ (Iop D (tor0 D cc δ) A₁ A₂ G) := by
  by_cases hi : (A₁.addSubgroupOf A₂).index = 0
  · have e : Iop D (tor0 D cc δ) A₁ A₂ G = fun z => ∑ _a ∈ (∅ : Finset Unit), 0 * G z := by
      funext z; simp [Iop, hi]
    rw [e]
    exact TA.comb _ _ _ (fun _ => zero_mem _) fun _ => h
  · haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Nat.finite_of_card_ne_zero hi
    haveI := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
    unfold Iop
    simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, ← mul_assoc]
    exact TA.comb _ _ _ (fun q => mul_mem (inv_mem (sqrt_nat_mem _)) (zpow_mem (neg_mem (one_mem _)) _))
      fun q => h.transl hC (hA (Quotient.out q).2)

theorem ta_thMoved (hC : Crv D cc δ) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') : TA cc δ (B.thMoved N N' L L') := by
  have hm := WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK B hC.1 hC.2) N N'
  have h0 : TA cc δ (B.thZero N N') := ⟨hm.1, fun x hx =>
    GlobalTheory.AlgTranslate.coefIn_translate D cc δ hC N N' _ _ (sd_std D N) (sd_std D N') _ hm (thZero_coefIn B hC N N') x hx⟩
  exact (h0.iop hC _ _ (la_le_sat hC hL (sd_std D N'))).iop hC _ _ (la_le_sat hC hL hL')

end Vacuum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

theorem derivAt0_mul {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (f : VCx ι a b → ℂ) (hf : ∀ k : ℕ, ContDiff ℂ k f)
    (m : DVar ι a b →₀ ℕ) : derivAt0 (fun z => c * f z) m = c * derivAt0 f m := by
  unfold derivAt0
  have e : (fun z => c * f z) = c • f := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((hf _).contDiffAt), _root_.smul_apply, smul_eq_mul]

theorem esmooth_jetAlg : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → Even a → Even b → (ambOf s B χ cD).ESmooth a b ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ), JetAlg (ambOf s B χ cD) a b S M := by
  intro D X s cc δ B χ cD a b hX hs hcc hδ _ _ _
  have hC : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hsa := (GlobalTheory.SeamSelfDual.seam_selfDual D X s hs a).2
  have hsb := (GlobalTheory.SeamSelfDual.seam_selfDual D X s hs b).2
  have hsm : (ambOf s B χ cD).ESmooth a b := by
    intro N N' hN hN' k
    let T : VCx X.Tau a b →L[ℂ] TaylorLogMetric.VC D a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
    have h1 : ContDiff ℂ k (B.thMoved a b (s.lat N) (s.lat N')) :=
      (GlobalTheory.SCV.analyticOnNhd_of_differentiable (ta_thMoved B hC (hsa N hN) (hsb N' hN')).1 Set.univ).contDiff
    exact contDiff_const.mul (h1.comp T.contDiff)
  refine ⟨hsm, fun S M N N' c x hR e => ?_⟩
  have hT := ta_thMoved B hC (hsa N hR.1) (hsb N' hR.2.1)
  have hI := indSmooth_of (ambOf s B χ cD) a b S M hsm N N' c x hR
  obtain ⟨k, r, y, hr, hy, -, hF⟩ :=
    GlobalTheory.ColNorms.IndPres.pres_thInd D X s cc δ B χ cD hX hs hC a b S N N' c x hR.1 hR.2.1 hR.2.2.1
  have hU := fun i => differentiable_U B.tor (y i) hT.1
  set F : TaylorLogMetric.VC D a b → ℂ := fun w => ∑ i, r i * TaylorLogMetric.U D B.tor (y i) (B.thMoved a b (s.lat N) (s.lat N')) w with hFdef
  have hdiff : Differentiable ℂ F := by fun_prop
  have hfun : (fun z => ((ambOf s B χ cD).chiF a b N N')⁻¹ * (ambOf s B χ cD).thInd S N N' c x z) =
      fun z : VCx X.Tau a b => F fun τ => z (s.iT.symm τ) := by
    funext z
    have h1 := congrFun hF fun τ => z (s.iT.symm τ)
    simp only [GlobalTheory.ColNorms.toHost, Equiv.symm_apply_apply] at h1
    exact h1
  rw [← derivAt0_mul _ _ hI, hfun, GlobalTheory.DerivReindex.derivAt0_reindex D X.Tau s.iT a b F hdiff e, hFdef,
    GlobalTheory.AlgTranslate.taylor_sum D _ _ _ hU, ← mem_algebraicClosure_iff]
  refine mul_mem (prod_mem fun _ _ => natCast_mem _ _) (sum_mem fun i _ => mul_mem (hr i) (hT.2 (y i) ?_ _))
  obtain ⟨m, hm, hmy⟩ := hy i
  exact GlobalTheory.ThetaAlgebraic.sat_of_nsmul hm (la_le_sat hC (hsa N hR.1) (hsb N' hR.2.1) hmy)

end GlobalTheory.Mem.Col2.JetAlgebraic

end
