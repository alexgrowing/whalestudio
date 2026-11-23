import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyT

noncomputable section

open MeasureTheory MvPolynomial
open scoped ComplexOrder Matrix

namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT

open AsmA

attribute [local irreducible] Tf

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

variable (ι A B) in

def invSub : Submodule ℂ (PV ι A B) where
  carrier := {q | IsInv q}
  add_mem' := fun {a b} ha hb u hu => by rw [map_add, ha u hu, hb u hu]
  zero_mem' := fun u _ => map_zero _
  smul_mem' := fun c q hq u hu => by rw [map_smul, hq u hu]

variable (ι A B) in

def Vd (d : ℕ) : Submodule ℂ (PV ι A B) := restrictTotalDegree ((ι × A) ⊕ (ι × B)) ℂ d ⊓ invSub ι A B

instance (d : ℕ) : FiniteDimensional ℂ (Vd ι A B d) := Submodule.finiteDimensional_of_le inf_le_left

theorem integrable_eval_act_blk_toMK (hA : Avg) (z : (ι × A) ⊕ (ι × B) → ℂ) (q : PV ι A B) :
    Integrable (fun k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true) =>
      eval (act (blk (Formalism.REAL.toMK k)) ((blk (Formalism.REAL.toMK k)).map star) z) q)
      (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
  integrable_eval_act hA _ _ continuous_blk (continuous_blk.matrix_map continuous_star) z q

theorem Tf_add (hA : Avg) (q1 q2 : PV ι A B) : Tf hA (q1 + q2) = Tf hA q1 + Tf hA q2 :=
  MvPolynomial.funext fun z => by
    rw [map_add, eval_Tf, eval_Tf, eval_Tf, ← integral_add (integrable_eval_act_blk_toMK hA z q1) (integrable_eval_act_blk_toMK hA z q2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [map_add]

theorem Tf_smul (hA : Avg) (c : ℂ) (q : PV ι A B) : Tf hA (c • q) = c • Tf hA q :=
  MvPolynomial.funext fun z => by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_Tf, eval_Tf,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [map_mul, eval_C]

theorem Tf_memVd (hS : Stable) (hA : Avg) {d : ℕ} {q : PV ι A B} (hq : q ∈ Vd ι A B d) :
    Tf hA q ∈ Vd ι A B d := by
  rw [Vd, Submodule.mem_inf] at hq ⊢
  refine ⟨(mem_restrictTotalDegree _ _ _).mpr ((Tf_deg hA q).trans ((mem_restrictTotalDegree _ _ _).mp hq.1)), ?_⟩
  show IsInv (Tf hA q)
  exact pair_inv (Tf_mem hS hA q)

def Tlin (hS : Stable) (hA : Avg) (d : ℕ) : Vd ι A B d →ₗ[ℂ] Vd ι A B d where
  toFun q := ⟨Tf hA q, Tf_memVd hS hA q.2⟩
  map_add' q1 q2 := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    exact Tf_add hA (q1 : PV ι A B) (q2 : PV ι A B)
  map_smul' c q := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact Tf_smul hA c (q : PV ι A B)

def Mk (k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true)) : Matrix ι ι ℂ :=
  (blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k)).transpose * (blk (Formalism.REAL.toMK k)).map star

theorem continuous_Mk : Continuous (Mk (ι := ι) (A := A) (B := B)) :=
  continuous_blk.matrix_transpose.matrix_mul (continuous_blk.matrix_map continuous_star)

theorem Mk_psd (k : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true)) : (Mk (ι := ι) (A := A) (B := B) k).PosSemidef := by
  have e : Mk (ι := ι) (A := A) (B := B) k =
      ((blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK k)).map star)ᴴ * (blk (Formalism.REAL.toMK k)).map star := by
    ext i j
    simp [Mk, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem Mk_one : Mk (ι := ι) (A := A) (B := B) 1 = 1 := by
  have hb : blk (ι := ι) (A := A) (B := B) (Formalism.REAL.toMK (1 : Formalism.REAL.KG (fun _ : Fin (NN ι A B) => true))) = 1 := by
    have h1 : Formalism.REAL.toM (1 : Formalism.REAL.UJ (fun _ : Fin (NN ι A B) => true)) = 1 := Units.val_one
    ext i j
    simp only [blk, Formalism.REAL.toMK, OneMemClass.coe_one, h1, Matrix.one_apply, emb_injective.eq_iff]
  simp [Mk, hb]

theorem eval_Tf_inv (hE : Ext) (hA : Avg) {q : PV ι A B} (hq : IsInv q) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (Tf hA q) = ∫ k, eval (act 1 (Mk (ι := ι) (A := A) (B := B) k) z) q ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
  rw [eval_Tf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  exact ext_all hE hq _ z

theorem Tlin_injective (hS : Stable) (hE : Ext) (hA : Avg) (hP : Pos) (d : ℕ) :
    Function.Injective (Tlin (ι := ι) (A := A) (B := B) hS hA d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq0
  by_contra hne
  have hq : (q : PV ι A B) ≠ 0 := fun h => hne (Subtype.ext h)
  have hqI : IsInv (q : PV ι A B) := (Submodule.mem_inf.mp q.2).2
  have hqd : (q : PV ι A B).totalDegree ≤ d := (mem_restrictTotalDegree _ _ _).mp (Submodule.mem_inf.mp q.2).1
  set W := restrictTotalDegree ((ι × A) ⊕ (ι × B)) ℂ d
  obtain ⟨c, hc⟩ := exists_points W ((gipL hP (q : PV ι A B)).comp W.subtype)
  have hsubW : ∀ k, sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B) ∈ W := fun k =>
    (mem_restrictTotalDegree _ _ _).mpr ((totalDegree_sub_le _ _ _).trans hqd)
  have hΨ : ∀ k, gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B) =
      ∑ z ∈ c.support, c z * eval (act 1 (Mk (ι := ι) (A := A) (B := B) k) z) (q : PV ι A B) := by
    intro k
    have h := hc ⟨_, hsubW k⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, gipL_apply, Finsupp.sum] at h
    rw [h]
    simp only [AsmA.eval_sub]
  have hΨc : Continuous fun k => gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B) := by
    simp_rw [hΨ]
    exact continuous_finsetSum _ fun z _ => continuous_const.mul (continuous_act_eval continuous_const continuous_Mk z _)
  have hint : Integrable (fun k => gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B))
      (Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) :=
    integrableOn_univ.mp (hΨc.continuousOn.integrableOn_compact isCompact_univ)
  have hTW : Tf hA (q : PV ι A B) ∈ W := (mem_restrictTotalDegree _ _ _).mpr ((Tf_deg hA _).trans hqd)
  have hT0 : Tf hA (q : PV ι A B) = 0 := congrArg Subtype.val hq0
  have hgipT : gip (Tf hA (q : PV ι A B)) (q : PV ι A B) =
      ∫ k, gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B) ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
    have h := hc ⟨_, hTW⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, gipL_apply, Finsupp.sum] at h
    rw [h]
    simp_rw [hΨ]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [eval_Tf_inv hE hA hqI z, integral_const_mul]
    · intro z _
      exact (integrable_eval_act hA (fun _ => 1) (Mk (ι := ι) (A := A) (B := B)) continuous_const continuous_Mk z _).const_mul _
  have hgip0 : gip (Tf hA (q : PV ι A B)) (q : PV ι A B) = 0 := by
    rw [hT0]; simp [gip]
  have hre : 0 < ∫ k, (gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B)).re
      ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
    refine (Complex.continuous_re.comp hΨc).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
      (fun k => (hP ι A B (Mk (ι := ι) (A := A) (B := B) k) (Mk_psd k) _).1) (x := 1) ?_
    have h1 := (hP ι A B (Mk (ι := ι) (A := A) (B := B) 1) (Mk_psd 1) (q : PV ι A B)).2.2 (by rw [Mk_one]; exact Matrix.PosDef.one) hq
    exact h1.ne'
  have hcomm : (∫ k, gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B)
      ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true))).re =
      ∫ k, (gip (sub 1 (Mk (ι := ι) (A := A) (B := B) k) (q : PV ι A B)) (q : PV ι A B)).re
      ∂(Formalism.REAL.muK (fun _ : Fin (NN ι A B) => true)) := by
    have := Complex.reCLM.integral_comp_comm hint
    simpa using this.symm
  rw [← hgipT, hgip0] at hcomm
  simp at hcomm
  linarith

end PositivityTheory.Rg.Sw.FFTSteps.AsmT

namespace PositivityTheory.Rg.Sw.FFTSteps

open AsmT

theorem assembly : Assembly := by
  intro hS hE hA hP ι A B _ _ _ _ p hp
  have hpI : IsInv p := fun u hu => hp u hu
  have hsurj := LinearMap.injective_iff_surjective.mp (Tlin_injective (ι := ι) (A := A) (B := B) hS hE hA hP p.totalDegree)
  obtain ⟨q, hq⟩ := hsurj ⟨p, Submodule.mem_inf.mpr ⟨(mem_restrictTotalDegree _ _ _).mpr le_rfl, hpI⟩⟩
  have h : Tf hA (q : PV ι A B) = p := congrArg Subtype.val hq
  rw [← h]
  exact Tf_mem hS hA _

end PositivityTheory.Rg.Sw.FFTSteps
