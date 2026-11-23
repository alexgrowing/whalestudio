import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct

namespace GlobalTheory.ShFam

section Pull

variable {X Z : Scheme.{0}} [IsIntegral X] (B : EffCartierData Z) (f : X ⟶ Z)
  (h : f (genericPoint X) ∉ B.idealSheaf.support)

def pullEqn (i : B.ι) {y : X} (hy : f y ∈ B.U i) : X.functionFieldˣ :=
  have hg : genericPoint X ∈ f ⁻¹ᵁ B.U i := gen_mem (x := y) hy
  Units.mk0 (fnOf (f ⁻¹ᵁ B.U i) hg (f.app _ (B.f i))) (UnitAt.ne_zero ((unitAt_fnOf_iff hg _ _).2 (by
    rw [← Scheme.preimage_basicOpen]
    exact not_not.1 (mt (B.mem_support_iff i hg).2 h))))

theorem germOf_pullEqn {i i' : B.ι} {y : X} (hi : f y ∈ B.U i) (hi' : f y ∈ B.U i') :
    germOf y (pullEqn B f h i hi) = germOf y (pullEqn B f h i' hi') := by
  obtain ⟨u, hu⟩ := ((B.associated_germ i i' _ hi hi').map (f.stalkMap y).hom)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at hu
  have e := congrArg (algebraMap _ X.functionField) hu
  rw [map_mul, algebraMap_germ (U := f ⁻¹ᵁ B.U i) hi, algebraMap_germ (U := f ⁻¹ᵁ B.U i') hi'] at e
  exact germOf_eq_iff.2 ⟨u, u.isUnit, (eq_div_iff (Units.ne_zero _)).2 ((mul_comm _ _).trans e)⟩

def pullDiv : CartierDiv X :=
  show cartierGroup X from ⟨fun y => germOf y (pullEqn B f h _ (B.exists_mem (f y)).choose_spec), fun y =>
    ⟨f ⁻¹ᵁ B.U _, (B.exists_mem (f y)).choose_spec, pullEqn B f h _ (B.exists_mem (f y)).choose_spec,
      fun _ hz => germOf_pullEqn B f h _ hz⟩⟩

theorem isEqn_pullDiv (i : B.ι) {y : X} (hy : f y ∈ B.U i) : (pullDiv B f h).IsEqn y (pullEqn B f h i hy) :=
  germOf_pullEqn B f h _ hy

theorem eff_pullDiv : (pullDiv B f h).Eff := fun y =>
  have ⟨i, hi⟩ := B.exists_mem (f y)
  ⟨_, isEqn_pullDiv B f h i hi, by rw [one_mul]; exact regAt_fnOf (U := f ⁻¹ᵁ B.U i) hi _ _⟩

theorem mem_supp_pullDiv (y : X) : y ∈ (pullDiv B f h).supp ↔ f y ∈ B.idealSheaf.support := by
  obtain ⟨i, hi⟩ := B.exists_mem (f y)
  rw [← not_iff_not, CartierDiv.notMem_supp_iff, (isEqn_pullDiv B f h i hi).generatesAt_iff, one_mul,
    B.mem_support_iff i hi, not_not]
  exact (unitAt_fnOf_iff (U := f ⁻¹ᵁ B.U i) hi _ _).trans (by rw [← Scheme.preimage_basicOpen]; rfl)

end Pull

section Comb

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def qDiv {C : CxSt F} (A : Adl C Y) : ℚ ⊗[ℤ] Y.Dv := ((A.n : ℕ) : ℚ)⁻¹ ⊗ₜ A.D

omit [NumberField F] in

theorem one_tmul_eq_iff {Δ Δ' : Y.Dv} : (1 : ℚ) ⊗ₜ[ℤ] Δ = 1 ⊗ₜ Δ' ↔ ∃ q : ℕ, 0 < q ∧ q • Δ = q • Δ' := by
  refine ⟨fun h => ?_, fun ⟨q, hq, h⟩ => ?_⟩
  · obtain ⟨⟨c, hc⟩, e⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ Y.Dv 1)).1 h
    refine ⟨c.natAbs, Int.natAbs_pos.2 (nonZeroDivisors.ne_zero hc), ?_⟩
    replace e : c • Δ = c • Δ' := e
    rw [← natCast_zsmul, ← natCast_zsmul, ← Int.sign_mul_self_eq_natAbs, mul_smul, mul_smul, e]
  · have := congrArg ((q : ℚ)⁻¹ ⊗ₜ[ℤ] ·) h
    simp only [← natCast_zsmul, ← TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast] at this
    rwa [mul_inv_cancel₀ (Nat.cast_pos.2 hq).ne'] at this

omit [NumberField F] in

def curvMet {σ : F →+* ℂ} {Δ : Y.Dv} (m : Var.Met Y σ Δ) : ChartForm Y.str σ Y.dim :=
  fun c y => ddcForm (m.wt (Var.eqn Δ y)) c y

variable {ι : Type} [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℚ) (g : ∀ σ, Pts Y σ → ℝ)

def combDen : ℕ+ := ⟨∏ i, (t i / ((ρ i).n : ℕ)).den, Finset.prod_pos fun _ _ => Rat.den_pos _⟩

def combNum (i : ι) : ℤ := ((combDen ρ t : ℕ) * (t i / ((ρ i).n : ℕ))).num

theorem combNum_mul (i : ι) : (combNum ρ t i : ℚ) * ((ρ i).n : ℕ) = (combDen ρ t : ℕ) * t i := by
  obtain ⟨c, hc⟩ : (t i / ((ρ i).n : ℕ)).den ∣ (combDen ρ t : ℕ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have e : ((combDen ρ t : ℕ) : ℚ) * (t i / ((ρ i).n : ℕ)) = ((c * (t i / ((ρ i).n : ℕ)).num : ℤ) : ℚ) := by
    rw [hc, Nat.cast_mul, mul_right_comm, Rat.den_mul_eq_num, mul_comm, Int.cast_mul, Int.cast_natCast]
  rw [combNum, e, Rat.num_intCast, ← e, mul_assoc, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (ρ i).n.ne_zero)]

def combEqn (x : Y.X) : Y.Fnˣ := ∏ i, eqn (ρ i).D x ^ combNum ρ t i

theorem isEqn_combEqn (x : Y.X) : (∑ i, combNum ρ t i • (ρ i).D).IsEqn x (combEqn ρ t x) := by
  classical
  unfold combEqn
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact ((Base.isEqn_eqn _ x).zsmul _).add ih

def comb : Adl (cxSt F) Y where
  D := ∑ i, combNum ρ t i • (ρ i).D
  n := combDen ρ t
  m σ := show Var.Met Y σ _ from
    { h := fun e y => ‖Var.tv e (combEqn ρ t (under y)) y‖ ^ 2 *
        Real.exp (2 * (∑ i, combNum ρ t i * lnAdl (ρ i) σ y - (combDen ρ t : ℕ) * g σ y))
      nonneg := fun _ _ => by positivity
      trans := fun e e' y he he' => by rw [← mul_assoc, ← mul_pow, ← norm_mul, Var.tv_mul he he'] }
  ci := 0
  lg v e y := Real.log (e.w (valAt y.1 (combEqn ρ t (below y.1) /
    eqn (∑ i, combNum ρ t i • (ρ i).D) (below y.1) : Y.Fn))) + ∑ i, combNum ρ t i * (ρ i).lg v e y

theorem isComb_comb : IsComb (comb ρ t g) ρ (fun i => t i) g := by
  have e (x : Y.X) : genAt (comb ρ t g).D x ^ 1 / ∏ i, genAt (ρ i).D x ^ combNum ρ t i =
      (combEqn ρ t x : Y.Fn) / eqn (comb ρ t g).D x := by
    simp [genAt, combEqn, div_eq_mul_inv, mul_comm]
  refine ⟨1, combNum ρ t, one_pos, fun i => ?_, one_smul _ _, fun σ z => ?_, fun v w y => ?_⟩
  · rw [Nat.cast_one, one_mul]
    have := congrArg (Rat.cast : ℚ → ℝ) (combNum_mul ρ t i).symm
    push_cast at this
    exact this
  · have h₁ : z ∈ Var.eqnSet σ (comb ρ t g).D (eqn (comb ρ t g).D (under z)) := Base.isEqn_eqn _ _
    have h₂ := Var.tv_ne_zero h₁ (isEqn_combEqn ρ t (under z))
    have h₃ : (cxSt F).pn Y σ _ ((comb ρ t g).m σ) ((cxSt F).cx Y σ (genAt (comb ρ t g).D (under z))) z = _ :=
      Var.pn_frame h₁
    refine ⟨(mul_pos (pow_pos (norm_pos_iff.2 h₂) 2) (Real.exp_pos _)).trans_eq h₃.symm, ?_⟩
    rw [e, ← Var.val_cx, lnAdl, lnN, h₃]
    erw [Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 h₂)) (Real.exp_ne_zero _)]
    rw [Real.log_exp, Real.log_pow]
    simp only [comb, Var.tv, Pi.zero_apply]
    push_cast
    ring
  · rw [e, Nat.cast_one, one_mul]
    rfl

theorem qDiv_comb : qDiv (comb ρ t g) = ∑ i, t i • qDiv (ρ i) := by
  simp only [qDiv, comb, TensorProduct.tmul_sum, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', zsmul_eq_mul,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => congrArg (· ⊗ₜ _) ?_
  have h₁ : ((combDen ρ t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (combDen ρ t).ne_zero
  have h₂ : (((ρ i).n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (ρ i).n.ne_zero
  field_simp
  rw [combNum_mul]

end Comb

section Weights

variable {T : Type} {N : ℕ}

def varpi (j : ℕ) (i : Fin N) : ℚ := if (i : ℕ) < j then 0 else -1

open Classical in

def fund (τ : T) (i : Fin N) : T → Fin N → ℝ := fun τ' a => if τ' = τ ∧ a ≤ i then 1 else 0

def coef (u : T → Fin N → ℝ) (τ : T) (i : Fin N) : ℝ := if h : (i : ℕ) + 1 < N then u τ i - u τ ⟨i + 1, h⟩ else u τ i

theorem sum_coef_fund [Fintype T] (u : T → Fin N → ℝ) (τ : T) (a : Fin N) :
    ∑ τ', ∑ i, coef u τ' i * fund τ' i τ a = u τ a := by
  classical
  let U : ℕ → ℝ := fun n => if h : n < N then u τ ⟨n, h⟩ else 0
  have e (i : Fin N) : coef u τ i * fund τ i τ a = if (a : ℕ) ≤ i then U i - U (i + 1) else 0 := by
    by_cases h : (i : ℕ) + 1 < N <;> simp [coef, fund, U, h]
  rw [Finset.sum_eq_single τ (fun τ' _ h => by simp [fund, h.symm]) (by simp), Finset.sum_congr rfl fun i _ => e i,
    Fin.sum_univ_eq_sum_range (fun n => if (a : ℕ) ≤ n then U n - U (n + 1) else 0), ← Finset.sum_filter,
    show (Finset.range N).filter ((a : ℕ) ≤ ·) = Finset.Ico (a : ℕ) N by ext; simp [and_comm],
    Finset.sum_Ico_eq_sub _ a.2.le, Finset.sum_range_sub', Finset.sum_range_sub']
  simp [U]

theorem coef_nonneg {u : T → Fin N → ℝ} (h : ∀ τ, Antitone (u τ)) (τ : T) {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    0 ≤ coef u τ i := by
  rw [coef, dif_pos hi]
  exact sub_nonneg.2 (h τ (Nat.le_succ _))

def ratOf (r : ℝ) : ℚ := Classical.epsilon fun q : ℚ => r = q

@[simp] theorem ratOf_cast (q : ℚ) : ratOf q = q :=
  (Rat.cast_injective (Classical.epsilon_spec (p := fun q' : ℚ => (q : ℝ) = q') ⟨q, rfl⟩)).symm

end Weights

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

theorem mem_support_BD_iff (k : s.Comp) (y : (Φ.C k).Y.X) :
    ((Φ.C k).π ≫ genι s.T.Z) y ∈ s.T.BD.idealSheaf.support ↔ (Φ.C k).π y ∈ genBd s.T.Z :=
  ⟨fun h => mem_genBd_iff.2 (s.T.BD_supp _ h), s.T.BD_pos _⟩

def bdPull (k : s.Comp) : (Φ.C k).Y.Dv :=
  pullDiv s.T.BD ((Φ.C k).π ≫ genι s.T.Z) fun h => CartierDiv.genericPoint_notMem_supp (Φ.C k).bd
    (((Φ.C k).bd_supp _).2 ((mem_support_BD_iff Φ k _).1 h))

theorem eff_bdPull (k : s.Comp) : (bdPull Φ k).Eff := eff_pullDiv _ _ _

theorem mem_supp_bdPull (k : s.Comp) (y : (Φ.C k).Y.X) : y ∈ (bdPull Φ k).supp ↔ (Φ.C k).π y ∈ genBd s.T.Z :=
  (mem_supp_pullDiv _ _ _ y).trans (mem_support_BD_iff Φ k y)

variable (S) in

abbrev rootExp (x : DV.Rt D.what₂.Tau N) : Letter S.Dw → ℤ := rootEx S.Dw (DV.tauEmb D x.1) x.2

def qL (k : s.Comp) (u : D.what₂.Tau → Fin N → ℚ) : ℚ ⊗[ℤ] (Φ.C k).Y.Dv :=
  -∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 ⊗ₜ divOf (Φ.C k) (rootExp S x)

abbrev RefMets : Type :=
  ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n)

def offBd (k : s.Comp) (σ : D.what₂.LL →+* ℂ) : Set (Pts (Φ.C k).Y σ) := {y | (Φ.C k).π (under y) ∉ genBd s.T.Z}

open Classical in

def extBd {k : s.Comp} {σ : D.what₂.LL →+* ℂ} (f : Pts (Φ.C k).Y σ → ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  if y ∈ offBd Φ k σ then f y else limsup f (𝓝[offBd Φ k σ] y)

variable {Φ} (hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)) (h0 : RefMets Φ)

def phW (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  2 * ∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 * lnRatio (hm k none σ (rootExp S x)) (h0 k σ (rootExp S x)) y

def thW (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) : ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim :=
  fun c y ξ => -∑ x : DV.Rt D.what₂.Tau N, u x.1 x.2 * curvMet (h0 k σ (rootExp S x)) c y ξ

theorem phW_eq_sum (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) (y : Pts (Φ.C k).Y σ) :
    phW hm h0 k σ u y = ∑ τ, ∑ i, coef u τ i * phW hm h0 k σ (fund τ i) y := by
  conv_lhs => rw [phW]; enter [2, 2, x]; rw [← sum_coef_fund u x.1 x.2]
  simp only [phW, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def CommonConst (om : ∀ k σ, ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim) (E : ∀ k σ, ChartMap (Φ.C k).Y.str σ (Φ.C k).Y.dim)
    (a K δ : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ K ∧ 0 < δ ∧ ∀ k σ τ (i : Fin N), (i : ℕ) + 1 < N →
    IsRegConst (om k σ) (thW h0 k σ (fund τ i)) (rho (om k σ) (E k σ) (phW hm h0 k σ (fund τ i))) a K δ

variable (s) in

def dirOf (b : ℕ) (η : ℚ) (μ : Fin N → ℤ) : D.what₂.Tau → Fin N → ℚ :=
  fun _ i => (2 * b * s.T.m0 : ℕ) * varpi j i + η * μ i

variable (s Φ) in

structure PolDat : Type where

  b : ℕ
  b_pos : 0 < b

  η : ℚ
  η_pos : 0 < η

  μ : Fin N → ℤ
  μ_anti : StrictAnti μ

  ab : ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y
  ab_div : ∀ k, qDiv (ab k) = qL Φ k (dirOf s b η μ) - 1 ⊗ₜ (b • bdPull Φ k)
  ab_ample : ∀ k, (Φ.C k).Y.ample (ab k).D
  ab_model : ∀ k, ∃ (M : TrueGeo.Model (Φ.C k).Y) (L : HermLB M.p) (q : ℕ+), (ab k).Induced M L q 0 ∧ ArInt.NefFib L
  ab_smooth : ∀ k σ, (cxSt D.what₂.LL).mSmooth _ σ _ ((ab k).m σ)

  om : ∀ k σ, ChartForm (Φ.C k).Y.str σ (Φ.C k).Y.dim
  om_kaehler : ∀ k σ, IsKaehlerForm ((Φ.C k).Y.an σ) (om k σ)
  om_conj : ∀ k σ σ' (ι : Pts (Φ.C k).Y σ' → Pts (Φ.C k).Y σ), IsConjMap ι → ∀ W φ,
    IsPotential ((Φ.C k).Y.an σ) (om k σ) W φ → IsPotential ((Φ.C k).Y.an σ') (om k σ') (ι ⁻¹' W) (φ ∘ ι)

  c₀ : ℝ
  c₀_pos : 0 < c₀
  curv_ge : ∀ k σ (c : AlgChart (Φ.C k).Y.str σ (Φ.C k).Y.dim), ∀ y ∈ c.e.source, ∀ ξ,
    c₀ * om k σ c y ξ ≤ curvMet ((ab k).m σ) c y ξ / ((ab k).n : ℕ)

  exph : ∀ k σ, ChartMap (Φ.C k).Y.str σ (Φ.C k).Y.dim
  exph_is : ∀ k σ, IsExph (om k σ) (exph k σ)
  exph_conj : ∀ k σ σ' (ι : Pts (Φ.C k).Y σ' → Pts (Φ.C k).Y σ), IsConjMap ι → ConjComm ι (exph k σ) (exph k σ')

  a : ℝ

  K : ℝ

  δ : ℝ
  const : (∃ a' K' δ', CommonConst hm h0 om exph a' K' δ') → CommonConst hm h0 om exph a K δ

namespace PolDat

variable {hm h0} (P : PolDat s Φ hm h0)

def m : ℕ := 2 * P.b * s.T.m0

theorem m_pos : 0 < P.m := Nat.mul_pos (Nat.mul_pos two_pos P.b_pos) s.T.torModel_multiplicity_pos

def bd (k : s.Comp) : (Φ.C k).Y.Dv := P.b • bdPull Φ k

def dirQ : D.what₂.Tau → Fin N → ℚ := dirOf s P.b P.η P.μ

def dir : D.what₂.Tau → Fin N → ℝ := fun τ i => P.dirQ τ i

theorem dir_apply (τ : D.what₂.Tau) (i : Fin N) : P.dir τ i = P.m * (varpi j i : ℚ) + P.η * P.μ i := by
  simp [dir, dirQ, dirOf, m]

theorem strictAnti_dir (τ : D.what₂.Tau) : StrictAnti (P.dir τ) := fun a b h => by
  have h₁ : (varpi j b : ℝ) ≤ varpi j a := by
    have : (a : ℕ) < b := h
    unfold varpi
    split_ifs <;> first | omega | simp
  have h₂ : (P.μ b : ℝ) < P.μ a := Int.cast_lt.2 (P.μ_anti h)
  have h₃ : (0 : ℝ) < P.η := Rat.cast_pos.2 P.η_pos
  rw [dir_apply, dir_apply]
  exact add_lt_add_of_le_of_lt (by gcongr) (by gcongr)

theorem qDiv_ab (k : s.Comp) : qDiv (P.ab k) = qL Φ k P.dirQ - 1 ⊗ₜ P.bd k := P.ab_div k

theorem eff_bd (k : s.Comp) : (P.bd k).Eff := by
  unfold bd
  induction P.b with
  | zero => exact zero_nsmul (bdPull Φ k) ▸ CartierDiv.eff_zero
  | succ n ih => exact succ_nsmul (bdPull Φ k) n ▸ ih.add (eff_bdPull Φ k)

theorem mem_supp_bd (k : s.Comp) (y : (Φ.C k).Y.X) : y ∈ (P.bd k).supp ↔ (Φ.C k).π y ∈ genBd s.T.Z := by
  obtain ⟨g, hg⟩ := (bdPull Φ k).exists_isEqn y
  obtain ⟨r, hr⟩ := CartierDiv.eff_iff.1 (eff_bdPull Φ k) y g hg
  rw [← mem_supp_bdPull, hg.mem_supp_iff, bd, (hg.nsmul _).mem_supp_iff, Units.val_pow_eq_pow_val, ← hr, ← map_pow]
  have e (a : (Φ.C k).Y.X.presheaf.stalk y) : UnitAt y (algebraMap _ (Φ.C k).Y.X.functionField a) ↔ IsUnit a :=
    ⟨fun ⟨_, hb, e⟩ => IsFractionRing.injective _ (Φ.C k).Y.X.functionField e ▸ hb, fun h => ⟨a, h, rfl⟩⟩
  rw [e, e, isUnit_pow_iff P.b_pos.ne']

theorem nefFib_ab (k : s.Comp) : (P.ab k).NefFib := have ⟨M, L, q, h⟩ := P.ab_model k; ⟨M, L, q, 0, h⟩

def regFund (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin N) (t : ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  if (i : ℕ) + 1 < N then rho (P.om k σ) (P.exph k σ) (phW hm h0 k σ (fund τ i)) y t + P.K * t ^ 2
  else extBd Φ (phW hm h0 k σ (fund τ i)) y

def reg (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin N → ℝ) (t : ℝ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  ∑ τ, ∑ i, coef u τ i * P.regFund k σ τ i t y

variable (k : s.Comp) (σ : D.what₂.LL →+* ℂ)

theorem reg_add (u v : D.what₂.Tau → Fin N → ℝ) (t : ℝ) (y : Pts (Φ.C k).Y σ) :
    P.reg k σ (u + v) t y = P.reg k σ u t y + P.reg k σ v t y := by
  simp only [reg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [coef, Pi.add_apply]
  split_ifs <;> ring

theorem reg_smul (r : ℝ) (u : D.what₂.Tau → Fin N → ℝ) (t : ℝ) (y : Pts (Φ.C k).Y σ) :
    P.reg k σ (r • u) t y = r * P.reg k σ u t y := by
  simp only [reg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [coef, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem reg_zero (u : D.what₂.Tau → Fin N → ℝ) {y : Pts (Φ.C k).Y σ} (hy : y ∈ offBd Φ k σ) :
    P.reg k σ u 0 y = phW hm h0 k σ u y := by
  rw [phW_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => congrArg _ ?_
  simp [regFund, extBd, hy, rho_zero (P.om_kaehler k σ) (P.exph_is k σ)]

theorem reg_central {u : D.what₂.Tau → Fin N → ℝ} (hu : ∀ τ a b, u τ a = u τ b) (t : ℝ) {y : Pts (Φ.C k).Y σ}
    (hy : y ∈ offBd Φ k σ) : P.reg k σ u t y = phW hm h0 k σ u y := by
  rw [phW_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) + 1 < N
  · simp [coef, h, hu τ i ⟨i + 1, h⟩]
  · simp [regFund, extBd, hy, h]

def gens (B : ℝ) : Option (DV.Rt D.what₂.Tau N) → Adl (cxSt D.what₂.LL) (Φ.C k).Y := fun o => o.elim (P.ab k) fun x =>
  adlOf (Φ.C k) (fun _ => h0 k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D x.1) x.2)

def mbarQ (B : ℝ) (u : D.what₂.Tau → Fin N → ℚ) (r : ℚ) : Adl (cxSt D.what₂.LL) (Φ.C k).Y :=
  comb (P.gens k B) (fun o => o.elim r fun x => -(u x.1 x.2 - r * P.dirQ x.1 x.2))
    fun σ y => P.reg k σ (fun τ i => u τ i - r * P.dir τ i) (Real.exp (-((r : ℝ) ^ 2)⁻¹)) y / 2

theorem qDiv_mbarQ (B : ℝ) (u : D.what₂.Tau → Fin N → ℚ) (r : ℚ) :
    qDiv (P.mbarQ k B u r) = qL Φ k u - r ⊗ₜ P.bd k := by
  have e (x : DV.Rt D.what₂.Tau N) : qDiv (P.gens k B (some x)) = 1 ⊗ₜ divOf (Φ.C k) (rootExp S x) := by
    simp [gens, qDiv, adlOf, expo_rootSym]
  rw [mbarQ, qDiv_comb, Fintype.sum_option, show P.gens k B none = P.ab k from rfl, qDiv_ab]
  simp only [e, qL, Option.elim, smul_sub, smul_neg, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.neg_tmul, TensorProduct.sub_tmul, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  abel

end PolDat

variable {hm h0}

open Classical in

def mbarOf (P : PolDat s Φ hm h0) (B : ℝ) (u : D.what₂.Tau → Fin N → ℝ) (r : ℚ) (k : s.Comp) :
    Adl (cxSt D.what₂.LL) (Φ.C k).Y :=
  if (∀ τ i, ∃ q : ℚ, u τ i = q) ∧ 0 < r then P.mbarQ k B (fun τ i => ratOf (u τ i)) r else Adl.triv _ _

theorem mbarOf_cast (P : PolDat s Φ hm h0) (B : ℝ) (u : D.what₂.Tau → Fin N → ℚ) {r : ℚ} (hr : 0 < r) (k : s.Comp) :
    mbarOf P B (fun τ i => u τ i) r k = P.mbarQ k B u r := by
  rw [mbarOf, if_pos ⟨fun τ i => ⟨_, rfl⟩, hr⟩]
  simp only [ratOf_cast]

theorem isComb_mbarOf (P : PolDat s Φ hm h0) (B : ℝ) {u : D.what₂.Tau → Fin N → ℝ} (hu : ∀ τ i, ∃ q : ℚ, u τ i = q) {r : ℚ}
    (hr : 0 < r) (k : s.Comp) : IsComb (mbarOf P B u r k) (P.gens k B)
      (fun o => o.elim (r : ℝ) fun x => -(u x.1 x.2 - r * P.dir x.1 x.2))
      fun σ y => P.reg k σ (fun τ i => u τ i - r * P.dir τ i) (Real.exp (-((r : ℝ) ^ 2)⁻¹)) y / 2 := by
  choose q hq using hu
  obtain rfl : u = fun τ i => (q τ i : ℝ) := funext₂ hq
  rw [mbarOf_cast P B q hr]
  refine cast (congrArg (IsComb _ _ · _) (funext fun o => ?_)) (isComb_comb (P.gens k B)
    (fun o => o.elim r fun x => -(q x.1 x.2 - r * P.dirQ x.1 x.2)) _)
  cases o <;> simp [PolDat.dir]

theorem mbIs_of_eq (O : Setup D) (P : PolDat O.s O.Φ O.met.hm O.met.h0) (h₁ : O.met.ab = P.ab) (h₂ : O.met.dir = P.dir)
    (h₃ : O.met.reg = P.reg) (h : O.Mb = mbarOf P) : O.MbIs := by
  rintro B - u r hu hr _ rfl - c
  rw [h, h₁, h₂, h₃, O.setB_eq]
  exact isComb_mbarOf P B hu hr c

example (O : Setup D) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (u : D.what₂.Tau → Fin O.N → ℝ) (z : Pts (O.var c) σ) :
    phW O.met.hm O.met.h0 c σ u z = 2 * O.chg c none u σ z := rfl

example (i : Fin N) (h : (i : ℕ) + 1 < N) :
    coef (fun (_ : Unit) a => (varpi j a : ℝ)) () i = if (i : ℕ) + 1 = j then 1 else 0 := by
  simp only [coef, dif_pos h, varpi]
  split_ifs <;> first | omega | simp

example {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Adl (cxSt F) Y) :
    (2 : ℚ) • qDiv (comb (fun _ : Unit => M) (fun _ => 1 / 2) fun _ _ => 0) = qDiv M := by
  simp [qDiv_comb, smul_smul]

end GlobalTheory.ShFam
