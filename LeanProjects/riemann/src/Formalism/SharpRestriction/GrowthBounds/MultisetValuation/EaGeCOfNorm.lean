import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaRestSExpVOf
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaNuTwoLeOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EGaussK

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def ea_ball (K' : Type) [NormedField K'] [IsUltrametricDist K'] : Subring K' where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by
    show ‖(1 : K')‖ ≤ 1
    rw [norm_one]
  add_mem' {a b} ha hb := le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)
  zero_mem' := by
    show ‖(0 : K')‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' {a} ha := by
    show ‖-a‖ ≤ 1
    rw [norm_neg]
    exact ha

theorem ea_mem_ball {K' : Type} [NormedField K'] [IsUltrametricDist K'] {x : K'} : x ∈ ea_ball K' ↔ ‖x‖ ≤ 1 := Iff.rfl

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

structure ea_NormExt (Y : Pend X) where
  K' : Type
  [nf : NormedField K']
  [um : IsUltrametricDist K']
  [a0 : Algebra (K0 p) K']
  [ac : Algebra Y.Kc K']
  [tw : IsScalarTower (K0 p) Y.Kc K']
  vp : K'
  vp_pow : vp ^ (p ^ 2 - 1) = (p : K')
  norm_p : ‖(p : K')‖ = (p : ℝ)⁻¹
  ball : ∀ x : Y.Kc, ‖algebraMap Y.Kc K' x‖ ≤ 1 ↔ x ∈ Y.Oc

attribute [instance] ea_NormExt.nf ea_NormExt.um ea_NormExt.a0 ea_NormExt.ac ea_NormExt.tw

def ea_RestNorm (Y : Pend X) : Prop := Nonempty (ea_NormExt Y)

theorem ea_geC_of_norm (Y : Pend X) (E : ea_NormExt Y) {x : Y.Kc} {g : ℝ}
    (h : ‖algebraMap Y.Kc E.K' x‖ ≤ (p : ℝ) ^ (-g)) : Y.geC x g := by
  intro a b _ hab
  rw [← E.ball, map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow, E.norm_p]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : ‖algebraMap Y.Kc E.K' x‖ ^ b ≤ ((p : ℝ) ^ (-g)) ^ b := pow_le_pow_left₀ (norm_nonneg _) h b
  have h2 : ((p : ℝ) ^ (-g)) ^ b = (p : ℝ) ^ (-g * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  have h3 : ((p : ℝ)⁻¹) ^ (-a) = (p : ℝ) ^ (a : ℝ) := by
    rw [inv_zpow, zpow_neg, inv_inv, Real.rpow_intCast]
  rw [h3]
  calc ‖algebraMap Y.Kc E.K' x‖ ^ b * (p : ℝ) ^ (a : ℝ) ≤ (p : ℝ) ^ (-g * b) * (p : ℝ) ^ (a : ℝ) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (-g * b + a) := by rw [Real.rpow_add hp0]
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)

theorem ea_Rp_le_ball (Y : Pend X) (E : ea_NormExt Y) : Rp p E.K' E.vp ≤ ea_ball E.K' := by
  unfold Rp
  rw [Subring.closure_le]
  rintro x (⟨y, rfl⟩ | hx)
  · show ‖algebraMap (K0 p) E.K' (algebraMap (WW p) (K0 p) y)‖ ≤ 1
    rw [IsScalarTower.algebraMap_apply (K0 p) Y.Kc E.K']
    exact (E.ball _).2 (Y.witt_mem_integers_Cp y)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    show ‖E.vp‖ ≤ 1
    have hn : p ^ 2 - 1 ≠ 0 := by
      have := hp.out.two_le
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    have h1 : ‖E.vp‖ ^ (p ^ 2 - 1) ≤ 1 := by
      rw [← norm_pow, E.vp_pow, E.norm_p]
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
      exact inv_le_one_of_one_le₀ this
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hn).1 h1

theorem ea_lowN (D : Formalism.BasicNotions.D7) (Y : Pend X) (hNm : ea_RestNorm Y) (hS : ea_RestSU X Y) (hA : admitted D X Y) (v : X.Pl)
    (j : ℕ) (P : X.ColCh j → MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) (g : ℝ)
    (hK : ∀ (K' : Type) [NormedField K'] [IsUltrametricDist K'] [Algebra (K0 p) K'] (vp : K')
      (u : Fin (X.G.P.n' v) → K') (F : MvPowerSeries (X.ZA j) K'), vp ^ (p ^ 2 - 1) = (p : K') →
      ‖(p : K')‖ = (p : ℝ)⁻¹ → (∀ s, ‖u s‖ ≤ 1) →
      ea_InClassA X (ea_ball K') j (X.hhA K' j v u) (atPi vp F) → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      ‖MvPolynomial.coeff n (applyD (P I) F)‖ ≤ (p : ℝ) ^ (-g)) :
    ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U) →
      ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
        Y.geC (MvPolynomial.coeff n (applyD (P I)
          (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U)))) g := by
  intro U hU I n
  obtain ⟨E⟩ := hNm
  obtain ⟨u, hu, hcls⟩ := hS (hA.1 p) hA.2.2.2.1 v j U hU E.K' (ea_ball E.K') E.vp E.vp_pow (ea_Rp_le_ball Y E)
    fun x hx => (E.ball x).2 hx
  have h1 := hK E.K' E.vp u _ E.vp_pow E.norm_p hu hcls I n
  rw [ea_applyD_map, MvPolynomial.coeff_map] at h1
  exact ea_geC_of_norm Y E h1

instance ea_neZero (X : Sys p) (v : X.Pl) : NeZero (X.G.P.n' v / 2) :=
  ⟨by have := (X.std v).two_le; omega⟩

theorem ea_hn (X : Sys p) (v : X.Pl) : X.G.P.n' v = 2 * (X.G.P.n' v / 2) := by
  obtain ⟨k, hk⟩ := (X.std v).even
  omega

def ea_eS {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν) : Fin n' ≃ ZMod (2 * ν) where
  toFun s := (s.val : ZMod (2 * ν))
  invFun x := ⟨x.val, by rw [hn]; exact ZMod.val_lt x⟩
  left_inv s := by
    apply Fin.ext
    show ((s.val : ZMod (2 * ν))).val = s.val
    exact ZMod.val_natCast_of_lt (by have := s.isLt; omega)
  right_inv x := by
    show ((x.val : ℕ) : ZMod (2 * ν)) = x
    exact ZMod.natCast_zmod_val x

abbrev ea_S (X : Sys p) (v : X.Pl) : Type := ZMod (2 * (X.G.P.n' v / 2))

def ea_e (X : Sys p) (v : X.Pl) : Fin (X.G.P.n' v) ≃ ea_S X v := ea_eS (ea_hn X v)

def ea_colN (X : Sys p) (v : X.Pl) (j : ℕ) (s : ea_S X v) : ℕ := (X.nuv v (j + 1) ((ea_e X v).symm s) 1).toNat

def ea_hts (X : Sys p) (v : X.Pl) (j : ℕ) (s : ea_S X v) (c : Fin (ea_colN X v j s)) : ℕ :=
  X.colHt v (j + 1) ((ea_e X v).symm s) c.val

theorem ea_hp (X : Sys p) (v : X.Pl) (j : ℕ) (s : ea_S X v) (c : Fin (ea_colN X v j s)) :
    ea_hts X v j s c ≤ NN X.G.P.m X.t j := ea_colH_le j _ _

def ea_Ic (X : Sys p) (v : X.Pl) (j : ℕ) (I : X.ColCh j) (s : ea_S X v) (c : Fin (ea_colN X v j s)) :
    Fin (ea_hts X v j s c) → Fin (NN X.G.P.m X.t (j + 1)) := fun i' => I v ((ea_e X v).symm s) c.val i'.val

def ea_TT (X : Sys p) (v : X.Pl) : Finset (ea_S X v) := (X.TT v).map (ea_e X v).toEmbedding

def ea_eps (X : Sys p) (v : X.Pl) (j : ℕ) :
    Formalism.InvariantFactorPaths.G7.ZV (X.G.P.n' v / 2) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) → X.ZA j :=
  fun y => ⟨v, ((ea_e X v).symm y.1, y.2.1, y.2.2)⟩

def ea_Exp (X : Sys p) (v : X.Pl) (j i : ℕ) (I : X.ColCh j) : ℕ :=
  ∑ s : ea_S X v, ∑ c : Fin (ea_colN X v j s),
    (if s.val % 2 = 0 then
      min (ea_hts X v j s c) i -
        ((univ.image (ea_Ic X v j I s c)) ∩ univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card
    else ((univ.image (ea_Ic X v j I s c)) ∩ univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card)

def ea_BrJet (X : Sys p) : Prop :=
  ∀ (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (F : MvPowerSeries (X.ZA j) K') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
    MvPolynomial.coeff n (applyD (X.PIv j I v) F) = 0 ∨
      ∃ n', MvPolynomial.coeff n (applyD (X.PIv j I v) F) =
        MvPolynomial.coeff n' (Formalism.DworkPowerSeriesWeights.frameJet (ea_colN X v j) (ea_hts X v j) (ea_hp X v j) (ea_Ic X v j I)
          (resV (ea_eps X v j) F))

def ea_BrScale (X : Sys p) : Prop :=
  ∀ (v : X.Pl) (j i : ℕ) (K' : Type) [Field K'] (F : MvPowerSeries (X.ZA j) K') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
    MvPolynomial.coeff n (applyD (PIvS X j I (fun _ => i) v) F) = 0 ∨
      MvPolynomial.coeff n (applyD (PIvS X j I (fun _ => i) v) F) =
        (p : K') ^ (ea_Exp X v j i I) * MvPolynomial.coeff n (applyD (X.PIv j I v) F)

def ea_BrClass (X : Sys p) : Prop :=
  ∀ (v : X.Pl) (j : ℕ) (K' : Type) [NormedField K'] [IsUltrametricDist K'] (vp : K') (u : Fin (X.G.P.n' v) → K')
    (F : MvPowerSeries (X.ZA j) K'), ea_InClassA X (ea_ball K') j (X.hhA K' j v u) (atPi vp F) →
    Formalism.InvariantFactorPaths.G7.InClass (p : K') (Formalism.InvariantFactorPaths.G7.hhS p fun s => u ((ea_e X v).symm s))
      (MvPowerSeries.subst (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x :
        MvPowerSeries (Formalism.InvariantFactorPaths.G7.ZV (X.G.P.n' v / 2) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) K'))
        (resV (ea_eps X v j) F))

def ea_BrNum (X : Sys p) : Prop :=
  ∀ (v : X.Pl), ∀ j < X.mm,
    Formalism.GrowthSums.excessGain (p : ℝ) (ea_TT X v) (Formalism.InvariantFactorPaths.G7.dSet (ea_TT X v))
              (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_TT X v) (ea_colN X v j) (ea_hts X v j) s : ℝ))
              (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_TT X v) (ea_colN X v j) (ea_hts X v j) s : ℝ))
              (Formalism.InvariantFactorPaths.G7.deLoss p (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) (ea_TT X v)
                (Formalism.InvariantFactorPaths.G7.alG (ea_TT X v) (ea_colN X v j) (ea_hts X v j))
                (Formalism.InvariantFactorPaths.G7.lsG (ea_TT X v) (ea_colN X v j) (ea_hts X v j))) = X.g0v v (j + 1) ∧
    Formalism.GrowthSums.gainG (p : ℝ) (ea_TT X v) (Formalism.InvariantFactorPaths.G7.oddT (ea_TT X v))
              (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_TT X v) (ea_colN X v j) (ea_hts X v j) s : ℝ))
              (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_TT X v) (ea_colN X v j) (ea_hts X v j) s : ℝ))
              (Formalism.InvariantFactorPaths.G7.deLoss p (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) (ea_TT X v)
                (Formalism.InvariantFactorPaths.G7.alG (ea_TT X v) (ea_colN X v j) (ea_hts X v j))
                (Formalism.InvariantFactorPaths.G7.lsG (ea_TT X v) (ea_colN X v j) (ea_hts X v j))) = X.gv v (j + 1) ∧
    ∑ s ∈ ea_TT X v \ Formalism.InvariantFactorPaths.G7.oddT (ea_TT X v),
      (Formalism.InvariantFactorPaths.G7.alG (ea_TT X v) (ea_colN X v j) (ea_hts X v j) s : ℝ) = X.alEven v

theorem ea_two_lt (X : Sys p) (v : X.Pl) : 2 < p := by
  have := (X.std v).five_le
  omega

theorem ea_A1U (D : Formalism.BasicNotions.D7) (Y : Pend X) (hNm : ea_RestNorm Y) (hS : ea_RestSU X Y) (hJ : ea_BrJet X)
    (hC : ea_BrClass X) (hN : ea_BrNum X) : EntryBoundOfHypotheses X Y D := by
  intro hA v j hj
  refine ea_lowN D Y hNm hS hA v j (fun I => X.PIv j I v) _ ?_
  intro K' _ _ _ vp u F hvp hnp hu hcls I n
  have := charZero_K' p K'
  rcases hJ v j K' F I n with h0 | ⟨n', h1⟩
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · rw [h1, ← (hN v j hj).1]
    exact Formalism.InvariantFactorPaths.G7.kernel_a_one_generic K' p _ _ _ _ vp _ (ea_TT X v) _ _ (ea_hp X v j) (ea_Ic X v j I)
      (ea_two_lt X v) hnp hvp (fun s => hu _) (hC v j K' vp u F hcls) n'

theorem ea_A2U (D : Formalism.BasicNotions.D7) (Y : Pend X) (hNm : ea_RestNorm Y) (hS : ea_RestSU X Y) (hJ : ea_BrJet X)
    (hC : ea_BrClass X) (hN : ea_BrNum X) : PlacewiseLowerBoundEvenShift X Y D := by
  intro hA v j hj
  refine ea_lowN D Y hNm hS hA v j (fun I => X.PIv j I v) _ ?_
  intro K' _ _ _ vp u F hvp hnp hu hcls I n
  have := charZero_K' p K'
  rcases hJ v j K' F I n with h0 | ⟨n', h1⟩
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · rw [h1, ← (hN v j hj).2.1, ← (hN v j hj).2.2]
    exact Formalism.InvariantFactorPaths.G7.kernel_a_two_generic K' p _ _ _ _ vp _ (ea_TT X v) _ _ (ea_hp X v j) (ea_Ic X v j I)
      (ea_two_lt X v) hnp hvp (fun s => hu _) (hC v j K' vp u F hcls) n'

theorem ea_BU (D : Formalism.BasicNotions.D7) (Y : Pend X) (hNm : ea_RestNorm Y) (hS : ea_RestSU X Y) (hJ : ea_BrJet X)
    (hSc : ea_BrScale X) (hC : ea_BrClass X) (hN : ea_BrNum X) : RestBU X Y D := by
  intro hA v j hj i hi
  refine ea_lowN D Y hNm hS hA v j (fun I => PIvS X j I (fun _ => i) v) _ ?_
  intro K' _ _ _ vp u F hvp hnp hu hcls I n
  have := charZero_K' p K'
  rcases hSc v j i K' F I n with h0 | h2
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  rw [h2]
  rcases hJ v j K' F I n with h0 | ⟨n', h1⟩
  · rw [h0, mul_zero, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · rw [h1, ← (hN v j hj).2.1]
    exact Formalism.InvariantFactorPaths.G7.kernel_b_generic K' p _ _ _ i _ vp _ (ea_TT X v) _ _ (ea_hp X v j) (ea_Ic X v j I)
      (ea_two_lt X v) hnp (Finset.mem_Icc.1 hi).1 hvp (fun s => hu _) (hC v j K' vp u F hcls) n'

end Formalism.MainNotions.FormalGroupSystem.Pf
