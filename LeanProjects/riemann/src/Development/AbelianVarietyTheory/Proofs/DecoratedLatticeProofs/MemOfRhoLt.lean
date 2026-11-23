import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevZeroUniq
open GlobalTheory.SplitWeil GlobalTheory.StepData

variable {D : D7} {c : Comm D} {v : VCom c} {PP : Formalism.L2.DIV.Pl D.host.E}

def rho (G : GLoc v) : 𝓞 D.host.E →+* G.k := (G.q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem rho_apply (G : GLoc v) (z : 𝓞 D.host.E) : rho G z = (ofSplit G.q).pr (z : D.host.E) := rfl

theorem rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E} (hz : z ∈ PP.asIdeal) :
    valuation G.k (rho G z) < 1 := by
  by_cases h0 : z = 0
  · subst h0; simp
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  have h1 := (hid.2 z h0).1 hz
  rw [← G.q.sec_pr, ← G.q.int_iff] at h1
  change (G.q.pr.comp (incA D)) _ ∉ _ at h1
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le] at h1
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).1 h1

theorem mem_of_rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E}
    (hz : valuation G.k (rho G z) < 1) : z ∈ PP.asIdeal := by
  by_cases h0 : z = 0
  · subst h0; exact zero_mem _
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  refine (hid.2 z h0).2 ?_
  rw [← G.q.sec_pr, ← G.q.int_iff]
  change (G.q.pr.comp (incA D)) _ ∉ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).2 hz

def out (y : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E := Function.surjInv (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem mk_out (y : Formalism.L2.DIV.kP PP) : Ideal.Quotient.mk PP.asIdeal (out y) = y :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem rho_sub_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {y : Formalism.L2.DIV.kP PP} {z : 𝓞 D.host.E}
    (hz : Ideal.Quotient.mk PP.asIdeal z = y) : valuation G.k (rho G (out y) - rho G z) < 1 := by
  rw [← map_sub]
  refine rho_lt G hid (Ideal.Quotient.eq.1 ?_)
  rw [mk_out, hz]

def pos (G : GLoc v) : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r :=
  finSumFinEquiv.trans (finCongr (by have := G.hs; unfold Ranks.r; omega))

theorem pos_val (G : GLoc v) (a : Fin D.R.k ⊕ Fin (G.s + 1)) : (pos G a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
  rcases a with a | a <;> rfl

def lift (G : GLoc v) (g : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) G.k :=
  fun a b => rho G (out (g (pos G a) (pos G b)))

theorem lift_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) :
    MaxM (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) := by
  intro a b
  have e : (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) a b =
      rho G (out ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) (pos G a) (pos G b))) -
      rho G (if a = b then 1 else 0) := by
    simp only [Matrix.sub_apply, lift, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  refine rho_sub_lt G hid ?_
  simp only [Matrix.one_apply, (pos G).injective.eq_iff]
  split_ifs <;> simp

theorem red_iff (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    GlobalTheory.LevZero.Red G PP x g ↔ MaxM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) := by
  constructor
  · intro h a b
    have := h a b (pos G a) (pos G b) (pos_val G a) (pos_val G b) _ (mk_out _)
    simpa only [Matrix.sub_apply, lift, rho_apply] using this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = pos G a := Fin.ext (ha.trans (pos_val G a).symm)
    obtain rfl : b' = pos G b := Fin.ext (hb.trans (pos_val G b).symm)
    have e : (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E) =
        ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) a b + (rho G (out (g.val (pos G a) (pos G b))) - rho G z) := by
      simp only [Matrix.sub_apply, lift, rho_apply]; ring
    rw [e]
    exact Valuation.map_add_lt _ (h a b) (rho_sub_lt G hid hz)

theorem intM_J (G : GLoc v) (x : G.S.P.J) : IntM (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val ∧
    IntM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹).val :=
  mem_KO.1 (G.S.P.le_KO x.2)

theorem red_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) : GlobalTheory.LevZero.Red G PP 1 1 := by
  rw [red_iff G hid]
  have := (lift_one G hid).neg
  simpa using this

theorem red_uniq (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {x x' : G.S.P.J} {g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)}
    (hx : GlobalTheory.LevZero.Red G PP x g) (hx' : GlobalTheory.LevZero.Red G PP x' g')
    (hk : x.1⁻¹ * x'.1 ∈ KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) : g = g' := by
  rw [red_iff G hid] at hx hx'
  set X := (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX
  set X' := (x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX'
  have h1 : MaxM ((X⁻¹ * X').val - 1) := mem_KOne.1 hk
  have h2 : MaxM (lift G g'.val - lift G g.val) := by
    have e : lift G g'.val - lift G g.val =
        (X.val - lift G g.val) + -(X'.val - lift G g'.val) + X.val * ((X⁻¹ * X').val - 1) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_one]
      abel
    rw [e]
    exact (hx.add hx'.neg).add ((intM_J G x).1.mul_maxM h1)
  refine Units.ext (Matrix.ext fun a' b' => ?_)
  obtain ⟨a, rfl⟩ := (pos G).surjective a'
  obtain ⟨b, rfl⟩ := (pos G).surjective b'
  have h3 : valuation G.k (rho G (out (g'.val (pos G a) (pos G b)) - out (g.val (pos G a) (pos G b)))) < 1 := by
    rw [map_sub]; simpa only [Matrix.sub_apply, lift] using h2 a b
  have h4 := Ideal.Quotient.eq.2 (mem_of_rho_lt G hid h3)
  rw [mk_out, mk_out] at h4
  exact h4.symm

end GlobalTheory.LevZeroUniq

theorem GlobalTheory.LevZeroUniq.main : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → GlobalTheory.LevZero.Red G PP 1 1 ∧ ∀ (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (kP PP)), GlobalTheory.LevZero.Red G PP x g → GlobalTheory.LevZero.Red G PP x' g' → x.1⁻¹ * x'.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1)) → g = g' := by
  intro D c v G PP hid
  exact ⟨GlobalTheory.LevZeroUniq.red_one G hid, fun x x' g g' hx hx' hk => GlobalTheory.LevZeroUniq.red_uniq G hid hx hx' hk⟩

end
