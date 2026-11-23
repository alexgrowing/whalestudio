import Formalism.SharpRestriction.LevelLetterCocycles.InvLevAtOf
import Formalism.SharpRestriction.LevelLetterCocycles.LevLetEMul
import Formalism.SharpRestriction.LevelLetterCocycles.CrtFamDet

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

theorem inId_sub {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f g : W.EE} (hf : InId W a e α f)
    (hg : InId W a e α g) : InId W a e α (f - g) := by
  have := inId_add W hf (inId_smul W hg (-1))
  convert this using 1
  simp [sub_eq_add_neg]

theorem inId_sum {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} (S : Finset ℕ) (f : ℕ → W.EE)
    (hf : ∀ i ∈ S, InId W a e α (f i)) : InId W a e α (∑ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact inId_add W (hf i (Finset.mem_insert_self i S)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem piece_upd (H : ℕ → ℕ) (a : ZMod n) (e s : ℕ) (hs : s < e) (z r : LetA O n) (hr : r ∈ W.AΔ)
    (hz : z = ps W s ^ H s * r) :
    InId W a e (Function.update (fun t => -((H t : ℕ) : ℤ)) s (H s)) (ιE (letE a * z)) := by
  unfold InId
  have en := numI_upd W H e s hs (H s)
  have ed := denI_upd W H e s hs (H s)
  simp only [numI, denI] at en ed
  rw [en, ed]
  refine ⟨(∏ t ∈ (Finset.range e).erase s, ps W t ^ H t) * r,
    Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun t _ =>
      Subalgebra.pow_mem _ (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _) hr, ?_⟩
  rw [← map_mul, hz]
  congr 1
  simp only [Int.toNat_natCast, show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero, one_mul]
  ring

variable [IsDomain O]

theorem value0 (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (a : ZMod n) (z : LetA O n) (hz : z ∈ W.AΔ) :
    ∃ (o : O) (w : LetA O n), w ∈ W.AΔ ∧
      (letE a : LetA O n) * z = letE a * (algebraMap O (LetA O n) o + W.π₀ * w) := by
  obtain ⟨f, hf, -⟩ := hR.2.1 z hz
  set c := PowerSeries.constantCoeff (f a) with hc
  set g := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (f a) with hg
  have hfa : f a = g * PowerSeries.X + c • (1 : PowerSeries O) := by
    rw [PowerSeries.smul_eq_C_mul, mul_one, hg, hc]
    exact PowerSeries.eq_shift_mul_X_add_const (f a)
  have ha0 : PowerSeries.constantCoeff W.π₀₁ = 0 := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR
  have hs0 := PowerSeries.HasSubst.of_constantCoeff_zero' ha0
  set w' : LetA O n := letE a * fun _ => PowerSeries.subst W.π₀₁ g with hw'
  have hza : z a = PowerSeries.subst W.π₀₁ g * W.π₀₁ + c • (1 : PowerSeries O) := by
    rw [hf a]
    change PowerSeries.subst W.π₀₁ (f a) = _
    rw [hfa, ← PowerSeries.coe_substAlgHom hs0, map_add, map_mul, PowerSeries.substAlgHom_X,
      map_smul, map_one]
  have key : (letE a : LetA O n) * z = letE a * (algebraMap O (LetA O n) c + W.π₀ * w') := by
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_eq_same, one_mul, hw', hza,
        LocWach.π₀, Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply]
      ring
    · simp [letE, Pi.single_eq_of_ne hi, hw']
  refine ⟨c, w', ?_, key⟩
  refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hR.1 (fun i => by
    show W.π₀₁ ≠ 0
    exact Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
  have hidem : w' * letE a = w' := by
    rw [hw', mul_comm, ← mul_assoc, Formalism.MainNotions.UnusedSlot80.DivLevR.letE_idem]
  have e : W.π₀ * w' = letE a * z - letE a * algebraMap O (LetA O n) c := by
    rw [key]; linear_combination (-W.π₀) * hidem
  rw [e]
  exact W.AΔ.sub_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.DivLevR.letE_mem a) hz)
    (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.DivLevR.letE_mem a) (W.AΔ.algebraMap_mem c))

theorem lE_add' (κ κ' : ℕ) : lE W (κ + κ') = lE W κ * lE W κ' := by simp [lE, pow_add]

theorem inId0_of_mem (H : ℕ → ℕ) (a : ZMod n) (e : ℕ) {z : LetA O n} (hz : z ∈ W.AΔ) :
    InId W a e (fun t => -((H t : ℕ) : ℤ)) (ιE (letE a * z)) := by
  unfold InId
  have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((H s : ℕ) : ℤ)).toNat) = 1 :=
    Finset.prod_eq_one fun s _ => by rw [show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
  rw [h1]
  refine ⟨(∏ s ∈ Finset.range e, ps W s ^ (-(-((H s : ℕ) : ℤ))).toNat) * z,
    Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun t _ =>
      Subalgebra.pow_mem _ (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _) hz, ?_⟩
  rw [← map_mul]; congr 1; ring

def Dv (H : ℕ → ℕ) (s : ℕ) (z : LetA O n) : Prop := ∃ r ∈ W.AΔ, z = ps W s ^ H s * r

theorem dv_add {H : ℕ → ℕ} {s : ℕ} {z z' : LetA O n} (h : Dv W H s z) (h' : Dv W H s z') :
    Dv W H s (z + z') := by
  obtain ⟨r, hr, rfl⟩ := h; obtain ⟨r', hr', rfl⟩ := h'
  exact ⟨r + r', W.AΔ.add_mem hr hr', by ring⟩

theorem dv_sum {H : ℕ → ℕ} {s : ℕ} (S : Finset ℕ) (f : ℕ → LetA O n) (hf : ∀ t ∈ S, Dv W H s (f t)) :
    Dv W H s (∑ t ∈ S, f t) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, W.AΔ.zero_mem, by simp⟩
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact dv_add W (hf i (Finset.mem_insert_self i S)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem dv_prod (H : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) (s : ℕ) (hs : s ∈ S) {r : LetA O n}
    (hr : r ∈ W.AΔ) : Dv W H s ((∏ t ∈ S, ps W t ^ (k * H t)) * r) := by
  have hps := Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
  refine ⟨ps W s ^ ((k - 1) * H s) * (∏ t ∈ S.erase s, ps W t ^ (k * H t)) * r,
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (hps s) _)
      (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)) hr, ?_⟩
  rw [← Finset.mul_prod_erase _ _ hs]
  have e : k * H s = H s + (k - 1) * H s := by
    have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    conv_lhs => rw [hk']
    ring
  rw [e, pow_add]; ring

theorem lE_smul (κ : ℕ) (z : W.EE) : lE W κ * z = (((PD.p : ℕ) : O) ^ κ) • z := by
  rw [Algebra.smul_def, map_pow, map_natCast]; rfl

theorem killer_elem (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W)
    (hS : PsStable W) (hRAT : CutU.RATCore W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (a : ZMod n) (e : ℕ) (M : ℕ)
    (hM : ∀ s < e, A.Hs a e s ≤ M) (hInv : ∀ s < e, InvLevAt W s) (κc : ℕ) (u₀ r₀ : LetA O n) (u rs : ℕ → LetA O n)
    (hr₀ : r₀ ∈ W.AΔ) (hrs : ∀ s < e, rs s ∈ W.AΔ)
    (hsum : lA W ^ κc = u₀ + ∑ s ∈ Finset.range e, u s)
    (hu₀ : u₀ = (∏ t ∈ Finset.range e, ps W t ^ (2 * A.Hs a e t)) * r₀)
    (hus : ∀ s < e, u s = W.π₀ * (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * A.Hs a e t)) * rs s)
    (y : W.EE) (hy : InFr W a 1 (abelian₂ W A a e) y) :
    ∃ (K : ℕ) (x : ℕ → O) (x₀ : O), InFr W a (W.π₀ * abelian₂ W A a e) 1
      (lE W K * PPγ W e (Finset.Ico (-(M : ℤ)) M) y -
        ∑ s ∈ Finset.range e, x s • ιE (letE a * u s) - x₀ • ιE (letE a * (abelian₂ W A a e * r₀))) := by
  set H : ℕ → ℕ := A.Hs a e with hH
  set Λ := abelian₂ W A a e with hΛ
  set JS : Finset ℤ := Finset.Ico (-(M : ℤ)) M with hJS
  set α0 : ℕ → ℤ := fun t => -((H t : ℕ) : ℤ) with hα0
  have hps := Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _
  have hy0 : InId W a e α0 y := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e y).1 hy
  have hlev := fun s (hs : s < e) => lev_const W hKL hS hCA h5 a e H M hM y hy0 s hs (hInv s hs)
  choose! κs xs hks using hlev
  set K₁ := ∑ s ∈ Finset.range e, κs s with hK₁
  set x' : ℕ → O := fun s => ((PD.p : ℕ) : O) ^ (K₁ - κs s) * xs s with hx'
  have hum : ∀ s < e, u s ∈ W.AΔ := fun s hs => by
    rw [hus s hs]
    exact W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W)
      (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)) (hrs s hs)
  set Y' := lE W (κc + K₁) * PPγ W e JS y - ∑ s ∈ Finset.range e, x' s • ιE (letE a * u s) with hY'
  have hPPm : InId W a e α0 (PPγ W e JS y) := inId_aeval W hS _ y hy0
  have hY'm : InId W a e α0 Y' :=
    inId_sub W (inId_lE W hPPm _) (inId_sum W _ _ fun s hs =>
      inId_smul W (inId0_of_mem W H a e (hum s (Finset.mem_range.1 hs))) _)
  obtain ⟨z', hz'm, hz'⟩ := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e Y').2 hY'm
  obtain ⟨o', w', hw'm, hval⟩ := value0 W hR a z' hz'm
  set C0 := ιE (letE a * (Λ * r₀)) with hC0
  have hC0m : InId W a e α0 C0 := inId0_of_mem W H a e (W.AΔ.mul_mem hΛm hr₀)
  set Y := lE W κc * Y' - o' • C0 with hYdef
  have hYm : InId W a e α0 Y := inId_sub W (inId_lE W hY'm _) (inId_smul W hC0m _)
  have hYΛ : InFr W a 1 Λ Y := (Formalism.MainNotions.UnusedSlot80.UnivC.inFr_lam_iff W A a e Y).2 hYm

  have hlevel : ∀ s < e, InId W a e (Function.update α0 s (H s)) Y := by
    intro s hs
    have hsm : s ∈ Finset.range e := Finset.mem_range.2 hs
    have hdvu : ∀ t ∈ (Finset.range e).erase s, Dv W H s (u t) := by
      intro t ht
      obtain ⟨hts, htm⟩ := Finset.mem_erase.1 ht
      rw [hus t (Finset.mem_range.1 htm)]
      have := dv_prod W H 2 (by norm_num) ((Finset.range e).erase t) s
        (Finset.mem_erase.2 ⟨Ne.symm hts, hsm⟩) (hrs t (Finset.mem_range.1 htm))
      obtain ⟨r, hr, he⟩ := this
      exact ⟨W.π₀ * r, W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hr, by rw [mul_assoc, he]; ring⟩
    have hdv0 : Dv W H s (lA W ^ κc - u s) := by
      have e1 : lA W ^ κc - u s = u₀ + ∑ t ∈ (Finset.range e).erase s, u t := by
        rw [hsum, ← Finset.add_sum_erase _ _ hsm]; ring
      rw [e1, hu₀]
      exact dv_add W (dv_prod W H 2 (by norm_num) _ s hsm hr₀) (dv_sum W _ _ hdvu)
    have hdvΛ : Dv W H s (Λ * r₀) := by
      have := dv_prod W H 1 le_rfl (Finset.range e) s hsm hr₀
      simpa [hΛ, abelian₂] using this
    have hdec : Y = lE W κc * (lE W κc * (lE W (K₁ - κs s) *
          (lE W (κs s) * PPγ W e JS y - ιE (letE a) * algebraMap O W.EE (xs s)))) +
        lE W κc * (x' s • ιE (letE a * (lA W ^ κc - u s))) -
        lE W κc * ∑ t ∈ (Finset.range e).erase s, x' t • ιE (letE a * u t) - o' • C0 := by
      have hK : κc + K₁ = κc + (K₁ - κs s) + κs s := by
        have : κs s ≤ K₁ := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hsm
        omega
      rw [hYdef, hY', ← Finset.add_sum_erase _ _ hsm, hK, lE_add', lE_add', hx']
      simp only [lE, lA, Algebra.smul_def, map_mul, map_sub, map_pow, map_natCast]
      ring
    rw [hdec]
    refine inId_sub W (inId_sub W (inId_add W ?_ ?_) ?_) ?_
    · exact inId_lE W (inId_lE W (inId_lE W (hks s hs) _) _) _
    · obtain ⟨r, hr, he⟩ := hdv0
      exact inId_lE W (inId_smul W (piece_upd W H a e s hs _ r hr he) _) _
    · refine inId_lE W (inId_sum W _ _ fun t ht => inId_smul W ?_ _) _
      obtain ⟨r, hr, he⟩ := hdvu t ht
      exact piece_upd W H a e s hs _ r hr he
    · obtain ⟨r, hr, he⟩ := hdvΛ
      exact inId_smul W (piece_upd W H a e s hs _ r hr he) _

  have hV : ∑ s ∈ Finset.range e, u s = W.π₀ *
      ∑ s ∈ Finset.range e, (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * H t)) * rs s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hus s (Finset.mem_range.1 hs)]; ring
  have hΛ2 : Λ * (Λ * r₀) = u₀ := by
    rw [hu₀, ← mul_assoc, ← sq, hΛ, abelian₂, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← pow_mul, mul_comm]
  have hπ : InFr W a W.π₀ Λ Y := by
    refine ⟨lA W ^ κc * w' + algebraMap O (LetA O n) o' *
        ∑ s ∈ Finset.range e, (∏ t ∈ (Finset.range e).erase s, ps W t ^ (2 * H t)) * rs s,
      W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.KL.lA_mem W) _) hw'm)
        (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.sum_mem fun s hs =>
          W.AΔ.mul_mem (W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem (hps t) _)
            (hrs s (Finset.mem_range.1 hs)))), ?_⟩
    have hE : ιE Λ * Y = ιE (lA W ^ κc * (letE a * 1 * z') -
        algebraMap O (LetA O n) o' * (letE a * (Λ * (Λ * r₀)))) := by
      have h1 : ιE Λ * Y = lE W κc * (ιE Λ * Y') - algebraMap O W.EE o' * (ιE Λ * C0) := by
        rw [hYdef, Algebra.smul_def]; ring
      rw [h1, hz', hC0, ← Formalism.MainNotions.UnusedSlot80.KL.ι_lE W κc, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      simp only [← map_mul, ← map_sub]
      congr 1
      ring
    rw [hE]
    congr 1
    linear_combination (lA W ^ κc) * hval - (algebraMap O (LetA O n) o' * letE a) * hΛ2 +
      (algebraMap O (LetA O n) o' * letE a) * hsum + (algebraMap O (LetA O n) o' * letE a) * hV

  obtain ⟨f₁, f₂, hYf, hf₁, hf₂⟩ := hRAT hCA h5 A a e 1 (fun s => ((H s : ℕ) : ℤ)) le_rfl
    (fun s _ => ⟨by omega, le_rfl⟩) Y hYΛ
    (fun s hs => ⟨0, Y, 0, by simp [lE], by
      have := hlevel s hs
      unfold InId at this
      have en := numI_upd W H e s hs (H s)
      have ed := denI_upd W H e s hs (H s)
      simp only [numI, denI] at en ed
      rw [en, ed] at this
      exact this, ⟨0, W.AΔ.zero_mem, by simp⟩⟩)
    (fun _ => ⟨0, Y, 0, by simp [lE], hπ, ⟨0, W.AΔ.zero_mem, by simp⟩⟩)
  have hf₁' : InFr W a (W.π₀ * Λ) 1 f₁ := by
    have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((H s : ℕ) : ℤ)).toNat) = 1 :=
      Finset.prod_eq_one fun s _ => by rw [show (-((H s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
    have h2 : (∏ s ∈ Finset.range e, ps W s ^ (((H s : ℕ) : ℤ)).toNat) = Λ := by
      rw [hΛ, abelian₂]; exact Finset.prod_congr rfl fun s _ => by rw [Int.toNat_natCast]
    rw [h1, h2, pow_one] at hf₁
    exact hf₁
  refine ⟨κc + (κc + K₁), fun s => ((PD.p : ℕ) : O) ^ κc * x' s, o', ?_⟩
  have hfin : lE W (κc + (κc + K₁)) * PPγ W e JS y -
      ∑ s ∈ Finset.range e, (((PD.p : ℕ) : O) ^ κc * x' s) • ιE (letE a * u s) -
        o' • ιE (letE a * (Λ * r₀)) = f₁ + f₂ := by
    rw [← hYf, hYdef, hY', hC0, lE_add']
    simp only [lE, Algebra.smul_def, map_mul, map_pow, map_natCast, Finset.mul_sum, mul_sub, mul_assoc]
  rw [hfin]
  obtain ⟨u₁, hu₁, e₁⟩ := hf₁'
  obtain ⟨u₂, hu₂, e₂⟩ := hf₂
  exact ⟨u₁ + u₂, W.AΔ.add_mem hu₁ hu₂, by rw [mul_add, e₁, e₂, ← map_add]; congr 1; ring⟩

end Formalism.MainNotions.UnusedSlot80.UGen
