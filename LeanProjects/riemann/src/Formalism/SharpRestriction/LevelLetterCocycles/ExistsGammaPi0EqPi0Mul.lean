import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.KWP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE

abbrev γL : Module.End O W.EE := (W.γE W.gam).toLinearMap

def fac (e : ℕ) (i : ℤ) : Polynomial O :=
  Polynomial.X ^ (PD.p ^ e) - Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ e) : Oˣ) : O)

theorem aeval_mul_apply (P Q : Polynomial O) (f : W.EE) :
    Polynomial.aeval (γL W) (P * Q) f = Polynomial.aeval (γL W) P (Polynomial.aeval (γL W) Q f) := by
  rw [map_mul]; rfl

theorem raise (hKL : KillerLevCore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (hS : PsStable W) {a : ZMod n} {e : ℕ}
    {α : ℕ → ℤ} {f : W.EE} (hf : InId W a e α f) {s : ℕ} (hs : s < e) (N : ℕ) (T : Finset ℤ)
    (hT : Finset.Ico (α s) (α s + N) ⊆ T) :
    ∃ κ : ℕ, InId W a e (Function.update α s (α s + N))
      (lE W κ * Polynomial.aeval (γL W) (∏ i ∈ T, fac W e i) f) := by
  have hprod : (∏ i ∈ T, fac W e i) = (∏ i ∈ Finset.Ico (α s) (α s + N), fac W e i) *
      ∏ i ∈ T \ Finset.Ico (α s) (α s + N), fac W e i := by
    rw [mul_comm, Finset.prod_sdiff hT]
  have hg := Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS (∏ i ∈ T \ Finset.Ico (α s) (α s + N), fac W e i) f hf
  obtain ⟨κ, hκ⟩ := ((hKL hCA e ∅).2 a α s hs _ hg).2.2 N
  exact ⟨κ, by rw [hprod, aeval_mul_apply]; exact hκ⟩

theorem inFr_add {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f)
    (hg : InFr W a num den g) : InFr W a num den (f + g) := by
  unfold InFr at *
  obtain ⟨u, hu, e1⟩ := hf
  obtain ⟨u', hu', e2⟩ := hg
  exact ⟨u + u', add_mem hu hu', by rw [mul_add, e1, e2, mul_add, map_add]⟩

theorem inFr_zero (a : ZMod n) (num den : LetA O n) : InFr W a num den 0 := by
  unfold InFr
  exact ⟨0, zero_mem _, by simp⟩

theorem inFr_num_drop {a : ZMod n} {num x den : LetA O n} {f : W.EE} (hx : x ∈ W.AΔ)
    (h : InFr W a (num * x) den f) : InFr W a num den f := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  exact ⟨x * u, mul_mem hx hu, by rw [e]; congr 1; ring⟩

theorem inFr_den_mul {a : ZMod n} {num den d : LetA O n} {f : W.EE} (hd : d ∈ W.AΔ)
    (h : InFr W a num den f) : InFr W a num (den * d) f := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  refine ⟨u * d, mul_mem hu hd, ?_⟩
  rw [map_mul, mul_right_comm, e, ← map_mul]
  congr 1; ring

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) (κ : ℕ) :
    InFr W a num den (lE W κ * f) := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  refine ⟨u * ((PD.p : ℕ) : LetA O n) ^ κ, mul_mem hu (pow_mem (natCast_mem _ _) _), ?_⟩
  have hl : lE W κ = algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) ^ κ) := by
    unfold lE; rw [map_pow, map_natCast]
  rw [hl, mul_left_comm, e, ← map_mul]
  congr 1; ring

theorem inFr_congr {a : ZMod n} {num num' den den' : LetA O n} {f : W.EE} (hn : num = num')
    (hd : den = den') (h : InFr W a num den f) : InFr W a num' den' f := by
  subst hn hd; exact h

theorem prod_ps_split (hπ : W.π₀ ∈ W.AΔ) (e : ℕ) (b a d : ℕ → ℕ)
    (h : ∀ s ∈ Finset.range e, b s = a s + d s) :
    (∏ s ∈ Finset.range e, ps W s ^ b s) =
      (∏ s ∈ Finset.range e, ps W s ^ a s) * ∏ s ∈ Finset.range e, ps W s ^ d s := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s hs => by rw [h s hs, pow_add]

theorem prod_ps_mem (hπ : W.π₀ ∈ W.AΔ) (e : ℕ) (d : ℕ → ℕ) :
    (∏ s ∈ Finset.range e, ps W s ^ d s) ∈ W.AΔ := by
  exact prod_mem fun s _ => pow_mem (Formalism.MainNotions.UnusedSlot80.KL.ps_mem (W := W) hπ s) _

theorem prod_ps_mem' (hπ : W.π₀ ∈ W.AΔ) (S : Finset ℕ) (d : ℕ → ℕ) :
    (∏ s ∈ S, ps W s ^ d s) ∈ W.AΔ := by
  exact prod_mem fun s _ => pow_mem (Formalism.MainNotions.UnusedSlot80.KL.ps_mem (W := W) hπ s) _

theorem level_form (hπ : W.π₀ ∈ W.AΔ) {a : ZMod n} {e s : ℕ} (hs : s ∈ Finset.range e) (α : ℕ → ℤ) (x : ℤ)
    (H : ℕ → ℕ) (hα : ∀ t ∈ (Finset.range e).erase s, -(H t : ℤ) ≤ α t) {g : W.EE}
    (hg : InId W a e (Function.update α s x) g) :
    InFr W a (ps W s ^ x.toNat) (ps W s ^ (-x).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ H t) g := by
  simp only [InId] at hg
  rw [← Finset.mul_prod_erase _ _ hs, ← Finset.mul_prod_erase _ _ hs] at hg
  simp only [Function.update_apply, if_pos rfl] at hg
  have e1 : (∏ t ∈ (Finset.range e).erase s, ps W t ^ (if t = s then x else α t).toNat) =
      ∏ t ∈ (Finset.range e).erase s, ps W t ^ (α t).toNat :=
    Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]
  have e2 : (∏ t ∈ (Finset.range e).erase s, ps W t ^ (-(if t = s then x else α t)).toNat) =
      ∏ t ∈ (Finset.range e).erase s, ps W t ^ (-α t).toNat :=
    Finset.prod_congr rfl fun t ht => by rw [if_neg (Finset.ne_of_mem_erase ht)]
  rw [e1, e2] at hg
  have h1 := inFr_num_drop W (prod_ps_mem' W hπ _ _) hg
  have h2 := inFr_den_mul W (prod_ps_mem' W hπ ((Finset.range e).erase s) (fun t => H t - (-α t).toNat)) h1
  refine inFr_congr W rfl ?_ h2
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [← pow_add]
  congr 1
  have := hα t ht
  show (-α t).toNat + (H t - (-α t).toNat) = H t
  omega

section ThetaShiftProofs

open Formalism.MainNotions.LocalTheoryWindows

def mmF (A : ArcP n) : LT → ℕ
  | .thin => A.G₀
  | .up b => b + A.S
  | .down _ => 0

def dnF : LT → ℕ
  | .thin => 0
  | .up _ => 0
  | .down b => b

def nnNF (A : ArcP n) : LT → ℕ
  | .thin => A.G₀
  | .up _ => 0
  | .down b => b + A.S

def nnDF : LT → ℕ
  | .thin => 0
  | .up b => b
  | .down _ => 0

theorem mmDen_eq (A : ArcP n) (c : ZMod n) :
    mmDen W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ mmF A (A.ty (c - (s : ZMod n))) := by
  unfold mmDen prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem downB_eq (A : ArcP n) (c : ZMod n) :
    downB W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ dnF (A.ty (c - (s : ZMod n))) := by
  unfold downB prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem nnNum_eq (A : ArcP n) (c : ZMod n) :
    nnNum W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ nnNF A (A.ty (c - (s : ZMod n))) := by
  unfold nnNum prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem nnDen_eq (A : ArcP n) (c : ZMod n) :
    nnDen W A c = ∏ s ∈ Finset.range (A.len c), ps W s ^ nnDF (A.ty (c - (s : ZMod n))) := by
  unfold nnDen prodTy
  refine Finset.prod_congr rfl fun s _ => ?_
  cases A.ty (c - (s : ZMod n)) <;> rfl

theorem letter_after (c : ZMod n) (e s : ℕ) (hs : s ≤ e) :
    c - (s : ZMod n) = (c - (e : ZMod n)) + ((e - s : ℕ) : ZMod n) := by
  rw [Nat.cast_sub hs]; ring

theorem thick_near_cut (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ}
    (hs : s < A.len c) (hj : A.len c - s ≤ A.j) (hth : (A.ty (c - (s : ZMod n))).thick) :
    (A.ty (c - (s : ZMod n))).size + A.S ≤ A.G₀ := by
  obtain ⟨-, -, hcuts, -, -, -, -, -, hlast⟩ := hOK
  obtain ⟨-, -, hc', -⟩ := hcuts c hc
  have hk1 : 1 ≤ A.len c - s := by omega
  have heq : c - (s : ZMod n) = (c - ((A.len c : ℕ) : ZMod n)) + ((A.len c - s : ℕ) : ZMod n) :=
    letter_after c (A.len c) s hs.le
  rcases hlast with h | ⟨hj', -, h⟩
  · have h0 := h _ hc' (A.len c - s) hk1 hj
    rw [heq, h0] at hth
    exact absurd hth (by decide)
  · have hk : A.len c - s = 1 := by omega
    rw [heq, hk, Nat.cast_one]
    exact h _ hc'

theorem thick_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ}
    (hs : s < A.len c) (hth : (A.ty (c - (s : ZMod n))).thick) :
    (A.ty (c - (s : ZMod n))).size + A.S ≤ A.Hs c (A.len c) s := by
  unfold ArcP.Hs
  split_ifs with hc'
  · rcases hc' with h | h
    · rw [h] at hth; exact absurd hth (by decide)
    · exact thick_near_cut A hOK hc hs h hth
  · exact hOK.2.2.2.2.2.2.2.1 _ hth

theorem G_le_H (A : ArcP n) (hOK : A.OK) (c : ZMod n) (s : ℕ) : A.G₀ ≤ A.Hs c (A.len c) s := by
  unfold ArcP.Hs
  split_ifs
  · exact le_rfl
  · exact hOK.2.2.2.2.2.1

theorem mmF_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ} (hs : s < A.len c) :
    mmF A (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  have hG := G_le_H A hOK c s
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin => exact hG
  | up b =>
    have h' := thick_le_H A hOK hc hs (by rw [hty]; rfl)
    rw [hty] at h'
    exact h'
  | down b => exact Nat.zero_le _

theorem nnNF_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ} (hs : s < A.len c) :
    nnNF A (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  have hG := G_le_H A hOK c s
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin => exact hG
  | up b => exact Nat.zero_le _
  | down b =>
    have h' := thick_le_H A hOK hc hs (by rw [hty]; rfl)
    rw [hty] at h'
    exact h'

theorem nnDF_le_H (A : ArcP n) (hOK : A.OK) {c : ZMod n} (hc : c ∈ A.cuts) {s : ℕ} (hs : s < A.len c) :
    nnDF (A.ty (c - (s : ZMod n))) ≤ A.Hs c (A.len c) s := by
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin => exact Nat.zero_le _
  | up b =>
    have h' := thick_le_H A hOK hc hs (by rw [hty]; rfl)
    rw [hty] at h'
    exact le_trans (Nat.le_add_right b A.S) h'
  | down b => exact Nat.zero_le _

theorem size_pos (A : ArcP n) (hOK : A.OK) (i : ZMod n) (hth : (A.ty i).thick) : 1 ≤ (A.ty i).size := by
  have hok := hOK.2.2.2.2.1 i
  cases hty : A.ty i with
  | thin => rw [hty] at hth; exact absurd hth (by decide)
  | up b =>
    rw [hty] at hok
    have h' : A.η < b := hok
    show 1 ≤ b
    omega
  | down b =>
    rw [hty] at hok
    have h' : A.η < b := hok
    show 1 ≤ b
    omega

end ThetaShiftProofs

theorem toNat_sub_of (a d : ℕ) (h : a = 0 ∨ d = 0) :
    ((a : ℤ) - d).toNat = a ∧ (-((a : ℤ) - d)).toNat = d := by
  rcases h with h | h <;> subst h <;> constructor <;> omega

theorem inId_of_inFr {a : ZMod n} (e : ℕ) (α δ : ℕ → ℕ) (h : ∀ s ∈ Finset.range e, α s = 0 ∨ δ s = 0)
    {f : W.EE} (hf : InFr W a (∏ s ∈ Finset.range e, ps W s ^ α s) (∏ s ∈ Finset.range e, ps W s ^ δ s) f) :
    InId W a e (fun s => (α s : ℤ) - δ s) f := by
  simp only [InId]
  refine inFr_congr W ?_ ?_ hf
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).1]
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).2]

theorem inFr_of_inId {a : ZMod n} (e : ℕ) (α δ : ℕ → ℕ) (h : ∀ s ∈ Finset.range e, α s = 0 ∨ δ s = 0)
    {f : W.EE} (hf : InId W a e (fun s => (α s : ℤ) - δ s) f) :
    InFr W a (∏ s ∈ Finset.range e, ps W s ^ α s) (∏ s ∈ Finset.range e, ps W s ^ δ s) f := by
  simp only [InId] at hf
  refine inFr_congr W ?_ ?_ hf
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).1]
  · exact Finset.prod_congr rfl fun s hs => by rw [(toNat_sub_of (α s) (δ s) (h s hs)).2]

theorem prod_zero_pow (e : ℕ) : (∏ s ∈ Finset.range e, ps W s ^ (fun _ => (0 : ℕ)) s) = 1 := by
  simp

section Pi0

open Formalism.MainNotions.UnusedSlot80.ToolsR Formalism.MainNotions.WachCoordinates

theorem exists_gamma_pi0_eq_pi0_mul [IsDomain O] [NeZero n] (hR : RingP W) : ∃ z ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * z := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.2.1
  have e : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      qP W := by
    funext i; simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP, LocWach.π₀]
  rw [e] at hw
  have hp0 := Formalism.MainNotions.WachCoordinates.Br.p_ne_zero_O W
  have hπ : W.π₀ ∈ W.AΔ := hR.1
  have hq : qP W ∈ W.AΔ := qP_AΔ hR
  have hc : W.π₀ * qP W ∈ W.AΔ := Subalgebra.mul_mem _ hπ hq
  have hc0 : ∀ i, (W.π₀ * qP W) i ≠ 0 := fun i => by
    show W.π₀₁ * qP W i ≠ 0
    exact mul_ne_zero (π₀₁_ne hR) (q_component_ne_zero' hR hp0 i)
  have hwΔ : (w : LetA O n) ∈ W.AΔ := by
    refine cancel_AΔ hc hc0 ?_
    have : W.π₀ * qP W * (w : LetA O n) = W.γA W.gam W.π₀ - W.π₀ := by rw [hw]; ring
    rw [this]
    exact Subalgebra.sub_mem _ (γA_mem W _ hπ) hπ
  refine ⟨1 + qP W * (w : LetA O n), Subalgebra.add_mem _ (Subalgebra.one_mem _)
    (Subalgebra.mul_mem _ hq hwΔ), ?_⟩
  linear_combination hw

def InIdπ (a : ZMod n) (e : ℕ) (α : ℕ → ℤ) (f : W.EE) : Prop :=
  ∃ u ∈ W.AΔ, ιE (denI W e α) * f = ιE (letE a * numI W e α * (W.π₀ * u))

theorem inIdπ_γ [IsDomain O] [NeZero n] (hR : RingP W) (hS : PsStable W) {a : ZMod n} {e : ℕ}
    {α : ℕ → ℤ} {f : W.EE} (hf : InIdπ W a e α f) : InIdπ W a e α (W.γE W.gam f) := by
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨z, hz, hγπ⟩ := exists_gamma_pi0_eq_pi0_mul W hR
  choose r hr r' hr' hrr hσ using hS
  have h := Formalism.MainNotions.UnusedSlot80.KL.transport W (W.γA W.gam) (W.γE W.gam) (fun x => W.γE_ext _ x)
    (Formalism.MainNotions.UnusedSlot80.KL.γA_letE W _) r r' hrr hσ hfu
  refine ⟨(∏ t ∈ Finset.range e, r' t ^ (-(α t)).toNat) * (∏ t ∈ Finset.range e, r t ^ (α t).toNat) *
    (z * W.γA W.gam u), ?_, ?_⟩
  · refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) (Subalgebra.mul_mem _ hz (γA_mem W _ hu))
    · exact Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr' t) _
    · exact Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (hr t) _
  · refine h.trans ?_
    rw [show W.γA W.gam (W.π₀ * u) = W.γA W.gam W.π₀ * W.γA W.gam u from map_mul _ _ _, hγπ]
    congr 1; ring

theorem inIdπ_add {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f g : W.EE} (hf : InIdπ W a e α f)
    (hg : InIdπ W a e α g) : InIdπ W a e α (f + g) := by
  unfold InIdπ at *
  obtain ⟨u, hu, e1⟩ := hf
  obtain ⟨u', hu', e2⟩ := hg
  exact ⟨u + u', add_mem hu hu', by rw [mul_add, e1, e2, ← map_add]; congr 1; ring⟩

theorem inIdπ_smul {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {f : W.EE} (hf : InIdπ W a e α f) (c : O) :
    InIdπ W a e α (c • f) := by
  unfold InIdπ at *
  obtain ⟨u, hu, e⟩ := hf
  refine ⟨u * algebraMap O (LetA O n) c, mul_mem hu (Subalgebra.algebraMap_mem _ c), ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, e, ← map_mul]
  congr 1; ring

theorem inIdπ_aeval [IsDomain O] [NeZero n] (hR : RingP W) (hS : PsStable W) {a : ZMod n} {e : ℕ}
    {α : ℕ → ℤ} (P : Polynomial O) : ∀ f, InIdπ W a e α f → InIdπ W a e α (Polynomial.aeval (γL W) P f) := by
  intro f hf
  induction P using Polynomial.induction_on' generalizing f with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact inIdπ_add W (hp f hf) (hq f hf)
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine inIdπ_smul W ?_ c
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact inIdπ_γ W hR hS ih

end Pi0

section Down

theorem lE_eq_alg (κ : ℕ) : lE W κ = algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ) := by
  unfold lE; rw [map_pow, map_natCast]

theorem γE_lE (κ : ℕ) : W.γE W.gam (lE W κ) = lE W κ := by
  unfold lE; rw [map_pow, map_natCast]

theorem γE_const (c : ZMod n) (x : O) :
    W.γE W.gam (ιE (letE c) * algebraMap O W.EE x) = ιE (letE c) * algebraMap O W.EE x := by
  have h1 := W.γE_ext W.gam (letE c)
  rw [map_mul, h1]
  erw [Formalism.MainNotions.UnusedSlot80.KL.γA_letE W W.gam c]
  rw [AlgHom.commutes]

theorem inFr_neg {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) :
    InFr W a num den (-f) := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  exact ⟨-u, neg_mem hu, by rw [mul_neg, e, ← map_neg]; congr 1; ring⟩

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f)
    (hg : InFr W a num den g) : InFr W a num den (f - g) := by
  simpa only [sub_eq_add_neg] using inFr_add W hf (inFr_neg W hg)

theorem inFr_smul {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) (c : O) :
    InFr W a num den (c • f) := by
  unfold InFr at *
  obtain ⟨u, hu, e⟩ := h
  refine ⟨u * algebraMap O (LetA O n) c, mul_mem hu (Subalgebra.algebraMap_mem _ c), ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, e, ← map_mul]
  congr 1; ring

def αk (e s : ℕ) (d : ℕ → ℕ) (k : ℕ) : ℕ → ℤ := fun t => if t = s then (k : ℤ) else -(d t : ℤ)

theorem inId_αk_iff {a : ZMod n} {e s : ℕ} (hs : s ∈ Finset.range e) (d : ℕ → ℕ) (k : ℕ) (y : W.EE) :
    InId W a e (αk e s d k) y ↔
      InFr W a (ps W s ^ k) (∏ t ∈ (Finset.range e).erase s, ps W t ^ d t) y := by
  have hn : (∏ t ∈ Finset.range e, ps W t ^ (αk e s d k t).toNat) = ps W s ^ k := by
    rw [← Finset.mul_prod_erase _ _ hs, Finset.prod_eq_one, mul_one]
    · simp [αk]
    · intro t ht
      have ht' := Finset.ne_of_mem_erase ht
      have h0 : (αk e s d k t).toNat = 0 := by simp only [αk, if_neg ht']; omega
      rw [h0, pow_zero]
  have hd : (∏ t ∈ Finset.range e, ps W t ^ (-(αk e s d k t)).toNat) =
      ∏ t ∈ (Finset.range e).erase s, ps W t ^ d t := by
    rw [← Finset.mul_prod_erase _ _ hs]
    have h1 : (-(αk e s d k s)).toNat = 0 := by
      have h3 : αk e s d k s = k := by simp [αk]
      rw [h3]; omega
    rw [h1, pow_zero, one_mul]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.ne_of_mem_erase ht
    have h2 : (-(αk e s d k t)).toNat = d t := by simp only [αk, if_neg ht']; omega
    rw [h2]
  simp only [InId]
  rw [hn, hd]

theorem update_αk (e s : ℕ) (d : ℕ → ℕ) (k : ℕ) :
    Function.update (αk e s d k) s ((k : ℤ) + 1) = αk e s d (k + 1) := by
  funext t
  by_cases h : t = s <;> simp [Function.update_apply, αk, h]

theorem inFr_pow_mono {a : ZMod n} {s k k' : ℕ} (hk : k ≤ k') {den : LetA O n} {f : W.EE}
    (hπ : W.π₀ ∈ W.AΔ) (h : InFr W a (ps W s ^ k') den f) : InFr W a (ps W s ^ k) den f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add] at h
  exact inFr_num_drop W (pow_mem (Formalism.MainNotions.UnusedSlot80.KL.ps_mem (W := W) hπ s) _) h

theorem div_of_val (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hvp : v (algebraMap O LL ((PD.p : ℕ) : O)) = 1) (c : O) (M : ℕ)
    (hc : v (algebraMap O LL c) = ((M : ℕ) : WithTop ℚ)) :
    ∃ o : O, ((PD.p : ℕ) : O) ^ M = c * o := by
  have hc0 : algebraMap O LL c ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hc
    simp at hc
  have hx : algebraMap O LL ((PD.p : ℕ) : O) ^ M / algebraMap O LL c * algebraMap O LL c =
      algebraMap O LL ((PD.p : ℕ) : O) ^ M := div_mul_cancel₀ _ hc0
  have hvM : v (algebraMap O LL ((PD.p : ℕ) : O) ^ M) = ((M : ℕ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hvp, nsmul_one]
  have key : v (algebraMap O LL ((PD.p : ℕ) : O) ^ M / algebraMap O LL c) + v (algebraMap O LL c) =
      v (algebraMap O LL c) := by
    rw [← AddValuation.map_mul, hx, hvM, hc]
  rw [hc] at key
  have h0 : 0 ≤ v (algebraMap O LL ((PD.p : ℕ) : O) ^ M / algebraMap O LL c) :=
    (WithTop.add_le_add_iff_right (WithTop.natCast_ne_top M)).1 (by rw [zero_add, key])
  obtain ⟨o, ho⟩ := hO2 _ h0
  refine ⟨o, hinj ?_⟩
  rw [map_pow, map_mul, ho, mul_comm, hx]

end Down

section Main

open Formalism.MainNotions.LocalTheoryWindows

theorem ppγ_eq (e : ℕ) (JS : Finset ℤ) (f : W.EE) :
    PPγ W e JS f = Polynomial.aeval (γL W) (∏ i ∈ JS.erase 0, fac W e i)
      (Polynomial.aeval (γL W) (∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k) f) := by
  unfold PPγ
  rw [show PPO W e JS = (∏ i ∈ JS.erase 0, fac W e i) *
      ∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k from rfl]
  exact aeval_mul_apply W _ _ f

theorem mem_JS_thin (A : ArcP n) {c : ZMod n} {s : ℕ} (hs : s < A.len c)
    (hth : A.ty (c - (s : ZMod n)) = LT.thin) {i : ℤ} (hi1 : -(2 * A.G₀ : ℤ) ≤ i) (hi2 : i ≤ A.G₀) :
    i ∈ A.JS c := by
  unfold ArcP.JS
  apply Finset.mem_union_left
  rw [if_pos ⟨s, hs, hth⟩]
  exact Finset.mem_Icc.2 ⟨hi1, hi2⟩

theorem mem_JS_up (A : ArcP n) {c : ZMod n} {s : ℕ} (hs : s < A.len c) {b : ℕ}
    (hτ : A.ty (c - (s : ZMod n)) = LT.up b) {i : ℤ} (hi : i ∈ Finset.Ico (-(b : ℤ) - A.S) (-(b : ℤ))) :
    i ∈ A.JS c := by
  unfold ArcP.JS
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_range.2 hs, ?_⟩
  rw [hτ]
  exact hi

theorem mem_JS_down (A : ArcP n) {c : ZMod n} {s : ℕ} (hs : s < A.len c) {b : ℕ}
    (hτ : A.ty (c - (s : ZMod n)) = LT.down b) {i : ℤ} (hi : i ∈ Finset.Ico (b : ℤ) ((b : ℤ) + A.S)) :
    i ∈ A.JS c := by
  unfold ArcP.JS
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_range.2 hs, ?_⟩
  rw [hτ]
  exact hi

theorem lam_eq (A : ArcP n) (c : ZMod n) (e : ℕ) :
    abelian₂ W A c e = ∏ s ∈ Finset.range e, ps W s ^ A.Hs c e s := rfl

theorem inId_Lam {A : ArcP n} {c : ZMod n} {e : ℕ} {f : W.EE} (h : InFr W c 1 (abelian₂ W A c e) f) :
    InId W c e (fun s => ((0 : ℕ) : ℤ) - (A.Hs c e s : ℕ)) f := by
  refine inId_of_inFr W e (fun _ => 0) (fun s => A.Hs c e s) (fun s _ => Or.inl rfl) ?_
  simp only [pow_zero, Finset.prod_const_one]
  exact h

theorem inFr_Lam {A : ArcP n} {c : ZMod n} {e : ℕ} {f : W.EE}
    (h : InId W c e (fun s => ((0 : ℕ) : ℤ) - (A.Hs c e s : ℕ)) f) : InFr W c 1 (abelian₂ W A c e) f := by
  have h' := inFr_of_inId W e (fun _ => 0) (fun s => A.Hs c e s) (fun s _ => Or.inl rfl) h
  simp only [pow_zero, Finset.prod_const_one] at h'
  exact h'

private theorem nnDF_le_mmF (A : ArcP n) (τ : Formalism.MainNotions.LocalTheoryWindows.LT) : nnDF τ ≤ mmF A τ := by
  cases τ with
  | thin => exact Nat.zero_le _
  | up b => exact Nat.le_add_right b A.S
  | down b => exact le_rfl

theorem part_b (hKL : KillerLevCore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) (hRAT : Formalism.MainNotions.UnusedSlot80.CutU.RATCore W) (A : ArcP n) (hOK : A.OK) {c : ZMod n}
    (hc : c ∈ A.cuts) {f : W.EE} (h1 : InFr W c 1 (abelian₂ W A c (A.len c)) f)
    (h2 : InFr W c 1 (mmDen W A c) f) :
    InFr W c 1 (nnDen W A c) (PPγ W (A.len c) (A.JS c) f) := by
  obtain ⟨α, hα_def⟩ : ∃ α : ℕ → ℤ,
      α = fun t : ℕ => ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ : ∃ E : ℕ → ℤ,
      E = fun t : ℕ => ((0 : ℕ) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  have hαt : ∀ t : ℕ, α t = ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hα_def]
  have hEt : ∀ t : ℕ, E t = ((0 : ℕ) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hE_def]
  have hf2 : InId W c (A.len c) α f := by
    rw [hα_def]
    refine inId_of_inFr W (A.len c) (fun _ => 0) (fun t => mmF A (A.ty (c - (t : ZMod n))))
      (fun _ _ => Or.inl rfl) ?_
    simp only [pow_zero, Finset.prod_const_one]
    rw [mmDen_eq] at h2
    exact h2
  have hg := Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS
    (∑ k ∈ Finset.range (PD.p ^ A.len c), (Polynomial.X : Polynomial O) ^ k) f hf2
  have hLam : InFr W c 1 (abelian₂ W A c (A.len c)) (PPγ W (A.len c) (A.JS c) f) :=
    inFr_Lam W (Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS (PPO W (A.len c) (A.JS c)) f (inId_Lam W h1))
  have hE : ∀ s < A.len c, -(A.Hs c (A.len c) s : ℤ) ≤ E s ∧ E s ≤ A.Hs c (A.len c) s := by
    intro s hs
    have := nnDF_le_H A hOK hc hs
    rw [hEt]
    constructor <;> omega
  have hdec : ∀ s < A.len c, ∃ κ : ℕ, ∃ f₁ f₂ : W.EE,
      lE W κ * PPγ W (A.len c) (A.JS c) f = f₁ + f₂ ∧
      InFr W c (ps W s ^ (E s).toNat)
        (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range (A.len c)).erase s, ps W t ^ A.Hs c (A.len c) t) f₁ ∧
      InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 f₂ := by
    intro s hs
    have hq : α s + ((mmF A (A.ty (c - (s : ZMod n))) - nnDF (A.ty (c - (s : ZMod n))) : ℕ) : ℤ) = E s := by
      have := nnDF_le_mmF A (A.ty (c - (s : ZMod n)))
      rw [hαt, hEt]
      omega
    have hT : Finset.Ico (α s) (α s + ((mmF A (A.ty (c - (s : ZMod n))) - nnDF (A.ty (c - (s : ZMod n))) : ℕ) : ℤ)) ⊆
        (A.JS c).erase 0 := by
      intro i hi
      rw [Finset.mem_Ico, hαt] at hi
      rw [Finset.mem_erase]
      cases hty : A.ty (c - (s : ZMod n)) with
      | thin =>
        rw [hty] at hi
        simp only [mmF, nnDF] at hi
        exact ⟨by omega, mem_JS_thin A hs hty (by omega) (by omega)⟩
      | up b =>
        rw [hty] at hi
        simp only [mmF, nnDF] at hi
        exact ⟨by omega, mem_JS_up A hs hty (Finset.mem_Ico.2 ⟨by omega, by omega⟩)⟩
      | down b =>
        rw [hty] at hi
        simp only [mmF, nnDF] at hi
        exfalso; omega
    obtain ⟨κ, hκ⟩ := raise W hKL hCA hS hg hs _ _ hT
    rw [hq] at hκ
    have hκ' : InId W c (A.len c) (Function.update α s (E s)) (lE W κ * PPγ W (A.len c) (A.JS c) f) := by
      rw [ppγ_eq]; exact hκ
    have hα' : ∀ t ∈ (Finset.range (A.len c)).erase s, -(A.Hs c (A.len c) t : ℤ) ≤ α t := by
      intro t ht
      have ht' := Finset.mem_range.1 (Finset.mem_of_mem_erase ht)
      have := mmF_le_H A hOK hc ht'
      rw [hαt]
      omega
    exact ⟨κ, _, 0, (add_zero _).symm,
      level_form W hπ (Finset.mem_range.2 hs) α (E s) (A.Hs c (A.len c)) hα' hκ', inFr_zero W c _ _⟩
  obtain ⟨f₁, f₂, hsum, hf₁, hf₂⟩ := hRAT hCA h5 A c (A.len c) 0 E (Nat.zero_le 1) hE _ hLam hdec
    (fun h => absurd h (by decide))
  have hf₁' : InFr W c 1 (nnDen W A c) f₁ := by
    rw [pow_zero, one_mul] at hf₁
    have hi : InId W c (A.len c) E f₁ := hf₁
    rw [hE_def] at hi
    have h' := inFr_of_inId W (A.len c) (fun _ => 0) (fun t => nnDF (A.ty (c - (t : ZMod n))))
      (fun _ _ => Or.inl rfl) hi
    simp only [pow_zero, Finset.prod_const_one] at h'
    rw [nnDen_eq]
    exact h'
  have hnn : nnDen W A c ∈ W.AΔ := by
    rw [nnDen_eq]; exact prod_ps_mem W hπ _ _
  have hLm : abelian₂ W A c (A.len c) ∈ W.AΔ := by
    unfold abelian₂; exact prod_ps_mem W hπ _ _
  have hf₂' : InFr W c 1 (nnDen W A c) f₂ := by
    have h' := inFr_den_mul W hnn hf₂
    rw [one_mul] at h'
    rw [← one_mul (W.π₀ * abelian₂ W A c (A.len c))] at h'
    exact inFr_num_drop W (mul_mem hπ hLm) h'
  rw [hsum]
  exact inFr_add W hf₁' hf₂'

theorem gsub_eq (x : W.EE) :
    W.γE W.gam x - x = Polynomial.aeval (γL W) (Polynomial.X - 1 : Polynomial O) x := by
  simp [γL]

theorem fac_zero (e : ℕ) : fac W e 0 = Polynomial.X ^ (PD.p ^ e) - 1 := by
  simp [fac]

theorem xsub_ppo (e : ℕ) (JS : Finset ℤ) :
    (Polynomial.X - 1 : Polynomial O) * PPO W e JS = ∏ i ∈ insert 0 (JS.erase 0), fac W e i := by
  have hg : (Polynomial.X - 1 : Polynomial O) *
      ∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k = Polynomial.X ^ (PD.p ^ e) - 1 :=
    mul_geom_sum _ _
  have hP : PPO W e JS = (∏ i ∈ JS.erase 0, fac W e i) *
      ∑ k ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ k := rfl
  rw [hP, Finset.prod_insert (by simp), fac_zero]
  linear_combination (∏ i ∈ JS.erase 0, fac W e i) * hg

private theorem dnF_eq_zero_or_mmF_eq_zero (A : ArcP n) (τ : Formalism.MainNotions.LocalTheoryWindows.LT) : dnF τ = 0 ∨ mmF A τ = 0 := by
  cases τ with
  | thin => exact Or.inl rfl
  | up b => exact Or.inl rfl
  | down b => exact Or.inr rfl

private theorem nnNF_eq_zero_or_nnDF_eq_zero (A : ArcP n) (τ : Formalism.MainNotions.LocalTheoryWindows.LT) : nnNF A τ = 0 ∨ nnDF τ = 0 := by
  cases τ with
  | thin => exact Or.inr rfl
  | up b => exact Or.inl rfl
  | down b => exact Or.inr rfl

theorem part_a [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) (hRAT : Formalism.MainNotions.UnusedSlot80.CutU.RATCore W) (A : ArcP n) (hOK : A.OK) {c : ZMod n}
    (hc : c ∈ A.cuts) {f : W.EE} (h1 : InFr W c 1 (abelian₂ W A c (A.len c)) f)
    (h2 : InFr W c 1 (mmDen W A c) f)
    (h3 : InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam f - f)) :
    InFr W c (W.π₀ * nnNum W A c) (nnDen W A c)
      (W.γE W.gam (PPγ W (A.len c) (A.JS c) f) - PPγ W (A.len c) (A.JS c) f) := by
  obtain ⟨hl1, hl2, -⟩ := hOK.2.2.1 c hc
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨F, hFdef⟩ : ∃ F : W.EE,
      F = W.γE W.gam (PPγ W (A.len c) (A.JS c) f) - PPγ W (A.len c) (A.JS c) f := ⟨_, rfl⟩
  rw [← hFdef]
  obtain ⟨α₂, hα₂_def⟩ : ∃ α : ℕ → ℤ,
      α = fun t : ℕ => ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  obtain ⟨α₃, hα₃_def⟩ : ∃ α : ℕ → ℤ, α = fun t : ℕ =>
      (dnF (A.ty (c - (t : ZMod n))) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  obtain ⟨E, hE_def⟩ : ∃ E : ℕ → ℤ, E = fun t : ℕ =>
      (nnNF A (A.ty (c - (t : ZMod n))) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := ⟨_, rfl⟩
  have hα₂t : ∀ t : ℕ, α₂ t = ((0 : ℕ) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) :=
    fun t => by rw [hα₂_def]
  have hα₃t : ∀ t : ℕ, α₃ t =
      (dnF (A.ty (c - (t : ZMod n))) : ℤ) - (mmF A (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hα₃_def]
  have hEt : ∀ t : ℕ, E t =
      (nnNF A (A.ty (c - (t : ZMod n))) : ℤ) - (nnDF (A.ty (c - (t : ZMod n))) : ℕ) := fun t => by rw [hE_def]
  have hF1 : F = Polynomial.aeval (γL W) (∏ i ∈ insert 0 ((A.JS c).erase 0), fac W (A.len c) i) f := by
    rw [hFdef, gsub_eq, show PPγ W (A.len c) (A.JS c) f =
      Polynomial.aeval (γL W) (PPO W (A.len c) (A.JS c)) f from rfl, ← aeval_mul_apply, xsub_ppo]
  have hF2' : F = Polynomial.aeval (γL W) (PPO W (A.len c) (A.JS c)) (W.γE W.gam f - f) := by
    rw [hFdef, gsub_eq, show PPγ W (A.len c) (A.JS c) f =
      Polynomial.aeval (γL W) (PPO W (A.len c) (A.JS c)) f from rfl, ← aeval_mul_apply, mul_comm,
      aeval_mul_apply, ← gsub_eq]
  have hF2 : F = Polynomial.aeval (γL W) (∏ i ∈ (A.JS c).erase 0, fac W (A.len c) i)
      (Polynomial.aeval (γL W) (∑ k ∈ Finset.range (PD.p ^ A.len c), (Polynomial.X : Polynomial O) ^ k)
        (W.γE W.gam f - f)) := by
    rw [hF2']; exact ppγ_eq W (A.len c) (A.JS c) _
  have hLamF : InFr W c 1 (abelian₂ W A c (A.len c)) F := by
    have h' : InId W c (A.len c) (fun s => ((0 : ℕ) : ℤ) - (A.Hs c (A.len c) s : ℕ)) F := by
      rw [hF1]
      exact Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS _ f (inId_Lam W h1)
    exact inFr_Lam W h'
  have hf2 : InId W c (A.len c) α₂ f := by
    rw [hα₂_def]
    refine inId_of_inFr W (A.len c) (fun _ => 0) (fun t => mmF A (A.ty (c - (t : ZMod n))))
      (fun _ _ => Or.inl rfl) ?_
    simp only [pow_zero, Finset.prod_const_one]
    have h2' := h2
    rw [mmDen_eq] at h2'
    exact h2'
  have hdn : downB W A c ∈ W.AΔ := by rw [downB_eq]; exact prod_ps_mem W hπ _ _
  have hnn : nnDen W A c ∈ W.AΔ := by rw [nnDen_eq]; exact prod_ps_mem W hπ _ _
  have hf3 : InId W c (A.len c) α₃ (W.γE W.gam f - f) := by
    have h3' := h3
    rw [mul_comm] at h3'
    have h3'' := inFr_num_drop W hπ h3'
    rw [downB_eq, mmDen_eq] at h3''
    rw [hα₃_def]
    exact inId_of_inFr W (A.len c) (fun t => dnF (A.ty (c - (t : ZMod n))))
      (fun t => mmF A (A.ty (c - (t : ZMod n)))) (fun t _ => dnF_eq_zero_or_mmF_eq_zero A (A.ty (c - (t : ZMod n)))) h3''
  have hg3 : InId W c (A.len c) α₃ (Polynomial.aeval (γL W)
      (∑ k ∈ Finset.range (PD.p ^ A.len c), (Polynomial.X : Polynomial O) ^ k) (W.γE W.gam f - f)) :=
    Formalism.MainNotions.UnusedSlot80.KL.inId_aeval (W := W) hS _ _ hf3
  have hH2 : ∀ t < A.len c, -(A.Hs c (A.len c) t : ℤ) ≤ α₂ t := fun t ht => by
    have := mmF_le_H A hOK hc ht; rw [hα₂t]; omega
  have hH3 : ∀ t < A.len c, -(A.Hs c (A.len c) t : ℤ) ≤ α₃ t := fun t ht => by
    have := mmF_le_H A hOK hc ht; rw [hα₃t]; omega
  have hnum3 : numI W (A.len c) α₃ = downB W A c := by
    unfold numI
    rw [downB_eq]
    exact Finset.prod_congr rfl fun t _ => by
      rw [hα₃t, (toNat_sub_of _ _ (dnF_eq_zero_or_mmF_eq_zero A (A.ty (c - (t : ZMod n))))).1]
  have hden3 : denI W (A.len c) α₃ = mmDen W A c := by
    unfold denI
    rw [mmDen_eq]
    exact Finset.prod_congr rfl fun t _ => by
      rw [hα₃t, (toNat_sub_of _ _ (dnF_eq_zero_or_mmF_eq_zero A (A.ty (c - (t : ZMod n))))).2]
  have hπ3 : InIdπ W c (A.len c) α₃ (W.γE W.gam f - f) := by
    have h3' := h3
    unfold InFr at h3'
    obtain ⟨u, hu, e⟩ := h3'
    unfold InIdπ
    refine ⟨u, hu, ?_⟩
    rw [hnum3, hden3, e]
    congr 1; ring
  have hLamM : abelian₂ W A c (A.len c) = mmDen W A c *
      ∏ s ∈ Finset.range (A.len c), ps W s ^ (A.Hs c (A.len c) s - mmF A (A.ty (c - (s : ZMod n)))) := by
    unfold abelian₂
    rw [mmDen_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [← pow_add]
    congr 1
    have := mmF_le_H A hOK hc (Finset.mem_range.1 ht)
    omega
  have hπF : InFr W c W.π₀ (abelian₂ W A c (A.len c)) F := by
    have hP := inIdπ_aeval W hR hS (PPO W (A.len c) (A.JS c)) (W.γE W.gam f - f) hπ3
    unfold InIdπ at hP
    obtain ⟨u, hu, e⟩ := hP
    rw [hnum3, hden3] at e
    unfold InFr
    refine ⟨(∏ s ∈ Finset.range (A.len c),
        ps W s ^ (A.Hs c (A.len c) s - mmF A (A.ty (c - (s : ZMod n))))) * downB W A c * u,
      mul_mem (mul_mem (prod_ps_mem W hπ _ _) hdn) hu, ?_⟩
    rw [hF2', hLamM, map_mul, mul_right_comm, e, ← map_mul]
    congr 1; ring
  have step : ∀ s < A.len c, ∀ (α : ℕ → ℤ) (g : W.EE) (T : Finset ℤ) (N : ℕ),
      InId W c (A.len c) α g → Finset.Ico (α s) (α s + N) ⊆ T → α s + N = E s →
      (∀ t < A.len c, -(A.Hs c (A.len c) t : ℤ) ≤ α t) →
      F = Polynomial.aeval (γL W) (∏ i ∈ T, fac W (A.len c) i) g →
      ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * F = f₁ + f₂ ∧
        InFr W c (ps W s ^ (E s).toNat)
          (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range (A.len c)).erase s, ps W t ^ A.Hs c (A.len c) t) f₁ ∧
        InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 f₂ := by
    intro s hs α g T N hg hT hN hH hFg
    obtain ⟨κ, hκ⟩ := raise W hKL hCA hS hg hs N T hT
    rw [hN, ← hFg] at hκ
    exact ⟨κ, _, 0, (add_zero _).symm,
      level_form W hπ (Finset.mem_range.2 hs) α (E s) (A.Hs c (A.len c))
        (fun t ht => hH t (Finset.mem_range.1 (Finset.mem_of_mem_erase ht))) hκ, inFr_zero W c _ _⟩
  have hdec : ∀ s < A.len c, ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * F = f₁ + f₂ ∧
      InFr W c (ps W s ^ (E s).toNat)
        (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range (A.len c)).erase s, ps W t ^ A.Hs c (A.len c) t) f₁ ∧
      InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 f₂ := by
    intro s hs
    cases hty : A.ty (c - (s : ZMod n)) with
    | thin =>
      refine step s hs α₂ f _ (2 * A.G₀) hf2 ?_ ?_ hH2 hF1
      · intro i hi
        rw [Finset.mem_Ico, hα₂t, hty] at hi
        simp only [mmF] at hi
        by_cases h0 : i = 0
        · rw [h0]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (Finset.mem_erase.2 ⟨h0, mem_JS_thin A hs hty (by omega) (by omega)⟩)
      · rw [hα₂t, hEt, hty]; simp only [mmF, nnNF, nnDF]; omega
    | up b =>
      refine step s hs α₃ _ _ A.S hg3 ?_ ?_ hH3 hF2
      · intro i hi
        rw [Finset.mem_Ico, hα₃t, hty] at hi
        simp only [dnF, mmF] at hi
        exact Finset.mem_erase.2 ⟨by omega, mem_JS_up A hs hty (Finset.mem_Ico.2 ⟨by omega, by omega⟩)⟩
      · rw [hα₃t, hEt, hty]; simp only [dnF, mmF, nnNF, nnDF]; omega
    | down b =>
      have hb : 1 ≤ b := by
        have h' := size_pos A hOK (c - (s : ZMod n)) (by rw [hty]; rfl)
        rw [hty] at h'
        exact h'
      refine step s hs α₃ _ _ A.S hg3 ?_ ?_ hH3 hF2
      · intro i hi
        rw [Finset.mem_Ico, hα₃t, hty] at hi
        simp only [dnF, mmF] at hi
        exact Finset.mem_erase.2 ⟨by omega, mem_JS_down A hs hty (Finset.mem_Ico.2 ⟨by omega, by omega⟩)⟩
      · rw [hα₃t, hEt, hty]; simp only [dnF, mmF, nnNF, nnDF]; omega
  have hE : ∀ s < A.len c, -(A.Hs c (A.len c) s : ℤ) ≤ E s ∧ E s ≤ A.Hs c (A.len c) s := by
    intro s hs
    have h₁ := nnDF_le_H A hOK hc hs
    have h₂ := nnNF_le_H A hOK hc hs
    rw [hEt]
    constructor <;> omega
  obtain ⟨f₁, f₂, hsum, hf₁, hf₂⟩ := hRAT hCA h5 A c (A.len c) 1 E le_rfl hE F hLamF hdec
    (fun _ => ⟨0, F, 0, by simp [lE], hπF, inFr_zero W c _ _⟩)
  have hf₁' : InFr W c (W.π₀ * nnNum W A c) (nnDen W A c) f₁ := by
    rw [pow_one] at hf₁
    refine inFr_congr W ?_ ?_ hf₁
    · rw [nnNum_eq]
      congr 1
      exact Finset.prod_congr rfl fun t _ => by
        rw [hEt, (toNat_sub_of _ _ (nnNF_eq_zero_or_nnDF_eq_zero A (A.ty (c - (t : ZMod n))))).1]
    · rw [nnDen_eq]
      exact Finset.prod_congr rfl fun t _ => by
        rw [hEt, (toNat_sub_of _ _ (nnNF_eq_zero_or_nnDF_eq_zero A (A.ty (c - (t : ZMod n))))).2]
  have hLamN : abelian₂ W A c (A.len c) = nnNum W A c *
      ∏ s ∈ Finset.range (A.len c), ps W s ^ (A.Hs c (A.len c) s - nnNF A (A.ty (c - (s : ZMod n)))) := by
    unfold abelian₂
    rw [nnNum_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [← pow_add]
    congr 1
    have := nnNF_le_H A hOK hc (Finset.mem_range.1 ht)
    omega
  have hf₂' : InFr W c (W.π₀ * nnNum W A c) (nnDen W A c) f₂ := by
    have h' := inFr_den_mul W hnn hf₂
    rw [one_mul, hLamN, ← mul_assoc] at h'
    exact inFr_num_drop W (prod_ps_mem W hπ _ _) h'
  rw [hsum]
  exact inFr_add W hf₁' hf₂'

theorem lE_add (a b : ℕ) : lE W (a + b) = lE W a * lE W b := by
  unfold lE; rw [pow_add]

theorem ppo_single_eval {e : ℕ} {k : ℤ} (hk : k ≠ 0) :
    (PPO W e {k}).eval 1 = ((((W.χΓ W.gam) ^ (k * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1) *
      (-(((PD.p ^ e : ℕ) : O))) := by
  have hks : ({k} : Finset ℤ).erase 0 = {k} := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨hk, rfl⟩
  unfold PPO
  rw [hks, Finset.prod_singleton]
  simp [Polynomial.eval_finset_sum] <;> ring

theorem part_c [IsDomain O] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hKL : KillerLevCore W)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (hS : PsStable W)
    (hπ : W.π₀ ∈ W.AΔ) (hRAT : Formalism.MainNotions.UnusedSlot80.CutU.RATCore W) (hInv : Formalism.MainNotions.UnusedSlot80.CutU.InvLevCore W)
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hvp : v (algebraMap O LL ((PD.p : ℕ) : O)) = 1)
    (A : ArcP n) (hOK : A.OK) {c : ZMod n}
    (hc : c ∈ A.cuts) {f : W.EE} (h1 : InFr W c 1 (abelian₂ W A c (A.len c)) f)
    (h2 : InFr W c 1 (mmDen W A c) f)
    (h3 : InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam f - f)) :
    ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c)
        (lE W κ * PPγ W (A.len c) (A.JS c) f -
          algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x) := by
  intro s hs b hτ
  set e := A.len c with he
  have hsm : s ∈ Finset.range e := Finset.mem_range.2 hs
  set d : ℕ → ℕ := fun t => nnDF (A.ty (c - (t : ZMod n))) with hd
  set D := ∏ t ∈ (Finset.range e).erase s, ps W t ^ d t with hD
  have hb1 : 1 ≤ b := by
    have := size_pos A hOK (c - (s : ZMod n)) (by rw [hτ]; rfl)
    rwa [hτ] at this
  have hnnDen : nnDen W A c = D := by
    rw [nnDen_eq, ← Finset.mul_prod_erase _ _ hsm, hτ]
    simp [nnDF, hD, hd]
  set f' := PPγ W e (A.JS c) f with hf'
  set g := W.γE W.gam f' - f' with hg
  have hf'D : InFr W c 1 D f' := hnnDen ▸ part_b W hKL hCA h5 hS hπ hRAT A hOK hc h1 h2
  have hgD : InFr W c (ps W s ^ (b + A.S)) D g := by
    have ha := part_a W hR hKL hCA h5 hS hπ hRAT A hOK hc h1 h2 h3
    rw [hnnDen, nnNum_eq, ← Finset.mul_prod_erase _ _ hsm, hτ] at ha
    refine inFr_num_drop W (x := W.π₀ * ∏ t ∈ (Finset.range e).erase s,
      ps W t ^ nnNF A (A.ty (c - (t : ZMod n)))) (Subalgebra.mul_mem _ hπ (prod_ps_mem' W hπ _ _)) ?_
    refine inFr_congr W ?_ rfl ha
    simp only [nnNF]; ring

  obtain ⟨κ0, x0, h0⟩ := hInv hCA h5 c s ((Finset.range e).erase s) d (Finset.notMem_erase s _) f' hf'D
    ⟨0, by rw [show lE W 0 = 1 by simp [lE], one_mul]; exact (pow_one (ps W s)) ▸
      inFr_pow_mono W (by omega) hπ hgD⟩
  set h := lE W κ0 * f' - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x0 with hh
  have hγh : W.γE W.gam h - h = lE W κ0 * g := by
    rw [hh, map_sub, map_mul, γE_lE, γE_const, hg]; ring

  have key : ∀ k, 1 ≤ k → k ≤ b + A.S → ∃ m, InFr W c (ps W s ^ k) D (lE W m * h) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base => intro _; exact ⟨0, by rw [show lE W 0 = 1 by simp [lE], one_mul, pow_one]; exact h0⟩
    | succ k hk ih =>
      intro hkb
      obtain ⟨m, hm⟩ := ih (by omega)
      set y := lE W m * h with hy
      have hyI : InId W c e (αk e s d k) y := (inId_αk_iff W hsm d k y).2 hm
      have hwin : Finset.Ico (αk e s d k s) (αk e s d k s + ((1 : ℕ) : ℤ)) ⊆ {(k : ℤ)} := by
        intro i hi
        simp only [αk, ↓reduceIte, Finset.mem_Ico] at hi
        simp only [Finset.mem_singleton]; push_cast at hi; omega
      obtain ⟨κ1, hκ1⟩ := raise W hKL hCA hS hyI hs 1 _ hwin
      rw [Finset.prod_singleton, show αk e s d k s + ((1 : ℕ) : ℤ) = (k : ℤ) + 1 by simp [αk],
        update_αk] at hκ1
      have hf1 := (inId_αk_iff W hsm d (k + 1) _).1 hκ1

      set Sp : Polynomial O := ∑ j ∈ Finset.range (PD.p ^ e), (Polynomial.X : Polynomial O) ^ j with hSp
      have hγy : W.γE W.gam y - y = lE W m * (lE W κ0 * g) := by
        rw [hy, map_mul, γE_lE, ← hγh]; ring
      have hγyI : InId W c e (αk e s d (k + 1)) (W.γE W.gam y - y) := by
        refine (inId_αk_iff W hsm d (k + 1) _).2 ?_
        rw [hγy]
        exact inFr_lE W (inFr_lE W (inFr_pow_mono W (by omega) hπ hgD) κ0) m
      have hN : Polynomial.aeval (γL W) (Polynomial.X ^ (PD.p ^ e) - 1 : Polynomial O) y =
          Polynomial.aeval (γL W) Sp (W.γE W.gam y - y) := by
        rw [gsub_eq, ← aeval_mul_apply, hSp, mul_comm, mul_geom_sum]
      have hf2 := (inId_αk_iff W hsm d (k + 1) _).1 (inId_lE W (hN ▸ inId_aeval W hS Sp _ hγyI) κ1)

      have hdiff : lE W κ1 * Polynomial.aeval (γL W) (Polynomial.X ^ (PD.p ^ e) - 1 : Polynomial O) y -
          lE W κ1 * Polynomial.aeval (γL W) (fac W e k) y =
          (((((W.χΓ W.gam) ^ ((k : ℤ) * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1) • (lE W κ1 * y)) := by
        rw [← mul_sub, ← LinearMap.sub_apply, ← map_sub]
        rw [show (Polynomial.X ^ (PD.p ^ e) - 1 : Polynomial O) - fac W e k =
          Polynomial.C ((((W.χΓ W.gam) ^ ((k : ℤ) * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1) by
            simp only [fac, map_sub, map_one]; ring]
        rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
          mul_smul_comm]
      have hz := inFr_sub W hf2 hf1
      rw [hdiff] at hz

      have hv := ((hKL hCA e {(k : ℤ)}).1)
      have hk0 : (k : ℤ) ≠ 0 := by omega
      rw [ppo_single_eval W hk0] at hv
      obtain ⟨o, ho⟩ := div_of_val hinj hO2 hvp _ _ hv
      set M := e + ∑ i ∈ ({(k : ℤ)} : Finset ℤ).erase 0, (e + 1 + padicValInt PD.p i) with hM
      have hw : lE W M * (lE W κ1 * y) = o • ((-(((PD.p ^ e : ℕ) : O))) •
          ((((((W.χΓ W.gam) ^ ((k : ℤ) * (PD.p : ℤ) ^ e) : Oˣ) : O) - 1)) • (lE W κ1 * y))) := by
        rw [lE_eq_alg W M, ← Algebra.smul_def, ho, smul_smul, smul_smul]
        congr 1; ring
      refine ⟨M + (κ1 + m), ?_⟩
      rw [show lE W (M + (κ1 + m)) * h = lE W M * (lE W κ1 * y) by
        rw [hy, show M + (κ1 + m) = (M + κ1) + m by ring, lE_add W (M + κ1) m, lE_add W M κ1]; ring, hw]
      exact inFr_smul W (inFr_smul W hz _) _
  obtain ⟨m, hm⟩ := key (b + A.S) (by omega) le_rfl
  refine ⟨m + κ0, ((PD.p : ℕ) : O) ^ m * x0, ?_⟩
  rw [hnnDen]
  convert hm using 1
  simp only [hh, lE_eq_alg, map_mul, map_pow, pow_add]
  ring

theorem killWinFromCut [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hvp : v (algebraMap O LL ((PD.p : ℕ) : O)) = 1) : Formalism.MainNotions.UnusedSlot80.CutU.KillWinFromCut W := by
  intro hR hKL hS hπ hRAT hInv hCA h5 A hOK c hc f h1 h2 h3
  exact ⟨part_a W hR hKL hCA h5 hS hπ hRAT A hOK hc h1 h2 h3,
    part_b W hKL hCA h5 hS hπ hRAT A hOK hc h1 h2,
    part_c W hR hKL hCA h5 hS hπ hRAT hInv hinj hO2 hvp A hOK hc h1 h2 h3⟩

end Main

end Formalism.MainNotions.UnusedSlot80.KWP
