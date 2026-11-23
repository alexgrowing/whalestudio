import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions

def RKShare (ρ : ℝ) (D : D7) (u : D.what₂.Word) : Prop :=
  0 < rkC (D.mem u).C (D.mem u).A (D.mem u).P ∧ ρ * (dU D u : ℝ) ≤ (rkC (D.mem u).C (D.mem u).A (D.mem u).P : ℝ)

def TIn (D : D7) (u : D.what₂.Word) (r s : ℝ) : Prop :=
  Real.log (D.mem u).A.Xu - r ≤ Real.log ((D.mem u).A.T : ℝ) ∧ Real.log ((D.mem u).A.T : ℝ) ≤ s

def TInAt (D : D7) (u : D.what₂.Word) (D' : D7) (u' : D'.what₂.Word) (r s : ℝ) : Prop :=
  Real.log (D.mem u).A.Xu - r ≤ Real.log ((D'.mem u').A.T : ℝ) ∧ Real.log ((D'.mem u').A.T : ℝ) ≤ s

def SameTops (D D' : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (τ' : D'.what₂.Tau) (t : D.host.TT) (t' : D'.host.TT) (h : 0 < D.R.k) (h' : 0 < D'.R.k),
    (D.eTau τ : D.R.GG) = D.R.tau1 t → (D'.eTau τ' : D'.R.GG) = D'.R.tau1 t' →
    (t : D.R.A).val = (t' : D'.R.A).val →
      (D.hc τ).u ⟨0, h⟩ = (D'.hc τ').u ⟨0, h'⟩ ∧
        (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D'.hc τ').u ⟨D'.R.k - 1, by omega⟩

structure SameHost (D D' : D7) : Prop where

  R_eq : D.R = D'.R

  TT_eq : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val
  realisedChain_torus_eq : D.host.T2 = D'.host.T2
  q_eq : D.host.q = D'.host.q
  d_eq : D.host.d = D'.host.d
  g_eq : D.host.g = D'.host.g
  pde_eq : D.host.pde = D'.host.pde
  pde'_eq : D.host.pde' = D'.host.pde'

  QS_eq : D.host.QS = D'.host.QS

  art_eq : ∀ (p : ℕ) (h : Nat.Coprime p D.host.condN) (h' : Nat.Coprime p D'.host.condN),
    (D.host.art (ZMod.unitOfCoprime p h)).1 = (D'.host.art (ZMod.unitOfCoprime p h')).1 ∧
      (D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p h)).2).val = (D'.R.iotaInv (D'.host.art (ZMod.unitOfCoprime p h')).2).val

theorem SameHost.condN_eq {D D' : D7} (h : SameHost D D') : D.host.condN = D'.host.condN := by
  show D.host.QS * D.host.q * D.host.d = D'.host.QS * D'.host.q * D'.host.d
  rw [h.QS_eq, h.q_eq, h.d_eq]

theorem SameHost.refl (D : D7) : SameHost D D := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem SameHost.symm {D D' : D7} (h : SameHost D D') : SameHost D' D :=
  ⟨h.1.symm, h.2.symm, h.3.symm, h.4.symm, h.5.symm, h.6.symm, h.7.symm, h.8.symm, h.9.symm,
    fun p k k' => ⟨(h.art_eq p k' k).1.symm, (h.art_eq p k' k).2.symm⟩⟩

theorem SameHost.trans {D D' D'' : D7} (h : SameHost D D') (h' : SameHost D' D'') : SameHost D D'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2, h.3.trans h'.3, h.4.trans h'.4, h.5.trans h'.5, h.6.trans h'.6, h.7.trans h'.7, h.8.trans h'.8,
    h.9.trans h'.9, fun p k k'' =>
      have k' : Nat.Coprime p D'.host.condN := h.condN_eq ▸ k
      ⟨(h.art_eq p k k').1.trans (h'.art_eq p k' k'').1, (h.art_eq p k k').2.trans (h'.art_eq p k' k'').2⟩⟩

theorem SameHost.exists_top {D D' : D7} (h : SameHost D D') (t : D.host.TT) :
    ∃ t' : D'.host.TT, (t : D.R.A).val = (t' : D'.R.A).val := by
  have hm : (t : D.R.A).val ∈ D'.host.TT.image Formalism.HC.Frame.A.val := h.TT_eq ▸ Finset.mem_image_of_mem _ t.2
  obtain ⟨s, hs, e⟩ := Finset.mem_image.1 hm
  exact ⟨⟨s, hs⟩, e.symm⟩

theorem SameTops.refl (D : D7) : SameTops D D := by
  intro τ τ' t t' h h' e e' ht
  have h1 : t = t' := Subtype.ext (Formalism.HC.Frame.A.val_injective _ ht)
  subst h1
  have h2 : τ = τ' := D.eTau.injective (Subtype.ext (e.trans e'.symm))
  subst h2
  exact ⟨rfl, rfl⟩

structure SameWord (D : D7) (u : D.what₂.Word) (D' : D7) (u' : D'.what₂.Word) : Prop where
  host : SameHost D D'
  unitVector_val_eq : D.host.u0.val = D'.host.u0.val
  hc_eq : ∀ (τ : D.what₂.Tau) (τ' : D'.what₂.Tau), HEq (D.eTau τ) (D'.eTau τ') → HEq (D.hcW u τ) (D'.hcW u' τ')

theorem SameWord.refl (D : D7) (u : D.what₂.Word) : SameWord D u D u :=
  ⟨SameHost.refl D, rfl, fun τ τ' h => by rw [D.eTau.injective (eq_of_heq h)]⟩

theorem SameWord.exists_place {D D' : D7} {u : D.what₂.Word} {u' : D'.what₂.Word} (h : SameWord D u D' u') (τ : D.what₂.Tau) :
    ∃ τ' : D'.what₂.Tau, HEq (D.eTau τ) (D'.eTau τ') ∧ HEq (D.hcW u τ) (D'.hcW u' τ') := by
  have key : ∀ (R R' : Ranks), R = R' → ∀ g : R.Psi, ∃ g' : R'.Psi, HEq g g' := by
    rintro R _ rfl g
    exact ⟨g, HEq.rfl⟩
  obtain ⟨g', hg⟩ := key _ _ h.host.R_eq (D.eTau τ)
  have e : HEq (D.eTau τ) (D'.eTau (D'.eTau.symm g')) := by rw [Equiv.apply_symm_apply]; exact hg
  exact ⟨_, e, h.hc_eq _ _ e⟩

theorem SameWord.sameTops {D D' : D7} {u : D.what₂.Word} {u' : D'.what₂.Word} (h : SameWord D u D' u') : SameTops D D' := by
  have key : ∀ (R R' : Ranks), R = R' → ∀ (g : R.Psi) (g' : R'.Psi) (t : R.A) (t' : R'.A),
      (g : R.GG) = R.tau1 t → (g' : R'.GG) = R'.tau1 t' → t.val = t'.val → HEq g g' := by
    rintro R _ rfl g g' t t' e e' ht
    obtain rfl : t = t' := Formalism.HC.Frame.A.val_injective _ ht
    exact heq_of_eq (Subtype.ext (e.trans e'.symm))
  have key2 : ∀ (R R' : Ranks), R = R' → ∀ (p : HCParam R) (p' : HCParam R'), HEq p p' → ∀ (k : 0 < R.k) (k' : 0 < R'.k),
      p.u ⟨0, k⟩ = p'.u ⟨0, k'⟩ ∧ p.u ⟨R.k - 1, by omega⟩ = p'.u ⟨R'.k - 1, by omega⟩ := by
    rintro R _ rfl p p' e k k'
    obtain rfl := eq_of_heq e
    exact ⟨rfl, rfl⟩
  intro τ τ' t t' k k' e e' ht
  have := key2 _ _ h.host.R_eq _ _ (h.hc_eq τ τ' (key _ _ h.host.R_eq _ _ _ _ e e' ht)) k k'
  rw [D.hcW_first u τ k, D'.hcW_first u' τ' k', D.hcW_last u τ k, D'.hcW_last u' τ' k'] at this
  exact this

structure Pts where

  Ix : ℝ → Type

  D : ∀ x, Ix x → D7

  Ix_ne : ∀ y, ∃ x, y ≤ x ∧ Nonempty (Ix x)

  same : ∀ x (i i' : Ix x), SameHost (D x i) (D x i')

namespace Pts

theorem ne_of_forall {Ix : ℝ → Type} (h : ∀ x, Nonempty (Ix x)) : ∀ y, ∃ x, y ≤ x ∧ Nonempty (Ix x) :=
  fun y => ⟨y, le_rfl, h y⟩

def single (D : ℝ → D7) : Pts :=
  ⟨fun _ => Unit, fun x _ => D x, ne_of_forall fun _ => ⟨()⟩, fun _ _ _ => SameHost.refl _⟩

variable (F : Pts)

def SomeAt (Q : ℝ → ∀ D : D7, D.what₂.Word → Prop) : Prop :=
  ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ (i₀ : F.Ix x) (u₀ : ℕ), u₀ < (F.D x i₀).R.n →
    ∃ i : F.Ix x, (F.D x i).host.u0.val = u₀ ∧ SameTops (F.D x i) (F.D x i₀) ∧ ∃ u, Q x (F.D x i) u

def RKAll : Prop := ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ i : F.Ix x, ∃ u, RK (F.D x i) u

def RKWin : Prop := F.SomeAt fun _ D u => RK D u

def RKRoom (ε : ℝ) : Prop :=
  ∃ CR CT : ℝ, F.SomeAt fun x D u => TIn D u (CR * x ^ ε) (CT * D.R.m * x ^ ε) ∧ RK D u

def RKWeak (ε : ℝ) : Prop :=
  ∃ CT : ℝ, F.SomeAt fun x D u => TIn D u (x ^ (13 * ε)) (CT * D.R.m * x ^ ε) ∧ RKShare (x ^ (-(12 * ε))) D u

def RKRoomOver (Tr : ℝ → D7 → Prop) (ε : ℝ) : Prop :=
  ∃ CR CT : ℝ, F.SomeAt fun x D u => ∃ (D' : D7) (u' : D'.what₂.Word), Tr x D' ∧ SameWord D u D' u' ∧
    TInAt D u D' u' (CR * x ^ ε) (CT * D.R.m * x ^ ε) ∧ RK D' u'

def RKWeakOver (Tr : ℝ → D7 → Prop) (ε : ℝ) : Prop :=
  ∃ CT : ℝ, F.SomeAt fun x D u => ∃ (D' : D7) (u' : D'.what₂.Word), Tr x D' ∧ SameWord D u D' u' ∧
    TInAt D u D' u' (x ^ (13 * ε)) (CT * D.R.m * x ^ ε) ∧ RKShare (x ^ (-(12 * ε))) D' u'

def Within (Tr : ℝ → D7 → Prop) : Prop := ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ i : F.Ix x, Tr x (F.D x i)

def Covered : Prop :=
  ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ (i₀ : F.Ix x) (u₀ : ℕ), u₀ < (F.D x i₀).R.n →
    ∃ i : F.Ix x, (F.D x i).host.u0.val = u₀ ∧ SameTops (F.D x i) (F.D x i₀)

variable {F}

theorem SomeAt.mono {Q Q' : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) (x₁ : ℝ)
    (hq : ∀ x, x₁ ≤ x → ∀ i u, Q x (F.D x i) u → Q' x (F.D x i) u) : F.SomeAt Q' := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨max x₀ x₁, fun x hx i₀ u₀ hu => ?_⟩
  obtain ⟨i, h1, h2, u, h3⟩ := h x (le_of_max_le_left hx) i₀ u₀ hu
  exact ⟨i, h1, h2, u, hq x (le_of_max_le_right hx) i u h3⟩

theorem SomeAt.exists {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → Nonempty (F.Ix x) → ∃ (i : F.Ix x) (u : (F.D x i).what₂.Word), Q x (F.D x i) u := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨x₀, fun x hx ⟨i₀⟩ => ?_⟩
  obtain ⟨i, -, -, u, hu⟩ := h x hx i₀ 0 (F.D x i₀).R.ord_pos
  exact ⟨i, u, hu⟩

theorem SomeAt.exists_ge {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) (y : ℝ) :
    ∃ x, y ≤ x ∧ ∃ (i : F.Ix x) (u : (F.D x i).what₂.Word), Q x (F.D x i) u := by
  obtain ⟨x₀, h⟩ := h.exists
  obtain ⟨x, hx, hne⟩ := F.Ix_ne (max x₀ y)
  exact ⟨x, le_of_max_le_right hx, h x (le_of_max_le_left hx) hne⟩

theorem SomeAt.covered {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) : F.Covered := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨x₀, fun x hx i₀ u₀ hu => ?_⟩
  obtain ⟨i, h1, h2, -⟩ := h x hx i₀ u₀ hu
  exact ⟨i, h1, h2⟩

theorem RKAll.rkWin (h : F.RKAll) (hc : F.Covered) : F.RKWin := by
  obtain ⟨x₀, h⟩ := h
  obtain ⟨x₁, hc⟩ := hc
  refine ⟨max x₀ x₁, fun x hx i₀ u₀ hu => ?_⟩
  obtain ⟨i, h1, h2⟩ := hc x (le_of_max_le_right hx) i₀ u₀ hu
  exact ⟨i, h1, h2, h x (le_of_max_le_left hx) i⟩

theorem RKRoom.rkWin {ε : ℝ} (h : F.RKRoom ε) : F.RKWin := by
  obtain ⟨CR, CT, h⟩ := h
  exact h.mono 0 fun _ _ _ _ h => h.2

theorem RKRoom.over {ε : ℝ} {Tr : ℝ → D7 → Prop} (h : F.RKRoom ε) (hT : F.Within Tr) : F.RKRoomOver Tr ε := by
  obtain ⟨CR, CT, h⟩ := h
  obtain ⟨x₁, hT⟩ := hT
  exact ⟨CR, CT, h.mono x₁ fun x hx i u h => ⟨_, u, hT x hx i, SameWord.refl _ u, h.1, h.2⟩⟩

theorem RKWeak.over {ε : ℝ} {Tr : ℝ → D7 → Prop} (h : F.RKWeak ε) (hT : F.Within Tr) : F.RKWeakOver Tr ε := by
  obtain ⟨CT, h⟩ := h
  obtain ⟨x₁, hT⟩ := hT
  exact ⟨CT, h.mono x₁ fun x hx i u h => ⟨_, u, hT x hx i, SameWord.refl _ u, h.1, h.2⟩⟩

theorem RKRoomOver.mono {ε : ℝ} {Tr Tr' : ℝ → D7 → Prop} (h : F.RKRoomOver Tr ε) (hT : ∀ x D, Tr x D → Tr' x D) :
    F.RKRoomOver Tr' ε := by
  obtain ⟨CR, CT, h⟩ := h
  exact ⟨CR, CT, h.mono 0 fun x _ _ _ ⟨D', u', h1, h2⟩ => ⟨D', u', hT x D' h1, h2⟩⟩

theorem RKWeakOver.mono {ε : ℝ} {Tr Tr' : ℝ → D7 → Prop} (h : F.RKWeakOver Tr ε) (hT : ∀ x D, Tr x D → Tr' x D) :
    F.RKWeakOver Tr' ε := by
  obtain ⟨CT, h⟩ := h
  exact ⟨CT, h.mono 0 fun x _ _ _ ⟨D', u', h1, h2⟩ => ⟨D', u', hT x D' h1, h2⟩⟩

theorem not_rkRoomOver {ε : ℝ} {Tr : ℝ → D7 → Prop} (hT : ∀ x D u, Tr x D → ¬ RK D u) : ¬ F.RKRoomOver Tr ε := by
  rintro ⟨CR, CT, h⟩
  obtain ⟨x, -, i, u, D', u', h1, -, -, h2⟩ := h.exists_ge 0
  exact hT _ _ _ h1 h2

end Pts

theorem RK.share {D : D7} {u : D.what₂.Word} (h : RK D u) {ρ : ℝ} (hρ : ρ ≤ 1 / 2) : RKShare ρ D u := by
  have h1 : dU D u < 2 * rkC (D.mem u).C (D.mem u).A (D.mem u).P := h
  refine ⟨by omega, ?_⟩
  have h2 : (dU D u : ℝ) < 2 * (rkC (D.mem u).C (D.mem u).A (D.mem u).P : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ (dU D u : ℝ) := by positivity
  nlinarith

theorem room_le_and_share_le {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ x₁ : ℝ, ∀ x, x₁ ≤ x → C * x ^ ε ≤ x ^ (13 * ε) ∧ x ^ (-(12 * ε)) ≤ 1 / 2 := by
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop (by linarith : 0 < 12 * ε)).eventually_ge_atTop (max C 2)).and (Filter.eventually_gt_atTop (0 : ℝ)))
  refine ⟨x₁, fun x hx => ?_⟩
  obtain ⟨h1, h0⟩ := hx₁ x hx
  have e : x ^ (13 * ε) = x ^ (12 * ε) * x ^ ε := by rw [← Real.rpow_add h0]; ring_nf
  refine ⟨?_, ?_⟩
  · rw [e]
    exact mul_le_mul_of_nonneg_right (le_of_max_le_left h1) (Real.rpow_pos_of_pos h0 _).le
  · rw [Real.rpow_neg h0.le, one_div]
    exact inv_anti₀ (by norm_num) (le_of_max_le_right h1)

theorem Xu_pos (D : D7) (u : D.what₂.Word) : 0 < (D.mem u).A.Xu := by
  have h1 := (D.mem u).A.Dstar_pos
  have h2 : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  unfold ColumnsAtT.Xu
  positivity

theorem f_mul_k_pos (R : Ranks) : (0 : ℝ) < (R.f : ℝ) * R.k := by
  have := R.m_add_three_le_k
  have h1 : 0 < R.k := by omega
  have h2 : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
  positivity

theorem T_lt_cap (D : D7) (u : D.what₂.Word) :
    ((D.mem u).A.T : ℝ) < (1 + 1 / ((D.R.f : ℝ) * D.R.k)) * (D.mem u).A.Xu := by
  have hf := f_mul_k_pos D.R
  refine (D.T_win u).2.trans_lt (mul_lt_mul_of_pos_left ?_ (by positivity))
  unfold ColumnsAtT.Tstar
  exact mul_lt_of_lt_one_right (Xu_pos D u)
    (Real.rpow_lt_one_of_one_lt_of_neg (D.mem u).A.one_lt_gammaP (div_neg_of_neg_of_pos (by norm_num) hf))

theorem le_log_alt (D : D7) (u : D.what₂.Word) :
    Real.log (D.mem u).A.Xu - 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ) := by
  have hG : 0 < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hs : 0 < (D.mem u).A.Tstar := mul_pos (Xu_pos D u) (Real.rpow_pos_of_pos hG _)
  refine le_trans (le_of_eq ?_) (Real.log_le_log hs (D.T_win u).1)
  unfold ColumnsAtT.Tstar
  rw [Real.log_mul (Xu_pos D u).ne' (Real.rpow_pos_of_pos hG _).ne', Real.log_rpow hG]
  ring

namespace Pts

variable {F : Pts}

theorem RKWin.rkRoom {ε : ℝ} (h : F.RKWin) (CR CT x₁ : ℝ) (hb : ∀ x, x₁ ≤ x → ∀ (i : F.Ix x) u,
    2 * Real.log ((F.D x i).mem u).A.GamP ≤ CR * x ^ ε * (((F.D x i).R.f : ℝ) * (F.D x i).R.k) ∧
      Real.log (((F.D x i).mem u).A.T : ℝ) ≤ CT * (F.D x i).R.m * x ^ ε) : F.RKRoom ε := by
  refine ⟨CR, CT, SomeAt.mono h x₁ fun x hx i u h => ⟨⟨le_trans ?_ (le_log_alt _ u), (hb x hx i u).2⟩, h⟩⟩
  have := (div_le_iff₀ (f_mul_k_pos (F.D x i).R)).2 (hb x hx i u).1
  linarith

theorem RKRoom.rkWeak {ε : ℝ} (h : F.RKRoom ε) (hε : 0 < ε) : F.RKWeak ε := by
  obtain ⟨CR, CT, h⟩ := h
  obtain ⟨x₁, hx₁⟩ := room_le_and_share_le hε CR
  exact ⟨CT, h.mono x₁ fun x hx i u h =>
    ⟨⟨le_trans (sub_le_sub_left (hx₁ x hx).1 _) h.1.1, h.1.2⟩, h.2.share (hx₁ x hx).2⟩⟩

theorem RKRoomOver.rkWeakOver {ε : ℝ} {Tr : ℝ → D7 → Prop} (h : F.RKRoomOver Tr ε) (hε : 0 < ε) : F.RKWeakOver Tr ε := by
  obtain ⟨CR, CT, h⟩ := h
  obtain ⟨x₁, hx₁⟩ := room_le_and_share_le hε CR
  exact ⟨CT, h.mono x₁ fun x hx i u ⟨D', u', h1, h2, h3, h4⟩ =>
    ⟨D', u', h1, h2, ⟨le_trans (sub_le_sub_left (hx₁ x hx).1 _) h3.1, h3.2⟩, h4.share (hx₁ x hx).2⟩⟩

example (D : D7) : ¬ (single fun _ => D).Covered := by
  rintro ⟨x₀, h⟩
  have hn : 1 < D.R.n := by
    have h1 := (Nat.le_of_dvd D.host.QS_pos D.host.tower_dvd).trans D.host.QS_le
    have h2 : 1 < 2 ^ (D.R.e + 2) := Nat.one_lt_two_pow (by omega)
    by_contra hc
    have h3 : D.R.n ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨_, h0, -⟩ := h x₀ le_rfl () 0 (lt_trans one_pos hn)
  obtain ⟨_, h1, -⟩ := h x₀ le_rfl () 1 hn
  exact zero_ne_one (h0.symm.trans h1)

example (D : D7) : (single fun _ => D).RKAll ↔ ∃ u, RK D u :=
  ⟨fun ⟨x₀, h⟩ => h x₀ le_rfl (), fun h => ⟨0, fun _ _ _ => h⟩⟩

example (ε : ℝ) : ¬ F.RKRoomOver (fun _ _ => False) ε := not_rkRoomOver fun _ _ _ h => h.elim

end Pts

section Hyp

variable (Fam : ℝ → Type 1) (Cl : ∀ ε, Fam ε → Prop) (pts : ∀ ε, Fam ε → Pts) (Form : ℝ → Pts → Prop)

def HypAll : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∀ F : Fam ε, Cl ε F → Form ε (pts ε F)

def HypEx : Prop := ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε < 1 / 52 ∧ ∃ F : Fam ε, Cl ε F ∧ Form ε (pts ε F)

def ClsInhabited : Prop := ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε < 1 / 52 ∧ ∃ F : Fam ε, Cl ε F

theorem hypEx_of_hypAll (h : HypAll Fam Cl pts Form) (hi : ClsInhabited Fam Cl) : HypEx Fam Cl pts Form := by
  intro δ hδ
  obtain ⟨ε, h0, h1, h2, F, hF⟩ := hi δ hδ
  exact ⟨ε, h0, h1, h2, F, hF, h ε h0 h2 F hF⟩

end Hyp

end GlobalTheory.Core.Rk

end
