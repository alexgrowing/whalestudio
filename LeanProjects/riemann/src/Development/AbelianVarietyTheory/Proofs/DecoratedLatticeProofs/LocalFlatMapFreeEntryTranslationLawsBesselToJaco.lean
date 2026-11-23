import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatTransLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_ι (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

theorem ι_mul (p : Place D k) (x : k) (z : AE D) : p.ι x * z = p.ι (x * p.π z) := by
  have h := p.ι_π (p.ι x * z)
  rw [map_mul, p.π_ι, ← mul_assoc, e_mul_ι] at h
  exact h.symm

theorem infPart_e (p : Place D k) : infPart D p.e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := p.split
  have h5 : infPart D (p.e + cA D p.e) = 0 := by
    rw [h4]
    exact TensorProduct.zero_tmul _ _
  have h6 : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, h5, mul_zero]

theorem ι_mem (p : Place D k) (x : k) : p.ι x ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => absurd trivial w.2⟩
  rw [RingHom.mem_ker, ← e_mul_ι, map_mul, infPart_e, zero_mul]

section Frames
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem sand (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (r : Y) (q : Y') (a : k)
    {m m' : ℕ} (N : Mx D m T.rank) (N' : Mx D S.rank m') (i : Fin m) (j : Fin m') :
    (N ⬝ p.up FS FT (Matrix.single r q a) ⬝ N') i j =
      p.ι ((N.map p.π * FT.β) i r * a * (FS.γ * N'.map p.π) q j) := by
  have hU : ∀ t u, p.up FS FT (Matrix.single r q a) t u = p.ι (FT.β t r * a * FS.γ q u) := by
    intro t u
    show p.ι ((FT.β * Matrix.single r q a * FS.γ) t u) = _
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single q]
    · rw [Matrix.mul_single_apply_same]
    · intro b _ hb
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
    · simp
  simp only [Matrix.mul_apply, hU, Finset.sum_mul, Finset.mul_sum, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm (N i t), ι_mul, ι_mul]
  congr 1
  ring

theorem col_coord {N : ℕ} (F : Frame k N Y) (j : Y) (c : k) (v : Fin N → k) (h : ∀ r, F.β r j = c * v r) (q : Y) :
    c * ∑ t, F.γ q t * v t = if q = j then 1 else 0 := by
  have h1 := congrFun (congrFun F.γβ q) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [← h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [h]; ring

theorem col_coord_ne {N : ℕ} (F : Frame k N Y) (j : Y) (c : k) (v : Fin N → k) (h : ∀ r, F.β r j = c * v r) (q : Y)
    (hq : q ≠ j) : ∑ t, F.γ q t * v t = 0 := by
  have h1 := col_coord F j c v h j
  have h2 := col_coord F j c v h q
  rw [if_pos rfl] at h1
  rw [if_neg hq] at h2
  exact (mul_eq_zero.1 h2).resolve_left (left_ne_zero_of_mul_eq_one h1)

theorem row_coord (p : Place D k) {N m m' : ℕ} (F : Frame k N Y) (j : Y) (c : k) (M : Mx D m N) (M' : Mx D N m')
    (i : Fin m') (h : ∀ r, F.β r j = c * p.π (M' r i)) (l : Fin m) :
    (M.map p.π * F.β) l j = c * p.π ((M ⬝ M') l i) := by
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply]
  exact Finset.sum_congr rfl fun t _ => by rw [h]; ring

end Frames

theorem symplO_skew (S T : HSp D) (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  have h2 : ∀ x y : WO S T, symplO S T x y = 2 * symplOH S T x y := fun x y => by
    rw [symplOH, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [h2, h2, symplOH_skew, mul_neg]

section Ch
variable {n n' : Type} [DecidableEq n] [DecidableEq n'] {c : ℕ}

theorem ch_single_succ (l : Fin c) (a : k) :
    ch (Matrix.single (Sum.inr l : n ⊕ Fin c) (Sum.inr l.succ : n' ⊕ Fin (c + 1)) a) = a := by
  rw [ch, Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    exact Matrix.single_apply_of_row_ne (fun h => hb (Sum.inr.inj h).symm) _ _ _
  · simp

theorem ch_single_ne (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) (a : k) (h : ∀ l, r = Sum.inr l → q ≠ Sum.inr l.succ) :
    ch (Matrix.single r q a) = 0 := by
  refine Finset.sum_eq_zero fun l _ => Matrix.single_apply_of_ne _ _ _ _ _ fun h' => h l h'.1 h'.2

end Ch

section Levels
variable (p : Place D k) {ρ : ℕ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

section Bes
variable {B : BesLev D ρ} {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)}
  {FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))}

theorem bes_X (hB : p.IsBesFrame B s FA FV) (q : n' ⊕ Fin (c + 1)) (hq : ∀ j, q = Sum.inr j → ρ ≤ j.val) (i : Fin ρ) :
    (FV.γ * B.d.jX.map p.π) q i = 0 := by
  have hc := hB.1
  have hi := i.2
  refine col_coord_ne FV (Sum.inr ⟨i.val, by omega⟩) _ _ (hB.2.2.1 i ⟨i.val, by omega⟩ rfl) q fun h => ?_
  have := hq _ h
  simp only at this
  omega

theorem bes_Y_ne (hB : p.IsBesFrame B s FA FV) (q : n' ⊕ Fin (c + 1)) (i : Fin ρ)
    (hq : ∀ j, q = Sum.inr j → j.val + i.val ≠ 2 * ρ) : (FV.γ * B.d.jY.map p.π) q i = 0 := by
  have hc := hB.1
  have hi := i.2
  refine col_coord_ne FV (Sum.inr ⟨2 * ρ - i.val, by omega⟩) _ _
    (hB.2.2.2.2 i ⟨2 * ρ - i.val, by omega⟩ (by simp only; omega)) q fun h => ?_
  have := hq _ h
  simp only at this
  omega

theorem bes_Y (hB : p.IsBesFrame B s FA FV) (j : Fin (c + 1)) (i : Fin ρ) (h : j.val + i.val = 2 * ρ) :
    s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * (FV.γ * B.d.jY.map p.π) (Sum.inr j) i = 1 :=
  (col_coord FV (Sum.inr j) _ _ (hB.2.2.2.2 i j h) (Sum.inr j)).trans (if_pos rfl)

theorem besselNormalFrame_lineVectorColumn (hB : p.IsBesFrame B s FA FV) (j : Fin (c + 1)) (h : j.val = ρ) (q : n' ⊕ Fin (c + 1)) :
    s * ∑ t, FV.γ q t * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) t) = if q = Sum.inr j then 1 else 0 :=
  col_coord FV (Sum.inr j) _ _ (hB.2.2.2.1 j h) q

theorem bes_zero (hC : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV) (j : Fin (c + 1)) (hj : ρ < j.val)
    (t : Fin B.V₀.rank) : (FV.γ * B.d.j0.map p.π) (Sum.inr j) t = 0 := by
  have hc := hB.1
  have key : ∀ y, (FV.γ * (B.d.j0.map p.π * F₀.β)) (Sum.inr j) y = 0 := by
    rintro (a | ⟨⟨⟩⟩)
    · refine col_coord_ne FV (Sum.inl a) 1 _ (fun r => ?_) _ (by simp)
      rw [hB.2.1, one_mul]
      have : (B.d.i₀ * B.o.iA).map p.pr = B.d.j0.map p.π * B.o.iA.map p.pr :=
        Matrix.map_mul (f := p.π.comp (incA D))
      rw [this, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hC.1]
    · refine col_coord_ne FV (Sum.inr ⟨ρ, by omega⟩) 1 _ (fun r => ?_) _ (fun h => ?_)
      · rw [hB.2.2.2.1 _ rfl, one_mul, Matrix.mul_apply]
        simp only [hC.2, Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [show B.d.j0 r u = incA D (B.d.i₀ r u) from rfl]
        ring
      · have := congrArg Fin.val (Sum.inr.inj h)
        simp only at this
        omega
  rw [← Matrix.mul_one (FV.γ * B.d.j0.map p.π), ← F₀.βγ, ← Matrix.mul_assoc, Matrix.mul_assoc FV.γ, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun y _ => by rw [key, zero_mul]

end Bes

section Jac
variable {J : JacLev D ρ} {hh : k} {G₀ : Frame k J.W₀.rank n} {FW : Frame k J.W.rank (n ⊕ Fin c)}

theorem jac_low (hJ : p.IsJacFrame J s hh G₀ FW) (l : Fin c) (hl : l.val < ρ) {m : ℕ} (M : Mx D m J.W.rank) (i : Fin m) :
    (M.map p.π * FW.β) i (Sum.inr l) = s * p.xi ^ (ρ - l.val) * p.π ((M ⬝ J.d.jX) i ⟨l.val, hl⟩) :=
  row_coord p FW (Sum.inr l) _ M J.d.jX ⟨l.val, hl⟩ (hJ.2.2.1 ⟨l.val, hl⟩ l rfl) i

theorem jac_Y (hJ : p.IsJacFrame J s hh G₀ FW) (l : Fin c) (i i' : Fin ρ) (h : l.val + i'.val + 1 = 2 * ρ) :
    (J.d.pY.map p.π * FW.β) i (Sum.inr l) =
      s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * if i = i' then 1 else 0 := by
  rw [row_coord p FW (Sum.inr l) _ J.d.pY J.d.jY i' (hJ.2.2.2 i' l h) i, HypDec.pY_jY, Matrix.one_apply]
  split_ifs <;> simp

theorem jac_Y_ne (hJ : p.IsJacFrame J s hh G₀ FW) (r : n ⊕ Fin c) (i : Fin ρ)
    (h : ∀ l, r = Sum.inr l → l.val + i.val + 1 ≠ 2 * ρ) : (J.d.pY.map p.π * FW.β) i r = 0 := by
  have hc := hJ.1
  rcases r with a | l
  · have h1 : (J.d.pY.map p.π * FW.β) i (Sum.inl a) = (J.d.pY.map p.π * (J.d.j0.map p.π * G₀.β)) i a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hJ.2.1]; rfl
    rw [h1, ← Matrix.mul_assoc, ← Matrix.map_mul, HypDec.pY_j0, Matrix.map_zero _ (map_zero _), Matrix.zero_mul]
    rfl
  · by_cases hl : l.val < ρ
    · rw [jac_low p hJ l hl, HypDec.pY_jX]
      simp
    · have hl' := l.2
      rw [jac_Y p hJ l i ⟨2 * ρ - 1 - l.val, by omega⟩ (by simp only; omega), if_neg, mul_zero]
      intro h'
      have h1 := h l rfl
      have h2 := congrArg Fin.val h'
      simp only at h2
      omega

end Jac
end Levels

theorem psi_xi (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hψ : p.IsChar ψ ψk) (x : k) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * cA D (p.ι (-x)))) = ψk x := by
  rw [hψ, psiE, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, map_neg, neg_mul_neg]

section Laws
variable (p : Place D k) {ρ : ℕ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {B : BesLev D ρ} {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)}
  {FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))}
  {J : JacLev D ρ} {G₀ : Frame k J.W₀.rank n} {FW : Frame k J.W.rank (n ⊕ Fin c)}

theorem up_mul_eq_zero (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) (a : k) {m : ℕ} (N : Mx D B.V.rank m)
    (h : ∀ j, (FV.γ * N.map p.π) q j = 0) : p.up FV FW (Matrix.single r q a) ⬝ N = 0 := by
  ext i j
  rw [← Matrix.one_mul (p.up FV FW (Matrix.single r q a)), sand, h, mul_zero, map_zero]
  rfl

theorem mul_up_eq_zero (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) (a : k) {m : ℕ} (N : Mx D m J.W.rank)
    (h : ∀ i, (N.map p.π * FW.β) i r = 0) : N ⬝ p.up FV FW (Matrix.single r q a) = 0 := by
  ext i j
  rw [← Matrix.mul_one (N ⬝ p.up FV FW (Matrix.single r q a)), sand, h, zero_mul, zero_mul, map_zero]
  rfl

theorem mxAt_sand (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)) (a : k) {m m' : ℕ} (N : Mx D m J.W.rank)
    (N' : Mx D B.V.rank m') : GlobalTheory.FinPl.MxAt (fun _ => True) (N ⬝ p.up FV FW (Matrix.single r q a) ⬝ N') := by
  intro i j
  rw [sand]
  exact ι_mem p _

theorem up_eq_extY (hC : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV) (r : n ⊕ Fin c) (j : Fin (c + 1))
    (hj : ρ < j.val) (a : k) : p.up FV FW (Matrix.single r (Sum.inr j) a) =
      B.d.extY J.W (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY) := by
  rw [HypDec.extY_apply]
  refine B.d.mat_ext ?_ ?_ ?_
  · rw [Matrix.mul_assoc _ B.d.pY, HypDec.pY_jX, Matrix.mul_zero]
    exact up_mul_eq_zero p _ _ _ _ (bes_X p hB _ fun j' h => by cases h; exact hj.le)
  · rw [Matrix.mul_assoc _ B.d.pY, HypDec.pY_j0, Matrix.mul_zero]
    exact up_mul_eq_zero p _ _ _ _ (bes_zero p hC hB j hj)
  · rw [Matrix.mul_assoc _ B.d.pY, HypDec.pY_jY, Matrix.mul_one]

theorem pairS_jX {W W₀ : HSp D} (d : HypDec W W₀ ρ) (u : Mx D ρ ρ) (y : Mx D W.rank ρ) :
    pairS W (d.jX ⬝ u) y = (adj (d.pY ⬝ y) ⬝ u).trace := by
  rw [pairS, adj_mul, d.pY_eq, adj_mul, adj_adj, adj_gA]
  simp only [Matrix.mul_assoc]

theorem uInv_up {hh : k} (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s hh G₀ FW) (r : n ⊕ Fin c)
    (j : Fin (c + 1)) (hr : ∀ l, r = Sum.inr l → l.val < j.val) (a : k) :
    GlobalTheory.FinPl.UInv J.W (xZero J.d) (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY) := by
  intro u
  have hu : ∀ i i' : Fin ρ, i' ≤ i → u.1.1 i i' = (1 : Mx D ρ ρ) i i' := by
    intro i i' h
    rcases h.lt_or_eq with h | rfl
    · rw [(u.2 i i').1 h, Matrix.one_apply_ne h.ne']
    · rw [(u.2 i' i').2, Matrix.one_apply_eq]
  have h1 := pairS_jX J.d 1 (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY)
  rw [Matrix.mul_one] at h1
  rw [xZero, pairS_jX, h1]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := adj _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  rcases le_or_gt i i' with h | h
  · rw [hu i' i h]
  · have h0 : (J.d.pY ⬝ (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY)) i' i = 0 := by
      rw [← Matrix.mul_assoc, sand]
      by_cases hji : j.val + i.val = 2 * ρ
      · rw [jac_Y_ne p hJ r i' fun l hl => by have := hr l hl; have := Fin.lt_def.1 h; omega, zero_mul, zero_mul,
          map_zero]
      · rw [bes_Y_ne p hB _ i fun j' h' => by cases h'; exact hji, mul_zero, map_zero]
    have h2 : adj (J.d.pY ⬝ (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY)) i i' = 0 := by
      show cA D _ = 0
      rw [h0, map_zero]
    rw [h2, zero_mul, zero_mul]

theorem trace_dual (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s (p.hz B) G₀ FW) (r : n ⊕ Fin c)
    (j : Fin (c + 1)) (hj : ρ < j.val) (a : k) :
    (J.d.pY ⬝ (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY)).trace =
      p.ι (-ch (Matrix.single r (Sum.inr j : n' ⊕ Fin (c + 1)) a)) := by
  have hc := hJ.1
  have hj' := j.2
  let i₀ : Fin ρ := ⟨2 * ρ - j.val, by omega⟩
  have hi₀ : j.val + i₀.val = 2 * ρ := by simp only [i₀]; omega
  rw [← Matrix.mul_assoc, Matrix.trace, Finset.sum_eq_single i₀, Matrix.diag, sand]
  · congr 1
    by_cases h : ∃ l : Fin c, r = Sum.inr l ∧ j = l.succ
    · obtain ⟨l, rfl, rfl⟩ := h
      have h1 := bes_Y p hB l.succ i₀ hi₀
      rw [ch_single_succ, jac_Y p hJ l i₀ i₀ (by rw [Fin.val_succ] at hi₀; omega), if_pos rfl]
      linear_combination (-a) * h1
    · rw [ch_single_ne _ _ _ fun l hl h' => h ⟨l, hl, Sum.inr.inj h'⟩,
        jac_Y_ne p hJ r i₀ fun l hl h' => h ⟨l, hl, Fin.ext (by rw [Fin.val_succ]; omega)⟩]
      simp
  · intro i _ hi
    rw [Matrix.diag, sand, bes_Y_ne p hB _ i fun j' h' h'' => hi (Fin.ext (by cases h'; omega)), mul_zero, map_zero]
  · simp

theorem value_dual {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hψ : p.IsChar ψ ψk)
    (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s (p.hz B) G₀ FW) (r : n ⊕ Fin c)
    (j : Fin (c + 1)) (hj : ρ < j.val) (a : k) :
    ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d))
      (B.d.extY J.W (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY))) =
      ψk (ch (Matrix.single r (Sum.inr j : n' ⊕ Fin (c + 1)) a)) := by
  have h := B.d.hO_ext J.W (xZero J.d) 0 0 (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace B.V₀, Matrix.mul_zero, trace_zero] at h
  have h1 := pairS_jX J.d 1 (p.up FV FW (Matrix.single r (Sum.inr j) a) ⬝ B.d.jY)
  rw [Matrix.mul_one, Matrix.mul_one] at h1
  rw [symplO_eq, h, show pairS J.W (0 : Mx D J.W.rank ρ) 0 = 0 by simp [pairS], add_zero, xZero, h1, trace_adj,
    trace_dual p hB hJ r j hj, psi_xi p hψ]

theorem up_eq_incX {hh : k} (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s hh G₀ FW) (l : Fin c) (hl : l.val < ρ)
    (q : n' ⊕ Fin (c + 1)) (hq : ∀ j, q = Sum.inr j → j.val = ρ) (a : k) :
    p.up FV FW (Matrix.single (Sum.inr l) q a) =
      B.d.ext0 J.W (J.d.incX B.V₀ (J.d.pX ⬝ p.up FV FW (Matrix.single (Sum.inr l) q a) ⬝ B.d.j0)) := by
  have h0 : J.d.p0 ⬝ p.up FV FW (Matrix.single (Sum.inr l) q a) = 0 :=
    mul_up_eq_zero p _ _ _ _ fun i => by rw [jac_low p hJ l hl, HypDec.p0_jX]; simp
  have hY : J.d.pY ⬝ p.up FV FW (Matrix.single (Sum.inr l) q a) = 0 :=
    mul_up_eq_zero p _ _ _ _ fun i => by rw [jac_low p hJ l hl, HypDec.pY_jX]; simp
  have hX : J.d.jX ⬝ (J.d.pX ⬝ p.up FV FW (Matrix.single (Sum.inr l) q a)) =
      p.up FV FW (Matrix.single (Sum.inr l) q a) := by
    conv_rhs => rw [← Matrix.one_mul (p.up FV FW (Matrix.single (Sum.inr l) q a)), ← J.d.sum_eq_one]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, h0, hY, Matrix.mul_zero,
      Matrix.mul_zero, add_zero, add_zero]
  rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, ← Matrix.mul_assoc J.d.jX, hX]
  refine B.d.mat_ext ?_ ?_ ?_
  · rw [Matrix.mul_assoc _ B.d.p0, HypDec.p0_jX, Matrix.mul_zero]
    exact up_mul_eq_zero p _ _ _ _ (bes_X p hB _ fun j h => (hq j h).ge)
  · rw [Matrix.mul_assoc _ B.d.p0, HypDec.p0_j0, Matrix.mul_one]
  · rw [Matrix.mul_assoc _ B.d.p0, HypDec.p0_jY, Matrix.mul_zero]
    exact up_mul_eq_zero p _ _ _ _ fun i => bes_Y_ne p hB _ i fun j h => by have := hq j h; have := i.2; omega

theorem splitComponent_wittZero_besselYZeroPoint (t : Fin B.V.rank) (i : Fin ρ) : p.π ((B.d.j0 ⬝ yZero B.V₀ ρ (vecB B.o B.ζ)) t i) =
    -(p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) t) * if i.val + 1 = ρ then 1 else 0) := by
  have h0 : ∀ u, p.π (yZero B.V₀ ρ (vecB B.o B.ζ) u i) =
      -(p.pr (vecB B.o B.ζ u) * if i.val + 1 = ρ then 1 else 0) := by
    intro u
    rw [yZero, Matrix.neg_apply, zEll, Matrix.vecMulVec_apply, map_neg, map_mul, ell, apply_ite p.π, map_one, map_zero]
    rfl
  rw [Matrix.mul_apply, map_sum, Place.pr, Matrix.mulVec, dotProduct, map_sum, map_sum, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_mul, h0, map_mul, map_mul, mul_assoc, mul_neg]
  rfl

theorem bes_yZero (hB : p.IsBesFrame B s FA FV) (j : Fin (c + 1)) (hj : j.val = ρ) (q : n' ⊕ Fin (c + 1)) (i : Fin ρ) :
    s * (FV.γ * (B.d.j0 ⬝ yZero B.V₀ ρ (vecB B.o B.ζ)).map p.π) q i =
      -((if q = Sum.inr j then 1 else 0) * if i.val + 1 = ρ then 1 else 0) := by
  rw [← besselNormalFrame_lineVectorColumn p hB j hj q, Matrix.mul_apply, mul_assoc, ← mul_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine congrArg (s * ·) (Finset.sum_congr rfl fun t _ => ?_)
  rw [Matrix.map_apply, splitComponent_wittZero_besselYZeroPoint, mul_neg, mul_assoc]

theorem trace_iso {hh : k} (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s hh G₀ FW) (l : Fin c) (hl : l.val < ρ)
    (q : n' ⊕ Fin (c + 1)) (hq : ∀ j, q = Sum.inr j → j.val = ρ) (a : k) :
    (yZero B.V₀ ρ (vecB B.o B.ζ) ⬝ (J.d.pX ⬝ p.up FV FW (Matrix.single (Sum.inr l) q a) ⬝ B.d.j0)).trace =
      -(incA D D.host.xi0 * p.ι (ch (Matrix.single (Sum.inr l : n ⊕ Fin c) q a))) := by
  have hc := hJ.1
  obtain ⟨j, hj⟩ : ∃ j : Fin (c + 1), j.val = ρ := ⟨⟨ρ, by omega⟩, rfl⟩
  have h1 := bes_yZero p hB j hj q ⟨l.val, hl⟩
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, mul_comm (incA D _), ι_mul, ← map_neg, Matrix.trace,
    Finset.sum_eq_single ⟨l.val, hl⟩, Matrix.diag, sand, jac_low p hJ l hl, HypDec.pX_jX, Matrix.one_apply_eq, map_one]
  · refine congrArg p.ι ?_
    rw [show p.π (incA D D.host.xi0) = p.xi from rfl]
    generalize (FV.γ * (B.d.j0 ⬝ yZero B.V₀ ρ (vecB B.o B.ζ)).map p.π) q ⟨l.val, hl⟩ = w at h1 ⊢
    by_cases h : q = Sum.inr l.succ
    · have h2 := hq _ h
      rw [if_pos (h.trans (congrArg Sum.inr (Fin.ext (h2.trans hj.symm)))), if_pos (show l.val + 1 = ρ from h2)] at h1
      rw [Fin.val_succ] at h2
      rw [show ρ - l.val = 1 by omega, pow_one, h, ch_single_succ]
      linear_combination (a * p.xi) * h1
    · rw [ch_single_ne _ _ _ fun l' hl' => by cases hl'; exact h]
      have h3 : ((if q = Sum.inr j then 1 else 0) * if l.val + 1 = ρ then 1 else 0 : k) = 0 := by
        split_ifs with h4 h5
        · exact absurd (h4.trans (congrArg Sum.inr (Fin.ext (hj.trans h5.symm)))) h
        all_goals simp
      rw [h3] at h1
      linear_combination (a * p.xi ^ (ρ - l.val)) * h1
  · intro i _ hi
    rw [Matrix.diag, sand, jac_low p hJ l hl, HypDec.pX_jX, Matrix.one_apply_ne hi, map_zero, mul_zero, zero_mul,
      zero_mul, map_zero]
  · simp

end Laws

theorem flatBF_trans : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), GlobalTheory.RootEx.Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → flatBF st (Tm Φ') = (ψk (GlobalTheory.RootEx.ch (Matrix.single r q a)) : ℂ) • flatBF st (Tm Φ) := by
  intro D _ hLaws _ k _ _ _ _ _ _ p ν _ ψ ψk hψ ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW hC hB hJ Tm hTm r q hfree hq
    a Φ Φ' hΦ
  have hF := ((hLaws ψ (fun _ => True)).1 ρ B J st).Heisenberg₂
  rw [hTm.trans _ Φ Φ' hΦ]
  by_cases hqa : ∃ j : Fin (c + 1), q = Sum.inr j ∧ ρ < j.val
  · obtain ⟨j, rfl, hj⟩ := hqa
    have hm := mxAt_sand p (FV := FV) (FW := FW) r (Sum.inr j) a (1 : Mx D J.W.rank J.W.rank) B.d.jY
    rw [Matrix.one_mul] at hm
    rw [up_eq_extY p hC hB r j hj a, hF.dual _ (hTm.theta Φ) _ hm
      (uInv_up p hB hJ r j (fun l hl => by subst hl; exact hfree) a), value_dual p hψ hB hJ r j hj]
  · have hq' : ∀ j, q = Sum.inr j → j.val = ρ := fun j hj =>
      le_antisymm (not_lt.1 fun h => hqa ⟨j, hj, h⟩) (hq j hj)
    obtain ⟨l, rfl, hl⟩ : ∃ l : Fin c, r = Sum.inr l ∧ l.val < ρ := by
      rcases r with m | l <;> rcases q with m' | j
      · exact hfree.elim
      · have h1 : ρ + 1 < j.val + 1 := hfree
        have := hq' j rfl
        omega
      · exact ⟨l, rfl, Nat.lt_of_succ_lt_succ hfree⟩
      · exact ⟨l, rfl, hq' j rfl ▸ hfree⟩
    rw [up_eq_incX p hB hJ l hl q hq' a, hF.iso _ (hTm.theta Φ) _ (mxAt_sand p _ _ _ _ _), symplO_skew,
      HypDec.symplO_incX_incAdj, trace_iso p hB hJ l hl q hq', LinearMap.map_neg, neg_neg, hψ]
    rfl

end GlobalTheory.FlatTransLaw
