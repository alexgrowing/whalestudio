import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarStartConjugationIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD

namespace Formalism.FourierDecayAlt.P.TLA.ColumnLift

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.TLA.L1

section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem fnc (L : LevelData A r) {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : x * y = y * x := L.fns_comm x (Set.mem_union_right _ hx) y (Set.mem_union_right _ hy)

theorem kLf {L : LevelData A r} {st : Start A} {n : ℕ} {Lf : ℕ → ℕ → A → Prop} (hS : LiftSys L st n Lf) {a : A}
    (ha : a ∈ kAlg st) : Lf 0 0 a := by
  unfold kAlg at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨Y, hY, rfl⟩ | ⟨Y, hYi, hY, rfl⟩
    · exact hS.x Y hY
    · exact hS.xi Y hYi hY
  | algebraMap z =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact hS.smul z hS.one
  | add x y _ _ hx hy => exact hS.add hx hy
  | mul x y _ _ hx hy => simpa using hS.mul hx hy

theorem gi_site (L : LevelData A r) : ∀ y ∈ siteOps L, Commute L.GGi y := by
  intro y hy
  simp only [siteOps, Set.mem_union, Set.mem_range] at hy
  rcases hy with (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
  · exact (L.p_GGi l).symm
  · exact (L.pb_GGi l).symm
  · exact L.fns_comm _ (by simp) _ (by simp)
  · exact L.fns_comm _ (by simp) _ (by simp)
  · exact L.fns_comm _ (by simp) _ (by simp)
  · exact L.fns_comm _ (by simp) _ (by simp)

theorem x_site {L : LevelData A r} {st : Start A} (h : AHyp L st) (Y : ℂ) : ∀ y ∈ siteOps L, Commute (st.x Y) y := by
  intro y hy
  have h1 : Commute (L.GG * st.x Y) y := by
    have := h.qq_site Y 1 1 y hy
    rwa [h.start.tau Y] at this
  have h3 : L.GGi * (L.GG * st.x Y) = st.x Y := by rw [← mul_assoc, L.GGi_GG, one_mul]
  rw [← h3]
  exact (gi_site L y hy).mul_left h1

theorem comm_TP {L : LevelData A r} {x : A} (hx : ∀ y ∈ siteOps L, Commute x y) (Y : ℂ) :
    Commute x (L.Ar Y) ∧ Commute x (L.Br Y) := by
  have hp : ∀ l, Commute x (L.p l) := fun l => hx _ (by simp [siteOps])
  have hc : ∀ l, Commute x (L.c l) := fun l => hx _ (by simp [siteOps])
  have hci : ∀ l, Commute x (L.ci l) := fun l => hx _ (by simp [siteOps])
  have key : ∀ (l : List (Matrix (Fin 2) (Fin 2) A)), (∀ M ∈ l, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (l.prod i j) := by
    intro l
    induction l with
    | nil =>
      intro _ i j
      rw [List.prod_nil, Matrix.one_apply]
      split_ifs
      · exact Commute.one_right x
      · exact Commute.zero_right x
    | cons M l ih =>
      intro h i j
      rw [List.prod_cons, Matrix.mul_apply]
      refine Commute.sum_right _ _ _ (fun k _ => ?_)
      exact (h M (List.mem_cons_self ..) i k).mul_right (ih (fun N hN => h N (List.mem_cons_of_mem _ hN)) k j)
  have hT : ∀ M ∈ (List.ofFn (L.Tl Y)).reverse, ∀ i j, Commute x (M i j) := by
    intro M hM i j
    rw [List.mem_reverse, List.mem_ofFn] at hM
    obtain ⟨l, rfl⟩ := hM
    fin_cases i <;> fin_cases j <;> simp [Formalism.FourierDecayAlt.R.LevelData.Tl, hc, hci] <;>
      first
      | exact Commute.add_right (Algebra.commutes Y x).symm (hp l)
      | exact hc l
      | exact (hc l).neg_right
      | exact hci l
  exact ⟨key _ hT 0 0, key _ hT 1 0⟩

theorem comm_TM {L : LevelData A r} {x : A} (hx : ∀ y ∈ siteOps L, Commute x y) (Y : ℂ) :
    Commute x (L.Avr Y) ∧ Commute x (L.Bvr Y) := by
  have hp : ∀ l, Commute x (L.pb l) := fun l => hx _ (by simp [siteOps])
  have hc : ∀ l, Commute x (L.cb l) := fun l => hx _ (by simp [siteOps])
  have hci : ∀ l, Commute x (L.cbi l) := fun l => hx _ (by simp [siteOps])
  have key : ∀ (l : List (Matrix (Fin 2) (Fin 2) A)), (∀ M ∈ l, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (l.prod i j) := by
    intro l
    induction l with
    | nil =>
      intro _ i j
      rw [List.prod_nil, Matrix.one_apply]
      split_ifs
      · exact Commute.one_right x
      · exact Commute.zero_right x
    | cons M l ih =>
      intro h i j
      rw [List.prod_cons, Matrix.mul_apply]
      refine Commute.sum_right _ _ _ (fun k _ => ?_)
      exact (h M (List.mem_cons_self ..) i k).mul_right (ih (fun N hN => h N (List.mem_cons_of_mem _ hN)) k j)
  have hT : ∀ M ∈ (List.ofFn (L.Tvl Y)).reverse, ∀ i j, Commute x (M i j) := by
    intro M hM i j
    rw [List.mem_reverse, List.mem_ofFn] at hM
    obtain ⟨l, rfl⟩ := hM
    fin_cases i <;> fin_cases j <;> simp [Formalism.FourierDecayAlt.R.LevelData.Tvl, hc, hci] <;>
      first
      | exact Commute.sub_right (Algebra.commutes Y x).symm (hp l)
      | exact hc l
      | exact (hc l).neg_right
      | exact hci l
  exact ⟨key _ hT 0 0, key _ hT 1 0⟩

theorem ent3 {L : LevelData A r} {st : Start A} {n : ℕ} {Lf : ℕ → ℕ → A → Prop} (hS : LiftSys L st n Lf)
    {α β γ : SlopeTestRemainingChoices S A} (hα : kMat st α) (hβ : kMat st β) (hγ : kMat st γ) {u : A} (hu : Lf n (3 * (r + 1) * n) u)
    (e e' : Ix S) : Lf n (7 * (r + 1) * n) ((α * (io u * β - β * io u) * γ : SlopeTestRemainingChoices S A) e e') := by
  have hk : ∀ (M : SlopeTestRemainingChoices S A), kMat st M → ∀ i j, Lf 0 0 (M i j) := fun M hM i j => kLf hS (hM i j)
  have hsum : ∀ {o κ : ℕ} (f : Ix S → A), (∀ k ∈ (Finset.univ : Finset (Ix S)), Lf o κ (f k)) →
      Lf o κ (∑ k, f k) := fun f hf =>
    Finset.sum_induction _ _ (fun a b ha hb => hS.add ha hb) (hS.zero _ _) hf
  have hsub : ∀ {o κ : ℕ} {a b : A}, Lf o κ a → Lf o κ b → Lf o κ (a - b) := by
    intro o κ a b ha hb
    have := hS.add ha (hS.smul (-1 : ℂ) hb)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hle : 3 * (r + 1) * n ≤ 5 * (r + 1) * n := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    norm_num
  have hD : ∀ k m, Lf n (5 * (r + 1) * n) ((io u * β - β * io u : SlopeTestRemainingChoices S A) k m) := by
    intro k m
    have e1 : (io u * β - β * io u : SlopeTestRemainingChoices S A) k m = u * β k m - β k m * u := by simp [io]
    rw [e1]
    refine hsub ?_ ?_
    · exact hS.mono (le_of_eq (by ring)) (le_of_eq (by ring)) (hS.mul hu (hk β hβ k m))
    · exact hS.mono (le_of_eq (by ring)) (le_trans (le_of_eq (by ring)) hle) (hS.mul (hk β hβ k m) hu)
  simp only [Matrix.mul_apply]
  refine hsum _ (fun m _ => ?_)
  have h1 : Lf n (5 * (r + 1) * n) (∑ k, α e k * (io u * β - β * io u : SlopeTestRemainingChoices S A) k m) :=
    hsum _ (fun k _ => hS.mono (le_of_eq (by ring)) (le_of_eq (by ring)) (hS.mul (hk α hα e k) (hD k m)))
  exact hS.mono (le_of_eq (by ring)) (le_of_eq (by ring)) (hS.mul h1 (hk γ hγ m e'))

theorem colLift {L : LevelData A r} {st : Start A} {n : ℕ} {Lf : ℕ → ℕ → A → Prop} (hst : IsLevelStart L st)
    (hS : LiftSys L st n Lf) (hn : r + 1 ≤ n) {E s V W u f t aa z2 : A} {X M : SlopeTestRemainingChoices S A} (hX : X = io E)
    (hs : ∀ Y, Commute (st.x Y) s) (hV : ∀ Y, Commute (st.x Y) V) (hW : ∀ Y, Commute (st.x Y) W)
    (hf : ∀ Y, Commute (st.x Y) f) (ht : ∀ Y, Commute (st.x Y) t)
    (hu : s * (E * V + W) = u) (hLu : Lf n (3 * (r + 1) * n) u) (ha : s * f * V = aa)
    (hLa : Lf n (8 * (r + 1) * n) aa) (hz : s * f * t * V = z2 * aa) (hLz : Lf 0 r z2)
    (hM : M - X ∈ dSpan st X (io f) (io t)) (e e' : Ix S) :
    Lf n (9 * (r + 1) * n) ((io s * (M * io V + io W) : SlopeTestRemainingChoices S A) e e') := by
  subst hX
  have comK : ∀ c : A, (∀ Y, Commute (st.x Y) c) → ∀ a ∈ kAlg st, Commute a c := by
    intro c hc a ha
    unfold kAlg at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨Y, _, rfl⟩ | ⟨Y, hYi, _, rfl⟩
      · exact hc Y
      · obtain ⟨h1, h2⟩ := hst.x_xi Y hYi
        show st.xi Y * c = c * st.xi Y
        calc st.xi Y * c = st.xi Y * c * (st.x Y * st.xi Y) := by rw [h1, mul_one]
          _ = st.xi Y * (c * st.x Y) * st.xi Y := by simp only [mul_assoc]
          _ = st.xi Y * (st.x Y * c) * st.xi Y := by rw [← (hc Y).eq]
          _ = st.xi Y * st.x Y * c * st.xi Y := by simp only [mul_assoc]
          _ = c * st.xi Y := by rw [h2, one_mul]
    | algebraMap z => exact Algebra.commutes z c
    | add x y _ _ hx hy => exact hx.add_left hy
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have hcomm : ∀ (c : A) (N : SlopeTestRemainingChoices S A), (∀ i j, Commute c (N i j)) → io c * N = N * io c := by
    intro c N h
    ext i j
    simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact (h i j).eq
  have h39 : 3 * (r + 1) * n ≤ 9 * (r + 1) * n := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    norm_num
  have h79 : 7 * (r + 1) * n ≤ 9 * (r + 1) * n := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    norm_num
  have h89 : 8 * (r + 1) * n ≤ 9 * (r + 1) * n := by
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_right
    norm_num
  have hr9 : r + 8 * (r + 1) * n ≤ 9 * (r + 1) * n := by nlinarith [hn]
  have key : ∀ D : SlopeTestRemainingChoices S A, D ∈ dSpan st (io E : SlopeTestRemainingChoices S A) (io f) (io t) → ∀ e e', Lf n (9 * (r + 1) * n) (s * D e e' * V) := by
    intro D hD
    unfold dSpan at hD
    induction hD using Submodule.span_induction with
    | mem D hD =>
      rcases hD with ⟨α, β, γ, hα, hβ, hγ, rfl⟩ | ⟨γ, hγ, rfl | rfl⟩
      · intro e e'
        have cs : ∀ N : SlopeTestRemainingChoices S A, kMat st N → io s * N = N * io s :=
          fun N hN => hcomm s N (fun i j => (comK s hs _ (hN i j)).symm)
        have cV : ∀ N : SlopeTestRemainingChoices S A, kMat st N → io V * N = N * io V :=
          fun N hN => hcomm V N (fun i j => (comK V hV _ (hN i j)).symm)
        have hsW : ∀ Y, Commute (st.x Y) (s * W) := fun Y => (hs Y).mul_right (hW Y)
        have cSW : io (s * W) * β = β * io (s * W) := hcomm _ β (fun i j => (comK _ hsW _ (hβ i j)).symm)
        have hsEV : s * E * V = u - s * W := by rw [← hu]; simp only [mul_add, mul_assoc]; abel
        have e3 : io s * (io E * β - β * io E) * io V = io u * β - β * io u := by
          have e2 : io s * (io E * β - β * io E) * io V =
              io s * io E * (β * io V) - io s * β * io E * io V := by simp only [mul_sub, sub_mul, mul_assoc]
          rw [e2, ← cV β hβ, cs β hβ]
          have e4 : io s * io E * (io V * β) - β * io s * io E * io V =
              io (s * E * V) * β - β * io (s * E * V) := by
            simp only [io, map_mul, mul_assoc]
          rw [e4, hsEV]
          have e5 : io (u - s * W) * β - β * io (u - s * W) =
              io u * β - β * io u - (io (s * W) * β - β * io (s * W)) := by
            simp only [io, map_sub, sub_mul, mul_sub]; abel
          rw [e5, cSW, sub_self, sub_zero]
        have e6 : io s * (α * (io E * β - β * io E) * γ) * io V = α * (io u * β - β * io u) * γ := by
          calc io s * (α * (io E * β - β * io E) * γ) * io V
              = io s * α * (io E * β - β * io E) * (γ * io V) := by simp only [mul_assoc]
            _ = α * io s * (io E * β - β * io E) * (io V * γ) := by rw [cs α hα, ← cV γ hγ]
            _ = α * (io s * (io E * β - β * io E) * io V) * γ := by simp only [mul_assoc]
            _ = α * (io u * β - β * io u) * γ := by rw [e3]
        have e7 : s * (α * (io E * β - β * io E) * γ : SlopeTestRemainingChoices S A) e e' * V =
            (io s * (α * (io E * β - β * io E) * γ) * io V : SlopeTestRemainingChoices S A) e e' := by
          simp [io, mul_assoc]
        rw [e7, e6]
        exact hS.mono le_rfl h79 (ent3 hS hα hβ hγ hLu e e')
      · intro e e'
        have c1 : Commute (γ e e') s := comK s hs _ (hγ e e')
        have c2 : Commute (γ e e') f := comK f hf _ (hγ e e')
        have eq : s * (io f * γ : SlopeTestRemainingChoices S A) e e' * V = γ e e' * aa := by
          rw [← ha]
          simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul]
          calc s * (f * γ e e') * V = s * (γ e e' * f) * V := by rw [← c2.eq]
            _ = s * γ e e' * f * V := by simp only [mul_assoc]
            _ = γ e e' * s * f * V := by rw [← c1.eq]
            _ = γ e e' * (s * f * V) := by simp only [mul_assoc]
        rw [eq]
        exact hS.mono (le_of_eq (by ring)) (le_trans (le_of_eq (by ring)) h89)
          (hS.mul (kLf hS (hγ e e')) hLa)
      · intro e e'
        have c1 : Commute (γ e e') s := comK s hs _ (hγ e e')
        have c2 : Commute (γ e e') f := comK f hf _ (hγ e e')
        have c4 : Commute (γ e e') t := comK t ht _ (hγ e e')
        have eq : s * (io f * io t * γ : SlopeTestRemainingChoices S A) e e' * V = γ e e' * z2 * aa := by
          rw [mul_assoc (γ e e'), ← hz]
          simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul]
          calc s * (f * t * γ e e') * V = s * f * (t * γ e e') * V := by simp only [mul_assoc]
            _ = s * f * (γ e e' * t) * V := by rw [← c4.eq]
            _ = s * (f * γ e e') * t * V := by simp only [mul_assoc]
            _ = s * (γ e e' * f) * t * V := by rw [← c2.eq]
            _ = s * γ e e' * f * t * V := by simp only [mul_assoc]
            _ = γ e e' * s * f * t * V := by rw [← c1.eq]
            _ = γ e e' * (s * f * t * V) := by simp only [mul_assoc]
        rw [eq]
        exact hS.mono (le_of_eq (by ring)) (le_trans (le_of_eq (by ring)) hr9)
          (hS.mul (hS.mul (kLf hS (hγ e e')) hLz) hLa)
    | zero => intro e e'; simpa using hS.zero n (9 * (r + 1) * n)
    | add x y _ _ hx hy => intro e e'; simpa [mul_add, add_mul] using hS.add (hx e e') (hy e e')
    | smul a x _ hx => intro e e'; simpa using hS.smul a (hx e e')
  have eM : (io s * (M * io V + io W) : SlopeTestRemainingChoices S A) e e' = (if e = e' then u else 0) + s * (M - io E : SlopeTestRemainingChoices S A) e e' * V := by
    simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.sub_apply, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [← hu]; simp only [mul_add, mul_sub, sub_mul, mul_assoc]; abel
    · simp [mul_assoc]
  rw [eM]
  refine hS.add ?_ (key (M - io E) hM e e')
  split_ifs
  · exact hS.mono le_rfl h39 hLu
  · exact hS.zero _ _

theorem s1p (L : LevelData A r) : L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζi := by
  have c1 : L.GG * L.ζb = L.ζb * L.GG := fnc L (by simp [zfns]) (by simp [zfns])
  have c2 : L.GG * L.ζi = L.ζi * L.GG := fnc L (by simp [zfns]) (by simp [zfns])
  calc L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζbi * (L.GG * L.ζb) * L.ζi * L.GGi := by simp only [mul_assoc]
    _ = L.ζbi * L.ζb * (L.GG * L.ζi) * L.GGi := by rw [c1]; simp only [mul_assoc]
    _ = L.ζi * (L.GG * L.GGi) := by rw [L.ζbi_ζb, c2, one_mul, mul_assoc]
    _ = L.ζi := by rw [L.GG_GGi, mul_one]

theorem s1m (L : LevelData A r) : L.ζi * L.GG * (L.ζ * L.ζbi * L.GGi) = L.ζbi := by
  have h1 : L.GG * L.ζ = L.ζ * L.GG := fnc L (by simp [zfns]) (by simp [zfns])
  have h2 : L.GG * L.ζbi = L.ζbi * L.GG := fnc L (by simp [zfns]) (by simp [zfns])
  calc L.ζi * L.GG * (L.ζ * L.ζbi * L.GGi)
      = L.ζi * (L.GG * L.ζ) * L.ζbi * L.GGi := by simp only [mul_assoc]
    _ = L.ζi * L.ζ * (L.GG * L.ζbi) * L.GGi := by rw [h1]; simp only [mul_assoc]
    _ = L.ζi * L.ζ * L.ζbi * (L.GG * L.GGi) := by rw [h2]; simp only [mul_assoc]
    _ = L.ζbi := by rw [L.ζi_ζ, L.GG_GGi, one_mul, mul_one]

theorem letter {L : LevelData A r} {st : Start A} {n : ℕ} {Lf : ℕ → ℕ → A → Prop} (hB : BasicLift) (hLS : LShape)
    (hMS : MShape) (h : AHyp L st) (hS : LiftSys L st n Lf) (hn : r + 1 ≤ n) (l : Letter ℂ S) (w : List (Letter ℂ S))
    (hA : admitted st (l :: w)) (i : Fin 2) (e e' : Ix S) : Lf n (9 * (r + 1) * n) (letterCol L st l w i e e') := by
  have hst := h.start
  have hL := h.starLev
  obtain ⟨hnd, hre, hpt, hpw⟩ := hA
  have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
    List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
  have hpw' := List.pairwise_cons.mp hpw
  have hAw : admitted st w :=
    ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
  obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
  have hd := hpw'.1
  have m0 : l.pt ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
    ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
  have m1 : l.pt + 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
    ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
  have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
    ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
  have hr : star l.pt = l.pt := hre l (by simp)
  obtain ⟨lbP, lbM, laP, laM⟩ := hB A r n L st Lf h hS hn l.pt hr pm1 p0 p1
  obtain ⟨fD, fDb, fDr, fDrb, fDi, fDbi, -⟩ := hS.fns
  have xz : ∀ g ∈ zfns L, ∀ Y, Commute (st.x Y) g := fun g hg Y => hst.x_fn Y g hg
  have hxx : st.xi l.pt * st.x l.pt = 1 := (hst.x_xi l.pt p0).2
  have xiz : ∀ g ∈ zfns L, Commute (st.xi l.pt) g := fun g hg => L1.xi_comm hst p0 (hst.x_fn l.pt g hg)
  have mζ : L.ζ ∈ zfns L := by simp [zfns]
  have mζi : L.ζi ∈ zfns L := by simp [zfns]
  have mζb : L.ζb ∈ zfns L := by simp [zfns]
  have mζbi : L.ζbi ∈ zfns L := by simp [zfns]
  have mG : L.GG ∈ zfns L := by simp [zfns]
  have mGi : L.GGi ∈ zfns L := by simp [zfns]
  have sum : ∀ {ι : Type} (s : Finset ι) (f : ι → A) o κ, (∀ i ∈ s, Lf o κ (f i)) → Lf o κ (∑ i ∈ s, f i) :=
    fun s f o κ hf => Finset.sum_induction f _ (fun _ _ => hS.add) (hS.zero o κ) hf
  have ioE : ∀ a : A, Lf n (8 * (r + 1) * n) a → Lf n (9 * (r + 1) * n) ((io a : SlopeTestRemainingChoices S A) e e') := fun a ha => by
    simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact hS.mono le_rfl (by nlinarith) ha
    · exact hS.zero _ _
  unfold letterCol
  by_cases hp : l.plus
  · simp only [hp, if_true]
    fin_cases i
    · exact ioE _ laP
    · simp only [Fin.mk_one, Matrix.cons_val_one]
      have hX : (st.frame : FrameData S A).l L l.pt =
          io (L.l0 l.pt + L.ζb * L.ζi * L.GGi * st.ee l.pt) := by
        show io (L.l0 l.pt) + io (L.ζb * L.ζi * L.GGi) * io (st.ee l.pt) = _
        rw [← M2.io_mul, ← M2.io_add]
      have hu : L.ζbi * L.GG * ((L.l0 l.pt + L.ζb * L.ζi * L.GGi * st.ee l.pt) * L.Ar l.pt + L.Br l.pt) =
          st.xi l.pt * bP L st l.pt := by
        unfold bP nP
        rw [hst.low l.pt p0, hst.tau]
        symm
        calc st.xi l.pt * (L.ζbi * (L.GG * st.x l.pt * (L.l0 l.pt + L.ζb * L.ζi * L.GGi * st.ee l.pt) * L.Ar l.pt +
              L.GG * st.x l.pt * L.Br l.pt)) = L.ζbi * (st.xi l.pt * (L.GG * (st.x l.pt *
              ((L.l0 l.pt + L.ζb * L.ζi * L.GGi * st.ee l.pt) * L.Ar l.pt + L.Br l.pt)))) := by
                rw [(xiz _ mζbi).left_comm]; congr 2; noncomm_ring
          _ = L.ζbi * (L.GG * (st.xi l.pt * (st.x l.pt *
              ((L.l0 l.pt + L.ζb * L.ζi * L.GGi * st.ee l.pt) * L.Ar l.pt + L.Br l.pt)))) := by
                rw [(xiz _ mG).left_comm]
          _ = _ := by rw [← mul_assoc (st.xi l.pt), hxx, one_mul, ← mul_assoc]
      have hz : L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) * (L.TT • L.ζbi) * L.Ar l.pt =
          (L.TT • L.ζbi) * aP L l.pt := by
        rw [s1p, aP, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, fnc L mζi mζbi, mul_assoc]
      have hLz : Lf 0 r (L.TT • L.ζbi) := by
        have e1 : L.Dbi * L.Drb = L.ζbi := by
          rw [LevelData.Dbi, mul_assoc, Drbi_Drb, mul_one]
        rw [← e1]
        exact hS.smul _ (hS.mono le_rfl (by simp) (hS.mul fDbi fDrb))
      exact colLift hst hS hn hX (fun Y => (xz _ mζbi Y).mul_right (xz _ mG Y))
        (fun Y => (comm_TP (x_site h Y) l.pt).1) (fun Y => (comm_TP (x_site h Y) l.pt).2)
        (fun Y => ((xz _ mζb Y).mul_right (xz _ mζi Y)).mul_right (xz _ mGi Y))
        (fun Y => (xz _ mζbi Y).smul_right L.TT) hu
        (hS.mono (by omega) (le_of_eq (by ring)) (hS.mul (hS.xi _ p0 hr) lbP))
        (by rw [s1p]; rfl) laP hz hLz ((hLS A S r L st w hL hst hAw).2.2 l.pt m0 m1) e e'
  · simp only [hp, Bool.false_eq_true, if_false]
    fin_cases i
    · exact ioE _ laM
    · simp only [Fin.mk_one, Matrix.cons_val_one]
      have hfr0 : IsFrame L (st.frame : FrameData S A) :=
        Formalism.FourierDecayAlt.P.frame_of_admissible_word A S r L st [] hL hst ⟨List.nodup_nil, by simp, by simp, List.Pairwise.nil⟩
      have fm := Formalism.FourierDecayAlt.P.frame_adjoint_m A S r L (st.frame : FrameData S A) l.pt hL hfr0 hr p0 pm1
      have fm' : (io (st.QQ l.pt 0 1) : SlopeTestRemainingChoices S A) = io L.GG * io (st.x l.pt) * (st.frame : FrameData S A).m L l.pt := by
        have := fm
        simp only [Start.frame, lift0, Matrix.map_apply, one_mul, mul_one] at this
        exact this
      have hX : (st.frame : FrameData S A).m L l.pt = io (st.xi l.pt * L.GGi * st.QQ l.pt 0 1) := by
        have h1 : st.xi l.pt * L.GGi * L.GG * st.x l.pt = 1 := by
          rw [mul_assoc (st.xi l.pt), L.GGi_GG, mul_one, hxx]
        calc (st.frame : FrameData S A).m L l.pt
            = io (st.xi l.pt * L.GGi * L.GG * st.x l.pt) * (st.frame : FrameData S A).m L l.pt := by
              rw [h1]; show _ = Matrix.scalar (Ix S) (1 : A) * _; rw [map_one, one_mul]
          _ = _ := by
              rw [M2.io_mul (st.xi l.pt * L.GGi), fm', M2.io_mul, M2.io_mul, M2.io_mul]; simp only [mul_assoc]
      have hxG : Commute (st.xi l.pt) L.GG := xiz _ mG
      have hu : L.ζi * L.GG * (st.xi l.pt * L.GGi * st.QQ l.pt 0 1 * L.Avr l.pt + L.Bvr l.pt) =
          st.xi l.pt * bM L st l.pt := by
        unfold bM
        rw [hst.tau]
        calc L.ζi * L.GG * (st.xi l.pt * L.GGi * st.QQ l.pt 0 1 * L.Avr l.pt + L.Bvr l.pt)
            = L.ζi * ((L.GG * st.xi l.pt) * L.GGi * st.QQ l.pt 0 1 * L.Avr l.pt + L.GG * L.Bvr l.pt) := by
              noncomm_ring
          _ = L.ζi * (st.xi l.pt * (L.GG * L.GGi) * st.QQ l.pt 0 1 * L.Avr l.pt + L.GG * L.Bvr l.pt) := by
              rw [← hxG.eq]; noncomm_ring
          _ = L.ζi * (st.xi l.pt * st.QQ l.pt 0 1 * L.Avr l.pt + L.GG * (st.xi l.pt * st.x l.pt) * L.Bvr l.pt) := by
              rw [L.GG_GGi, hxx]; noncomm_ring
          _ = L.ζi * (st.xi l.pt * st.QQ l.pt 0 1 * L.Avr l.pt + (st.xi l.pt * L.GG) * st.x l.pt * L.Bvr l.pt) := by
              rw [hxG.eq]; noncomm_ring
          _ = st.xi l.pt * (L.ζi * (st.QQ l.pt 0 1 * L.Avr l.pt + L.GG * st.x l.pt * L.Bvr l.pt)) := by
              rw [(xiz _ mζi).left_comm]; congr 1; noncomm_ring
      have hz : L.ζi * L.GG * (L.ζ * L.ζbi * L.GGi) * (L.TT • L.ζi) * L.Avr l.pt =
          (L.TT • L.ζi) * aM L l.pt := by
        rw [s1m, aM, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, fnc L mζbi mζi, mul_assoc]
      have hLz : Lf 0 r (L.TT • L.ζi) := by
        have e1 : L.Di * L.Dr = L.ζi := by
          rw [LevelData.Di, mul_assoc, Dri_Dr, mul_one]
        rw [← e1]
        exact hS.smul _ (hS.mono le_rfl (by simp) (hS.mul fDi fDr))
      exact colLift hst hS hn hX (fun Y => (xz _ mζi Y).mul_right (xz _ mG Y))
        (fun Y => (comm_TM (x_site h Y) l.pt).1) (fun Y => (comm_TM (x_site h Y) l.pt).2)
        (fun Y => ((xz _ mζ Y).mul_right (xz _ mζbi Y)).mul_right (xz _ mGi Y))
        (fun Y => (xz _ mζi Y).smul_right L.TT) hu
        (hS.mono (by omega) (le_of_eq (by ring)) (hS.mul (hS.xi _ p0 hr) lbM))
        (by rw [s1m]; rfl) laM hz hLz (hMS A S r L st w hL hst hAw l.pt m0 hr mm1) e e'

end

end Formalism.FourierDecayAlt.P.TLA.ColumnLift

namespace Formalism.FourierDecayAlt.P

theorem letter_lift_of_parts : Formalism.FourierDecayAlt.TL.LetterLiftOfParts := by
  intro hB hLS hMS A S _ _ _ _ _ _ r n L st Lf l w h hS hn hA i e e'
  exact TLA.ColumnLift.letter hB hLS hMS h hS hn l w hA i e e'

theorem m_shape_of_l_shape : Formalism.FourierDecayAlt.TL.MShape := TLA.M2.mShape_of l_shape

end Formalism.FourierDecayAlt.P
