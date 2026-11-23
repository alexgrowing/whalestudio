import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftVectorZeroBlock

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

section rel

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def Rel (T : V →ₗ[ℂ] V') (A : Pr V) (A' : Pr V') : Prop :=
  A'.1 ∘ₗ T = T ∘ₗ A.1 ∧ A'.2.unop ∘ₗ T = T ∘ₗ A.2.unop

variable {T : V →ₗ[ℂ] V'}

private theorem rel_iff_forall_apply {A : Pr V} {A' : Pr V'} :
    Rel T A A' ↔ ∀ v, A'.1 (T v) = T (A.1 v) ∧ A'.2.unop (T v) = T (A.2.unop v) := by
  unfold Rel
  constructor
  · intro h v
    exact ⟨LinearMap.congr_fun h.1 v, LinearMap.congr_fun h.2 v⟩
  · intro h
    exact ⟨LinearMap.ext fun v => (h v).1, LinearMap.ext fun v => (h v).2⟩

theorem rel_mk {X : Module.End ℂ V} {Xs : Module.End ℂ V} {X' Xs' : Module.End ℂ V'}
    (h1 : ∀ v, X' (T v) = T (X v)) (h2 : ∀ v, Xs' (T v) = T (Xs v)) : Rel T (mkP X Xs) (mkP X' Xs') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨h1 v, h2 v⟩

theorem rel_add {A B : Pr V} {A' B' : Pr V'} (hA : Rel T A A') (hB : Rel T B B') : Rel T (A + B) (A' + B') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show A'.1 (T v) + B'.1 (T v) = T (A.1 v + B.1 v)
    rw [map_add, (hA v).1, (hB v).1]
  · show A'.2.unop (T v) + B'.2.unop (T v) = T (A.2.unop v + B.2.unop v)
    rw [map_add, (hA v).2, (hB v).2]

theorem rel_neg {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (-A) (-A') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show -A'.1 (T v) = T (-A.1 v)
    rw [map_neg, (hA v).1]
  · show -A'.2.unop (T v) = T (-A.2.unop v)
    rw [map_neg, (hA v).2]

theorem rel_zero : Rel T (0 : Pr V) (0 : Pr V') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨(map_zero T).symm, (map_zero T).symm⟩

theorem rel_mul {A B : Pr V} {A' B' : Pr V'} (hA : Rel T A A') (hB : Rel T B B') : Rel T (A * B) (A' * B') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show A'.1 (B'.1 (T v)) = T (A.1 (B.1 v))
    rw [(hB v).1, (hA _).1]
  · show B'.2.unop (A'.2.unop (T v)) = T (B.2.unop (A.2.unop v))
    rw [(hA v).2, (hB _).2]

theorem rel_algebraMap (s : ℂ) : Rel T (algebraMap ℂ (Pr V) s) (algebraMap ℂ (Pr V') s) := by
  rw [rel_iff_forall_apply]
  intro v
  constructor
  · show (algebraMap ℂ (Module.End ℂ V') s) (T v) = T ((algebraMap ℂ (Module.End ℂ V) s) v)
    simp [Module.algebraMap_end_apply]
  · show (algebraMap ℂ (Module.End ℂ V') (conj s)) (T v) = T ((algebraMap ℂ (Module.End ℂ V) (conj s)) v)
    simp [Module.algebraMap_end_apply]

theorem rel_one : Rel T (1 : Pr V) (1 : Pr V') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨rfl, rfl⟩

theorem rel_smul (s : ℂ) {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (s • A) (s • A') := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact rel_mul (rel_algebraMap s) hA

theorem rel_star {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (star A) (star A') := by
  rw [rel_iff_forall_apply] at *
  intro v
  exact ⟨(hA v).2, (hA v).1⟩

theorem rel_sum {ι : Type*} (s : Finset ι) {A : ι → Pr V} {A' : ι → Pr V'} (h : ∀ i ∈ s, Rel T (A i) (A' i)) :
    Rel T (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rel_zero : Rel T (0 : Pr V) (0 : Pr V'))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact rel_add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

def MRel (T : V →ₗ[ℂ] V') (M : Matrix (Fin 2) (Fin 2) (Pr V)) (M' : Matrix (Fin 2) (Fin 2) (Pr V')) : Prop :=
  ∀ a b, Rel T (M a b) (M' a b)

theorem mrel_mul {M N : Matrix (Fin 2) (Fin 2) (Pr V)} {M' N' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') (hN : MRel T N N') : MRel T (M * N) (M' * N') := by
  intro a b
  simp only [Matrix.mul_apply]
  exact rel_sum _ (fun c _ => rel_mul (hM a c) (hN c b))

theorem mrel_conjTranspose {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') : MRel T Mᴴ M'ᴴ := by
  intro a b
  exact rel_star (hM b a)

theorem mrel_one : MRel T (1 : Matrix (Fin 2) (Fin 2) (Pr V)) 1 := by
  intro a b
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact rel_one
  · exact rel_zero

theorem mrel_smul (s : ℂ) {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') : MRel T (s • M) (s • M') := by
  intro a b
  exact rel_smul s (hM a b)

theorem mrel_Tm (Y : ℂ) {p c ci : Pr V} {p' c' ci' : Pr V'} (hp : Rel T p p') (hc : Rel T c c') (hci : Rel T ci ci') :
    MRel T (Formalism.YangianSpanCharacter.T.Tm Y p c ci) (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact rel_add (rel_algebraMap Y) hp
  · exact rel_neg hc
  · exact hci
  · exact rel_zero

end rel

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem t_tr {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))) (Y : ℂ) (a b : Fin 2)
    (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    Xs.t Y a b (trL ht z z' π π' Φ) = trL ht z z' π π' (X.t Y a b Φ) := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ DomR k ρ z z'
  · have hx' := (domR_iota ht z z' c g).2 hx
    rw [Xs.t_apply Y a b _ (c, g) hx, trL_apply]
    show _ = (X.t Y a b Φ).1 (consC t c) (ιLev k 1 ρ g)
    rw [X.t_apply Y a b Φ _ hx']
    exact (tL_iota (E := Wq →L[ℂ] Wp) hz hz' Y a b ((Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) (consC t c)) hx.2.1).symm
  · rw [(Xs.t Y a b (trL ht z z' π π' Φ)).2.1 (c, g) hx, trL_apply]
    exact ((X.t Y a b Φ).2.1 _ (fun h => hx ((domR_iota ht z z' c g).1 h))).symm

theorem op_tr {t : ℂ} (ht : t ≠ 0)
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))) (l : Fin ρ) (i : Fin 6)
    (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    Xs.op l i (trL ht z z' π π' Φ) = trL ht z z' π π' (X.op (shS l) i Φ) := by
  apply Subtype.ext
  rw [Xs.op_apply, trL_apply, trL_apply, X.op_apply]
  funext c g
  exact opL_consC ht (fun c' => (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) c' (ιLev k 1 ρ g)) c
    (fun h => diff_rad Φ.2 _ h) l i

end ops

section chain

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_rel {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (Wd.Ts (P5.site L (shS l)) Y) (Wd.Ts (P5.site Ls l) Y) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine mrel_Tm Y ?_ ?_ ?_
  · show Rel _ (L.p (shS l)) (Ls.p l)
    rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · show Rel _ (L.c (shS l)) (Ls.c l)
    rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · show Rel _ (L.ci (shS l)) (Ls.ci l)
    rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem tprod_rel {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (Y : ℂ) :
    ∀ m n : ℕ, ρ - n = m → MRel (trL ht z z' π π') (P5.tprod L Y (n + 1)) (P5.tprod Ls Y n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have e1 : P5.tprod L Y (n + 1) = 1 := by rw [P5.tprod, dif_neg (by omega)]
    have e2 : P5.tprod Ls Y n = 1 := by rw [P5.tprod, dif_neg (by omega)]
    rw [e1, e2]
    exact mrel_one
  | succ m ih =>
    intro n hn
    have e1 : P5.tprod L Y (n + 1) = P5.tprod L Y (n + 1 + 1) * Wd.Ts (P5.site L ⟨n + 1, by omega⟩) Y := by
      rw [P5.tprod, dif_pos (by omega)]
    have e2 : P5.tprod Ls Y n = P5.tprod Ls Y (n + 1) * Wd.Ts (P5.site Ls ⟨n, by omega⟩) Y := by
      rw [P5.tprod, dif_pos (by omega)]
    rw [e1, e2]
    refine mrel_mul (ih (n + 1) (by omega)) ?_
    have e : (⟨n + 1, by omega⟩ : Fin (1 + ρ)) = shS ⟨n, by omega⟩ := rfl
    rw [e]
    exact site_rel ht hL hLs _ Y

theorem qqi_rel {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st 1 Y) (P5.QQi Ls sts 0 Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    refine mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  have h1 : ((1 : Fin (1 + ρ + 1)) : ℕ) = 0 + 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have h0 : ((0 : Fin (ρ + 1)) : ℕ) = 0 := rfl
  rw [h1, h0]
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ 0 rfl)) hQ) (tprod_rel ht hL hLs _ _ 0 rfl)

end chain

end Formalism.FourierDecayAlt.P.PBH
