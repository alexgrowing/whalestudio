import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section comp

variable {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V'']
  [Module ℂ V''] {T : V →ₗ[ℂ] V'} {T' : V' →ₗ[ℂ] V''}

theorem rel_comp {A : Pr V} {A' : Pr V'} {A'' : Pr V''} (h : Rel T A A') (h' : Rel T' A' A'') :
    Rel (T' ∘ₗ T) A A'' := by
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have h1 := LinearMap.congr_fun h.1 v
    have h2 := LinearMap.congr_fun h'.1 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]
  · have h1 := LinearMap.congr_fun h.2 v
    have h2 := LinearMap.congr_fun h'.2 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]

theorem mrel_comp {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    {M'' : Matrix (Fin 2) (Fin 2) (Pr V'')} (h : MRel T M M') (h' : MRel T' M' M'') : MRel (T' ∘ₗ T) M M'' :=
  fun a b => rel_comp (h a b) (h' a b)

variable {S : Type} [Fintype S] [DecidableEq S]

end comp

section bT

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem mrel_Ts {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) (Y : ℂ) : MRel T (Wd.Ts σ Y) (Wd.Ts σ' Y) := by
  unfold Wd.Ts; exact mrel_Tm Y hp hc hci

theorem arel_bT {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) : ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.bT σ w) (Wd.bT σ' w)
  | [] => by unfold Wd.bT; exact arel_one
  | l :: w => by
    unfold Wd.bT Wd.vlet
    refine arel_mul (arel_ins _ (brel_lift0 ?_)) (arel_bT hp hc hci w)
    split_ifs
    · exact mrel_Ts hp hc hci _
    · intro a b
      rw [Matrix.map_apply, Matrix.map_apply]
      exact rel_star (mrel_Ts hp hc hci _ a b)

end bT

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_ops {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) :
    Rel (trL ht z z' π π') (L.p (shS l)) (Ls.p l) ∧ Rel (trL ht z z' π π') (L.c (shS l)) (Ls.c l) ∧
      Rel (trL ht z z' π π') (L.ci (shS l)) (Ls.ci l) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine ⟨?_, ?_, ?_⟩
  · rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem qqi_rel_n {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (n : ℕ) (hn : n ≤ ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st ⟨n + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨n, by omega⟩ Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    exact mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ n rfl)) hQ) (tprod_rel ht hL hLs _ _ n rfl)

end one

end Formalism.FourierDecayAlt.P.PTieB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

end Formalism.FourierDecayAlt.P
