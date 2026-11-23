import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.FinRangeListSplitting

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section split

variable {k ρ : ℕ} {z z' : Fin (2 * (1 + ρ) + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem finRange_split (ρ : ℕ) :
    (List.finRange (1 + ρ)).reverse = (List.finRange ρ).reverse.map shS ++ [⟨0, by omega⟩] := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  by_cases hi : i < ρ
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_finRange, List.length_finRange]
    ext
    simp [shS]
    omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_reverse, List.getElem_finRange, List.length_finRange, List.length_map,
      List.length_reverse, List.getElem_singleton]
    ext
    simp
    omega

theorem bTall_split (L : R.LevelData (Pr (RadSp k (1 + ρ) z z' π π')) (1 + ρ)) (w : List (Wd.Letter ℂ S)) :
    P5.bTall L w = ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod * P5.bTl L ⟨0, by omega⟩ w := by
  unfold P5.bTall
  rw [finRange_split, List.map_append, List.map_map, List.prod_append]
  simp [Function.comp_def]

end split

section rel

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem arel_listProd {ι : Type} (f : ι → Wd.SlopeTestRemainingChoices S (Pr V)) (f' : ι → Wd.SlopeTestRemainingChoices S (Pr V'))
    (h : ∀ i, ARel T (f i) (f' i)) : ∀ l : List ι, ARel T (l.map f).prod (l.map f').prod
  | [] => by simp only [List.map_nil, List.prod_nil]; exact arel_one
  | a :: l => by
    simp only [List.map_cons, List.prod_cons]
    exact arel_mul (h a) (arel_listProd f f' h l)

end rel

section tr

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem bTall_tr {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (e : Wd.Ix S) :
    trL ht z z' π π' (P5.act (P5.bTall L w) x e) =
      P5.act (P5.bTall Ls w) (fun a => trL ht z z' π π' (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  have hop := fun (l : Fin ρ) (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  have hsite : ∀ l : Fin ρ, ARel (trL ht z z' π π') (P5.bTl L (shS l) w) (P5.bTl Ls l w) := by
    intro l
    refine Formalism.FourierDecayAlt.P.PBP.arel_bT ?_ ?_ ?_ w
    · show Rel _ (L.p (shS l)) (Ls.p l)
      rw [hL.1, hLs.1]
      exact rel_mk (fun v => hop l 0 v) (fun v => by simp only [LinearMap.neg_apply, hop l 3, map_neg])
    · show Rel _ (L.c (shS l)) (Ls.c l)
      rw [hL.2.2.1, hLs.2.2.1]
      exact rel_mk (fun v => hop l 1 v) (fun v => hop l 4 v)
    · show Rel _ (L.ci (shS l)) (Ls.ci l)
      rw [hL.2.2.2.1, hLs.2.2.2.1]
      exact rel_mk (fun v => hop l 2 v) (fun v => hop l 5 v)
  have hall : ARel (trL ht z z' π π') ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod
      (P5.bTall Ls w) := arel_listProd _ _ hsite _
  rw [bTall_split, Formalism.FourierDecayAlt.P5.act_mul]
  exact act_tr hall _ e

end tr

section cast

variable {k n ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem bTall_cast (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ)
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {t : ℂ} (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ g))) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k n z z' π π')
        (e : Wd.Ix S),
        T (P5.act (P5.bTall L w) x e) =
          P5.act (P5.bTall Ls w) (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun S _ _ w x e => bTall_tr ht hL hLs w x e⟩
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  rfl

end cast

section misc

theorem exists_cons {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin n → ℂ) :
    ∃ (t : ℂ) (c' : Fin ρ → ℂ), c = fun l => consC t c' (Fin.cast hn.symm l) := by
  refine ⟨c ⟨0, by omega⟩, fun i => c ⟨i.val + 1, by omega⟩, funext fun l => ?_⟩
  unfold consC
  by_cases h : l.val = 0
  · rw [dif_pos (by simpa using h)]
    exact congrArg c (Fin.ext h)
  · rw [dif_neg (by simpa using h)]
    exact congrArg c (Fin.ext (by simp; omega))

theorem omX_cons {n ρ : ℕ} (hn : 1 + ρ = n) {t : ℂ} {c : Fin ρ → ℂ}
    (h : (fun l => consC t c (Fin.cast hn.symm l)) ∈ OmX n) : t ≠ 0 ∧ c ∈ OmX ρ := by
  refine ⟨?_, fun i => ?_⟩
  · have := h ⟨0, by omega⟩
    simpa [consC] using this
  · have := h ⟨i.val + 1, by omega⟩
    simpa [consC] using this

theorem hcell_cons {n ρ : ℕ} (hn : 1 + ρ = n) (t : ℂ) (c : Fin ρ → ℂ) :
    PBI.hcell (fun l : Fin n => consC t c (Fin.cast hn.symm l)) = (1, t) :: PBI.hcell c := by
  subst hn
  refine List.ext_getElem (by simp [PBI.hcell]; omega) fun i h1 h2 => ?_
  simp only [PBI.hcell, List.getElem_ofFn]
  rcases i with _ | i
  · simp [consC]
  · simp [consC]

theorem hcell_nil {n : ℕ} (hn : n = 0) (c : Fin n → ℂ) : PBI.hcell c = [] := by
  subst hn; rfl

theorem prod_cons {n ρ : ℕ} (hn : 1 + ρ = n) (k : ℕ) (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ i : Fin n, ‖consC t c (Fin.cast hn.symm i)‖ ^ (2 * (n - (i : ℕ)) + k)) =
      ‖t‖ ^ (2 * n + k) * ∏ i : Fin ρ, ‖c i‖ ^ (2 * (ρ - (i : ℕ)) + k) := by
  subst hn
  rw [← (finCongr (Nat.add_comm ρ 1)).prod_comp, Fin.prod_univ_succ]
  congr 1
  simp only [consC, finCongr_apply, Fin.val_cast, Fin.val_succ]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  omega

theorem iota_split {k n ρ m : ℕ} (hn : 1 + ρ = n) (hm : m = 0) (e1 : n + m = n) (e2 : ρ + m = ρ)
    (g : B.Mat k m) :
    D.castM e1 (ιLev k n m g) = D.castM hn (ιLev k 1 ρ (D.castM e2 (ιLev k ρ m g))) := by
  subst hn hm
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  exact (ιLev_comp g).symm

theorem castM_iota_self {k a : ℕ} (ha : a = 0) (e : a + a = a) (g : B.Mat k a) : D.castM e (ιLev k a a g) = g := by
  subst ha
  exact Formalism.FourierDecayAlt.P.Dx2.Tower.castMat_levelEmbed_zero e g

theorem resG_empty {k a : ℕ} (ha : a = 0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Mx k a → E)
    (c : Fin a → ℂ) (g : Mx k a) : resG k a (Fin.last a) J c g = J g := by
  subst ha
  simp [resG, wCell]

theorem ptSize_append (h h' : C.LPt) : D.ptSize (h ++ h') = D.ptSize h + D.ptSize h' := by
  simp [D.ptSize]

end misc

end Formalism.FourierDecayAlt.P.FinRangeListSplitting
