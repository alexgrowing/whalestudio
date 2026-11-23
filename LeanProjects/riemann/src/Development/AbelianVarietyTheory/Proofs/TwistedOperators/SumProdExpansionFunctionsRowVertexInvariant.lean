import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermDatumRowMoveLevelEdgeFactorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumScalarsEqProductEdgeFactorsRowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) :=
  Function.update (Function.update z (.inr ⟨j, by omega⟩)
    (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
      (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
    (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
      WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))

theorem movPt_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j + 1, hj⟩) = actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :=
  Function.update_self _ _ _

theorem movPt_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j, by omega⟩) = actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 (z (.inr ⟨j, by omega⟩)) :=
  (Function.update_of_ne (by simp) _ _).trans (Function.update_self _ _ _)

theorem movPt_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movPt S j hj k z a = z a :=
  (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)

theorem movFn_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j + 1, hj⟩) x = v (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) := by
  unfold movFn; rw [Function.update_self]

theorem movFn_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j, by omega⟩) x = v (.inr ⟨j, by omega⟩) (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) := by
  unfold movFn; rw [Function.update_of_ne (by simp), Function.update_self]

theorem movFn_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movFn S j hj k v a = v a := by
  unfold movFn; rw [Function.update_of_ne h2, Function.update_of_ne h1]

theorem scale_movFn_apply (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (a : Fin D.R.m ⊕ Fin D.R.m) :
    (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) =
      ((Pi.mulSingle (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) c₁ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a *
        (Pi.mulSingle (.inr ⟨j + 1, hj⟩ : Fin D.R.m ⊕ Fin D.R.m) c₂ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a) *
        v a (movPt S j hj k z a) := by
  have hne : (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨j + 1, hj⟩ := by simp
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    have e1 : movFn S j hj k v (.inr ⟨j + 1, hj⟩) (z (.inr ⟨j + 1, hj⟩)) =
        v (.inr ⟨j + 1, hj⟩) (movPt S j hj k z (.inr ⟨j + 1, hj⟩)) :=
      (movFn_two S j hj k v (z (.inr ⟨j + 1, hj⟩))).trans (congrArg (v _) (movPt_two S j hj k z).symm)
    rw [Pi.smul_apply, smul_eq_mul, e1]
    simp [scaleAt, Pi.mulSingle_apply, hne.symm]
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      have e1 : movFn S j hj k v (.inr ⟨j, by omega⟩) (z (.inr ⟨j, by omega⟩)) =
          v (.inr ⟨j, by omega⟩) (movPt S j hj k z (.inr ⟨j, by omega⟩)) :=
        (movFn_one S j hj k v (z (.inr ⟨j, by omega⟩))).trans (congrArg (v _) (movPt_one S j hj k z).symm)
      rw [Pi.smul_apply, smul_eq_mul, e1]
      simp [scaleAt, Pi.mulSingle_apply, hne, Function.update_of_ne hne]
    · rw [Pi.smul_apply, smul_eq_mul, movFn_other S j hj k v a h1' h2', movPt_other S j hj k z a h1' h2']
      simp [scaleAt, Pi.mulSingle_apply, h1', h2', Function.update_of_ne h1', Function.update_of_ne h2']

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem prod_scale_movFn (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) = c₁ * c₂ * ∏ a, v a (movPt S j hj k z a) := by
  rw [Finset.prod_congr rfl fun a _ => scale_movFn_apply S j hj k c₁ c₂ v z a, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle']

theorem isHalf_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (e : AE D) (a : Fin D.R.m ⊕ Fin D.R.m) :
    IsHalf e (movPt S j hj k z a) ↔ IsHalf e (z a) := by
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    rw [movPt_two]
    exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      rw [movPt_one]
      exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · rw [movPt_other S j hj k z a h1' h2']

theorem sum_fn_eq_zero {t : T} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hsupp : ∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (ha : ¬ IsHalf e (z a)) : (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) = 0 := by
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun d hd => ?_
  beta_reduce
  rw [Finset.prod_eq_zero (Finset.mem_univ a), mul_zero]
  rcases a with j | i
  · by_contra hne
    have h := (d.1 j).sb.1 _ hne
    rw [((hsupp d hd).1 j).2.1] at h
    exact ha h
  · by_contra hne
    have h := (d.2 i).sb.1 _ hne
    rw [((hsupp d hd).2 i).2.1] at h
    exact ha h

theorem sum_fn_of_half (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hexp : ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (x j)) →
      (∀ i, IsHalf e (y i)) → (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) =
        ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (h : ∀ a, IsHalf e (z a)) :
    (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w fun j => z (.inl j)) (S.rowAt t w fun i => z (.inr i)) := by
  rw [← hexp (fun j => z (.inl j)) (fun i => z (.inr i)) (fun j => h _) (fun i => h _)]
  refine Finsupp.sum_congr fun d _ => ?_
  rw [Fintype.prod_sum_type, mul_assoc]
  rfl

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inl_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inl i)) = fun i => z (.inl i) :=
  funext fun i => movPt_other S j hj k z _ (by simp) (by simp)

theorem inr_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inr i)) = Function.update (Function.update (fun i => z (.inr i)) ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) := by
  funext i
  let B : Fin D.R.m → Type := fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := by simp
  by_cases h2' : i = ⟨j + 1, hj⟩
  · subst h2'
    exact (movPt_two S j hj k z).trans (Function.update_self (β := B) (⟨j + 1, hj⟩ : Fin D.R.m) _ _).symm
  · by_cases h1' : i = ⟨j, by omega⟩
    · subst h1'
      exact (movPt_one S j hj k z).trans ((Function.update_of_ne (β := B) hne _ _).trans (Function.update_self (β := B) _ _ _)).symm
    · refine (movPt_other S j hj k z _ (fun h => h1' (Sum.inr_injective h)) (fun h => h2' (Sum.inr_injective h))).trans ?_
      symm
      refine (Function.update_of_ne (β := B) (a := i) h2' _ _).trans ?_
      exact Function.update_of_ne (β := B) (a := i) h1' _ _

theorem local_prod (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T} (hμ : L.Is μ₀)
    (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hU : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.grid (j + 1) D.R.m)) (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (c₁ c₂ : ℂ)
    (h1 : W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m))
    (h2 : W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m))
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    c₁ * c₂ * ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))))) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) := by
  have hκ : ∀ w : locPl G t, inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ givenLevel G t w.1 (j + 1, D.R.m) := fun w =>
    Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w
  rw [GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row S hμ hU j hj k hk c₁ c₂ h1 h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [GlobalTheory.RowMoveAt.rowAt_move S hU j hj k w.1 w.2 y]
  exact GlobalTheory.T.termDatum_rowMove_level_edgeFactors S β hμ hq hc hU w j hj _ (hκ w) _ _

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv

theorem sum_prod_scale_movFn_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hc hU hβ hE hv j hj k hk c₁ c₂ h1 h2 z
  obtain ⟨e, -, hsupp, hexp⟩ := hE
  have hL : (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) =
      c₁ * c₂ * τ.sum fun d c => c * ∏ a, fnOf d a (movPt S j hj k z a) := by
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [prod_scale_movFn]
    ring
  rw [hL]
  by_cases hall : ∀ a, IsHalf e (z a)
  · rw [sum_fn_of_half S τ e hexp z hall,
      sum_fn_of_half S τ e hexp _ fun a => (isHalf_movPt S j hj k z e a).2 (hall a), inl_movPt, inr_movPt]
    exact local_prod S β hμ hq hc hU j hj k hk c₁ c₂ h1 h2 (fun i => z (.inl i)) (fun i => z (.inr i))
  · push_neg at hall
    obtain ⟨a, ha⟩ := hall
    rw [sum_fn_eq_zero τ e hsupp z a ha,
      sum_fn_eq_zero τ e hsupp _ a (fun h => ha ((isHalf_movPt S j hj k z e a).1 h)), mul_zero]

end GlobalTheory.RowVertexInv
