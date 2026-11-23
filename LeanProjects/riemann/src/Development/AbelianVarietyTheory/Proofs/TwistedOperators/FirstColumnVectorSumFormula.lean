import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShift0Model
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowVertexWeilValueStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowDatum

private theorem prod_apply_update_eq_mul_prod_erase {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (F : ∀ i, X i → ℂ) (x : ∀ i, X i) (j : ι) (y : X j) :
    ∏ i, F i (Function.update x j y i) = F j y * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private theorem sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (s : Finset ι) :
    ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert j s hj ih =>
    intro x

    have hg : (∑ d ∈ S, (c d * ∏ i ∈ Finset.univ.erase j,
        (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i)) • Φ d j) = 0 := by
      funext y
      rw [Finset.sum_apply, Pi.zero_apply, ← ih (Function.update x j y)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [prod_apply_update_eq_mul_prod_erase (fun i => if i ∈ s then Tm i (Φ d i) else Φ d i) x j y]
      simp only [Pi.smul_apply, smul_eq_mul, if_neg hj]
      ring

    have hT := congrArg (fun g => Tm j g (x j)) hg
    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hT
    rw [← hT]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have h2 : ∏ i ∈ Finset.univ.erase j, (if i ∈ insert j s then Tm i (Φ d i) else Φ d i) (x i) =
        ∏ i ∈ Finset.univ.erase j, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [Finset.mem_insert, hij, false_or]
    rw [h2, if_pos (Finset.mem_insert_self j s)]
    ring

theorem sum_prod_map_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (x : ∀ i, X i) :
    ∑ d ∈ S, c d * ∏ i, Tm i (Φ d i) (x i) = 0 := by
  have := sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero Tm S c Φ h Finset.univ x
  simpa using this

theorem sum_prod_map_eq_zero₂ {κ : Type} {m : ℕ} {X Y : Fin m → Type} (TX : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ))
    (TY : ∀ i, (Y i → ℂ) →ₗ[ℂ] (Y i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ j, X j → ℂ) (Ψ : κ → ∀ i, Y i → ℂ)
    (h : ∀ (x : ∀ j, X j) (y : ∀ i, Y i), ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ d i (y i) = 0)
    (x : ∀ j, X j) (y : ∀ i, Y i) :
    ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) = 0 := by

  have hx : ∀ (y : ∀ i, Y i) (x : ∀ j, X j),
      ∑ d ∈ S, (c d * ∏ i, Ψ d i (y i)) * ∏ j, TX j (Φ d j) (x j) = 0 := by
    intro y
    refine sum_prod_map_eq_zero TX S (fun d => c d * ∏ i, Ψ d i (y i)) Φ (fun x => ?_)
    rw [← h x y]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

  have hy := sum_prod_map_eq_zero TY S (fun d => c d * ∏ j, TX j (Φ d j) (x j)) Ψ (fun y' => by
    rw [← hx y' x]
    exact Finset.sum_congr rfl fun d _ => by ring) y
  rw [← hy]

private theorem mul_sum_prod_map_eq_of_sum_prod_eq {κ : Type} {m : ℕ} {X Y : Fin m → Type} (TX : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ))
    (TY : ∀ i, (Y i → ℂ) →ₗ[ℂ] (Y i → ℂ)) (S : Finset κ) (c : κ → ℂ) (u : ℂ) (Φ : κ → ∀ j, X j → ℂ)
    (Ψ Ψ' : κ → ∀ i, Y i → ℂ)
    (h : ∀ (x : ∀ j, X j) (y : ∀ i, Y i), u * ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ d i (y i) =
      ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ' d i (y i))
    (x : ∀ j, X j) (y : ∀ i, Y i) :
    u * ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) =
      ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ' d i) (y i) := by

  have key := sum_prod_map_eq_zero₂ TX TY (S.disjSum S) (Sum.elim (fun d => u * c d) fun d => -c d)
    (Sum.elim Φ Φ) (Sum.elim Ψ Ψ') (fun x' y' => by
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have e1 : ∑ d ∈ S, u * c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ d i (y' i) =
          u * ∑ d ∈ S, c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ d i (y' i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
      have e2 : ∑ d ∈ S, -c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ' d i (y' i) =
          -∑ d ∈ S, c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ' d i (y' i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun d _ => by ring
      rw [e1, e2, h x' y', add_neg_cancel]) x y
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr] at key
  have e1 : ∑ d ∈ S, u * c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) =
      u * ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have e2 : ∑ d ∈ S, -c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ' d i) (y i) =
      -∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ' d i) (y i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [e1, e2, add_neg_eq_zero] at key
  exact key

private theorem apply_update_eq_update_apply {ι : Type} [DecidableEq ι] {X : ι → Type} (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ))
    (F : ∀ i, X i → ℂ) (i₀ : ι) (g : X i₀ → ℂ) (i : ι) :
    Tm i (Function.update F i₀ g i) = Function.update (fun i => Tm i (F i)) i₀ (Tm i₀ g) i := by
  by_cases h : i = i₀
  · subst h
    simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

set_option maxHeartbeats 2000000 in
private theorem vec_law_lemma_5 {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) {t : T} (ht : t ∈ U) {Φ : G.Datum} {β : CosFam G t}
    {τ : PureDat G t →₀ ℂ} (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (k : FinPt G (.grid 0 D.R.m)) (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) (s : ℂ)
    (hlaw : ∀ c : ℂ, W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)
        (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      ∀ (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
        (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
        s * c * (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
        τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i))
    (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    s * (τ.sum fun d c => c * (∏ j, S.Z.vec (d.1 j) (xs j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
        (GlobalTheory.FirstRowVertex.rowShift0 S k (S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, S.Z.vec (d.1 j) (xs j)) * ∏ i, S.Z.vec (d.2 i) (ys i) := by
  obtain ⟨e, he, hsup, -⟩ := id hτ
  obtain ⟨c, hc, hmod⟩ := GlobalTheory.FirstRowShift.rowShift0_model S hL ht he k hk
  rcases τ.support.eq_empty_or_nonempty with hne | ⟨d₀, hd₀⟩
  · simp only [Finsupp.sum, hne, Finset.sum_empty, mul_zero]

  have hTXe : ∀ j : Fin D.R.m, ∃ Tm : (WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (GlobalTheory.LastVertexMove.stdLat S (.top t j)) 1 (S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, ⟨Tm, hTm⟩, -⟩ := (hv d₀ hd₀).1 j
    rw [((hsup d₀ hd₀).1 j).2.1] at hTm
    exact ⟨Tm, hTm⟩
  have hTYe : ∀ i : Fin D.R.m, ∃ Tm : (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (GlobalTheory.LastVertexMove.stdLat S (.chi i D.R.m)) 1 (S.Z.vac (.chi i D.R.m)) Tm := by
    intro i
    obtain ⟨f, ⟨Tm, hTm⟩, -⟩ := (hv d₀ hd₀).2 i
    rw [((hsup d₀ hd₀).2 i).2.1] at hTm
    exact ⟨Tm, hTm⟩
  choose TX hTX using hTXe
  choose TY hTY using hTYe

  have hvx : ∀ d ∈ τ.support, ∀ j, S.Z.vec (d.1 j) = TX j (d.1 j).fn := fun d hd j =>
    GlobalTheory.LastVertexTensor.vec_eq_model S (d.1 j) ((hv d hd).1 j) ((hsup d hd).1 j).2.2 (TX j)
      (by rw [((hsup d hd).1 j).2.1]; exact hTX j)
  have hvy : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = TY i (d.2 i).fn := fun d hd i =>
    GlobalTheory.LastVertexTensor.vec_eq_model S (d.2 i) ((hv d hd).2 i) ((hsup d hd).2 i).2.2 (TY i)
      (by rw [((hsup d hd).2 i).2.1]; exact hTY i)

  have key := mul_sum_prod_map_eq_of_sum_prod_eq TX TY τ.support (fun d => τ d) (s * c) (fun d j => (d.1 j).fn)
    (fun d => Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
      (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)))
    (fun d i => (d.2 i).fn) (fun x y => hlaw c hc x y) xs ys

  have hL' : ∀ d ∈ τ.support, τ d * (∏ j, S.Z.vec (d.1 j) (xs j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
        (GlobalTheory.FirstRowVertex.rowShift0 S k (S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i) =
      c * (τ d * (∏ j, TX j (d.1 j).fn (xs j)) * ∏ i, TY i (Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
      (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i) (ys i)) := by
    intro d hd
    have hsb : IsSBHalf e (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (G.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True)
        (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn := by
      have h0 := (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).sb
      rw [((hsup d hd).2 (GlobalTheory.FirstRowVertex.firstIx D)).2.1] at h0
      exact h0
    rw [hvy d hd (GlobalTheory.FirstRowVertex.firstIx D), hmod (TY _) (hTY _) _ hsb]
    simp only [hvx d hd, hvy d hd]
    rw [GlobalTheory.FirstRowVertex.prod_update_smul]
    simp only [apply_update_eq_update_apply]
    ring
  have hR' : ∀ d ∈ τ.support, τ d * (∏ j, S.Z.vec (d.1 j) (xs j)) * ∏ i, S.Z.vec (d.2 i) (ys i) =
      τ d * (∏ j, TX j (d.1 j).fn (xs j)) * ∏ i, TY i (d.2 i).fn (ys i) := by
    intro d hd
    simp only [hvx d hd, hvy d hd]
  unfold Finsupp.sum
  rw [Finset.sum_congr rfl hL', Finset.sum_congr rfl hR', ← Finset.mul_sum, ← mul_assoc]
  exact key

theorem main_law : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  intro hP hS
  obtain ⟨CF0, hB⟩ := GlobalTheory.T.first_row_vertex_weil_value hP hS
  obtain ⟨CF1, hO⟩ := hS
  refine ⟨max CF0 CF1, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hB ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x₁, hx1⟩ := hO ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x₀ x₁, ?_⟩
  intro D large₂ hε hxs Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc
  have H := hx D large₂ hε (le_trans (le_max_left _ _) hxs) Γ Pl0 T A Ks R F hSet ch hch hsc
  have HO := hx1 D large₂ hε (le_trans (le_max_right _ _) hxs) Γ Pl0 T A Ks R F hSet ch hch hsc
  intro t a β hβ τ hτ k hk hkχ xs ys
  exact vec_law_lemma_5 ch.S.toGridChoice hSet.core.lev (Set.mem_univ t) hτ ((HO t a).vec β τ hτ) k hk _
    (fun c hc => H t a β hβ τ hτ k hk hkχ c hc) xs ys

end GlobalTheory.FirstRowDatum

end
