import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.MixedDiscriminantZeroSlot

theorem mdisc_eq_zero_of_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D) (hk : A k = 0) :
    mdisc A = 0 := by
  have h := ReciprocityTheory.AnForm.A.mdisc_update_smul A k 0 0
  rw [zero_smul, ← hk, Function.update_eq_self, zero_mul] at h
  exact h

theorem hessC_zero {D : ℕ} (z : Fin D → ℂ) : hessC (fun _ : Fin D → ℂ => (0 : ℝ)) z = 0 := by
  funext i j
  simp [hessC]

theorem mInt_eq_zero {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : Fin e → LocPot X) (g : X → ℝ) (hP : ∀ i, IsPotential A (P i)) (i₀ : Fin e)
    (h₀ : LeviEq A (P i₀) (LocPot.ofFun fun _ => 0)) : mInt A P g = 0 := by
  set Q : Fin e → LocPot X := Function.update P i₀ (LocPot.ofFun fun _ => 0) with hQ
  have hpot0 : IsPotential A (LocPot.ofFun fun _ : X => (0 : ℝ)) :=
    isPotential_ofFun A _ (fun j => contDiffOn_const)
  have hQp : ∀ i, IsPotential A (Q i) := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simpa [hQ] using hpot0
    · simpa [hQ, Function.update_of_ne hi] using hP i
  have hL : ∀ i, LeviEq A (P i) (Q i) := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simpa [hQ] using h₀
    · simp only [hQ, Function.update_of_ne hi]
      exact fun _ _ _ _ => rfl
  rw [(GlobalTheory.LeviOnly.mInt_eq_of_leviEq e X A P Q g hP hQp hL).1]
  have hd : ∀ j y, locDens A Q j y = 0 := by
    intro j y
    unfold locDens maDens
    rw [mdisc_eq_zero_of_eq_zero _ i₀ (by simp [hQ, LocPot.ofFun, hessC_zero])]
    simp
  unfold mInt integralWith
  split_ifs
  · simp [hd]
  · rfl

theorem int_eq_zero {e : ℕ} (M : Man e) (P : Fin e → M.Pot) (u : M.Fun) (hP : ∀ i σ, IsPotential (M.A σ) (P i σ))
    (i₀ : Fin e) (h₀ : ∀ σ, LeviEq (M.A σ) (P i₀ σ) (LocPot.ofFun fun _ => 0)) : M.int P u = 0 := by
  unfold Man.int
  rw [Finset.sum_eq_zero fun σ _ => mInt_eq_zero (M.A σ) (fun i => P i σ) (u σ) (fun i => hP i σ) i₀ (h₀ σ),
    mul_zero]

theorem num_cons_eq_zero {e : ℕ} {M : Man e} (K : Calc M) (x : K.V) (f : M.Fun) (hf : M.Smooth f)
    (hx : ∀ σ, LeviEq (M.A σ) (K.c1 x σ) (LocPot.ofFun fun _ => 0)) (u : Fin e → K.V) (i : Fin e)
    (hi : u i = K.ar f) : K.num (Fin.cons x u) = 0 := by
  set v : Fin (e + 1) → K.V := (Fin.cons x u : Fin (e + 1) → K.V) ∘ Equiv.swap 0 i.succ with hv
  have h1 : K.num (Fin.cons x u) = K.num v := (K.symm _ _).symm
  have h0 : v 0 = K.ar f := by simp [hv, hi]
  have ht : Fin.tail v i = x := by simp [hv, Fin.tail]
  rw [h1, ← Fin.cons_self_tail v, h0, K.num_ar f hf]
  exact int_eq_zero M _ f (fun j σ => K.firstChern_isPotential _ σ) i fun σ => by rw [ht]; exact hx σ

theorem num_add_ar {e : ℕ} (M : Man e) (K : Calc M) (x w : K.V) (f : M.Fun) (hf : M.Smooth f)
    (hx : ∀ σ, LeviEq (M.A σ) (K.c1 x σ) (LocPot.ofFun fun _ => 0)) :
    K.num (Fin.cons x fun _ => w + K.ar f) = K.num (Fin.cons x fun _ => w) := by
  have key : ∀ u : Fin e → K.V, K.num (Fin.cons x u) = K.num.curryLeft x u := fun u =>
    (MultilinearMap.curryLeft_apply _ _ _).symm
  have hsum : (fun _ : Fin e => w + K.ar f) = (fun _ => w) + (fun _ => K.ar f) := rfl
  rw [key, key, hsum, MultilinearMap.map_add_univ, Finset.sum_eq_single Finset.univ]
  · rw [Finset.piecewise_univ]
  · intro s _ hs
    obtain ⟨i, hi⟩ : ∃ i, i ∉ s := by
      by_contra hne
      push_neg at hne
      exact hs (Finset.eq_univ_iff_forall.2 hne)
    rw [← key]
    exact num_cons_eq_zero K x f hf hx _ i (by simp [Finset.piecewise_eq_of_notMem _ _ _ hi])
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.MixedDiscriminantZeroSlot
