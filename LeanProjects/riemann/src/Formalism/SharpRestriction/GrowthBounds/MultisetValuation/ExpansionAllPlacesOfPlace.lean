import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser eq_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Rename₂

variable {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ)

theorem th_ren_eq (f : MvPowerSeries κ R) : ren φ f = MvPowerSeries.substAlgHom (th_ren_hasSubst (R := R) φ) f := by
  unfold ren
  rw [MvPowerSeries.coe_substAlgHom]

theorem th_ren_sum {α : Type} (s : Finset α) (f : α → MvPowerSeries κ R) :
    ren φ (∑ a ∈ s, f a) = ∑ a ∈ s, ren φ (f a) := by
  simp only [th_ren_eq φ, map_sum]

theorem th_ren_mul (f g : MvPowerSeries κ R) : ren φ (f * g) = ren φ f * ren φ g := by
  simp only [th_ren_eq φ, map_mul]

theorem th_ren_neg (f : MvPowerSeries κ R) : ren φ (-f) = -ren φ f := by
  simp only [th_ren_eq φ, map_neg]

theorem th_ren_pow (f : MvPowerSeries κ R) (n : ℕ) : ren φ (f ^ n) = ren φ f ^ n := by
  simp only [th_ren_eq φ, map_pow]

theorem th_ren_C (r : R) : ren φ (MvPowerSeries.C r : MvPowerSeries κ R) = MvPowerSeries.C r := by
  first
  | (unfold ren; exact MvPowerSeries.subst_C (th_ren_hasSubst φ) r)
  | (rw [th_ren_eq φ]; exact (MvPowerSeries.substAlgHom (th_ren_hasSubst (R := R) φ)).commutes r)

theorem th_ren_X (k : κ) : ren φ (MvPowerSeries.X k : MvPowerSeries κ R) = MvPowerSeries.X (φ k) := by
  unfold ren
  exact MvPowerSeries.subst_X (th_ren_hasSubst φ) k

theorem th_subst_ren {τ : Type} {T : σ → MvPowerSeries τ R} (hT : MvPowerSeries.HasSubst T) (f : MvPowerSeries κ R) :
    MvPowerSeries.subst T (ren φ f) = MvPowerSeries.subst (fun k => T (φ k)) f := by
  unfold ren
  rw [MvPowerSeries.subst_comp_subst_apply (th_ren_hasSubst φ) hT f]
  congr 1
  funext k
  exact MvPowerSeries.subst_X hT (φ k)

theorem th_ren_subst {ρ : Type} {t : ρ → MvPowerSeries κ R} (ht : MvPowerSeries.HasSubst t) (f : MvPowerSeries ρ R) :
    ren φ (MvPowerSeries.subst t f) = MvPowerSeries.subst (fun x => ren φ (t x)) f := by
  unfold ren
  exact MvPowerSeries.subst_comp_subst_apply ht (th_ren_hasSubst φ) f

theorem th_ren_psubst {L : MvPowerSeries κ R} (hL : MvPowerSeries.constantCoeff L = 0) (f : PowerSeries R) :
    ren φ (PowerSeries.subst L f) = PowerSeries.subst (ren φ L) f := by
  have hL' := (PowerSeries.HasSubst.of_constantCoeff_zero hL).const
  exact th_ren_subst φ hL' f

theorem th_ren_ren {ρ : Type} [Finite σ] (ψ : σ → ρ) (f : MvPowerSeries κ R) :
    ren ψ (ren φ f) = ren (fun k => ψ (φ k)) f := th_subst_ren φ (th_ren_hasSubst ψ) f

theorem th_map_ren {S : Type} [CommRing S] (h : R →+* S) (f : MvPowerSeries κ R) :
    MvPowerSeries.map h (ren φ f) = ren φ (MvPowerSeries.map h f) := by
  unfold ren
  rw [MvPowerSeries.map_subst (th_ren_hasSubst φ)]
  congr 1
  funext k
  simp

end Rename₂

section RenField

variable {κ σ K : Type} [Finite κ] [Field K] (φ : κ → σ)

theorem th_ren_expK {f : MvPowerSeries κ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    ren φ (expK f) = expK (ren φ f) :=
  th_subst_expK _ (fun _ => MvPowerSeries.constantCoeff_X _) hf

theorem th_IntR_ren {R : Subring K} {f : MvPowerSeries κ K} (hf : IntR R f) : IntR R (ren φ f) :=
  IntR_subst _ (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => IntR_X _) hf

theorem th_expK_sum [CharZero K] {ι α : Type} (s : Finset α) (a : α → MvPowerSeries ι K)
    (h : ∀ v ∈ s, MvPowerSeries.constantCoeff (a v) = 0) : expK (∑ v ∈ s, a v) = ∏ v ∈ s, expK (a v) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, th_expK_zero]
  | insert v s hv ih =>
    rw [Finset.sum_insert hv, Finset.prod_insert hv,
      expK_add (h v (Finset.mem_insert_self _ _))
        (by rw [map_sum]; exact Finset.sum_eq_zero fun v' hv' => h v' (Finset.mem_insert_of_mem hv')),
      ih fun v' hv' => h v' (Finset.mem_insert_of_mem hv')]

def altS (p : ℕ) {ι : Type} [DecidableEq ι] (x : ℕ → ι) : MvPowerSeries ι K :=
  fun n => ∑ l ∈ range (n.degree + 1), if n = Finsupp.single (x l) (p ^ (2 * l)) then (-1) ^ l else 0

def altPart (p : ℕ) {ι : Type} (x : ℕ → ι) (M : ℕ) : MvPowerSeries ι K :=
  ∑ l ∈ range M, MvPowerSeries.C ((-1 : K) ^ l) * MvPowerSeries.X (x l) ^ (p ^ (2 * l))

theorem th_low_alt {p : ℕ} (hp : 2 ≤ p) {ι : Type} [DecidableEq ι] (x : ℕ → ι) (M : ℕ) :
    Low M (altS (K := K) p x - altPart p x M) := by
  intro d hd
  rw [map_sub, sub_eq_zero]
  show (∑ l ∈ range (d.degree + 1), if d = Finsupp.single (x l) (p ^ (2 * l)) then ((-1 : K) ^ l) else 0) = _
  unfold altPart
  rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l _ hl => if_neg fun h => ?_
  have h1 : d.degree = p ^ (2 * l) := by rw [h, Finsupp.degree_single]
  have h2 : l < (p ^ 2) ^ l := Nat.lt_pow_self (by nlinarith)
  rw [← pow_mul] at h2
  simp only [mem_range] at hl
  omega

theorem th_ren_altS [DecidableEq κ] [DecidableEq σ] {p : ℕ} (hp : 2 ≤ p) (x : ℕ → κ) :
    ren φ (altS (K := K) p x) = altS p (fun l => φ (x l)) := by
  refine eq_of_low fun M => ?_
  have e : ren φ (altS (K := K) p x) - altS p (fun l => φ (x l)) =
      ren φ (altS (K := K) p x - altPart p x M) - (altS p (fun l => φ (x l)) - altPart p (fun l => φ (x l)) M) := by
    have : ren φ (altPart (K := K) p x M) = altPart p (fun l => φ (x l)) M := by
      unfold altPart
      simp only [th_ren_sum, th_ren_mul, th_ren_C, th_ren_pow, th_ren_X]
    rw [th_ren_sub, this]
    ring
  rw [e]
  exact low_sub (Formalism.DworkPowerSeriesWeights.low_subst_of_low (fun _ => MvPowerSeries.constantCoeff_X _) (th_low_alt hp x M))
    (th_low_alt hp _ M)

end RenField

section Places

variable {p : ℕ} [hp : Fact p.Prime]

theorem th_Gt_sigma {Pl : Type} [Fintype Pl] (E : Pl → Type) [∀ v, Fintype (E v)] (c c' : K0 p) :
    Gt p (Σ v, E v) c c' = ∑ v, ren (Sum.map (Sigma.mk v) (Sigma.mk v)) (Gt p (E v) c c') := by
  unfold Gt
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [th_ren_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [th_ren_ren]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem th_Gt_const (E : Type) [Fintype E] (c c' : K0 p) : MvPowerSeries.constantCoeff (Gt p E c c') = 0 := by
  unfold Gt
  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => th_ren_const _ (th_Gser_const c c')

variable (X : Sys p)

theorem th_hhA_eq (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (u : Fin (X.G.P.n' v) → K') :
    X.hhA K' j v u = ren (fun z => (⟨v, z⟩ : X.ZA j)) (hhS p K' u) := by
  have hs : ∀ (e : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j)) (b : Fin (NN X.G.P.m X.t (j + 1))),
      ren (fun z => (⟨v, z⟩ : X.ZA j)) (sSer p K' e a b) = X.sSA K' j v e a b := fun e a b =>
    th_ren_altS (K := K') (fun z => (⟨v, z⟩ : X.ZA j)) hp.out.two_le (fun l => (posSub e (2 * l), a, b))
  unfold Sys.hhA hhS
  simp only [th_ren_sum, th_ren_mul, th_ren_C, th_ren_pow, hs]

theorem th_coordZA_eq (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (v : X.Pl)
    (x : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕
      Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) :
    X.coordZA K' j (Sum.map (Sigma.mk v) (Sigma.mk v) x) =
      ren (fun z => (⟨v, z⟩ : X.ZA j)) (coordZ (X.om v) K' 1 x) := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
  · simp only [Sum.map_inl, Sum.map_inr, Sys.coordZA, coordZ, th_ren_sum, th_ren_mul, th_ren_C, th_ren_X, one_mul]

theorem restGcA_of (hG : RestGc p) : RestGcA X := by
  intro c hc j K' _ _ vp hvp μ h0 h1
  have hcz := charZero_K' p K'
  choose u hu V hV hEq using fun v : X.Pl => hG (X.std v).five_le c hc (X.G.P.n' v) (NN X.G.P.m X.t j)
    (NN X.G.P.m X.t (j + 1)) (X.std v).two_le (X.std v).even (X.om v) K' vp hvp μ h0 h1
  refine ⟨u, hu, ∏ v, ren (fun z => (⟨v, z⟩ : X.ZA j)) (V v),
    IntR_prod _ _ fun v _ => th_IntR_ren _ (hV v), ?_⟩
  have hT0 := th_tOf_const vp μ h0 (X.coordZA K' j) (coordZA_const X K' j)
  have hT := MvPowerSeries.hasSubst_of_constantCoeff_zero hT0
  have hmG : ∀ v : X.Pl, MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap (K0 p) K')
      (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (wK p c) (wK p (sigW p c)))) = 0 := by
    intro v
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, th_Gt_const, map_zero]
  have e1 : expK (-(MvPowerSeries.map (algebraMap (K0 p) K') (Gt p (X.EA j) (wK p c) (wK p (sigW p c))))) =
      ∏ v : X.Pl, ren (Sum.map (Sigma.mk v) (Sigma.mk v)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
        (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (wK p c) (wK p (sigW p c)))))) := by
    rw [th_Gt_sigma, map_sum, ← Finset.sum_neg_distrib, th_expK_sum]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [th_ren_expK _ (by rw [map_neg, hmG v, neg_zero]), th_ren_neg, th_map_ren]
    · intro v _
      rw [map_neg, th_map_ren, th_ren_const _ (hmG v), neg_zero]
  rw [e1, ← MvPowerSeries.coe_substAlgHom hT, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hT, th_subst_ren _ hT]
  have e2 : (fun k => tOf vp μ (X.coordZA K' j) (Sum.map (Sigma.mk v) (Sigma.mk v) k)) =
      fun k => ren (fun z => (⟨v, z⟩ : X.ZA j)) (tOf vp μ (coordZ (X.om v) K' 1) k) := by
    funext k
    unfold tOf
    rw [th_coordZA_eq, th_ren_psubst _ (coordZ_const (X.om v) K' 1 k)]
  rw [e2, ← th_ren_subst _ (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (th_tOf_const vp μ h0 _ (coordZ_const (X.om v) K' 1))), hEq v, th_ren_mul,
    th_ren_expK _ (by rw [map_neg, map_mul, hhS_const, mul_zero, neg_zero]), th_ren_neg, th_ren_mul, th_ren_C,
    th_hhA_eq]

end Places

end Formalism.MainNotions.FormalGroupSystem.Pf
