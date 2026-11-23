import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupOnCopies
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

variable {R : Type} [CommRing R] {d n : ℕ}

def Vc (d : ℕ) (T : Finset (Fin n)) : Set (Fin n × Fin d) := {p | p.1 ∈ T}

theorem onCopies_iff (T : Finset (Fin n)) (f : PS R n d) : OnCopies T f ↔ f ∈ subV R (Vc d T) := by
  unfold OnCopies subV Vc
  rfl

theorem ev_mem {m : ℕ} (V : Set (Fin n × Fin d)) (a : Fin m → Pt R n d)
    (h0 : ∀ q i, constantCoeff (a q i) = 0) (hV : ∀ q i, a q i ∈ subV R V) (g : PS R m d) :
    ev a g ∈ subV R V := by
  have hs : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => h0 p.1 p.2
  exact subst_mem (fun p : Fin m × Fin d => a p.1 p.2) hs (fun p => hV p.1 p.2) g

theorem ev_cc {m : ℕ} (a : Fin m → Pt R n d) (h0 : ∀ q i, constantCoeff (a q i) = 0)
    (g : PS R m d) (hg : constantCoeff g = 0) : constantCoeff (ev a g) = 0 := by
  unfold ev
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  all_goals first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => h0 p.1 p.2)
    | exact fun p => h0 p.1 p.2
    | exact hg

theorem ptz_cc (b : Fin n) :
    ∀ (q : Fin 2) (i : Fin d), constantCoeff ((![pt R d b, 0] : Fin 2 → Pt R n d) q i) = 0 := by
  intro q i
  fin_cases q <;> simp [pt]

theorem ptz_mem (T : Finset (Fin n)) (b : Fin n) (hb : b ∈ T) :
    ∀ (q : Fin 2) (i : Fin d), (![pt R d b, 0] : Fin 2 → Pt R n d) q i ∈ subV R (Vc d T) := by
  intro q i
  fin_cases q
  · show OnV (Vc d T) (pt R d b i)
    unfold OnV pt
    intro e he p hp
    rw [MvPowerSeries.coeff_X] at he
    split_ifs at he with h
    · subst h
      have hp' := Finsupp.support_single_subset hp
      rw [Finset.mem_singleton] at hp'
      subst hp'
      exact hb
    · exact absurd rfl he
  · exact (subV R (Vc d T)).zero_mem

theorem single_point_const_coeff (b : Fin n) :
    ∀ (q : Fin 1) (i : Fin d), constantCoeff ((![pt R d b] : Fin 1 → Pt R n d) q i) = 0 := by
  intro q i
  fin_cases q
  simp [pt]

theorem single_point_mem_subspace (T : Finset (Fin n)) (b : Fin n) (hb : b ∈ T) :
    ∀ (q : Fin 1) (i : Fin d), (![pt R d b] : Fin 1 → Pt R n d) q i ∈ subV R (Vc d T) := by
  intro q i
  fin_cases q
  show OnV (Vc d T) (pt R d b i)
  unfold OnV pt
  intro e he p hp
  rw [MvPowerSeries.coeff_X] at he
  split_ifs at he with h
  · subst h
    have hp' := Finsupp.support_single_subset hp
    rw [Finset.mem_singleton] at hp'
    subst hp'
    exact hb
  · exact absurd rfl he

theorem dofN_mem (F : Fin d → PS R 2 d) (T : Finset (Fin n)) {b : Fin n} (hb : b ∈ T)
    (u : Fin d → R) (g : PS R n d) (hg : g ∈ subV R (Vc d T)) :
    DofN F b u g ∈ subV R (Vc d T) := by
  unfold DofN
  exact sum_mem fun j _ => mul_mem (sum_mem fun i _ =>
    mul_mem (C_mem _ _) (ev_mem _ _ (ptz_cc b) (ptz_mem T b hb) _)) (pderiv_mem _ hg)

theorem dofN_mul_right (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hB : ∀ j, pderiv R (b, j) B = 0) : DofN F b u (A * B) = DofN F b u A * B := by
  unfold DofN
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hB j, smul_zero, zero_add, smul_eq_mul]
  ring

theorem dofN_mul_left (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hA : ∀ j, pderiv R (b, j) A = 0) : DofN F b u (A * B) = A * DofN F b u B := by
  unfold DofN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hA j, smul_zero, add_zero, smul_eq_mul]
  ring

theorem it_right (D : PS R n d → PS R n d) (B : PS R n d) (hD : ∀ A, D (A * B) = D A * B) :
    ∀ (N : ℕ) (A : PS R n d), D^[N] (A * B) = D^[N] A * B
  | 0, _ => rfl
  | N + 1, A => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hD, it_right D B hD N]

theorem it_left (D : PS R n d → PS R n d) (A : PS R n d) (hD : ∀ B, D (A * B) = A * D B) :
    ∀ (N : ℕ) (B : PS R n d), D^[N] (A * B) = A * D^[N] B
  | 0, _ => rfl
  | N + 1, B => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hD, it_left D A hD N]

theorem it_mem (D : PS R n d → PS R n d) (Q : Subalgebra R (PS R n d)) (hD : ∀ g ∈ Q, D g ∈ Q) :
    ∀ (N : ℕ) (g : PS R n d), g ∈ Q → D^[N] g ∈ Q
  | 0, _, hg => hg
  | N + 1, g, hg => by
    rw [Function.iterate_succ_apply']
    exact hD _ (it_mem D Q hD N g hg)

section Fold

variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem fold_mem (T : Finset (Fin n)) (mm : ι →₀ ℕ) (hm : ∀ l, mm l ≠ 0 → cp l ∈ T) (L : List ι)
    (A : PS R n d) (hA : A ∈ subV R (Vc d T)) :
    L.foldr (fun l g => (DofN F (cp l) (u l))^[mm l] g) A ∈ subV R (Vc d T) := by
  induction L with
  | nil => exact hA
  | cons l L ih =>
    rw [List.foldr_cons]
    by_cases hl : mm l = 0
    · rw [hl, Function.iterate_zero_apply]
      exact ih
    · exact it_mem (DofN F (cp l) (u l)) (subV R (Vc d T))
        (fun g hg => dofN_mem F T (hm l hl) (u l) g hg) (mm l) _ ih

theorem fold_mul (S : Finset (Fin n)) (m₁ m₂ : ι →₀ ℕ) (hm1 : ∀ l, m₁ l ≠ 0 → cp l ∈ S)
    (hm2 : ∀ l, m₂ l ≠ 0 → cp l ∈ Sᶜ) (L : List ι) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    L.foldr (fun l g => (DofN F (cp l) (u l))^[(m₁ + m₂) l] g) (A * B) =
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m₁ l] g) A *
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m₂ l] g) B := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [ih, Finsupp.add_apply]
    have hA' := fold_mem F cp u S m₁ hm1 L A hA
    have hB' := fold_mem F cp u Sᶜ m₂ hm2 L B hB
    by_cases hl : cp l ∈ S
    · have h2 : m₂ l = 0 := by
        by_contra h
        exact (Finset.mem_compl.1 (hm2 l h)) hl
      rw [h2, add_zero, it_right _ _ (fun X => dofN_mul_right F _ _ X _ (fun j =>
        pderiv_kill (i := (cp l, j)) (V := Vc d Sᶜ)
          (fun hc => (Finset.mem_compl.1 (show cp l ∈ Sᶜ from hc)) hl) hB'))]
      rfl
    · have h1 : m₁ l = 0 := by
        by_contra h
        exact hl (hm1 l h)
      rw [h1, zero_add, it_left _ _ (fun X => dofN_mul_left F _ _ _ X (fun j =>
        pderiv_kill (i := (cp l, j)) (V := Vc d S) (fun hc => hl (show cp l ∈ S from hc)) hA'))]
      rfl

theorem dmon_mul (S : Finset (Fin n)) (m₁ m₂ : ι →₀ ℕ) (hm1 : ∀ l, m₁ l ≠ 0 → cp l ∈ S)
    (hm2 : ∀ l, m₂ l ≠ 0 → cp l ∈ Sᶜ) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DmonN F cp u (m₁ + m₂) (A * B) = DmonN F cp u m₁ A * DmonN F cp u m₂ B := by
  unfold DmonN
  exact fold_mul F cp u S m₁ m₂ hm1 hm2 _ A B hA hB

theorem dmon_zero (g : PS R n d) : DmonN F cp u 0 g = g := by
  simp [DmonN]

theorem dpoly_sup (P : MvPolynomial ι R) (T : Finset (ι →₀ ℕ)) (hT : P.support ⊆ T)
    (g : PS R n d) : DpolyN F cp u P g = ∑ mm ∈ T, C (P.coeff mm) * DmonN F cp u mm g := by
  unfold DpolyN
  apply Finset.sum_subset hT
  intro mm _ hmm
  have h0 : P.coeff mm = 0 := by simpa [MvPolynomial.mem_support_iff] using hmm
  rw [h0, map_zero, zero_mul]

theorem dpoly_add (P Q : MvPolynomial ι R) (g : PS R n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [dpoly_sup F cp u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    dpoly_sup F cp u P (P.support ∪ Q.support) Finset.subset_union_left,
    dpoly_sup F cp u Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mm _ => ?_)
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem dpoly_monomial (mm : ι →₀ ℕ) (a : R) (g : PS R n d) :
    DpolyN F cp u (MvPolynomial.monomial mm a) g = C a * DmonN F cp u mm g := by
  classical
  rw [dpoly_sup F cp u _ {mm} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem dpoly_one (g : PS R n d) : DpolyN F cp u 1 g = g := by
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, dpoly_monomial, map_one, one_mul, dmon_zero]

def dpolyHom (g : PS R n d) : MvPolynomial ι R →+ PS R n d where
  toFun P := DpolyN F cp u P g
  map_zero' := by simp [DpolyN]
  map_add' P Q := dpoly_add F cp u P Q g

theorem dpoly_mul (S : Finset (Fin n)) (P₁ P₂ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (h2 : ∀ l ∈ P₂.vars, cp l ∉ S) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u (P₁ * P₂) (A * B) = DpolyN F cp u P₁ A * DpolyN F cp u P₂ B := by
  have e : P₁ * P₂ = ∑ m1 ∈ P₁.support, ∑ m2 ∈ P₂.support,
      MvPolynomial.monomial (m1 + m2) (P₁.coeff m1 * P₂.coeff m2) := by
    conv_lhs => rw [P₁.as_sum, P₂.as_sum]
    rw [Finset.sum_mul_sum]
    simp_rw [MvPolynomial.monomial_mul]
  calc DpolyN F cp u (P₁ * P₂) (A * B) = dpolyHom F cp u (A * B) (P₁ * P₂) := rfl
    _ = ∑ m1 ∈ P₁.support, ∑ m2 ∈ P₂.support,
          C (P₁.coeff m1) * DmonN F cp u m1 A * (C (P₂.coeff m2) * DmonN F cp u m2 B) := by
      rw [e, map_sum]
      refine Finset.sum_congr rfl fun m1 hm1 => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun m2 hm2 => ?_
      have hq1 : ∀ l, m1 l ≠ 0 → cp l ∈ S := fun l hl =>
        h1 l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m1, hm1, Finsupp.mem_support_iff.2 hl⟩)
      have hq2 : ∀ l, m2 l ≠ 0 → cp l ∈ Sᶜ := fun l hl =>
        Finset.mem_compl.2 (h2 l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m2, hm2, Finsupp.mem_support_iff.2 hl⟩))
      show DpolyN F cp u _ (A * B) = _
      rw [dpoly_monomial, dmon_mul F cp u S m1 m2 hq1 hq2 A B hA hB, map_mul]
      ring
    _ = DpolyN F cp u P₁ A * DpolyN F cp u P₂ B := by
      unfold DpolyN
      rw [Finset.sum_mul_sum]

theorem key_left (S : Finset (Fin n)) (P₁ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (A B : PS R n d) (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u P₁ (A * B) = DpolyN F cp u P₁ A * B := by
  have h := dpoly_mul F cp u S P₁ 1 h1 (by intro l hl; simp [MvPolynomial.vars_one] at hl) A B hA hB
  rwa [mul_one, dpoly_one] at h

theorem key_right (S : Finset (Fin n)) (P₂ : MvPolynomial ι R) (h2 : ∀ l ∈ P₂.vars, cp l ∉ S)
    (A B : PS R n d) (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u P₂ (A * B) = A * DpolyN F cp u P₂ B := by
  have h := dpoly_mul F cp u S 1 P₂ (by intro l hl; simp [MvPolynomial.vars_one] at hl) h2 A B hA hB
  rwa [one_mul, dpoly_one] at h

theorem value_split (S : Finset (Fin n)) (P₁ P₂ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (h2 : ∀ l ∈ P₂.vars, cp l ∉ S) (f₁ f₂ ES ET : PS R n d) (hf1 : f₁ ∈ subV R (Vc d S))
    (hf2 : f₂ ∈ subV R (Vc d Sᶜ)) (hES : ES ∈ subV R (Vc d S)) (hET : ET ∈ subV R (Vc d Sᶜ))
    (c1 : constantCoeff ES = 1) (c2 : constantCoeff ET = 1) :
    constantCoeff (DpolyN F cp u (P₁ * P₂) (f₁ * f₂ * (ES * ET))) =
      constantCoeff (DpolyN F cp u P₁ (f₁ * (ES * ET))) *
        constantCoeff (DpolyN F cp u P₂ (f₂ * (ES * ET))) := by
  have hA : f₁ * ES ∈ subV R (Vc d S) := Subalgebra.mul_mem _ hf1 hES
  have hB : f₂ * ET ∈ subV R (Vc d Sᶜ) := Subalgebra.mul_mem _ hf2 hET
  have e1 : f₁ * f₂ * (ES * ET) = (f₁ * ES) * (f₂ * ET) := by ring
  have e2 : f₁ * (ES * ET) = (f₁ * ES) * ET := by ring
  have e3 : f₂ * (ES * ET) = ES * (f₂ * ET) := by ring
  rw [e1, e2, e3, dpoly_mul F cp u S P₁ P₂ h1 h2 _ _ hA hB, key_left F cp u S P₁ h1 _ _ hA hET,
    key_right F cp u S P₂ h2 _ _ hES hB, map_mul, map_mul, map_mul, c1, c2, mul_one, one_mul]

end Fold

end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

theorem columnsStatement_holds : ColumnsStatement := by
  intro R _ d O _ _ B k _ _ _ h w0 h0 m n S f₁ f₂ ι _ cp u P₁ P₂ hf1 hf2 hP1 hP2
  classical
  have gcc : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt k d b] (B.hL k h w0)) = 0 :=
    fun b => ev_cc _ (single_point_const_coeff b) _ h0
  have xcc : ∀ T : Finset (Fin n),
      constantCoeff ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0)) = 0 := by
    intro T
    rw [smul_eq_C_mul, map_mul, map_sum]
    simp [gcc]
  have xmem : ∀ T : Finset (Fin n),
      ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0)) ∈ subV k (Vc d T) :=
    fun T => Subalgebra.smul_mem _
      (sum_mem fun b hb => ev_mem _ _ (single_point_const_coeff b) (single_point_mem_subspace T b hb) _) _
  have emem : ∀ T : Finset (Fin n),
      FB.expS k ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0)) ∈ subV k (Vc d T) := by
    intro T
    unfold FB.expS
    rw [PowerSeries.subst_def]
    exact subst_mem _ (hasSubst_of_constantCoeff_zero fun _ => xcc T) (fun _ => xmem T) _
  have ecc : ∀ T : Finset (Fin n),
      constantCoeff (FB.expS k ((m : k) • ∑ b ∈ T, ev (n := n) ![pt k d b] (B.hL k h w0))) = 1 := by
    intro T
    unfold FB.expS
    exact cc_exp _ (xcc T)
  have hE : FB.expS k ((m : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0)) =
      FB.expS k ((m : k) • ∑ b ∈ S, ev (n := n) ![pt k d b] (B.hL k h w0)) *
        FB.expS k ((m : k) • ∑ b ∈ Sᶜ, ev (n := n) ![pt k d b] (B.hL k h w0)) := by
    rw [← Finset.sum_add_sum_compl S, smul_add]
    unfold FB.expS
    exact expS_add _ _ (xcc S) (xcc Sᶜ)
  have key := value_split (B.FK k) cp u S P₁ P₂ hP1 hP2 f₁ f₂ _ _ ((onCopies_iff _ _).1 hf1)
    ((onCopies_iff _ _).1 hf2) (emem S) (emem Sᶜ) (ecc S) (ecc Sᶜ)
  rw [← hE] at key
  exact key

end Formalism.MainNotions.ModuliIntegralCharts.H1
