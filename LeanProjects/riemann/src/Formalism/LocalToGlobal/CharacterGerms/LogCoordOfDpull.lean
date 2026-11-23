import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfLogUnitGerm

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def DPullSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  ∀ (n : ℕ) (b : Fin n) (c : WVO I → C) (F : PS C n dd),
    pullN Y p (DofN (Y.B.FK C) b (fun i => ∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i) F) =
      ∑ w : WVO I, c w • MvPowerSeries.pderiv C (b, w) (pullN Y p F)

namespace VP

theorem cc_subst_eq {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  set c := MvPowerSeries.constantCoeff f with hc
  have hg : MvPowerSeries.constantCoeff (f - algebraMap C (MvPowerSeries σ C) c) = 0 := by
    simp [hc, MvPowerSeries.algebraMap_apply]
  have hf : f = algebraMap C (MvPowerSeries σ C) c + (f - algebraMap C (MvPowerSeries σ C) c) := by
    ring
  have h1 : MvPowerSeries.subst a (algebraMap C (MvPowerSeries σ C) c) =
      algebraMap C (MvPowerSeries τ C) c := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact (MvPowerSeries.substAlgHom hs).commutes c
  rw [hf, MvPowerSeries.subst_add hs, map_add, h1, constantCoeff_subst_zero ha hg]
  simp [MvPowerSeries.algebraMap_apply]

private theorem jetAt0_zero_left' {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  simp [jetAt0]

private theorem jetAt0_finset_sum_left {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0_zero_left']
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

theorem jet_lin {σ ι : Type} [Fintype ι] (e : ι → σ) (q : MvPolynomial σ C) (c : ι → C) (G : MvPowerSeries σ C) :
    jetAt0 (q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X (e w)) G =
      jetAt0 q (∑ w, c w • MvPowerSeries.pderiv C (e w) G) := by
  rw [Finset.mul_sum, jetAt0_finset_sum_left, jet_sum_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc, jet_mul_X, jet_mul_C, jet_smul_right, dVar_eq_pderiv]

variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

theorem jet_iter (hD : DPullSt Y p) {n : ℕ} (b : Fin n) (u : Fin dd → C) (c : WVO I → C)
    (hu : u = ∑ w : WVO I, c w • (Y.raw (p w.1)).u w.2.1 w.2.2) (k : ℕ) :
    ∀ (q : MvPolynomial (Fin n × WVO I) C) (g : PS C n dd),
      jetAt0 q (pullN Y p ((DofN (Y.B.FK C) b u)^[k] g)) =
        jetAt0 (q * (∑ w : WVO I, MvPolynomial.C (c w) * MvPolynomial.X (b, w)) ^ k) (pullN Y p g) := by
  have hu' : u = fun i => ∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i := by
    rw [hu]; funext i; rw [Finset.sum_apply]; rfl
  subst hu'
  induction k with
  | zero => intro q g; simp
  | succ k ih =>
    intro q g
    rw [Function.iterate_succ_apply, ih, hD, ← jet_lin (fun w : WVO I => (b, w)), pow_succ, mul_assoc]

theorem jet_list (hD : DPullSt Y p) {n : ℕ} {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (co : ι → WVO I → C)
    (m : ι →₀ ℕ) (f : PS C n dd) :
    ∀ (ls : List ι), (∀ ℓ ∈ ls, m ℓ ≠ 0 → uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2) →
    ∀ q : MvPolynomial (Fin n × WVO I) C,
      jetAt0 q (pullN Y p (ls.foldr (fun l g => (DofN (Y.B.FK C) (cp l) (uv l))^[m l] g) f)) =
        jetAt0 (q * (ls.map fun l => (∑ w : WVO I, MvPolynomial.C (co l w) * MvPolynomial.X (cp l, w)) ^ m l).prod)
          (pullN Y p f) := by
  intro ls
  induction ls with
  | nil => intro _ q; simp
  | cons l ls ih =>
    intro hls q
    have htl : ∀ ℓ ∈ ls, m ℓ ≠ 0 → uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2 :=
      fun ℓ hℓ => hls ℓ (List.mem_cons_of_mem l hℓ)
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    by_cases hm : m l = 0
    · rw [hm, Function.iterate_zero, id, pow_zero, one_mul]
      exact ih htl q
    · rw [jet_iter hD (cp l) (uv l) (co l) (hls l List.mem_cons_self hm) (m l), ih htl, mul_assoc]

end VP

private theorem jetAt0_one_eq_constantCoeff {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  rw [← MvPolynomial.C_1, jet_C, one_mul]

private theorem jetAt0_C_mul' {σ : Type} (a : C) (q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a * q) G = a * jetAt0 q G := by
  rw [mul_comm, jet_mul_C]

theorem logCoord_of_dpull {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)} (hD : DPullSt Y p) :
    LogCoordSt Y p := by
  classical
  intro n ι _ cp uv P Q hQ F
  obtain ⟨co, hco, rfl⟩ := hQ
  have hcc : ∀ H : PS C n dd, MvPowerSeries.constantCoeff (pullN Y p H) = MvPowerSeries.constantCoeff H :=
    fun H => VP.cc_subst_eq (fun q => VP.cc_pullPt (Y := Y) (p := p) q) H
  have hmon : ∀ m ∈ P.support, MvPowerSeries.constantCoeff (DmonN (Y.B.FK C) cp uv m F) =
      jetAt0 (∏ ℓ, (∑ w : WVO I, MvPolynomial.C (co ℓ w) * MvPolynomial.X (cp ℓ, w)) ^ m ℓ) (pullN Y p F) := by
    intro m hm
    have hv : ∀ ℓ ∈ (Finset.univ : Finset ι).toList, m ℓ ≠ 0 →
        uv ℓ = ∑ w : WVO I, co ℓ w • (Y.raw (p w.1)).u w.2.1 w.2.2 := fun ℓ _ hℓ =>
      hco ℓ ((MvPolynomial.mem_vars ℓ).2 ⟨m, hm, Finsupp.mem_support_iff.2 hℓ⟩)
    have h1 := VP.jet_list hD cp uv co m F _ hv 1
    rw [one_mul, Finset.prod_map_toList, jetAt0_one_eq_constantCoeff, hcc] at h1
    exact h1
  rw [DpolyN, map_sum, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', VP.jetAt0_finset_sum_left]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_mul, hmon m hm, MvPolynomial.algebraMap_eq, jetAt0_C_mul']
  simp

end Formalism.L2.FormalSeriesBounds
