import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.ColDefs
import Development.AutomorphicArithmetic.OrbitLabellings.ExistsFrobeniusEquivariantLocalBasisCoordinates
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd UpperTheory.G2 Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual)
open Formalism.InvariantFactorPaths.G7 (UnrOK)

namespace UpperTheory.EvenLinearSubstitution

section Alg

variable {K Lt β ι : Type} [Field K] {σ : K →+* K} {i : ℕ} {pos : Lt → ℕ → Lt}

private lemma pp (a b : ℕ) (x : K) : (σ ^ a) ((σ ^ b) x) = (σ ^ (a + b)) x := by
  rw [pow_add]; rfl

private lemma sum_even {M : Type} [AddCommMonoid M] (i : ℕ) [NeZero i] (F : ℕ → M) :
    (∑ s : ZMod (2 * i), if s.val % 2 = 0 then F s.val else 0) = ∑ m : Fin i, F (2 * m.val) := by
  rw [Formalism.L2.Th1.D.TraceDualSums.sum_zmod (2 * i) (fun k => if k % 2 = 0 then F k else 0),
    Formalism.L2.Th1.D.TraceDualSums.sum_range_even i F, Finset.sum_range]

private noncomputable def gam (σ : K →+* K) (i : ℕ) (pos : Lt → ℕ → Lt) (c : K) (g : Lt → K) (r : Lt) : K :=
  ∑ m : Fin i, (σ ^ (2 * m.val)) c * g (pos r (2 * m.val))

private lemma move_even (hp : IsPos i pos) {g : Lt → K} (hg : ∀ z, σ (σ (g z)) = g (pos z 2)) (j : ℕ) (z : Lt) :
    (σ ^ (2 * j)) (g z) = g (pos z (2 * j)) := by
  induction j with
  | zero => rw [mul_zero, hp.zero]; rfl
  | succ j ih =>
    rw [mul_add, mul_one, ← hp.add, ← hg, ← ih, add_comm, ← pp]
    rfl

private lemma gam_fix (hp : IsPos i pos) {g : Lt → K} (hg : ∀ z, σ (σ (g z)) = g (pos z 2)) {c : K}
    (hc : (σ ^ (2 * i)) c = c) (r : Lt) : σ (σ (gam σ i pos c g r)) = gam σ i pos c g r := by
  have h1 := Finset.sum_range_succ (fun m => (σ ^ (2 * m)) c * g (pos r (2 * m))) i
  have h2 := Finset.sum_range_succ' (fun m => (σ ^ (2 * m)) c * g (pos r (2 * m))) i
  have e : pos r (2 * i) = r := by rw [two_mul, ← hp.add, hp.period, hp.period]
  rw [h1, hc, e, mul_zero, hp.zero] at h2
  have h3 := add_right_cancel (b := c * g r) h2
  unfold gam
  rw [← Finset.sum_range (fun m => (σ ^ (2 * m)) c * g (pos r (2 * m)))]
  refine Eq.trans ?_ h3.symm
  simp only [map_sum, map_mul, hg, hp.add]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_add, mul_one, add_comm (2 * m) 2, ← pp]
  rfl

private lemma fix_even {c : K} (hc : σ (σ c) = c) (k : ℕ) : (σ ^ (2 * k)) c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mul_add, ← pp]
    exact (congrArg _ hc).trans ih

private lemma gam_conj (hp : IsPos i pos) (hi : Odd i) {g h : Lt → K} (hg : ∀ z, σ (g z) = h (pos z 1))
    (hg2 : ∀ z, σ (σ (g z)) = g (pos z 2)) {c : K} (hc : (σ ^ (2 * i)) c = c) (r : Lt) :
    σ (gam σ i pos c g r) = gam σ i pos ((σ ^ i) c) h r := by
  obtain ⟨j, hj⟩ := hi
  have e1 : ∀ x : K, (σ ^ i) x = σ ((σ ^ (2 * j)) x) := fun x => by
    rw [hj, add_comm, ← pp, pow_one]
  have e2 : ∀ z, (σ ^ i) (g z) = h z := fun z => by
    rw [e1, move_even hp hg2, hg, hp.add, ← hj, hp.period]
  rw [← fix_even (gam_fix hp hg2 hc r) j, ← e1]
  simp only [gam, map_sum, map_mul, e2, pp, add_comm]

private lemma dual_swap {om oms : Fin i → K}
    (hd : ∀ ρ ρ', ∑ m : Fin i, (σ ^ (2 * m.val)) (om ρ * oms ρ') = if ρ = ρ' then 1 else 0) (t s : Fin i) :
    ∑ ρ, (σ ^ (2 * t.val)) (om ρ) * (σ ^ (2 * s.val)) (oms ρ) = if t = s then 1 else 0 := by
  let V : Matrix (Fin i) (Fin i) K := Matrix.of fun k r => (σ ^ (2 * k.val)) (om r)
  let Q : Matrix (Fin i) (Fin i) K := Matrix.of fun r k => (σ ^ (2 * k.val)) (oms r)
  have hQV : Q * V = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := hd r' r
    simp only [map_mul] at this
    simp only [V, Q, Matrix.of_apply, mul_comm ((σ ^ _) (oms r)), this, eq_comm]
  have hVQ : V * Q = 1 := mul_eq_one_comm.1 hQV
  have := congrFun (congrFun hVQ t) s
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

private lemma gam_pair [Fintype ι] {R : Finset Lt}
    (hB : Function.Injective fun y : {z // z ∈ R} × Fin i => pos y.1.1 (2 * y.2.val))
    {g h : Lt → ι → K} {q : Prop} (hpair : ∀ w z, ∑ k, h w k * g z k = if w = z ∧ q then 1 else 0)
    (c c' : K) (r r' : {z // z ∈ R}) :
    ∑ k, gam σ i pos c (fun z => h z k) r.1 * gam σ i pos c' (fun z => g z k) r'.1 =
      if r = r' ∧ q then ∑ m : Fin i, (σ ^ (2 * m.val)) (c' * c) else 0 := by
  have e : ∀ m m' : Fin i, ∑ k, (σ ^ (2 * m.val)) c * h (pos r.1 (2 * m.val)) k *
      ((σ ^ (2 * m'.val)) c' * g (pos r'.1 (2 * m'.val)) k) =
      if m = m' then (if r = r' ∧ q then (σ ^ (2 * m.val)) (c' * c) else 0) else 0 := by
    intro m m'
    have e1 : ∀ k, (σ ^ (2 * m.val)) c * h (pos r.1 (2 * m.val)) k *
      ((σ ^ (2 * m'.val)) c' * g (pos r'.1 (2 * m'.val)) k) = (σ ^ (2 * m'.val)) c' * (σ ^ (2 * m.val)) c *
        (h (pos r.1 (2 * m.val)) k * g (pos r'.1 (2 * m'.val)) k) := fun k => by ring
    simp only [e1]
    rw [← Finset.mul_sum, hpair]
    by_cases hz : pos r.1 (2 * m.val) = pos r'.1 (2 * m'.val)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hB (a₁ := (r, m)) (a₂ := (r', m')) hz)
      by_cases hq : q <;> simp [hq]
    · rw [if_neg fun h => hz h.1, mul_zero]
      by_cases hm : m = m'
      · rw [if_pos hm, if_neg]
        rintro ⟨rfl, -⟩
        exact hz (by rw [hm])
      · rw [if_neg hm]
  simp only [gam, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun m _ => Finset.sum_comm]
  simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  split_ifs <;> simp

private lemma gam_lin {C : Type} [Field C] (j : K →+* C) [NeZero i] [Fintype Lt] [Fintype β] {R : Finset Lt}
    (hB : Function.Bijective fun y : {z // z ∈ R} × Fin i => pos y.1.1 (2 * y.2.val))
    {om oms : Fin i → K}
    (hd : ∀ ρ ρ', ∑ m : Fin i, (σ ^ (2 * m.val)) (om ρ * oms ρ') = if ρ = ρ' then 1 else 0) (g : Lt → β → K) :
    (∑ e : ({z // z ∈ R} × Fin i) × β, MvPowerSeries.C (j (gam σ i pos (om e.1.2) (fun z => g z e.2) e.1.1.1)) *
      linS j σ i pos (oms e.1.2) e.1.1.1 e.2 : MvPowerSeries (Lt × β) C) =
      ∑ v : Lt × β, MvPowerSeries.C (j (g v.1 v.2)) * MvPowerSeries.X v := by
  have e1 : ∀ (c : K) (r : Lt) (b : β), (linS j σ i pos c r b : MvPowerSeries (Lt × β) C) =
      ∑ s : Fin i, MvPowerSeries.C (j ((σ ^ (2 * s.val)) c)) * MvPowerSeries.X (pos r (2 * s.val), b) := by
    intro c r b
    unfold linS
    rw [sum_even i (fun s => (MvPowerSeries.C (j (σ^[s] c)) * MvPowerSeries.X (pos r s, b) : MvPowerSeries (Lt × β) C))]
    simp only [RingHom.coe_pow]
  have e2 : ∀ (r : Lt) (b : β) (s : Fin i),
      ∑ ρ, gam σ i pos (om ρ) (fun z => g z b) r * (σ ^ (2 * s.val)) (oms ρ) = g (pos r (2 * s.val)) b := by
    intro r b s
    simp only [gam, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e3 : ∀ t : Fin i, ∑ ρ, (σ ^ (2 * t.val)) (om ρ) * g (pos r (2 * t.val)) b * (σ ^ (2 * s.val)) (oms ρ) =
        g (pos r (2 * t.val)) b * if t = s then 1 else 0 := fun t => by
      rw [← dual_swap hd, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    simp only [e3]
    simp
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hB.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← e2, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [map_mul, map_mul, mul_assoc]

end Alg

private lemma bij_even (D : D7) (p : ℕ) (hi : Odd (nP D p)) (R : Finset (Bool × HH D))
    (hR : ∀ z, ∃! r, r ∈ R ∧ ∃ e : ℕ, posPl D p r e = z) :
    Function.Bijective fun y : {z // z ∈ R} × Fin (nP D p) => posPl D p y.1.1 (2 * y.2.val) := by
  have hpos : 0 < nP D p := hi.pos
  constructor
  · rintro ⟨⟨r, hr⟩, m⟩ ⟨⟨r', hr'⟩, m'⟩ h
    have h' : posPl D p r (2 * m.val) = posPl D p r' (2 * m'.val) := h
    obtain rfl : r = r' := (hR _).unique ⟨hr, _, rfl⟩ ⟨hr', _, h'.symm⟩
    rw [← posPl_mod D p r (2 * m.val), ← posPl_mod D p r (2 * m'.val)] at h'
    have h2 : 2 * m.val ≡ 2 * m'.val [MOD nP D p] :=
      posPl_inj D p r _ _ (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h'
    have h3 := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm (Nat.coprime_two_left.2 hi)) h2
    rw [Fin.ext (Nat.ModEq.eq_of_lt_of_lt h3 m.2 m'.2)]
  · intro z
    obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
    obtain ⟨j, hj⟩ := hi
    refine ⟨(⟨r, hr⟩, ⟨(e * (j + 1)) % nP D p, Nat.mod_lt _ hpos⟩), ?_⟩
    show posPl D p r (2 * ((e * (j + 1)) % nP D p)) = z
    rw [← posPl_mod, Nat.mul_mod_mod, show 2 * (e * (j + 1)) = e + nP D p * e by rw [hj]; ring,
      Nat.add_mul_mod_self_left, posPl_mod, he]

private lemma subst_lin {σ τ : Type} [Fintype σ] {K : Type} [Field K] {a : σ → MvPowerSeries τ K}
    (ha : MvPowerSeries.HasSubst a) (α : σ → K) :
    MvPowerSeries.subst a (∑ j, MvPowerSeries.C (α j) * MvPowerSeries.X j : MvPowerSeries σ K) =
      ∑ j, MvPowerSeries.C (α j) * a j := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_C]

private lemma subst_atLin {p : ℕ} [Fact p.Prime] {ν ι s : Type} [Fintype ν] [Fintype ι] [Fintype s]
    (m : s → ν → ℂ_[p]) (t : s → ι → ℂ_[p]) (g : ι → ν → ℂ_[p]) (c : ℂ_[p])
    (h : ∀ k j, m k j * c = ∑ i, t k i * g i j) (G : MvPowerSeries s ℂ_[p]) :
    (MvPowerSeries.subst (fun v : ν => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries ν ℂ_[p]))
      (atLin m (fun j => MvPowerSeries.X j) G) : MvPowerSeries ν ℂ_[p]) =
    MvPowerSeries.subst (fun i : ι => (∑ j, MvPowerSeries.C (g i j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p]))
      (MvPowerSeries.subst (fun k : s => (∑ i, MvPowerSeries.C (t k i) * MvPowerSeries.X i : MvPowerSeries ι ℂ_[p])) G :
        MvPowerSeries ι ℂ_[p]) := by
  have h1 : MvPowerSeries.HasSubst (fun k : s =>
      (∑ j, algebraMap ℂ_[p] (MvPowerSeries ν ℂ_[p]) (m k j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have h2 : MvPowerSeries.HasSubst (fun v : ν => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries ν ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have h3 : MvPowerSeries.HasSubst (fun k : s => (∑ i, MvPowerSeries.C (t k i) * MvPowerSeries.X i : MvPowerSeries ι ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have h4 : MvPowerSeries.HasSubst (fun i : ι => (∑ j, MvPowerSeries.C (g i j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold atLin
  rw [MvPowerSeries.subst_comp_subst_apply h1 h2, MvPowerSeries.subst_comp_subst_apply h3 h4]
  congr 1
  funext k
  have e : (∑ j, algebraMap ℂ_[p] (MvPowerSeries ν ℂ_[p]) (m k j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p]) =
      ∑ j, MvPowerSeries.C (m k j) * MvPowerSeries.X j := rfl
  rw [e, subst_lin h2, subst_lin h4]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← map_mul, h k j, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

end UpperTheory.EvenLinearSubstitution

open UpperTheory.EvenLinearSubstitution in
theorem UpperTheory.stdSeries_orbit_coordinate_change_of_odd_inert :
    ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → 5 ≤ p → IsResidueClassZero D p →
    ∀ [NeZero (nP D p)], Odd (nP D p) → ∀ om : Fin (nP D p) → MaximalUnramifiedExtension p,
    OwOK (2 * nP D p) σ om (fun r => σ^[nP D p] (om r)) → TrDual (2 * nP D p) σ om (fun r => σ^[nP D p] (om r)) →
    ∀ R : Finset ((Bool × HH D)), (∀ z, ∃! r, r ∈ R ∧ ∃ e : ℕ, posPl D p r e = z) →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
    admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' →
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b →
    ∃ γ : Fin r → (({z // z ∈ R} × Fin (nP D p)) × Fin N × Fin N') → MaximalUnramifiedExtension p,
      (∀ k e, ‖γ k e‖ ≤ 1 ∧ σ (σ (γ k e)) = γ k e) ∧ (∀ e e', ∑ k, σ (γ k e) * γ k e' = if e = e' then 1 else 0) ∧
      ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
        (MvPowerSeries.subst (fun v : (Bool × HH D) × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p]))
          (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p]) =
        MvPowerSeries.subst (fun k => (∑ e, MvPowerSeries.C (γ k e : ℂ_[p]) *
          linS (MaximalUnramifiedExtension p).subtype σ (nP D p) (posPl D p) (σ^[nP D p] (om e.1.2)) e.1.1.1 e.2 : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p]))
          (MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
            (∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p])) G :
            MvPowerSeries (Fin r) ℂ_[p]) := by
  intro D p _ lam σ hσ _ hc _ hi om hOw hTr R hR N N' L L' P P' hA hP hP' r b hb ho
  obtain ⟨g, h, hg, hh, hpair, hint, hlin⟩ :=
    UpperTheory.exists_frobenius_equivariant_localBasis_coordinates D p lam σ hσ (Or.inl hc) N N' L L' P P' hA hP hP' r b hb ho
  have hp : IsPos (nP D p) (posPl D p) := ⟨posPl_zero D p, posPl_add D p, posPl_period D p⟩
  have hB := bij_even D p hi R hR
  have hg2 : ∀ z a b₀ i, σ (σ (g z a b₀ i)) = g (posPl D p z 2) a b₀ i := fun z a b₀ i => by
    rw [hg, hh, posPl_add]
  have hfix : ∀ ρ, (σ ^ (2 * nP D p)) (om ρ) = om ρ := fun ρ => by
    rw [RingHom.coe_pow]; exact (hOw.2 ρ).1
  have hd : ∀ ρ ρ', ∑ m : Fin (nP D p), (σ ^ (2 * m.val)) (om ρ * σ^[nP D p] (om ρ')) = if ρ = ρ' then 1 else 0 := by
    intro ρ ρ'
    have h1 := hTr.2 ρ ρ'
    rw [sum_even (nP D p) (fun s => σ^[s] (om ρ * σ^[nP D p] (om ρ')))] at h1
    simp only [RingHom.coe_pow]
    convert h1
  have hiso : ∀ (n : ℕ) (x : MaximalUnramifiedExtension p), ‖(σ ^ n) x‖ = ‖x‖ := fun n x => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, Formalism.L2.Th1.D.sigmaIsom (MaximalUnramifiedExtension p) p σ hσ, ih]
  refine ⟨fun k e => gam σ (nP D p) (posPl D p) (om e.1.2) (fun z => g z e.2.1 e.2.2 k) e.1.1.1,
    fun k e => ⟨?_, gam_fix hp (fun z => hg2 z _ _ _) (hfix _) _⟩, ?_, fun c G => ?_⟩
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun m _ => ?_
    rw [norm_mul, hiso]
    exact mul_le_one₀ (hOw.1 _).1 (norm_nonneg _) (hint _ _ _ _)
  · rintro ⟨⟨r₁, ρ₁⟩, a₁, b₁⟩ ⟨⟨r₂, ρ₂⟩, a₂, b₂⟩
    have e1 : ∀ k, σ (gam σ (nP D p) (posPl D p) (om ρ₁) (fun z => g z a₁ b₁ k) r₁.1) =
        gam σ (nP D p) (posPl D p) ((σ ^ nP D p) (om ρ₁)) (fun z => h z a₁ b₁ k) r₁.1 := fun k =>
      gam_conj hp hi (fun z => hg z _ _ _) (fun z => hg2 z _ _ _) (hfix _) _
    simp only [e1]
    rw [gam_pair hB.1 (g := fun z k => g z a₂ b₂ k) (h := fun z k => h z a₁ b₁ k) (q := a₁ = a₂ ∧ b₁ = b₂)
      (fun w z => by convert hpair w z a₁ b₁ a₂ b₂), RingHom.coe_pow σ (nP D p), hd]
    by_cases h1 : r₁ = r₂ ∧ a₁ = a₂ ∧ b₁ = b₂
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      simp [eq_comm]
    · rw [if_neg h1, if_neg]
      intro h2
      simp only [Prod.mk.injEq] at h2
      exact h1 ⟨h2.1.1, h2.2⟩
  · have e1 := fun k => gam_lin (MaximalUnramifiedExtension p).subtype hB (om := om) (oms := fun ρ => σ^[nP D p] (om ρ)) hd
      (fun z (y : Fin N × Fin N') => g z y.1 y.2 k)
    refine Eq.trans (subst_atLin _ (fun k i => c * lamC lam (embT D k.1 (b i k.2.1 k.2.2)))
      (fun i j => (g j.1 j.2.1 j.2.2 i : ℂ_[p])) c (fun k j => ?_) G) ?_
    · rw [one_mul, ← hlin k j.1 j.2.1 j.2.2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    · congr 1
      funext k
      exact (e1 k).symm
