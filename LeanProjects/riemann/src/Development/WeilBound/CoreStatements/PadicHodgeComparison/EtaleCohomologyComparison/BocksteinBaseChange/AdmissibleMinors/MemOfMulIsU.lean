import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.ConnAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.ExistsWeightBasisFiltration
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.FilRZero

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Inj

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K}

theorem isU_of_mul {x y : R.B} (hx : x ∈ R.P) (hy : y ∈ R.P) (h : R.IsU (x * y)) : R.IsU y := by
  obtain ⟨-, w, hw, e⟩ := h
  exact ⟨hy, x * w, R.P.mul_mem hx hw, by rw [← e]; ring⟩

theorem not_isU_zero : ¬ R.IsU 0 := by
  rintro ⟨-, w, -, e⟩
  rw [zero_mul] at e
  exact zero_ne_one e

theorem mem_of_mul_isU {x u : R.B} (h : x * u ∈ R.P) (hu : R.IsU u) : x ∈ R.P := by
  obtain ⟨-, w, hw, e⟩ := hu
  have : x = x * u * w := by rw [mul_assoc, e, mul_one]
  rw [this]
  exact R.P.mul_mem h hw

theorem isU_σ (hR : R.Facts) (g : K.fixingSubgroup) {x : R.B} (h : R.IsU x) : R.IsU (R.σ g x) := by
  obtain ⟨hx, y, hy, e⟩ := h
  exact ⟨hR.σ_mem g x hx, R.σ g y, hR.σ_mem g y hy, by rw [← map_mul, e, map_one]⟩

theorem isU_sum (hR : R.Facts) {ι : Type*} (S : Finset ι) (x : ι → R.B) (hx : ∀ i, x i ∈ R.P)
    (h : R.IsU (∑ i ∈ S, x i)) : ∃ i, R.IsU (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty] at h; exact absurd h not_isU_zero
  | insert a S ha ih =>
    rw [Finset.sum_insert ha] at h
    rcases hR.loc _ (hx a) _ (R.P.sum_mem fun i _ => hx i) h with h1 | h1
    · exact ⟨a, h1⟩
    · exact ih h1

theorem toV_exists (M : Model l K) (n : ℕ) (v : M.V n) :
    ∃ ζ : ℤ_[l], ζ ≠ 0 ∧ ∃ x : M.T n, (ζ : ℚ_[l]) • v = M.toV n x :=
  exists_int_mul (T := GlobalTheory.EtC.Hl l M.spc n 0) v

variable {G : Model l K → Prop}

theorem key (P : Pre G R) (M : Model l K) (hM : G M) {i j : ℕ} {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V i))
    (z : Fin a → R.B) (g : M.V (i + j)) (y : M.T j) (f : Module.Dual ℚ_[l] (M.V i))
    (hf : ∀ x : M.T i, ∃ w, M.CupT x y w ∧ M.toV (i + j) w = f (M.toV i x) • g)
    {m m' : ℕ} (β : Module.Basis (Fin m) K (HdR M.q i)) (β' : Module.Basis (Fin m') K (HdR M.q j))
    (φ : Module.Dual K (HdR M.q (i + j))) :
    (∑ k, z k * R.q (f (b k))) * P.c M (i + j) g φ =
      ∑ s, ∑ s', (∑ k, z k * P.c M i (b k) (β.coord s)) * P.c M j (M.toV j y) (β'.coord s') *
        R.o (φ (P.cupR M i j (β s) (β' s'))) := by
  have hk : ∀ k, z k * R.q (f (b k)) * P.c M (i + j) g φ = ∑ s, ∑ s', z k * P.c M i (b k) (β.coord s) *
      P.c M j (M.toV j y) (β'.coord s') * R.o (φ (P.cupR M i j (β s) (β' s'))) := by
    intro k
    obtain ⟨ζ, hζ, x, hx⟩ := toV_exists M i (b k)
    obtain ⟨w, hw, hw'⟩ := hf x
    have e := P.cup M hM x y w hw β β' φ
    rw [hw', ← hx] at e
    simp only [P.lin, map_smul, smul_eq_mul, map_mul] at e
    have hq : R.q (ζ : ℚ_[l]) ≠ 0 := (map_ne_zero R.q).mpr (fun h => hζ (Subtype.ext h))
    have hk0 : R.q (f (b k)) * P.c M (i + j) g φ = ∑ s, ∑ s', P.c M i (b k) (β.coord s) *
        P.c M j (M.toV j y) (β'.coord s') * R.o (φ (P.cupR M i j (β s) (β' s'))) := by
      apply mul_left_cancel₀ hq
      rw [← mul_assoc, e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [mul_assoc, hk0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  rw [Finset.sum_mul]
  simp_rw [hk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]

theorem coords {M : Model l K} {n : ℕ} (A : Set (Module.Dual ℚ_[l] (M.V n)))
    (hA : Submodule.span ℚ_[l] A = ⊤) (T : R.B → Prop) (h0 : T 0) (hadd : ∀ x y, T x → T y → T (x + y))
    (hsmul : ∀ (c : ℚ_[l]) x, T x → T (R.q c * x)) {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n))
    (z : Fin a → R.B) (h : ∀ f ∈ A, T (∑ k, z k * R.q (f (b k)))) : ∀ k, T (z k) := by
  intro k0
  have hall : ∀ f ∈ Submodule.span ℚ_[l] A, T (∑ k, z k * R.q (f (b k))) := by
    intro f hf
    refine Submodule.span_induction (p := fun f _ => T (∑ k, z k * R.q (f (b k)))) ?_ ?_ ?_ ?_ hf
    · exact fun f hf => h f hf
    · simpa using h0
    · intro f f' _ _ h1 h2
      simp only [LinearMap.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      exact hadd _ _ h1 h2
    · intro c f _ h1
      have e : ∑ k, z k * R.q ((c • f) (b k)) = R.q c * ∑ k, z k * R.q (f (b k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [LinearMap.smul_apply, smul_eq_mul, map_mul]
        ring
      show T (∑ k, z k * R.q ((c • f) (b k)))
      rw [e]
      exact hsmul c _ h1
  have := hall (b.coord k0) (by rw [hA]; trivial)
  have e : ∑ k, z k * R.q (b.coord k0 (b k)) = z k0 := by
    rw [Finset.sum_eq_single k0]
    · simp
    · intro k _ hk
      simp [Module.Basis.coord_apply, hk]
    · simp
  rwa [e] at this

theorem conn (P : Pre G R) (hR : R.Facts) (hE : EtSide G) (M : Model l K) (hM : G M) (d : ℕ) (hc : M.Conn d)
    (n : ℕ) : P.Inj M n ∧ P.Strict M n := by
  obtain ⟨hsub, hdual⟩ := hE.dual M hM d hc
  by_cases hn : 2 * d < n
  · have := hsub n hn
    exact ⟨fun b z _ => funext fun i => absurd (Subsingleton.elim (b i) 0) (b.ne_zero i),
      fun b z _ i => absurd (Subsingleton.elim (b i) 0) (b.ne_zero i)⟩
  replace hn : n ≤ 2 * d := by omega
  obtain ⟨j, hj⟩ : ∃ j, n + j = 2 * d := ⟨2 * d - n, by omega⟩
  obtain ⟨r, g, hg, htr, hspan⟩ := hdual n j hj
  obtain ⟨v, φ, hu⟩ : ∃ (v : M.V (n + j)) (φ : Module.Dual K (HdR M.q (n + j))),
      R.IsU (R.tB ^ d * P.c M (n + j) v φ) := by
    have key : ∀ k, k = 2 * d → ∃ (v : M.V k) (φ : Module.Dual K (HdR M.q k)), R.IsU (R.tB ^ d * P.c M k v φ) := by
      rintro k rfl
      exact P.c1 M hM d hc
    exact key _ hj
  have hfil : ∀ s, R.tB ^ d * P.c M (n + j) (g s) φ ∈ R.P := fun s =>
    P.fil M (n + j) hM d (g s) φ (fun x hx => by rw [P.top M hM d hc (n + j) x hx, map_zero])
  have hv : v ∈ Submodule.span ℚ_[l] (Set.range g) := by rw [hg]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).mp hv
  have e1 : R.tB ^ d * P.c M (n + j) v φ = ∑ s, R.q (a s) * (R.tB ^ d * P.c M (n + j) (g s) φ) := by
    rw [← ha, map_sum, AddMonoidHom.finsetSum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [P.lin]
    ring
  rw [e1] at hu
  obtain ⟨s0, hs0⟩ := isU_sum hR Finset.univ _ (fun s => R.P.mul_mem (hR.q_mem _) (hfil s)) hu
  have h0 := isU_of_mul (hR.q_mem _) (hfil s0) hs0
  have hall : ∀ s, R.IsU (R.tB ^ d * P.c M (n + j) (g s) φ) := by
    intro s
    obtain ⟨σ, ζ, -, he⟩ := htr s0 s
    have := isU_σ hR σ h0
    rw [map_mul, map_pow, ← P.equi M (n + j) hM σ, he, P.lin] at this
    obtain ⟨u, hu, hut⟩ := hR.galois_t_transform σ
    rw [hut, mul_pow] at this
    have e : u ^ d * R.tB ^ d * (R.q ζ * P.c M (n + j) (g s) φ) =
        (u ^ d * R.q ζ) * (R.tB ^ d * P.c M (n + j) (g s) φ) := by ring
    rw [e] at this
    exact isU_of_mul (R.P.mul_mem (R.P.pow_mem hu.1 _) (hR.q_mem _)) (hfil s) this
  have hne : ∀ s, P.c M (n + j) (g s) φ ≠ 0 := by
    intro s h
    have := hall s
    rw [h, mul_zero] at this
    exact not_isU_zero this
  obtain ⟨hfin_i, htop_i⟩ := P.fin M hM n
  obtain ⟨hfin_j, htop_j⟩ := P.fin M hM j
  have := hfin_i
  have := hfin_j
  obtain ⟨m, β, w, hβ⟩ := wt_basis (K := K) (FilR M.q n) (filR_anti M.q n) (filR_zero M.q n) (n + 1) htop_i
  obtain ⟨m', β', w', hβ'⟩ := wt_basis (K := K) (FilR M.q j) (filR_anti M.q j) (filR_zero M.q j) (j + 1) htop_j
  refine ⟨fun {a'} b z hz => ?_, fun {a'} b z hz => ?_⟩
  · funext k
    refine coords _ hspan (fun x => x = 0) rfl (fun x y hx hy => by rw [hx, hy, add_zero])
      (fun c x hx => by rw [hx, mul_zero]) b z ?_ k
    rintro f ⟨s, y, hf⟩
    have e := key P M hM b z (g s) y f hf β β' φ
    simp only [hz, zero_mul, Finset.sum_const_zero] at e
    exact (mul_eq_zero.mp e).resolve_right (hne s)
  · refine coords _ hspan (fun x => x ∈ R.P) R.P.zero_mem (fun x y hx hy => R.P.add_mem hx hy)
      (fun c x hx => R.P.mul_mem (hR.q_mem c) hx) b z ?_
    rintro f ⟨s, y, hf⟩
    have e := key P M hM b z (g s) y f hf β β' φ
    have hp := cup_fil R.P R.tB hR.t_mem R.o hR.o_mem (FilR M.q n) (FilR M.q j) (FilR M.q (n + j))
      (P.cupR M n j) (P.cupR_fil M hM n j) d
      (fun e hde x hx => P.top M hM d hc (n + j) x (filR_anti M.q (n + j) (by omega : d + 1 ≤ e) hx))
      β w hβ β' w' hβ' (fun ψ => ∑ k, z k * P.c M n (b k) ψ) (fun r ψ h => hz r ψ h)
      (fun ψ => P.c M j (M.toV j y) ψ) (fun r ψ h => P.fil M j hM r _ ψ h) φ
    rw [← e, mul_comm, mul_assoc, mul_comm (P.c M (n + j) (g s) φ)] at hp
    exact mem_of_mul_isU hp (hall s)

end CrystallineSemistableComparison.Inj
