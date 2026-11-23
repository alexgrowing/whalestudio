import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.UnfoldedLatticeData

noncomputable section

namespace GlobalTheory.PadicUnfold

open Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData

variable {g : ℕ} [Fact g.Prime]

def Dv (g : ℕ) [Fact g.Prime] (a : ℤ) (x : ℚ_[g]) : Prop := ∃ u : ℤ_[g], x = (g : ℚ_[g]) ^ a * (u : ℚ_[g])

theorem g_ne : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero

theorem Dv.zero (a : ℤ) : Dv g a 0 := ⟨0, by simp⟩

theorem Dv.add {a : ℤ} {x y : ℚ_[g]} (hx : Dv g a x) (hy : Dv g a y) : Dv g a (x + y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact ⟨u + w, by simp [mul_add]⟩

theorem Dv.mul {a b : ℤ} {x y : ℚ_[g]} (hx : Dv g a x) (hy : Dv g b y) : Dv g (a + b) (x * y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  exact ⟨u * w, by rw [zpow_add₀ g_ne]; push_cast; ring⟩

theorem Dv.pow (a : ℤ) : Dv g a ((g : ℚ_[g]) ^ a) := ⟨1, by simp⟩

theorem Dv.mono {a b : ℤ} {x : ℚ_[g]} (h : a ≤ b) (hx : Dv g b x) : Dv g a x := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Int.le.dest h
  exact ⟨(g : ℤ_[g]) ^ k * u, by rw [zpow_add₀ g_ne]; push_cast; rw [zpow_natCast]; ring⟩

def eSt (n : ℕ) (l : ℕ) : ℕ := if l < n then 0 else l - n + 1

theorem eN_eq {k : Type} [CommRing k] {N : ℕ} (s : Fin N) : Loc.eN k N s.1 = Pi.single s 1 := by
  funext l
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem atN_eq {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (l : Fin N) : Loc.atN v l.1 = v l := by
  simp [Loc.atN]

section Affine

variable {k : Type} [CommRing k] {n' c' n c : ℕ}

theorem linearMap_unfolding_apply_single (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : Loc.FC n' c' n c → k)
    (s : Fin (n' + c')) (l : Fin (n + c)) :
    Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then
        (if hl : l.1 < n then xj (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  simp [Loc.xx1, Matrix.toLin'_apply, LinearMap.toMatrix'_apply]

def frM (τ : Loc.FC n' c' n c → k) : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : Loc.IsFree n' n c l.1 s.1 then τ ⟨(l, s), hf⟩ else 0)

theorem hom_ext {a b : ℕ} {x y : (Fin a → k) →ₗ[k] (Fin b → k)}
    (h : ∀ s l, x (Pi.single s 1) l = y (Pi.single s 1) l) : x = y := by
  refine LinearMap.pi_ext' fun s => LinearMap.ext_ring ?_
  funext l
  simpa using h s l

theorem chArg_add (x y : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) :
    Loc.chArg (x + y) = Loc.chArg x + Loc.chArg y := by
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Loc.atN
  split_ifs <;> simp

theorem chArg_eq (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) :
    Loc.chArg x = ∑ i : Fin c,
      x (Pi.single ⟨n' + i.1 + 1, by omega⟩ 1) ⟨n + i.1, by omega⟩ := by
  unfold Loc.chArg
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← eN_eq]
  exact atN_eq _ ⟨n + i.1, by omega⟩

end Affine

def integrand {n' n c : ℕ} (ψ : AddChar ℚ_[g] ℂ) (G : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
    (xj : HomQ g n' n) (t : Loc.FC n' (c + 1) n c → ℚ_[g]) : ℂ :=
  G (Loc.xx1 xj t) * ψ (-Loc.chArg (Loc.xx1 xj t))

def sumModG {n' n c : ℕ} (ψ : AddChar ℚ_[g] ℂ) (G : Loc.SF ℚ_[g] ℂ (n' + (c + 1)) (n + c))
    (xj : HomQ g n' n) : ℂ :=
  ∑ k ∈ Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => Finset.range g,
    integrand ψ G xj fun p => (g : ℚ_[g]) ^ ((eSt n p.1.1.1 : ℤ) - eSt n' p.1.2.1) * (k p : ℚ_[g])

abbrev NPos (n c : ℕ) : Type := {p : Fin (n + c) × Fin (n + c) // n < p.2.1 ∧ p.1.1 < p.2.1}

def Ncong (g : ℕ) [Fact g.Prime] (n c M : ℕ) : Subgroup (Aut g (n + c)) where
  carrier := {r | r ∈ Loc.N1 ℚ_[g] n c ⊓ GLlat (lamSt g n c) ∧
    ∀ v ∈ lamSt g n c, ∃ u ∈ lamSt g n c, r v - v = (g : ℚ_[g]) ^ M • u}
  one_mem' := ⟨one_mem _, fun v _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v hv => by
    obtain ⟨u, hu, e⟩ := hb.2 v hv
    obtain ⟨w, hw, e'⟩ := ha.2 (b v) ((hb.1.2 v).2 hv)
    refine ⟨w + u, add_mem hw hu, ?_⟩
    rw [smul_add, ← e, ← e']
    show a (b v) - v = _
    abel⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v hv => by
    obtain ⟨u, hu, e⟩ := ha.2 (a.symm v) (((inv_mem ha.1 : a⁻¹ ∈ _).2 v).2 hv)
    refine ⟨-u, neg_mem hu, ?_⟩
    rw [smul_neg, ← e, LinearEquiv.apply_symm_apply]
    show a.symm v - v = _
    abel⟩

end GlobalTheory.PadicUnfold
