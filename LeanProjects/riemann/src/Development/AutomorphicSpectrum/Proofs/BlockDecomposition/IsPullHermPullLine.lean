import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev Bk (n : Fin (m + 1) → ℕ) : Fin (m + 1) → Type := fun c => Fin (n c + 1)

abbrev σ₀ : ℤ →+* ℂ := Int.castRingHom ℂ

abbrev prB (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) : MP ℤ m n ⟶ PSpace ℤ (n k) := pr ℤ m n k

abbrev blockChart (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) (i : Bk n k) : (MP ℤ m n).Opens :=
  prB n k ⁻¹ᵁ chart ℤ (n k) i

def mchart (c : ∀ k, Bk n k) : (MP ℤ m n).Opens :=
  ⟨⋂ k, (blockChart n k (c k) : Set (MP ℤ m n)),
    isOpen_iInter_of_finite fun k => (blockChart n k (c k)).isOpen⟩

theorem mchart_le (c : ∀ k, Bk n k) (k : Fin (m + 1)) : mchart c ≤ blockChart n k (c k) :=
  fun _ hx => Set.mem_iInter.1 hx k

def blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) : Γ(MP ℤ m n, W)ˣ :=
  res h (pullU (prB n k) _ (ratioUnit _ i j inf_le_left inf_le_right))

def ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : Bk n k :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose

theorem mem_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : x ∈ blockChart n k (ptChart x k) :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose_spec

def ptCoord (x : MP ℤ m n) (p : Σ k, Bk n k) : (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (blockChart n p.1 (ptChart x p.1)) x (mem_ptChart x p.1)).hom
    (pullRatio (prB n p.1) _ (ptChart x p.1) le_rfl p.2)

def ptIdeal (x : MP ℤ m n) : Ideal (Geo.MRing (Bk n)) := Geo.mCoordIdeal (ptCoord x)

def IsUnder (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) : Prop :=
  ∀ (k : Fin (m + 1)) (i : Bk n k), (y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0) ∧
    ∀ j : Bk n k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) →
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y = z ⟨k, j⟩ / z ⟨k, i⟩

def IsHermRep (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) : Prop :=
  ∃ u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) (u j c) =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) (u i c) =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) ∧
    ∀ (i : M.B.ι) (c : ∀ k, Bk n k) (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder y z →
      y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) →
      A.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) *
        ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
          Real.exp ((M.φ σ₀).φ i y / 2)

abbrev consN (n' : ℕ) (n : Fin (m + 1) → ℕ) : Fin (m + 2) → ℕ := Fin.cons n' n

def sv (n' : ℕ) (n : Fin (m + 1) → ℕ) : (Σ k, Bk n k) → Σ k', Bk (consN n' n) k' :=
  fun p => ⟨p.1.succ, p.2⟩

theorem isBlockMap_sv (n' : ℕ) (n : Fin (m + 1) → ℕ) :
    IsBlockMap (ι := Bk n) (ι' := Bk (consN n' n)) Fin.succ (sv n' n) := by
  refine ⟨Fin.succ_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', j⟩ h
    have hk : k.succ = k'.succ := congrArg Sigma.fst h
    obtain rfl : k = k' := Fin.succ_injective _ hk
    have h' : (⟨k.succ, i⟩ : Σ k', Bk (consN n' n) k') = ⟨k.succ, j⟩ := h
    have hij : i = j := sigma_mk_injective (β := Bk (consN n' n)) (i := k.succ) h'
    rw [hij]
  · rintro ⟨k', j⟩ ⟨k, rfl⟩
    exact ⟨⟨k, j⟩, rfl⟩

def pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) : Geo.HermLine (Bk (consN n' n)) where
  a := pullDeg Fin.succ A.a
  h z := A.h fun p => z (sv n' n p)
  pos z hz := A.pos _ fun k => hz k.succ
  smul c z hc := by
    have e := A.smul (fun k => c k.succ) (fun p => z (sv n' n p)) fun k => hc k.succ
    refine e.trans ?_
    have h0 : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a 0 = 0 := by
      unfold pullDeg
      rw [Function.extend_apply']
      · rfl
      · rintro ⟨k, hk⟩
        exact Fin.succ_ne_zero k hk
    have hs (k : Fin (m + 1)) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a k.succ = A.a k :=
      (Fin.succ_injective _).extend_apply _ _ _
    rw [Fin.prod_univ_succ (fun k' => ‖c k'‖ ^ pullDeg Fin.succ A.a k'), h0, zpow_zero, one_mul]
    simp only [hs]

theorem isPullHerm_pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) :
    IsPullHerm Fin.succ (sv n' n) A (pullLine n' A) :=
  ⟨rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.MPDict
