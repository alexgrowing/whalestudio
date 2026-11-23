import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.IwaCell

variable {k : Type} [Field k] {m : ℕ}

def tD (ϖ : kˣ) (a : Fin m → ℤ) : GL (Fin m) k := diagT k (Fin m) fun i => ϖ ^ a i

variable [ValuativeRel k]

def cell (ϖ : kˣ) (a : Fin m → ℤ) : Set (GL (Fin m) k) :=
  {g | ∃ u ∈ unipB k (Fin m), ∃ κ ∈ KO k (Fin m), g = u * tD ϖ a * κ}

variable (m) in

def wt (a : Fin m → ℤ) : ℤ := ∑ i : Fin m, ((m : ℤ) - 1 - 2 * (i : ℕ)) * a i

theorem val_tD (ϖ : kˣ) (a : Fin m → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  val_diagT k _

theorem tD_add (ϖ : kˣ) (a b : Fin m → ℤ) : tD ϖ (a + b) = tD ϖ a * tD ϖ b := by
  rw [tD, tD, tD, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem mul_mem_cell {ϖ : kˣ} {a : Fin m → ℤ} {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) {κ : GL (Fin m) k}
    (hκ : κ ∈ KO k (Fin m)) : u * tD ϖ a * κ ∈ cell ϖ a := ⟨u, hu, κ, hκ, rfl⟩

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tD_zero (ϖ : kˣ) : tD ϖ (0 : Fin m → ℤ) = 1 := by
  rw [tD, ← map_one (diagT k (Fin m))]
  congr 1
  funext i
  simp

theorem tD_neg (ϖ : kˣ) (a : Fin m → ℤ) : tD ϖ (-a) = (tD ϖ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← tD_add, neg_add_cancel, tD_zero])

theorem diag_entry (ϖ : kˣ) (s t : Fin m → ℤ) {w : GL (Fin m) k} (hw : w ∈ unipB k (Fin m)) (i : Fin m) :
    (tD ϖ s * w * tD ϖ t).val i i = ((ϖ ^ (s i + t i) : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD, val_tD, Matrix.mul_diagonal, Matrix.diagonal_mul, ((mem_unipB k).1 hw).2 i,
    mul_one, _root_.zpow_add, Units.val_mul]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x n
  have h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd (o x ^ n) := congrArg _ h
  simpa [o, mul_comm] using h2

theorem eq_of_mem_cell {ϖ : kˣ} (hϖ : ord k ϖ = 1) {a b : Fin m → ℤ} {g : GL (Fin m) k} (ha : g ∈ cell ϖ a)
    (hb : g ∈ cell ϖ b) : a = b := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ := ha
  obtain ⟨u', hu', κ', hκ', e⟩ := hb
  have hw : u'⁻¹ * u ∈ unipB k (Fin m) := mul_mem (inv_mem hu') hu
  have hx : tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a = κ' * κ⁻¹ := by
    rw [tD_neg]
    calc (tD ϖ b)⁻¹ * (u'⁻¹ * u) * tD ϖ a = (u' * tD ϖ b)⁻¹ * (u * tD ϖ a * κ) * κ⁻¹ := by group
      _ = (u' * tD ϖ b)⁻¹ * (u' * tD ϖ b * κ') * κ⁻¹ := by rw [e]
      _ = κ' * κ⁻¹ := by group
  have hxi : (tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a)⁻¹ = tD ϖ (-a) * (u'⁻¹ * u)⁻¹ * tD ϖ b := by
    simp only [tD_neg, _root_.mul_inv_rev, inv_inv]; group
  have hK := (GlobalTheory.SplitFlip.mem_KO_iff _).1 (hx ▸ mul_mem hκ' (inv_mem hκ))
  funext i
  have h1 := hK.1 i i
  have h2 := hK.2 i i
  rw [diag_entry ϖ _ _ hw] at h1
  rw [hxi, diag_entry ϖ _ _ (inv_mem hw)] at h2
  simp only [Pi.neg_apply] at h1 h2
  set y : kˣ := ϖ ^ (-b i + a i)
  have h2' : ((y⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    have : (ϖ ^ (-a i + b i) : kˣ) = y⁻¹ := by rw [← _root_.zpow_neg]; congr 1; ring
    rwa [this] at h2
  have v1 : valuation k (y : k) ≤ 1 := h1
  have v2 : valuation k ((y⁻¹ : kˣ) : k) ≤ 1 := h2'
  have hv : valuation k (y : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀] at v2
    have hpos : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
    exact le_antisymm v1 ((inv_le_one₀ hpos).1 v2)
  have h3 := ord_eq_zero hv
  rw [ord_zpow, hϖ, mul_one] at h3
  omega

end GlobalTheory.IwaCell
