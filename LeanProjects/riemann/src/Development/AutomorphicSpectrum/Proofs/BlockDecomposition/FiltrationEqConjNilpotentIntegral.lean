import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.IwJac.FiltTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_le_one_of_ord {ϖ : kˣ} (h : ord k ϖ = 1) : valuation k (ϖ : k) ≤ 1 := by
  have h' : -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (valuation k (ϖ : k))) = 1 := h
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (valuation k (ϖ : k)) ≠ 0 := by simp
  have h1 : WithZero.log (φ (valuation k (ϖ : k))) = -1 := by omega
  rw [← φ.strictMono.le_iff_le, map_one, ← WithZero.exp_log h0, h1, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem tor_neg (ϖ : kˣ) (x : Fin n → ℤ) : tor ϖ (-x) = (tor ϖ x)⁻¹ := by
  unfold tor; rw [← map_inv]; congr 1; funext i; simp [_root_.zpow_neg]

theorem conj_tor_apply (ϖ : kˣ) (y : Fin n → ℤ) (m : GL (Fin n) k) (i j : Fin n) :
    ((MulAut.conj (tor ϖ y) m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ (y i - y j) : kˣ) : k) * (m : Matrix (Fin n) (Fin n) k) i j := by
  rw [MulAut.conj_apply, ← tor_neg, Units.val_mul, Units.val_mul]
  unfold tor
  rw [val_diagT, val_diagT, mul_diagonal, diagonal_mul, _root_.zpow_sub]
  simp only [Pi.neg_apply, _root_.zpow_neg, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

theorem int_of_mem_KO {m : GL (Fin n) k} (h : m ∈ GlobalTheory.SplitWeil.KO k (Fin n)) (i j : Fin n) :
    valuation k ((m : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
  obtain ⟨u, rfl⟩ := h
  exact (u.val i j).2

theorem mem_KO_of_int {g : GL (Fin n) k}
    (h1 : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    g ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  have inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hB : (algebraMap 𝒪[k] k).mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_nO_of {g : GL (Fin n) k} (hg : g ∈ unipB k (Fin n))
    (h1 : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    g ∈ nO k n := by
  refine ⟨mem_iwahori.2 ⟨mem_KO_of_int h1 h2, fun i j hji => ?_⟩, hg⟩
  rw [((mem_unipB k).1 hg).1 i j hji, map_zero]
  exact zero_lt_one

theorem conj_mem_nO {ϖ : kˣ} {y : Fin n → ℤ} {m : GL (Fin n) k} (hm : m ∈ unipB k (Fin n))
    (h1 : ∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * (m : Matrix (Fin n) (Fin n) k) i j) ≤ 1)
    (h2 : ∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1) :
    MulAut.conj (tor ϖ y) m ∈ nO k n := by
  have hu : ∀ m' ∈ unipB k (Fin n), (∀ i j, i < j →
      valuation k (((ϖ ^ (y i - y j) : kˣ) : k) * (m' : Matrix (Fin n) (Fin n) k) i j) ≤ 1) →
      MulAut.conj (tor ϖ y) m' ∈ unipB k (Fin n) ∧
        ∀ i j, valuation k (((MulAut.conj (tor ϖ y) m' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro m' hm' h
    obtain ⟨h0, hd⟩ := (mem_unipB k).1 hm'
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i j => ?_⟩
    · rw [conj_tor_apply, h0 i j hji, mul_zero]
    · rw [conj_tor_apply, hd, sub_self, zpow_zero, Units.val_one, mul_one]
    · rw [conj_tor_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact h i j hij
      · rw [hd, sub_self, zpow_zero, Units.val_one, mul_one, map_one]
      · rw [h0 i j hij, mul_zero, map_zero]; exact zero_le'
  obtain ⟨a1, a2⟩ := hu m hm h1
  obtain ⟨_, b2⟩ := hu m⁻¹ (inv_mem hm) h2
  exact mem_nO_of a1 a2 (by rw [← map_inv]; exact b2)

theorem filt_top (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ) (hϖ : ord k ϖ = 1) (x : Fin n → ℤ) (hx : StrictAnti x) :
    filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom := by
  have hv := val_le_one_of_ord hϖ
  have pint : ∀ i j : Fin n, i < j → valuation k ((ϖ ^ (x i - x j) : kˣ) : k) ≤ 1 := by
    intro i j hij
    obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (hx hij).le)
    rw [he, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one₀ zero_le' hv
  have cancel : ∀ i j : Fin n, valuation k ((ϖ ^ ((-x) i - (-x) j) : kˣ) : k) *
      valuation k ((ϖ ^ (x i - x j) : kˣ) : k) = 1 := by
    intro i j
    rw [← map_mul, ← Units.val_mul, ← _root_.zpow_add,
      show (-x) i - (-x) j + (x i - x j) = 0 by simp only [Pi.neg_apply]; ring,
      zpow_zero, Units.val_one, map_one]
  ext g
  rw [Subgroup.mem_map, mem_filt]
  constructor
  · rintro ⟨hg, dg, dg'⟩
    refine ⟨MulAut.conj (tor ϖ (-x)) g, conj_mem_nO hg.2 (fun i j hij => ?_) (fun i j hij => ?_), ?_⟩
    · rw [map_mul, ← cancel i j]
      exact mul_le_mul_right (dg i j hij (by have := j.isLt; omega)) _
    · rw [map_mul, ← cancel i j]
      exact mul_le_mul_right (dg' i j hij (by have := j.isLt; omega)) _
    · show MulAut.conj (tor ϖ x) (MulAut.conj (tor ϖ (-x)) g) = g
      rw [tor_neg]
      simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨m, hm, rfl⟩
    show MulAut.conj (tor ϖ x) m ∈ nO k n ∧ Deep ϖ x n (MulAut.conj (tor ϖ x) m) ∧
      Deep ϖ x n (MulAut.conj (tor ϖ x) m)⁻¹
    have key : ∀ m' ∈ nO k n, ∀ i j : Fin n,
        valuation k (((ϖ ^ (x i - x j) : kˣ) : k) * (m' : Matrix (Fin n) (Fin n) k) i j) ≤
          valuation k ((ϖ ^ (x i - x j) : kˣ) : k) := by
      intro m' hm' i j
      rw [map_mul]
      exact mul_le_of_le_one_right' (int_of_mem_KO (iwahori_le_KO k (Fin n) hm'.1) i j)
    have hm' := inv_mem hm
    refine ⟨conj_mem_nO hm.2 (fun i j hij => (key m hm i j).trans (pint i j hij))
      (fun i j hij => (key _ hm' i j).trans (pint i j hij)), fun i j _ _ => ?_, fun i j _ _ => ?_⟩
    · rw [conj_tor_apply]; exact key m hm i j
    · rw [← map_inv, conj_tor_apply]; exact key _ hm' i j

theorem filt_top' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
      filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom :=
  fun k _ _ _ _ n ϖ hϖ x hx => filt_top k n ϖ hϖ x hx

end GlobalTheory.CompanionTheory.IwJac.FiltTop

end
