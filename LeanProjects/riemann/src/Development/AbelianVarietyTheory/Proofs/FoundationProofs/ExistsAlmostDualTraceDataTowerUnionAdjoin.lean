import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationAlmostEtaleTowerFixerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinOfGaloisFixedStatement

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.TrTower

section Sep

variable {L : Type*} [Field L] {G : Type*} [Group G] [MulSemiringAction G L]

theorem isSep_mul_right {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) {d : L} (hd : d ∈ Fix L N) (hdv : v d ≤ 1) (hcd : v (c * d) ≤ 1) :
    IsSep v N (fun i => a i * d) b (c * d) where
  a_mem i := mul_mem (h.a_mem i) hd
  b_mem := h.b_mem
  c_mem := mul_mem h.c_mem hd
  a_le i := by rw [map_mul]; exact mul_le_one' (h.a_le i) hdv
  b_le := h.b_le
  c_le := hcd
  sum_in σ hσ := by
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_in σ hσ]
  sum_out σ hσ := by
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_out σ hσ, zero_mul]

theorem isSep_swap {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) : IsSep v N b a c where
  a_mem := h.b_mem
  b_mem := h.a_mem
  c_mem := h.c_mem
  a_le := h.b_le
  b_le := h.a_le
  c_le := h.c_le
  sum_in σ hσ := by
    have h1 := congrArg (σ • ·) (h.sum_in σ⁻¹ (inv_mem hσ))
    have hc : σ • c = c := h.c_mem ⟨σ, hσ⟩
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, hc] at h1
    simpa [mul_comm] using h1
  sum_out σ hσ := by
    have h1 := congrArg (σ • ·) (h.sum_out σ⁻¹ (fun h' => hσ (by simpa using inv_mem h')))
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, smul_zero] at h1
    simpa [mul_comm] using h1

end Sep

section Tower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fixInt {H : Subgroup (Gal p Ω)} (V : Subgroup H) :
    Subalgebra (O0 p) (integralClosure (O0 p) Ω) where
  carrier := {s | ∀ g : V, g • (s : Ω) = s}
  mul_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_mul] at *
    rw [smul_mul', hx g, hy g]
  add_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
    rw [smul_add, hx g, hy g]
  algebraMap_mem' r g := by
    show g • (algebraMap (O0 p) Ω r) = _
    exact ((g : H) : Gal p Ω).commutes r

theorem towerAlg_fixed (T : Tower p Ω) {s : integralClosure (O0 p) Ω} (hs : s ∈ towerAlg T)
    (g : ↥(⨅ n, Gn T n)) : g • (s : Ω) = s := by
  have hle : towerAlg T ≤ fixInt (⊤ : Subgroup ↥(⨅ n, Gn T n)) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩) g
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).1
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).2
  exact hle hs ⟨g, trivial⟩

end Tower

end GlobalTheory.AlmostEt.TrTower

namespace GlobalTheory.AlmostEt.TrTower

theorem exists_trData_towerAlg : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (F : Finset (integralClosure (O0 p) Ω)),
    ∃ (C : Subalgebra (O0 p) (integralClosure (O0 p) Ω))
      (tr : (integralClosure (O0 p) Ω) → (integralClosure (O0 p) Ω)) (n : ℕ)
      (a b : Fin n → (integralClosure (O0 p) Ω)),
      (↑F : Set (integralClosure (O0 p) Ω)) ⊆ C ∧
        IsTrData (towerAlg T) C tr a b (p : (integralClosure (O0 p) Ω)) := by
  intro p _ Ω _ _ hp2 hclo T F
  classical
  have hpcoe : ((p : integralClosure (O0 p) Ω) : Ω) = p := map_natCast (integralClosure (O0 p) Ω).val p
  obtain ⟨v, hvint, hvinv, hp0, hp1, hS⟩ := GlobalTheory.T.exists_valuation_almostEtale_towerFixer p Ω hp2 hclo T
  obtain ⟨U, -, hUfin, hUfix, hUsep⟩ := hS (F.image Subtype.val)
  obtain ⟨n, a, b, c, hsep, hc⟩ := hUsep (v p) hp1
  haveI := hUfin
  haveI : Fintype (↥(⨅ n, Gn T n) ⧸ U) := Fintype.ofFinite _
  have hvinv' : ∀ (g : ↥(⨅ n, Gn T n)) (x : Ω), v (g • x) = v x := fun g x => hvinv g x
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (not_lt_zero' hc)
  have hvc : 0 < v c := lt_of_le_of_lt (by positivity) hc

  have hpfix : ∀ (g : ↥(⨅ n, Gn T n)), g • (p : Ω) = p := fun g => by
    change ((g : Gal p Ω)) (p : Ω) = p
    exact map_natCast _ p
  have hd : (p : Ω) / c ∈ Fix Ω U := div_mem (fun g => hpfix g) hsep.c_mem
  have hdv : v ((p : Ω) / c) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ hc.le (by positivity)
  have hsep' : IsSep v U (fun i => a i * ((p : Ω) / c)) b (p : Ω) := by
    have := isSep_mul_right hsep hd hdv (by rw [mul_div_cancel₀ _ hc0]; exact hp1.le)
    rwa [mul_div_cancel₀ _ hc0] at this
  have hsw := isSep_swap hsep'
  have hint : ∀ x : Ω, v x ≤ 1 → x ∈ integralClosure (O0 p) Ω := fun x hx => (hvint x).1 hx
  let a' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.a_le i)⟩
  let b' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.b_le i)⟩
  have htrint : ∀ s : integralClosure (O0 p) Ω, cosetTrace U (s : Ω) ∈ integralClosure (O0 p) Ω :=
    fun s => Subalgebra.sum_mem _ fun q _ => GlobalTheory.K5.Basic.isInt_gal _ s.2
  let tr : integralClosure (O0 p) Ω → integralClosure (O0 p) Ω := fun s => ⟨_, htrint s⟩
  have htr : ∀ s, (tr s : Ω) = cosetTrace U (s : Ω) := fun s => rfl
  have hle : towerAlg T ≤ fixInt U := fun s hs g => towerAlg_fixed T hs (g : ↥(⨅ n, Gn T n))
  refine ⟨fixInt U, tr, n, a', b', ?_, ?_⟩
  · intro s hs
    exact hUfix _ (Finset.mem_image_of_mem _ hs)
  refine
    { le := hle
      e_mem := Subalgebra.natCast_mem _ p
      a_mem := fun i => hsep'.a_mem i
      b_mem := fun i => hsep'.b_mem i
      tr_mem := ?_
      tr_add := ?_
      tr_mul := ?_
      left := ?_
      right := ?_
      sum := ?_ }
  · intro x hx
    apply GlobalTheory.T.mem_towerUnionAdjoin_of_galois_fixed p Ω hclo T
    intro g hg
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).1 ⟨g, hg⟩
  · intro x _ y _
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_add, cosetTrace, smul_add, Finset.sum_add_distrib]
  · intro β hβ x hx
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_mul]
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).2.2 _ (towerAlg_fixed T hβ)
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsep' _ hx
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsw _ hx
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum]
    simpa using hsep'.sum_in 1 (one_mem _)

end GlobalTheory.AlmostEt.TrTower
