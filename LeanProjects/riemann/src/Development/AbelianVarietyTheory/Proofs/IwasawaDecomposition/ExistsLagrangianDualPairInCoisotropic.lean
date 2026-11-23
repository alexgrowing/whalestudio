import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Module

theorem exists_lagrangian_dual_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  classical
  intro r M W hskew hdet hW
  set B : LinearMap.BilinForm ℝ (Fin r → ℝ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hrefl : B.IsRefl := fun x y h => by rw [hskewB, h, neg_zero]
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℝ (Fin r → ℝ), L ≤ W ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℝ L = n
  have P0 : P 0 := ⟨⊥, bot_le, by simp, finrank_bot ℝ _⟩
  obtain ⟨L, hLW, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hmax : ∀ v ∈ W, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvW hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℝ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℝ {v}, ∀ y ∈ L ⊔ Submodule.span ℝ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add, map_smul, h1, h2, h3, h4]
    have hle : L ⊔ Submodule.span ℝ {v} ≤ W :=
      sup_le hLW (by rw [Submodule.span_le]; simpa using hvW)
    have hP : P (finrank ℝ ↥(L ⊔ Submodule.span ℝ {v})) := ⟨_, hle, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℝ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hWo : B.orthogonal W ≤ L := by
    intro x hx
    have hxW : x ∈ W := hW x (fun w hw => by rw [← hB, hskewB, hx w hw, neg_zero])
    exact hmax x hxW (fun l hl => by rw [hskewB, hx l (hLW hl), neg_zero])
  let b := Module.finBasis ℝ L
  let e : Fin (finrank ℝ L) → Fin r → ℝ := fun i => ((b i : L) : Fin r → ℝ)
  have heL : ∀ i, e i ∈ L := fun i => (b i).2
  have hext : ∀ (φ : (Fin r → ℝ) →ₗ[ℝ] ℝ), (∀ j, φ (e j) = 0) → ∀ l ∈ L, φ l = 0 := by
    intro φ hφ l hl
    have : φ ∘ₗ L.subtype = 0 := b.ext (fun j => by simpa using hφ j)
    simpa using LinearMap.congr_fun this ⟨l, hl⟩
  let φ : (Fin r → ℝ) →ₗ[ℝ] (Fin (finrank ℝ L) → ℝ) := LinearMap.pi (fun j => B.flip (e j))
  have hφ : ∀ v j, φ v j = B v (e j) := fun v j => rfl
  have hker : LinearMap.ker φ = B.orthogonal L := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h l hl
      have h' := hext (B v) (fun j => by rw [← hφ, h]; rfl) l hl
      rw [hskewB, h', neg_zero]
    · intro h
      funext j
      rw [Pi.zero_apply, hφ, hskewB, h _ (heL j), neg_zero]
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    have h2 : finrank ℝ L ≤ r := by simpa using Submodule.finrank_le L
    simp only [Module.finrank_fin_fun] at h1 ⊢
    omega
  have hsurj : ∀ y, ∃ x, φ x = y := fun y => by
    have : y ∈ LinearMap.range φ := by rw [hrange]; trivial
    exact this
  choose f hf using fun i : Fin (finrank ℝ L) => hsurj (Pi.single i 1)
  have hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hφ, hf i, Pi.single_apply]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  refine ⟨finrank ℝ L, e, f, fun i => hLW (heL i),
    fun i j => by rw [← hB]; exact hLiso _ (heL i) _ (heL j),
    fun i j => by rw [← hB]; exact hfe i j, ?_⟩
  set U := Submodule.span ℝ (Set.range (Sum.elim e f)) with hU
  have hUo : B.orthogonal U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hve : ∀ j, B (e j) v = 0 := fun j => hv _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    have hvf : ∀ i, B (f i) v = 0 := fun i => hv _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
    have hvL : ∀ l ∈ L, B v l = 0 := hext (B v) (fun j => by rw [hskewB, hve j, neg_zero])
    have hvW : v ∈ W := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
      intro x hx
      rw [hskewB, hvL x (hWo hx), neg_zero]
    have hvL' : v ∈ L := hmax v hvW hvL
    have hv' : v = ∑ j, b.repr ⟨v, hvL'⟩ j • e j := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hvL'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hc : ∀ i, b.repr ⟨v, hvL'⟩ i = 0 := by
      intro i
      have h := hvf i
      rw [hv', map_sum] at h
      simpa [map_smul, hfe] using h
    have h0 : (⟨v, hvL'⟩ : L) = 0 := b.repr.injective (by ext i; simp [hc])
    simpa using congrArg Subtype.val h0
  have hdimU := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [hUo, finrank_bot] at hdimU
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le U
  simp only [Module.finrank_fin_fun] at hdimU this ⊢
  omega

end GlobalTheory
