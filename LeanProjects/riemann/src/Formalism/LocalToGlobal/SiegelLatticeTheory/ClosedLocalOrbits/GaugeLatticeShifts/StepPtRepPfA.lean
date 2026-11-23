import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem

noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting

section Calc

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_apply (x y : Fin n → ℂ) :
    hJ ε x y = ∑ i, star (x i) * ((if ε i then 1 else -1) * y i) := by
  simp [hJ, Formalism.REAL.Jm, dotProduct, mulVec_diagonal]

theorem hJ_conj (x y : Fin n → ℂ) : star (hJ ε x y) = hJ ε y x := by
  rw [hJ_apply, hJ_apply, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h] <;> ring

theorem hJ_add_right (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, mulVec_add, dotProduct_add]

theorem hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  simp only [hJ, star_add, add_dotProduct]

theorem hJ_sub_right (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp only [hJ, mulVec_sub, dotProduct_sub]

theorem hJ_smul_right (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_smul_left (c : ℂ) (x y : Fin n → ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_zero_right (x : Fin n → ℂ) : hJ ε x 0 = 0 := by simp [hJ]

theorem hJ_zero_left (y : Fin n → ℂ) : hJ ε 0 y = 0 := by simp [hJ]

def formB : (Fin n → ℂ) →ₗ⋆[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => hJ ε x y)
    (fun x x' y => hJ_add_left ε x x' y)
    (fun c x y => by rw [hJ_smul_left, smul_eq_mul, starRingEnd_apply])
    (fun x y y' => hJ_add_right ε x y y')
    (fun c x y => by rw [hJ_smul_right, smul_eq_mul, RingHom.id_apply])

theorem formB_apply (x y : Fin n → ℂ) : formB ε x y = hJ ε x y := rfl

theorem hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, y i) = ∑ i ∈ s, hJ ε x (y i) := by
  simp only [← formB_apply, map_sum]

theorem hJ_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, x i) y = ∑ i ∈ s, hJ ε (x i) y := by
  simp only [← formB_apply, map_sum, LinearMap.sum_apply]

theorem hJ_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (A *ᵥ x) (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * Formalism.REAL.Jm ε * A) *ᵥ y) := by
  unfold hJ
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hJ_UJ (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  rw [hJ_mulVec, show (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε from g.2]
  rfl

theorem mat_eq_of_mulVec {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem inUJ_of_iso (A : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x y, hJ ε (A *ᵥ x) (A *ᵥ y) = hJ ε x y) :
    Formalism.REAL.inUJ ε A := by
  unfold Formalism.REAL.inUJ
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hJ_mulVec] at this
  unfold hJ at this
  simpa [mulVec_single_one] using this

theorem eq_zero_of_hJ (d : Fin n → ℂ) (h : ∀ x, hJ ε x d = 0) : d = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  rw [hJ_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h1
  by_cases hi : ε i <;> simp_all

theorem li_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (s d : ι → Fin n → ℂ) (M : Matrix ι ι ℂ)
    (hM : IsUnit M.det) (h : ∀ j i, hJ ε (d j) (s i) = M j i) : LinearIndependent ℂ s := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hMc : M *ᵥ c = 0 := by
    funext j
    have := congrArg (hJ ε (d j)) hc
    rw [hJ_sum_right, hJ_zero_right] at this
    simp only [hJ_smul_right, h] at this
    simpa [mulVec, dotProduct, mul_comm] using this
  have h0 : c = 0 := by
    have := congrArg (fun v => M⁻¹ *ᵥ v) hMc
    simpa [mulVec_mulVec, nonsing_inv_mul _ hM] using this
  intro i
  simp [h0]

theorem expand_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (φ d : ι → Fin n → ℂ)
    (hcard : Fintype.card ι = n) (hd : ∀ j i, hJ ε (d j) (φ i) = if j = i then 1 else 0)
    (v : Fin n → ℂ) : v = ∑ i, hJ ε (d i) v • φ i := by
  have hli : LinearIndependent ℂ d := li_of_pair ε d φ 1 (by simp) (fun j i => by
    rw [← hJ_conj, hd, one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij])
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [hcard, Module.finrank_fin_fun])
  rw [← sub_eq_zero]
  apply eq_zero_of_hJ ε
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range d) := by rw [hspan]; trivial
  refine Submodule.span_induction (p := fun x _ => hJ ε x (v - ∑ i, hJ ε (d i) v • φ i) = 0)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    rw [hJ_sub_right, hJ_sum_right]
    simp only [hJ_smul_right, hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      sub_self]
  · exact hJ_zero_left ε _
  · intro x y _ _ hx hy; rw [hJ_add_left, hx, hy, add_zero]
  · intro c x _ hx; rw [hJ_smul_left, hx, mul_zero]

end Calc

section Witt

variable {n : ℕ} (ε : Fin n → Bool)

theorem wittFam {ι : Type*} [Fintype ι] (s t : ι → Fin n → ℂ) (hs : LinearIndependent ℂ s)
    (ht : LinearIndependent ℂ t) (hG : ∀ i j, hJ ε (t i) (t j) = hJ ε (s i) (s j)) :
    ∃ g : Formalism.REAL.UJ ε, ∀ i, uMat g *ᵥ s i = t i := by
  classical
  let U := Submodule.span ℂ (Set.range s)
  let bs : Module.Basis ι ℂ U := Module.Basis.span hs
  let f : U →ₗ[ℂ] (Fin n → ℂ) := bs.constr ℂ t
  have hf : ∀ i, f (bs i) = t i := fun i => bs.constr_basis ℂ t i
  have hsum : ∀ x : U, (x : Fin n → ℂ) = ∑ i, bs.repr x i • s i := by
    intro x
    have := congrArg (fun y : U => (y : Fin n → ℂ)) (bs.sum_repr x)
    simp only [Submodule.coe_sum, Submodule.coe_smul, bs] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    congr 1
    exact congrArg Subtype.val (Module.Basis.span_apply hs i)
  have hfsum : ∀ x : U, f x = ∑ i, bs.repr x i • t i := by
    intro x
    have := congrArg f (bs.sum_repr x)
    rw [map_sum] at this
    simp only [map_smul, hf] at this
    exact this.symm
  have e1 : ∀ x : U, Finsupp.linearCombination ℂ t (bs.repr x) = f x := fun x => by
    rw [hfsum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  have finj : Function.Injective f := by
    intro x y hxy
    apply bs.repr.injective
    exact (show Function.Injective (Finsupp.linearCombination ℂ t) from ht) (by rw [e1, e1, hxy])
  have hiso : ∀ x y : U, formB ε (f x) (f y) = formB ε (x : Fin n → ℂ) y := by
    intro x y
    simp only [formB_apply, hfsum, hsum, hJ_sum_left, hJ_sum_right, hJ_smul_left, hJ_smul_right, hG]
  have hnd : ∀ x, (∀ y, formB ε x y = 0) → x = 0 := by
    intro x hx
    apply eq_zero_of_hJ ε
    intro y
    rw [← hJ_conj ε x y, ← formB_apply, hx y, star_zero]
  obtain ⟨g, hgiso, hgext⟩ := witt_extension_theorem ℂ (Fin n → ℂ) (formB ε)
    (fun x y => hJ_conj ε x y) hnd U f finj hiso
  let A : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  let Ai : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  have hA : ∀ v, A *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hAi : ∀ v, Ai *ᵥ v = g.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have h1 : A * Ai = 1 := mat_eq_of_mulVec fun v => by
    rw [← mulVec_mulVec, hAi, hA, one_mulVec, LinearEquiv.apply_symm_apply]
  have h2 : Ai * A = 1 := mat_eq_of_mulVec fun v => by
    rw [← mulVec_mulVec, hA, hAi, one_mulVec, LinearEquiv.symm_apply_apply]
  have hmem : Formalism.REAL.inUJ ε A := inUJ_of_iso ε A fun x y => by
    rw [hA, hA, ← formB_apply, hgiso, formB_apply]
  refine ⟨⟨⟨A, Ai, h1, h2⟩, hmem⟩, fun i => ?_⟩
  show A *ᵥ s i = t i
  rw [hA]
  have := hgext (bs i)
  rw [Module.Basis.span_apply] at this
  rw [this, ← Module.Basis.span_apply hs i]
  exact hf i

end Witt

section Rot

variable {n : ℕ} (ε : Fin n → Bool)

def rotM (ω : Fin n → ℂ) (φ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (φ - 1) * ω i * (star (ω j) * (if ε j then 1 else -1))

theorem rotM_mulVec (ω : Fin n → ℂ) (φ : ℂ) (v : Fin n → ℂ) :
    rotM ε ω φ *ᵥ v = v + ((φ - 1) * hJ ε ω v) • ω := by
  funext i
  simp only [rotM, mulVec, dotProduct, of_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hJ_apply]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

theorem rotM_mul (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (α β : ℂ) (hab : α * β = 1) :
    rotM ε ω α * rotM ε ω β = 1 := mat_eq_of_mulVec fun v => by
  rw [← mulVec_mulVec, rotM_mulVec, rotM_mulVec, hJ_add_right, hJ_smul_right, hω, one_mulVec, add_assoc,
    ← add_smul]
  have e : ∀ c : ℂ, c = 0 → v + c • ω = v := fun c hc => by rw [hc, zero_smul, add_zero]
  apply e
  linear_combination (hJ ε ω v) * hab

theorem rotM_iso (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) (x y : Fin n → ℂ) :
    hJ ε (rotM ε ω φ *ᵥ x) (rotM ε ω φ *ᵥ y) = hJ ε x y := by
  simp only [rotM_mulVec, hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hω, star_mul', star_sub,
    star_one]
  rw [← hJ_conj ε ω x]
  linear_combination (star (hJ ε ω x) * hJ ε ω y) * hφ

def rotU (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) : Formalism.REAL.UJ ε :=
  ⟨⟨rotM ε ω φ, rotM ε ω (star φ), rotM_mul ε ω hω _ _ (by rw [mul_comm]; exact hφ),
    rotM_mul ε ω hω _ _ hφ⟩, inUJ_of_iso ε _ (rotM_iso ε ω hω φ hφ)⟩

theorem rotU_mulVec (ω : Fin n → ℂ) (hω : hJ ε ω ω = 1) (φ : ℂ) (hφ : star φ * φ = 1) (v : Fin n → ℂ) :
    uMat (rotU ε ω hω φ hφ) *ᵥ v = v + ((φ - 1) * hJ ε ω v) • ω :=
  rotM_mulVec ε ω φ v

end Rot

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
