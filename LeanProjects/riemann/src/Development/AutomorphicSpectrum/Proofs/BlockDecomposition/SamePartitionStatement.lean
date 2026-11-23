import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinSamePart

theorem avg_of_surjective {G Q : Type} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (f : G →* Q) (hf : Function.Surjective f) (F : Q → ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, F (f g) = (Fintype.card Q : ℂ)⁻¹ * ∑ q, F q := by
  classical
  set N : ℕ := (Finset.univ.filter fun g => f g = 1).card with hN
  have hfib : ∀ q, (Finset.univ.filter fun g => f g = q).card = N := fun q =>
    MonoidHom.card_fiber_eq_of_mem_range f (hf q) (hf 1)
  have hsum : ∀ F' : Q → ℂ, ∑ g, F' (f g) = N * ∑ q, F' q := by
    intro F'
    rw [← Finset.sum_fiberwise Finset.univ f (fun g => F' (f g)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => F' q)
      (by intro g hg; rw [(Finset.mem_filter.mp hg).2])]
    simp [hfib q]
  have hcard : (Fintype.card G : ℂ) = N * Fintype.card Q := by
    simpa using hsum fun _ => 1
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hN0 : (N : ℂ) ≠ 0 := fun h => hG (by rw [hcard, h, zero_mul])
  have hQ : (Fintype.card Q : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hsum, hcard]
  field_simp

theorem ip_coe {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ) [Fintype H] (a c : Γ → ℂ) :
    ip (H : Set Γ) a c = (Fintype.card H : ℂ)⁻¹ * ∑ h : H, a (h : Γ)⁻¹ * c h := by
  classical
  unfold ip
  have h1 : (H : Set Γ).ncard = Fintype.card H := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_eq_fintype_card
  rw [h1, ← Finset.sum_filter]
  congr 1
  exact Finset.sum_subtype _ (by simp) (fun g => a g⁻¹ * c g)

theorem ip_univ {Γ : Type} [Group Γ] [Fintype Γ] (a c : Γ → ℂ) :
    ip Set.univ a c = (Fintype.card Γ : ℂ)⁻¹ * ∑ g, a g⁻¹ * c g := by
  simp [ip, Set.ncard_univ, Nat.card_eq_fintype_card]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

def bd (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) : Matrix ι ι K :=
  fun i j => if h : b j = b i then L (b i) ⟨i, rfl⟩ ⟨j, h⟩ else 0

theorem bd_blk (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) (c : Fin s) :
    blk K b c (bd b L) = L c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  subst hi
  simp [blk, bd, hj]

theorem bd_off (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) {i j : ι}
    (h : b j ≠ b i) : bd b L i j = 0 := dif_neg h

theorem eq_bd (b : ι → Fin s) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) {M : Matrix ι ι K}
    (h1 : ∀ c, blk K b c M = L c) (h2 : ∀ i j, b j ≠ b i → M i j = 0) : M = bd b L := by
  ext i j
  by_cases h : b j = b i
  · have := congrFun (congrFun (h1 (b i)) ⟨i, rfl⟩) ⟨j, h⟩
    simpa [bd, h, blk] using this
  · rw [bd_off b L h, h2 i j h]

theorem isBlockUT_bd {s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s')
    (hb : ∀ i j, b' j < b' i → b j ≠ b i) (L : ∀ c, Matrix {i // b i = c} {i // b i = c} K) :
    IsBlockUT K b' (bd b L) := fun i j h => bd_off b L (hb i j h)

theorem bd_one (b : ι → Fin s) : bd b (fun c => (1 : Matrix {i // b i = c} {i // b i = c} K)) = 1 := by
  symm
  apply eq_bd
  · intro c
    exact Matrix.submatrix_one _ Subtype.val_injective
  · intro i j h
    exact Matrix.one_apply_ne fun e => h (by rw [e])

theorem bd_mul (b : ι → Fin s) (L L' : ∀ c, Matrix {i // b i = c} {i // b i = c} K) :
    bd b (fun c => L c * L' c) = bd b L * bd b L' := by
  have hut : ∀ M : ∀ c, Matrix {i // b i = c} {i // b i = c} K, IsBlockUT K b (bd b M) := fun M =>
    isBlockUT_bd b b (fun i j h e => by rw [e] at h; exact lt_irrefl _ h) M
  symm
  apply eq_bd
  · intro c
    rw [blk_mul b c (hut L) (hut L'), bd_blk, bd_blk]
  · intro i j h
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : b k = b i
    · rw [bd_off b L' (i := k) (j := j) (by rw [hk]; exact h), mul_zero]
    · rw [bd_off b L hk, zero_mul]

def dGL (b : ι → Fin s) (L : ∀ c, GL {i // b i = c} K) : GL ι K where
  val := bd b fun c => (L c : Matrix _ _ K)
  inv := bd b fun c => ((L c)⁻¹ : GL _ K).1
  val_inv := by
    rw [← bd_mul]
    simp only [Units.mul_inv]
    exact bd_one b
  inv_val := by
    rw [← bd_mul]
    simp only [Units.inv_mul]
    exact bd_one b

theorem dGL_mem {s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s')
    (hb : ∀ i j, b' j < b' i → b j ≠ b i) (L : ∀ c, GL {i // b i = c} K) : dGL b L ∈ parab K b' :=
  ⟨show IsBlockUT K b' (bd b fun c => (L c).1) from isBlockUT_bd b b' hb _,
    show IsBlockUT K b' (bd b fun c => ((L c)⁻¹ : GL _ K).1) from isBlockUT_bd b b' hb _⟩

def leviHom (b : ι → Fin s) : parab K b →* ∀ c, GL {i // b i = c} K where
  toFun p c := levi K b c p
  map_one' := by
    funext c
    apply Units.ext
    exact Matrix.submatrix_one _ Subtype.val_injective
  map_mul' p q := by
    funext c
    apply Units.ext
    exact blk_mul b c p.2.1 q.2.1

theorem blkGL_of_mem (b : ι → Fin s) (c : Fin s) {g : GL ι K} (h : g ∈ parab K b) :
    blkGL b c g = leviHom b ⟨g, h⟩ c := dif_pos h

theorem blkGL_inv (b : ι → Fin s) (c : Fin s) {g : GL ι K} (h : g ∈ parab K b) :
    blkGL b c g⁻¹ = (leviHom b ⟨g, h⟩ c)⁻¹ := by
  rw [blkGL_of_mem b c (inv_mem h), ← Pi.inv_apply, ← map_inv]
  rfl

abbrev ren {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') (c : Fin s) :
    {i // b i = c} ≃ {i // (π ∘ b) i = π c} :=
  Equiv.subtypeEquivRight (p := fun i => b i = c) (q := fun i => (π ∘ b) i = π c)
    fun _ => π.injective.eq_iff.symm

theorem blkGL_ren {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') (c : Fin s) {g : GL ι K}
    (h : g ∈ parab K b) (h' : g ∈ parab K (π ∘ b)) :
    blkGL (π ∘ b) (π c) g = glEquiv K (ren b π c) (leviHom b ⟨g, h⟩ c) := by
  rw [blkGL_of_mem _ _ h']
  apply Units.ext
  ext i j
  rfl

def ell {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') :
    (parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)) →* ∀ c, GL {i // b i = c} K :=
  (leviHom b).comp (Subgroup.inclusion inf_le_left)

theorem ell_surjective {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') :
    Function.Surjective (ell (K := K) b π) := by
  intro L
  have h1 : dGL b L ∈ parab K b := dGL_mem b b (fun i j h e => by rw [e] at h; exact lt_irrefl _ h) L
  have h2 : dGL b L ∈ parab K (π ∘ b) :=
    dGL_mem b (π ∘ b) (fun i j h e => by simp only [Function.comp, e] at h; exact lt_irrefl _ h) L
  refine ⟨⟨dGL b L, h1, h2⟩, ?_⟩
  funext c
  apply Units.ext
  exact bd_blk b (fun c => (L c).1) c

theorem samePart : ReciprocityTheory.Ty.Fin.St.SamePart := by
  intro K _ _ _ ι _ _ s s' b π χ ψ
  classical
  let F : (∀ c, GL {i // b i = c} K) → ℂ := fun q =>
    ∏ c, (χ c (q c)⁻¹ * ψ (π c) (glEquiv K (ren b π c) (q c)))
  have key : ∀ h : (parab K b ⊓ parab K (π ∘ b) : Subgroup (GL ι K)),
      hcFun b χ (h : GL ι K)⁻¹ * hcFun (π ∘ b) ψ h = F (ell b π h) := by
    rintro ⟨g, h1, h2⟩
    simp only [F, Finset.prod_mul_distrib, hcFun]
    congr 1
    · exact Finset.prod_congr rfl fun c _ => by rw [blkGL_inv b c h1]; rfl
    · rw [← Equiv.prod_comp π]
      exact Finset.prod_congr rfl fun c _ => by rw [blkGL_ren b π c h1 h2]; rfl
  rw [ip_coe, Finset.sum_congr rfl (fun h _ => key h),
    avg_of_surjective (ell (K := K) b π) (ell_surjective b π) F]
  simp only [ip_univ, F]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end GlobalTheory.CompanionTheory.TyFinSamePart
