import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSimpleAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement

open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinJacquet

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

def leviHom (b : ι → Fin s) : parab K b →* (∀ c, GL {i // b i = c} K) where
  toFun p c := levi K b c p
  map_one' := by
    funext c
    apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show ((1 : GL ι K) : Matrix ι ι K) i j = (1 : Matrix {i // b i = c} {i // b i = c} K) ⟨i, hi⟩ ⟨j, hj⟩
    simp [Matrix.one_apply]
  map_mul' p q := by
    funext c
    apply Units.ext
    exact blk_mul b c p.2.1 q.2.1

theorem mem_unip_iff (b : ι → Fin s) (p : parab K b) : p.1 ∈ unip K b ↔ leviHom b p = 1 := by
  constructor
  · intro h
    funext c
    apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have h1 := h.2 i j (hi.trans hj.symm)
    show (p.1 : Matrix ι ι K) i j = (1 : Matrix {i // b i = c} {i // b i = c} K) ⟨i, hi⟩ ⟨j, hj⟩
    rw [h1, Matrix.one_apply]
    simp
  · intro h
    refine ⟨p.2, fun i j hij => ?_⟩
    have h1 := congrArg (fun f : (∀ c, GL {i // b i = c} K) =>
      ((f (b i) : GL {k // b k = b i} K) : Matrix {k // b k = b i} {k // b k = b i} K) ⟨i, rfl⟩ ⟨j, hij.symm⟩) h
    have h2 : (p.1 : Matrix ι ι K) i j =
        (1 : Matrix {k // b k = b i} {k // b k = b i} K) ⟨i, rfl⟩ ⟨j, hij.symm⟩ := h1
    rw [h2, Matrix.one_apply]
    simp

theorem blockDiagonal_entry (b : ι → Fin s) (M : ∀ c, Matrix {i // b i = c} {i // b i = c} K) (k k' : Fin s)
    (x : {i // b i = k}) (y : {i // b i = k'}) :
    Matrix.blockDiagonal' M ⟨k, x⟩ ⟨k', y⟩ = if h : k' = k then M k x ⟨y.1, y.2.trans h⟩ else 0 := by
  by_cases h : k' = k
  · subst h
    simp
  · have h' : k ≠ k' := fun e => h e.symm
    simp [Matrix.blockDiagonal'_apply, h, h']

def blockHom (b : ι → Fin s) : (∀ c, Matrix {i // b i = c} {i // b i = c} K) →* Matrix ι ι K where
  toFun M := (Matrix.blockDiagonal' M).submatrix (Equiv.sigmaFiberEquiv b).symm (Equiv.sigmaFiberEquiv b).symm
  map_one' := by
    rw [Matrix.blockDiagonal'_one]
    simp
  map_mul' M N := by
    show (Matrix.blockDiagonal' (fun k => M k * N k)).submatrix _ _ = _
    rw [Matrix.blockDiagonal'_mul, Matrix.submatrix_mul_equiv]

theorem blockHom_apply (b : ι → Fin s) (M : ∀ c, Matrix {i // b i = c} {i // b i = c} K) (i j : ι) :
    blockHom b M i j = if h : b j = b i then M (b i) ⟨i, rfl⟩ ⟨j, h⟩ else 0 :=
  blockDiagonal_entry b M (b i) (b j) ⟨i, rfl⟩ ⟨j, rfl⟩

def dGL (b : ι → Fin s) : (∀ c, GL {i // b i = c} K) →* GL ι K :=
  (Units.map (blockHom b)).comp
    (MulEquiv.piUnits (M := fun c => Matrix {i // b i = c} {i // b i = c} K)).symm.toMonoidHom

theorem dGL_val (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    ((dGL b g : GL ι K) : Matrix ι ι K) =
      blockHom b (fun c => ((g c : GL {i // b i = c} K) : Matrix {i // b i = c} {i // b i = c} K)) := rfl

theorem isBlockUT_dGL (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    IsBlockUT K b ((dGL b g : GL ι K) : Matrix ι ι K) := by
  intro i j h
  rw [dGL_val, blockHom_apply, dif_neg (ne_of_lt h)]

theorem dGL_mem (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) : dGL b g ∈ parab K b :=
  ⟨isBlockUT_dGL b g, by rw [← map_inv]; exact isBlockUT_dGL b g⁻¹⟩

theorem leviHom_dGL (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    leviHom b ⟨dGL b g, dGL_mem b g⟩ = g := by
  funext c
  apply Units.ext
  ext ⟨i, hi⟩ ⟨j, hj⟩
  subst hi
  show ((dGL b g : GL ι K) : Matrix ι ι K) i j = _
  rw [dGL_val, blockHom_apply, dif_pos hj]

theorem unip_conj (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) {u : GL ι K} (hu : u ∈ unip K b) :
    (dGL b g)⁻¹ * u * dGL b g ∈ unip K b := by
  have hd := dGL_mem b g
  have hl := (mem_unip_iff b ⟨u, hu.1⟩).1 hu
  have := (mem_unip_iff b ((⟨dGL b g, hd⟩ : parab K b)⁻¹ * ⟨u, hu.1⟩ * ⟨dGL b g, hd⟩)).2
    (by rw [map_mul, map_mul, hl, map_inv, mul_one, inv_mul_cancel])
  exact this

theorem unip_of_levi (b : ι → Fin s) (p : parab K b) : (dGL b (leviHom b p))⁻¹ * p.1 ∈ unip K b := by
  have hd := dGL_mem b (leviHom b p)
  have := (mem_unip_iff b ((⟨dGL b (leviHom b p), hd⟩ : parab K b)⁻¹ * p)).2
    (by rw [map_mul, map_inv, leviHom_dGL, inv_mul_cancel])
  exact this

def fixSub (τ : FDRep ℂ (GL ι K)) (b : ι → Fin s) : Submodule ℂ τ where
  carrier := {v | ∀ u ∈ unip K b, τ.ρ u v = v}
  add_mem' := by
    intro x y hx hy u hu
    rw [map_add, hx u hu, hy u hu]
  zero_mem' := by
    intro u _
    exact map_zero _
  smul_mem' := by
    intro a x hx u hu
    rw [map_smul, hx u hu]

theorem fixSub_stable (τ : FDRep ℂ (GL ι K)) (b : ι → Fin s) (g : ∀ c, GL {i // b i = c} K) :
    ∀ v ∈ fixSub τ b, τ.ρ (dGL b g) v ∈ fixSub τ b := by
  intro v hv u hu
  have h := hv _ (unip_conj b g hu)
  have e : u * dGL b g = dGL b g * ((dGL b g)⁻¹ * u * dGL b g) := by group
  calc τ.ρ u (τ.ρ (dGL b g) v) = τ.ρ (u * dGL b g) v := by rw [map_mul]; rfl
    _ = τ.ρ (dGL b g * ((dGL b g)⁻¹ * u * dGL b g)) v := by rw [e]
    _ = τ.ρ (dGL b g) (τ.ρ ((dGL b g)⁻¹ * u * dGL b g) v) := by rw [map_mul]; rfl
    _ = τ.ρ (dGL b g) v := by rw [h]

def wRep (τ : FDRep ℂ (GL ι K)) (b : ι → Fin s) :
    Representation ℂ (∀ c, GL {i // b i = c} K) (fixSub τ b) where
  toFun g := (τ.ρ (dGL b g)).restrict (fixSub_stable τ b g)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

def HasFixed (τ : FDRep ℂ (GL ι K)) (s : ℕ) : Prop :=
  ∃ b : ι → Fin s, Function.Surjective b ∧ ∃ v : τ, v ≠ 0 ∧ ∀ u ∈ unip K b, τ.ρ u v = v

theorem unip_trivial (b : ι → Fin s) (hb : ∀ i j, b i = b j) {u : GL ι K} (hu : u ∈ unip K b) : u = 1 := by
  apply Units.ext
  ext i j
  rw [hu.2 i j (hb i j)]
  simp [Matrix.one_apply]

theorem hasFixed_exists (τ : FDRep ℂ (GL ι K)) [Nontrivial τ] : ∃ s, HasFixed τ s := by
  obtain ⟨v, hv⟩ := exists_ne (0 : τ)
  rcases isEmpty_or_nonempty ι with h | h
  · refine ⟨0, fun i => isEmptyElim i, fun c => c.elim0, v, hv, fun u hu => ?_⟩
    rw [unip_trivial _ (fun i => isEmptyElim i) hu]
    simp
  · obtain ⟨i₀⟩ := h
    refine ⟨1, fun _ => 0, fun c => ⟨i₀, Subsingleton.elim _ _⟩, v, hv, fun u hu => ?_⟩
    rw [unip_trivial _ (fun _ _ => rfl) hu]
    simp

theorem hasFixed_le {τ : FDRep ℂ (GL ι K)} {s : ℕ} (h : HasFixed τ s) : s ≤ Fintype.card ι := by
  obtain ⟨b, hb, _⟩ := h
  simpa using Fintype.card_le_of_surjective b hb

section Refine

variable (b : ι → Fin s) (c : Fin s) {t : ℕ} (b₁ : {i // b i = c} → Fin t) (ht : 1 ≤ t)

def refine (i : ι) : Fin (s + t - 1) :=
  if h : b i = c then ⟨c + b₁ ⟨i, h⟩, by have := c.2; have := (b₁ ⟨i, h⟩).2; omega⟩
  else if h2 : (b i : ℕ) < c then ⟨b i, by have := c.2; omega⟩
  else ⟨b i + t - 1, by have := (b i).2; omega⟩

theorem refine_of_eq {i : ι} (h : b i = c) : (refine b c b₁ ht i : ℕ) = c + b₁ ⟨i, h⟩ := by
  simp [refine, h]

theorem refine_of_lt {i : ι} (h : (b i : ℕ) < c) : (refine b c b₁ ht i : ℕ) = b i := by
  have h' : b i ≠ c := fun e => by rw [e] at h; exact lt_irrefl _ h
  simp [refine, h, h']

theorem refine_of_gt {i : ι} (h : (c : ℕ) < b i) : (refine b c b₁ ht i : ℕ) = b i + t - 1 := by
  have h' : b i ≠ c := fun e => by rw [e] at h; exact lt_irrefl _ h
  have h2 : ¬ (b i : ℕ) < c := by omega
  simp [refine, h2, h']

theorem refine_cases (i : ι) :
    ((b i : ℕ) < c ∧ (refine b c b₁ ht i : ℕ) = b i) ∨
    ((b i : ℕ) = c ∧ (c : ℕ) ≤ refine b c b₁ ht i ∧ (refine b c b₁ ht i : ℕ) < c + t) ∨
    ((c : ℕ) < b i ∧ (refine b c b₁ ht i : ℕ) = b i + t - 1) := by
  rcases lt_trichotomy (b i : ℕ) c with h | h | h
  · exact Or.inl ⟨h, refine_of_lt b c b₁ ht h⟩
  · have h' : b i = c := Fin.ext h
    have := refine_of_eq b c b₁ ht h'
    have := (b₁ ⟨i, h'⟩).2
    exact Or.inr (Or.inl ⟨h, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨h, refine_of_gt b c b₁ ht h⟩)

theorem refine_lt {i j : ι} (h : b j < b i) : refine b c b₁ ht j < refine b c b₁ ht i := by
  have h' : (b j : ℕ) < b i := h
  rw [Fin.lt_def]
  rcases refine_cases b c b₁ ht i with h1 | h1 | h1 <;> rcases refine_cases b c b₁ ht j with h2 | h2 | h2 <;> omega

theorem refine_eq_of_ne {i j : ι} (h : b i = b j) (hc : b i ≠ c) : refine b c b₁ ht i = refine b c b₁ ht j := by
  have h' : (b i : ℕ) = b j := by rw [h]
  have hc' : (b i : ℕ) ≠ c := fun e => hc (Fin.ext e)
  apply Fin.ext
  rcases refine_cases b c b₁ ht i with h1 | h1 | h1 <;> rcases refine_cases b c b₁ ht j with h2 | h2 | h2 <;> omega

theorem refine_surjective (hb : Function.Surjective b) (hb₁ : Function.Surjective b₁) :
    Function.Surjective (refine b c b₁ ht) := by
  intro k
  have hk := k.2
  have hcs := c.2
  by_cases h1 : (k : ℕ) < c
  · obtain ⟨i, hi⟩ := hb ⟨k, by omega⟩
    have hi' : (b i : ℕ) = k := by rw [hi]
    refine ⟨i, Fin.ext ?_⟩
    rw [refine_of_lt b c b₁ ht (by omega), hi']
  · by_cases h2 : (k : ℕ) < c + t
    · obtain ⟨x, hx⟩ := hb₁ ⟨k - c, by omega⟩
      have hx' : (b₁ x : ℕ) = k - c := by rw [hx]
      refine ⟨x.1, Fin.ext ?_⟩
      rw [refine_of_eq b c b₁ ht x.2]
      have : b₁ ⟨x.1, x.2⟩ = b₁ x := rfl
      rw [this, hx']
      omega
    · obtain ⟨i, hi⟩ := hb ⟨k + 1 - t, by omega⟩
      have hi' : (b i : ℕ) = k + 1 - t := by rw [hi]
      refine ⟨i, Fin.ext ?_⟩
      rw [refine_of_gt b c b₁ ht (by omega), hi']
      omega

theorem refine_parts {u : GL ι K} (hu : u ∈ unip K (refine b c b₁ ht)) :
    ∃ hp : u ∈ parab K b, (∀ c', c' ≠ c → levi K b c' ⟨u, hp⟩ = 1) ∧ levi K b c ⟨u, hp⟩ ∈ unip K b₁ := by
  have hp : u ∈ parab K b :=
    ⟨fun i j h => hu.1.1 i j (refine_lt b c b₁ ht h), fun i j h => hu.1.2 i j (refine_lt b c b₁ ht h)⟩
  refine ⟨hp, fun c' hc' => ?_, ⟨?_, ?_⟩, ?_⟩
  · apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have h1 := hu.2 i j (refine_eq_of_ne b c b₁ ht (hi.trans hj.symm) (by rw [hi]; exact hc'))
    show (u : Matrix ι ι K) i j = (1 : Matrix {i // b i = c'} {i // b i = c'} K) ⟨i, hi⟩ ⟨j, hj⟩
    rw [h1, Matrix.one_apply]
    simp
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    refine hu.1.1 i j ?_
    have h' : (b₁ ⟨j, hj⟩ : ℕ) < b₁ ⟨i, hi⟩ := h
    rw [Fin.lt_def, refine_of_eq b c b₁ ht hi, refine_of_eq b c b₁ ht hj]
    omega
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    refine hu.1.2 i j ?_
    have h' : (b₁ ⟨j, hj⟩ : ℕ) < b₁ ⟨i, hi⟩ := h
    rw [Fin.lt_def, refine_of_eq b c b₁ ht hi, refine_of_eq b c b₁ ht hj]
    omega
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    have h1 : refine b c b₁ ht i = refine b c b₁ ht j := by
      apply Fin.ext
      rw [refine_of_eq b c b₁ ht hi, refine_of_eq b c b₁ ht hj, h]
    have h2 := hu.2 i j h1
    show (u : Matrix ι ι K) i j = _
    rw [h2]
    simp

end Refine

section Cusp

variable {τ : FDRep ℂ (GL ι K)} {b : ι → Fin s} {lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)}
  {Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ}

theorem equivariant_tprod (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (p : parab K b)
    (f : ∀ c, (lam c : Type)) :
    Φ (PiTensorProduct.tprod ℂ fun c => (lam c).ρ (levi K b c p) (f c)) = τ.ρ p.1 (Φ (PiTensorProduct.tprod ℂ f)) := by
  have := LinearMap.congr_fun (heq p) (PiTensorProduct.tprod ℂ f)
  simpa [infl, PiTensorProduct.map_tprod] using this

def killSub (Φ : PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] τ) (c : Fin s) : Submodule ℂ (lam c) where
  carrier := {x | ∀ f : ∀ c, (lam c : Type), Φ (PiTensorProduct.tprod ℂ (Function.update f c x)) = 0}
  add_mem' := by
    intro x y hx hy f
    rw [MultilinearMap.map_update_add, map_add, hx f, hy f, add_zero]
  zero_mem' := by
    intro f
    rw [MultilinearMap.map_update_zero, map_zero]
  smul_mem' := by
    intro a x hx f
    rw [MultilinearMap.map_update_smul, map_smul, hx f, smul_zero]

theorem killSub_eq_bot (hΦ : Φ ≠ 0) (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (c : Fin s)
    (hirr : IsIrr (lam c).ρ) : killSub Φ c = ⊥ := by
  have hinv : ∀ g, ∀ x ∈ killSub Φ c, (lam c).ρ g x ∈ killSub Φ c := by
    intro g x hx f
    let gh : ∀ c', GL {i // b i = c'} K := Function.update 1 c g
    let p : parab K b := ⟨dGL b gh, dGL_mem b gh⟩
    have hl : ∀ c', levi K b c' p = gh c' := fun c' => congrFun (leviHom_dGL b gh) c'
    have h1 := equivariant_tprod heq p (Function.update f c x)
    have h2 : (fun c' => (lam c').ρ (levi K b c' p) (Function.update f c x c')) =
        Function.update f c ((lam c).ρ g x) := by
      funext c'
      rw [hl]
      by_cases e : c' = c
      · subst e
        simp [gh]
      · simp [gh, e]
    rw [h2] at h1
    rw [h1, hx f, map_zero]
  rcases hirr.2 (killSub Φ c) hinv with h | h
  · exact h
  · exfalso
    apply hΦ
    apply PiTensorProduct.ext
    ext f
    have h1 : f c ∈ killSub Φ c := by rw [h]; trivial
    have h2 := h1 f
    rw [Function.update_eq_self] at h2
    simpa using h2

theorem cusp_step (hb : Function.Surjective b) (hΦ : Φ ≠ 0)
    (heq : ∀ p : parab K b, Φ ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ Φ) (c : Fin s) (hirr : IsIrr (lam c).ρ)
    {t : ℕ} (ht : 1 ≤ t) (b₁ : {i // b i = c} → Fin t) (hb₁ : Function.Surjective b₁)
    (v : lam c) (hv : v ≠ 0) (hfix : ∀ u ∈ unip K b₁, (lam c).ρ u v = v) : HasFixed τ (s + t - 1) := by
  have hnot : v ∉ killSub Φ c := by
    rw [killSub_eq_bot hΦ heq c hirr]
    simpa using hv
  have hex : ∃ f : ∀ c, (lam c : Type), Φ (PiTensorProduct.tprod ℂ (Function.update f c v)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnot hcon
  obtain ⟨f, hf⟩ := hex
  refine ⟨refine b c b₁ ht, refine_surjective b c b₁ ht hb hb₁, _, hf, fun u hu => ?_⟩
  obtain ⟨hp, h1, h2⟩ := refine_parts b c b₁ ht hu
  have h3 := equivariant_tprod heq ⟨u, hp⟩ (Function.update f c v)
  have h4 : (fun c' => (lam c').ρ (levi K b c' ⟨u, hp⟩) (Function.update f c v c')) = Function.update f c v := by
    funext c'
    by_cases e : c' = c
    · subst e
      simpa using hfix _ h2
    · rw [h1 c' e]
      simp
  rw [h4] at h3
  exact h3.symm

end Cusp

theorem jacquetAll : ReciprocityTheory.Ty.Fin.St.JacquetAll := by
  intro K _ _ _ ι _ _ τ hτ
  have hirrτ := ((GlobalTheory.T.simple_iff_irreducible).1 _ τ).1 hτ
  haveI : Nontrivial τ := hirrτ.1
  classical
  obtain ⟨s₀, h₀⟩ := hasFixed_exists τ
  obtain ⟨m, hm, hmax⟩ : ∃ m, HasFixed τ m ∧ ∀ s', HasFixed τ s' → s' ≤ m :=
    ⟨Nat.findGreatest (HasFixed τ) (Fintype.card ι), Nat.findGreatest_spec (hasFixed_le h₀) h₀,
      fun s' h => Nat.le_findGreatest (hasFixed_le h) h⟩
  obtain ⟨b, hb, v, hv, hfix⟩ := hm
  haveI : Nontrivial (fixSub τ b) :=
    ⟨⟨⟨v, hfix⟩, 0, fun e => hv (congrArg Subtype.val e)⟩⟩
  obtain ⟨lam, Φ', hsimple, hΦ', heq'⟩ :=
    (GlobalTheory.T.product_simple_all : PI.GreenHCLabel.ProdSimple) m (fun c => GL {i // b i = c} K) (fixSub τ b) (wRep τ b)
  have hΦ : (fixSub τ b).subtype ∘ₗ Φ' ≠ 0 := by
    intro h
    apply hΦ'
    ext x
    have := LinearMap.congr_fun h (PiTensorProduct.tprod ℂ x)
    simpa using this
  have heq : ∀ p : parab K b, ((fixSub τ b).subtype ∘ₗ Φ') ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ ((fixSub τ b).subtype ∘ₗ Φ') := by
    intro p
    ext x
    have h1 := LinearMap.congr_fun (heq' (leviHom b p)) (PiTensorProduct.tprod ℂ x)
    have h2 : ((Φ' (PiTensorProduct.map (fun c => (lam c).ρ (leviHom b p c)) (PiTensorProduct.tprod ℂ x)) : fixSub τ b) : τ) =
        τ.ρ (dGL b (leviHom b p)) (Φ' (PiTensorProduct.tprod ℂ x)) := by
      have := congrArg Subtype.val h1
      exact this
    have h3 : τ.ρ p.1 (Φ' (PiTensorProduct.tprod ℂ x)) = τ.ρ (dGL b (leviHom b p)) (Φ' (PiTensorProduct.tprod ℂ x)) := by
      have h4 := (Φ' (PiTensorProduct.tprod ℂ x)).2 _ (unip_of_levi b p)
      have e : p.1 = dGL b (leviHom b p) * ((dGL b (leviHom b p))⁻¹ * p.1) := by group
      calc τ.ρ p.1 (Φ' (PiTensorProduct.tprod ℂ x))
          = τ.ρ (dGL b (leviHom b p) * ((dGL b (leviHom b p))⁻¹ * p.1)) (Φ' (PiTensorProduct.tprod ℂ x)) := by rw [← e]
        _ = τ.ρ (dGL b (leviHom b p)) (τ.ρ ((dGL b (leviHom b p))⁻¹ * p.1) (Φ' (PiTensorProduct.tprod ℂ x))) := by
            rw [map_mul]; rfl
        _ = _ := by rw [h4]
    show ((Φ' (PiTensorProduct.map (fun c => (lam c).ρ (leviHom b p c)) (PiTensorProduct.tprod ℂ x)) : fixSub τ b) : τ) =
      τ.ρ p.1 (Φ' (PiTensorProduct.tprod ℂ x))
    rw [h2, h3]
  refine ⟨m, b, lam, (fixSub τ b).subtype ∘ₗ Φ', hb, fun c => ⟨hsimple c, ?_⟩, hΦ, heq⟩
  intro t b₁ hb₁ ht w hw
  by_contra hne
  have hirr := ((GlobalTheory.T.simple_iff_irreducible).1 _ (lam c)).1 (hsimple c)
  have := hmax _ (cusp_step hb hΦ heq c hirr (by omega) b₁ hb₁ w hne hw)
  omega

end GlobalTheory.CompanionTheory.TyFinJacquet
