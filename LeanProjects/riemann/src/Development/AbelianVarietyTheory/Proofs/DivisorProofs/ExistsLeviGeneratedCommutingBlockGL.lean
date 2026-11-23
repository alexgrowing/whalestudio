import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

noncomputable section

namespace GlobalTheory.Parabolic.LeviGen

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism Matrix

variable {F : Type} [Field F] {r d d' : ℕ}

theorem mem_range_blockEnum (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (i : Fin r) :
    i ∈ Set.range (blockEnum b c h) ↔ b i = c := by
  have e : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) := Finset.range_orderEmbOfFin _ h
  rw [e]
  simp [block]

theorem extendMat_comm (e : Fin d ↪ Fin r) (e' : Fin d' ↪ Fin r) (h : ∀ a a', e a ≠ e' a')
    (M : Matrix (Fin d) (Fin d) F) (N : Matrix (Fin d') (Fin d') F) :
    extendMat e M * extendMat e' N = extendMat e' N * extendMat e M := by
  have h1 : (incl F e)ᵀ * incl F e' = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, h a a']
  have h2 : (incl F e')ᵀ * incl F e = 0 := by
    ext a a'
    simp [incl, Matrix.mul_apply, Matrix.one_apply, (h a' a).symm]
  have h3 : incl F e * (M - 1) * (incl F e)ᵀ * (incl F e' * (N - 1) * (incl F e')ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e)ᵀ, h1]; simp
  have h4 : incl F e' * (N - 1) * (incl F e')ᵀ * (incl F e * (M - 1) * (incl F e)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl F e')ᵀ, h2]; simp
  simp only [extendMat, MonoidHom.coe_mk, OneHom.coe_mk]
  simp only [add_mul, mul_add, h3, h4, one_mul, mul_one]
  abel

def leviIncl (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    GL (Fin d) F →* levi F b :=
  ((blockTri (κ := F) b).subtype.comp (blockHom F b c h)).codRestrict _ fun g => by
    refine mem_levi.2 fun i j hij => ?_
    show extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) i j = 0
    rw [extendMat_out, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
    simp only [mem_range_blockEnum]
    omega

theorem leviIncl_val (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    ((leviIncl F b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      extendMat (blockEnum b c h) (g : Matrix (Fin d) (Fin d) F) := rfl

def leviRes (F : Type) [Field F] (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) :
    levi F b →* GL (Fin d) F :=
  leviBlock b (blockEnum b c h) (blockEnum b c h).injective fun i j hij => by
    rw [mem_range_blockEnum, ← hij, blockEnum_mem b c h]

theorem leviRes_apply (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (m : levi F b) (a a' : Fin d) :
    (leviRes F b c h m : Matrix (Fin d) (Fin d) F) a a' =
      ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (blockEnum b c h a) (blockEnum b c h a') := rfl

theorem leviRes_leviIncl (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (g : GL (Fin d) F) :
    leviRes F b c h (leviIncl F b c h g) = g := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_in]

theorem leviRes_leviIncl_ne (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c' ≠ c) (g : GL (Fin d) F) : leviRes F b c' h' (leviIncl F b c h g) = 1 := by
  refine Units.ext (Matrix.ext fun a a' => ?_)
  rw [leviRes_apply, leviIncl_val, extendMat_out]
  · simp [Matrix.one_apply]
  · left
    rw [mem_range_blockEnum, blockEnum_mem b c' h']
    exact hc

theorem leviIncl_comm (b : Fin r → ℕ) {c c' : ℕ} (h : (block b c).card = d) (h' : (block b c').card = d')
    (hc : c ≠ c') (g : GL (Fin d) F) (g' : GL (Fin d') F) :
    Commute (leviIncl F b c h g) (leviIncl F b c' h' g') := by
  refine Subtype.ext (Units.ext ?_)
  refine extendMat_comm _ _ (fun a a' e => hc ?_) _ _
  rw [← blockEnum_mem b c h a, e, blockEnum_mem b c' h']

theorem iSup_range_leviIncl (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c) :
    (⨆ c : Set.range b, (leviIncl F b c (h c)).range) = ⊤ := by
  classical
  have key : ∀ s : Finset (Set.range b), ∀ m : levi F b,
      (∀ c : Set.range b, c ∉ s → leviRes F b c (h c) m = 1) →
        m ∈ ⨆ c : Set.range b, (leviIncl F b c (h c)).range := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro m hm
      have : m = 1 := by
        refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
        by_cases hij : b i = b j
        · let c : Set.range b := ⟨b i, i, rfl⟩
          obtain ⟨a, ha⟩ := (mem_range_blockEnum b c (h c) i).2 rfl
          obtain ⟨a', ha'⟩ := (mem_range_blockEnum b c (h c) j).2 hij.symm
          have h1 := leviRes_apply b c (h c) m a a'
          rw [hm c (Finset.notMem_empty _), ha, ha'] at h1
          rw [← h1]
          have : i = j ↔ a = a' := by rw [← (blockEnum b c (h c)).injective.eq_iff, ha, ha']
          simp [Matrix.one_apply, this]
        · rw [m.2 i j hij]
          simp [Matrix.one_apply_ne (fun e => hij (congrArg b e))]
      rw [this]
      exact Subgroup.one_mem _
    | insert c s _ ih =>
      intro m hm
      have e : m = m * leviIncl F b c (h c) (leviRes F b c (h c) m)⁻¹ *
          leviIncl F b c (h c) (leviRes F b c (h c) m) := by simp
      rw [e]
      refine Subgroup.mul_mem _ (ih _ fun c' hc' => ?_) (Subgroup.mem_iSup_of_mem c ⟨_, rfl⟩)
      by_cases hcc : c' = c
      · subst hcc
        rw [map_mul, leviRes_leviIncl, mul_inv_cancel]
      · rw [map_mul, leviRes_leviIncl_ne b _ _ (fun e => hcc (Subtype.ext e)), mul_one]
        exact hm c' (by simp [hcc, hc'])
  have := Fintype.ofFinite (Set.range b)
  exact eq_top_iff.2 fun m _ => key Finset.univ m fun c hc => absurd (Finset.mem_univ c) hc

theorem levi_generated : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ)
    (h : ∀ c : Set.range b, (block b c).card = d c), ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi F b,
    (∀ (c : Set.range b) (g : GL (Fin (d c)) F),
      (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧ (⨆ c, (f c).range) = ⊤ ∧
    ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F), Commute (f c x) (f c' y) :=
  fun F _ _ b d h => ⟨fun c => leviIncl F b c (h c), fun _ _ => rfl, iSup_range_leviIncl b d h,
    fun c c' hc x y => leviIncl_comm b (h c) (h c') (fun e => hc (Subtype.ext e)) x y⟩

end GlobalTheory.Parabolic.LeviGen
