import Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGLev
import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Shape

variable {k : Type} [Field k] {n : ℕ} {a t : ℕ}

theorem blkOf_eq (a t x : ℕ) : Formalism.L2.Forms.blkOf a t x = lvlX a t x := rfl

theorem mem_JBar_iff_InJ (zl : Bool) (fc : ℕ) (g : GL (Fin n) k) :
    g ∈ JBar k n a t zl fc ↔ Formalism.L2.Forms.InJ a t fc zl (g : Matrix (Fin n) (Fin n) k) := by
  show ((g : Matrix (Fin n) (Fin n) k).BlockTriangular (lvF n a t) ∧
    (∀ x : Fin n, x.val < a → (g : Matrix (Fin n) (Fin n) k) x x = 1) ∧
    (zl = true → ∀ l y : Fin n, l.val + 1 = n →
      (g : Matrix (Fin n) (Fin n) k) l y = (1 : Matrix (Fin n) (Fin n) k) l y ∧
      (g : Matrix (Fin n) (Fin n) k) y l = (1 : Matrix (Fin n) (Fin n) k) y l) ∧
    (∀ x y : Fin n, y.val = fc → (g : Matrix (Fin n) (Fin n) k) x y = (1 : Matrix (Fin n) (Fin n) k) x y)) ↔ _
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun x y hxy => h1 (by rw [blkOf_eq, blkOf_eq] at hxy; exact hxy), h2,
      fun x y hy => by rw [h4 x y hy, Matrix.one_apply], fun hz x y hy => ?_⟩
    obtain ⟨e1, e2⟩ := h3 hz y x hy
    exact ⟨by rw [e2, Matrix.one_apply], by rw [e1, Matrix.one_apply]; exact if_congr eq_comm rfl rfl⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun ⦃x y⦄ hxy => h1 x y (by rw [blkOf_eq, blkOf_eq]; exact hxy), h2, fun hz l y hl => ?_,
      fun x y hy => by rw [h3 x y hy, Matrix.one_apply]⟩
    obtain ⟨e1, e2⟩ := h4 hz y l hl
    exact ⟨by rw [e2, Matrix.one_apply]; exact if_congr eq_comm rfl rfl, by rw [e1, Matrix.one_apply]⟩

theorem lvlX_eq_blk (ht : 0 < t) (i x : ℕ) : lvlX a t x = a + i ↔ a + i * t ≤ x ∧ x < a + (i + 1) * t := by
  unfold lvlX
  split_ifs with h
  · constructor
    · intro h'; omega
    · rintro ⟨h1, h2⟩; omega
  · constructor
    · intro h'
      have hq : (x - a) / t = i := by omega
      have e1 : i * t ≤ x - a := (Nat.le_div_iff_mul_le ht).1 hq.ge
      have e2 : x - a < (i + 1) * t := (Nat.div_lt_iff_lt_mul ht).1 (by omega)
      rw [Nat.add_mul, Nat.one_mul] at e2 ⊢
      omega
    · rintro ⟨h1, h2⟩
      have h2' : x < a + i * t + t := by rw [Nat.add_mul, Nat.one_mul] at h2; omega
      have e1 : i ≤ (x - a) / t := (Nat.le_div_iff_mul_le ht).2 (by omega)
      have e2 : (x - a) / t < i + 1 := (Nat.div_lt_iff_lt_mul ht).2 (by rw [Nat.add_mul, Nat.one_mul]; omega)
      omega

def blkEquiv (ht : 0 < t) (i : ℕ) (hn : a + (i + 1) * t ≤ n) : Fin t ≃ {x : Fin n // lvF n a t x = a + i} where
  toFun s := ⟨⟨a + i * t + s.val, by have := s.2; rw [Nat.add_mul, Nat.one_mul] at hn; omega⟩,
    (lvlX_eq_blk ht i _).2 ⟨by show a + i * t ≤ a + i * t + s.val; omega,
      by show a + i * t + s.val < a + (i + 1) * t; have := s.2; rw [Nat.add_mul, Nat.one_mul]; omega⟩⟩
  invFun x := ⟨x.1.val - (a + i * t), by
    have := (lvlX_eq_blk ht i _).1 x.2
    rw [Nat.add_mul, Nat.one_mul] at this
    omega⟩
  left_inv s := by
    apply Fin.ext
    show a + i * t + s.val - (a + i * t) = s.val
    omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have := (lvlX_eq_blk ht i _).1 x.2
    show a + i * t + (x.1.val - (a + i * t)) = x.1.val
    omega

theorem sum_sup (han : a ≤ n) (skip : ℕ) (Sd : Finset ℕ) (hSd : ∀ x, x + 1 < a → (x ∈ Sd ↔ x + 1 ≠ skip))
    (M : Matrix (Fin n) (Fin n) k) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip then M x y else 0) =
      ∑ x ∈ Sd.filter (fun x => x + 1 < a), entN M x (x + 1) := by
  have key : ∀ x : Fin n, (∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip then M x y else 0) =
      if (x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ skip then entN M x ((x : ℕ) + 1) else 0 := by
    intro x
    by_cases hx : (x : ℕ) + 1 < a
    · have hxn : (x : ℕ) + 1 < n := by omega
      rw [Finset.sum_eq_single (⟨(x : ℕ) + 1, hxn⟩ : Fin n)]
      · have hE : entN M x ((x : ℕ) + 1) = M x ⟨(x : ℕ) + 1, hxn⟩ := by
          unfold entN; exact dif_pos ⟨x.2, hxn⟩
        rw [hE]
        simp [hx]
      · intro y _ hy
        rw [if_neg]
        rintro ⟨h1, -, -⟩
        exact hy (Fin.ext h1.symm)
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hn : ¬((x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ skip) := fun h => hx h.1
      rw [if_neg hn]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg]
      rintro ⟨h1, h2, -⟩
      omega
  simp only [key]
  rw [Fin.sum_univ_eq_sum_range (fun x => if x + 1 < a ∧ x + 1 ≠ skip then entN M x (x + 1) else 0) n]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨(hSd x h2).2 h3, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2, (hSd x h2).1 h1⟩

end Shape

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

def SplitStabL (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (Lb : Submodule (𝓞 E) (Fin n → E))
    (fr : GL (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ x ∈ UPts σ J (v.adicCompletion F), x ∈ levelVL σ J v Lb ↔
    toFr v spl fr x ∈ (bc (n := Fin n) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range

theorem redM_bc (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (v.adicCompletionIntegers F)) :
    Formalism.L2.Forms.redM F v ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g :
      GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
    ((redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g : GL (Fin n) (resV F v)) :
      Matrix (Fin n) (Fin n) (resV F v)) := by
  ext a b
  have h : ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F :=
    ((g : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) a b).2
  unfold Formalism.L2.Forms.redM
  exact dif_pos h

theorem red_mem_iff (v : HeightOneSpectrum (𝓞 F)) (a t fc : ℕ) (zl : Bool)
    (g : GL (Fin n) (v.adicCompletionIntegers F)) :
    redGL (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) g ∈ JBar (resV F v) n a t zl fc ↔
      Formalism.L2.Forms.InJ a t fc zl (Formalism.L2.Forms.redM F v
        ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g :
          GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) := by
  exact (mem_JBar_iff_InJ (k := Formalism.L2.Forms.kv F v) zl fc _).trans (by rw [redM_bc])

def levAtG_of_GLev (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (G : Formalism.L2.Forms.GLoc F E σ gp) (k m t j nb skip fc : ℕ)
    (hfc : fc = fcX k m j n) (X : Formalism.L2.Forms.GLev S G (aX k m j) t nb skip fc (fixX m j))
    (hst : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
      SplitStabL σ J v (G.sp i v h) S.Lb (X.fr i v h)) :
    LevAtG σ J gp G.sp S.Lb S.Uloc k m t j where
  frG := X.fr
  frG_lat := X.fr_lat
  Uloc_g := by
    intro i v h
    subst hfc
    ext x
    rw [mem_JU]
    constructor
    · intro hx
      have hU := S.Uloc_le v hx
      have hl := S.Uloc_lev v hx
      obtain ⟨g, hg⟩ := (hst i v h x hU).1 hl
      refine ⟨hU, ?_⟩
      rw [← toFr_apply, ← hg]
      refine ⟨g, (red_mem_iff v _ t _ _ g).2 ?_, rfl⟩
      have := (X.mem i v h x hl).1 hx
      have e : G.mat i v h (X.fr i v h) x = ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g :
          GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
        rw [hg, toFr_apply]; rfl
      rwa [e] at this
    · rintro ⟨hU, g, hg, hgx⟩
      have hgx' : bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g = toFr v (G.sp i v h) (X.fr i v h) x := by
        rw [toFr_apply]; exact hgx
      have hl : x ∈ levelVL σ J v S.Lb := (hst i v h x hU).2 ⟨g, hgx'⟩
      refine (X.mem i v h x hl).2 ?_
      have e : G.mat i v h (X.fr i v h) x = ((bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) g :
          GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
        rw [hgx', toFr_apply]; rfl
      rw [e]
      exact (red_mem_iff v _ t _ _ g).1 hg

end Lev

end Formalism.L2.G
