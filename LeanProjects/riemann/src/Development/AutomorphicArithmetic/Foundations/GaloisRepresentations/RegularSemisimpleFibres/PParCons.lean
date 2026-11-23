import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section ParConsAux

variable {F : Type} [Field F]

private theorem tl_entry {a n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin a) (I J : Fin n)
    (hI : (I : ℕ) = i) (hJ : (J : ℕ) = j) : GlobalTheory.Shin.tl a M i j = M I J := by
  unfold GlobalTheory.Shin.tl GlobalTheory.Shin.ent
  rw [dif_pos ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem br_entry {a b n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin b) (I J : Fin n)
    (hI : (I : ℕ) = a + i) (hJ : (J : ℕ) = a + j) : GlobalTheory.Shin.br a b M i j = M I J := by
  unfold GlobalTheory.Shin.br GlobalTheory.Shin.ent
  rw [dif_pos ⟨by rw [← hI]; exact I.isLt, by rw [← hJ]; exact J.isLt⟩]
  congr 1 <;> ext <;> simp [hI, hJ]

private theorem units_of {a b n : ℕ} (hn : n = a + b) (p : GL (Fin n) F) (h : GlobalTheory.Shin.InPar a p) :
    IsUnit (GlobalTheory.Shin.tl a (p : Matrix (Fin n) (Fin n) F)) ∧
      IsUnit (GlobalTheory.Shin.br a b (p : Matrix (Fin n) (Fin n) F)) := by
  subst hn
  have hM : (p : Matrix (Fin (a + b)) (Fin (a + b)) F).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (GlobalTheory.Shin.tl a (p : Matrix (Fin (a + b)) (Fin (a + b)) F))
        (Matrix.of fun i j => (p : Matrix (Fin (a + b)) (Fin (a + b)) F) (Fin.castAdd b i) (Fin.natAdd a j)) 0
        (GlobalTheory.Shin.br a b (p : Matrix (Fin (a + b)) (Fin (a + b)) F)) := by
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
      exact (tl_entry _ i j _ _ (by simp) (by simp)).symm
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, Matrix.zero_apply]
      exact h _ _ (by simp) (by simp)
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
      exact (br_entry _ i j _ _ (by simp) (by simp)).symm
  have hu : IsUnit (p : Matrix (Fin (a + b)) (Fin (a + b)) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hM, Matrix.det_fromBlocks_zero₂₁,
    IsUnit.mul_iff] at hu
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).2 hu.1, (Matrix.isUnit_iff_isUnit_det _).2 hu.2⟩

private theorem toG_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((GlobalTheory.Shin.toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold GlobalTheory.Shin.toG
  rw [dif_pos h]
  rfl

private theorem sv0 {s n : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n) (i : Fin (d 0)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩ : Fin n) : ℕ) = i := by
  rw [GlobalTheory.SmGL.stdBlocks_val]
  simp

private theorem svS {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (c : Fin s) (i : Fin (d c.succ)) :
    ((GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩ : Fin n) : ℕ) =
      d 0 + ((GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩ : Fin b) : ℕ) := by
  rw [GlobalTheory.SmGL.stdBlocks_val, GlobalTheory.SmGL.stdBlocks_val]
  erw [Fin.sum_univ_succ]
  rw [add_assoc]
  congr 2

private theorem inPar_of {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (p : GL (Fin n) F)
    (hp : p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd)) : GlobalTheory.Shin.InPar (d 0) p := by
  intro i j hj hi
  obtain ⟨⟨α, i'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective i
  obtain ⟨⟨β, j'⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.mem_parab_iff] at hp
  cases β using Fin.cases with
  | zero =>
    cases α using Fin.cases with
    | zero =>
      rw [sv0] at hi
      exact absurd i'.isLt (by omega)
    | succ c => exact hp _ _ _ _ (Fin.succ_pos c)
  | succ c =>
    rw [svS d hd hb] at hj
    omega

private theorem brG_entry {s n b : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∑ i, d i = n)
    (hb : ∑ i : Fin s, d i.succ = b) (hn : n = d 0 + b) (p : GL (Fin n) F)
    (h : GlobalTheory.Shin.InPar (d 0) p) (c c' : Fin s) (i : Fin (d c.succ)) (j : Fin (d c'.succ)) :
    ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c', j⟩) =
      (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c'.succ, j⟩) := by
  unfold GlobalTheory.Shin.brG
  rw [toG_coe (units_of hn p h).2]
  exact br_entry _ _ _ _ _ (svS d hd hb c i) (svS d hd hb c' j)

end ParConsAux

theorem UpperTheory.Gal.InertialTypesAlt.parCons :
    ParCons := by
  intro F _ s n d hd b hb p
  have hn : n = d 0 + b := by rw [← hd, ← hb, Fin.sum_univ_succ]
  refine ⟨⟨fun hp => ⟨inPar_of d hd hb p hp, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩, fun hp hp' => ⟨?_, fun c => ?_⟩⟩
  · have h1 := inPar_of d hd hb p hp
    rw [GlobalTheory.SmGL.mem_parab_iff] at hp ⊢
    intro c c' i j hc
    rw [brG_entry d hd hb hn p h1]
    exact hp _ _ _ _ (Fin.succ_lt_succ_iff.2 hc)
  · rw [GlobalTheory.SmGL.mem_parab_iff] at h2 ⊢
    intro α β i j hαβ
    cases α using Fin.cases with
    | zero => exact absurd hαβ (Fin.not_lt_zero _)
    | succ c =>
      cases β using Fin.cases with
      | zero =>
        apply h1
        · rw [sv0]; exact j.isLt
        · rw [svS d hd hb]; omega
      | succ c' =>
        rw [← brG_entry d hd hb hn p h1]
        exact h2 _ _ _ _ (Fin.succ_lt_succ_iff.1 hαβ)
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨0, i⟩)
      (GlobalTheory.SmGL.stdBlocks d hd ⟨0, j⟩) = _
    unfold GlobalTheory.Shin.tlG
    rw [toG_coe (units_of hn p h1).1]
    exact (tl_entry _ _ _ _ _ (sv0 d hd i) (sv0 d hd j)).symm
  · have h1 := inPar_of d hd hb p hp
    ext i j
    change (p : Matrix (Fin n) (Fin n) F) (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, i⟩)
        (GlobalTheory.SmGL.stdBlocks d hd ⟨c.succ, j⟩) =
      ((GlobalTheory.Shin.brG (d 0) b p : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, i⟩)
        (GlobalTheory.SmGL.stdBlocks (fun i : Fin s => d i.succ) hb ⟨c, j⟩)
    rw [brG_entry d hd hb hn p h1]
