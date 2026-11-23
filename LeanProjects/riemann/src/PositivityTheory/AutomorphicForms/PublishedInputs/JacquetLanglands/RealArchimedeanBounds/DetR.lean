import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

namespace LatticeCountingLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def box (r : ℝ) : Set F := {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ r}

theorem place_eq (v : InfinitePlace F) (t : F) : v t = |sg v t| := by
  rw [← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]

theorem det_r {c : Pl F → ℕ} (χ : Hc c →* ℂˣ) (v : InfinitePlace F) (g : GL (Fin 2) F) :
    ((mkDat c χ).r v g).val.det = sg v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  rfl

theorem bnd (v : InfinitePlace F) (N : ℕ) (x : F) {b : ℝ} (h : |sg v x| ≤ b) : v ((N : F) * x) ≤ N * b := by
  rw [place_eq, map_mul, map_natCast, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

end LatticeCountingLemmas

open LatticeCountingLemmas in
theorem dCnt : DScale → DBox → DEntry → DCnt := by
  intro hS hB hE F _ _ _ cc hcc χ ω δ C c hδ hc
  classical
  obtain ⟨N, C0, hN, hC0, hg⟩ := hS F cc hcc χ ω
  obtain ⟨CB, hCB⟩ := hB F
  obtain ⟨B, hBd⟩ := hE δ (max C C0) c hδ hc
  choose gg hgg using hg
  have ha : 0 ≤ (N : ℝ) * max B 0 := by positivity
  have hCB0 : 0 ≤ CB := by
    have h0 : ((box (F := F) 0).ncard : ℝ) ≤ CB * (1 + 0 ^ Fintype.card (InfinitePlace F)) := (hCB 0 le_rfl).2
    have h1 : (0 : ℝ) < 1 + 0 ^ Fintype.card (InfinitePlace F) := by positivity
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg h1
    linarith [Nat.cast_nonneg (α := ℝ) (box (F := F) 0).ncard]
  refine ⟨(CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F))) ^ 3 * CB *
    (1 + ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F)), fun z hz => ?_⟩
  obtain ⟨v0⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hz v0).1
  have hR : 0 ≤ (N : ℝ) * max B 0 * C * |(z v0).1.im| := by positivity
  let f : PG F → F × F × F × F := fun γ => if h : γ • ω = ω then
    ((N : F) * gg γ h 1 0, (N : F) * gg γ h 0 0, (N : F) * gg γ h 1 1, (N : F) * gg γ h 0 1) else 0
  have hinj : Set.InjOn f {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)} := by
    intro γ1 h1 γ2 h2 he
    simp only [f, dif_pos h1.1, dif_pos h2.1, Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3, e4⟩ := he
    have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
    have hgeq : gg γ1 h1.1 = gg γ2 h2.1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact mul_left_cancel₀ hN' e2
      · exact mul_left_cancel₀ hN' e4
      · exact mul_left_cancel₀ hN' e1
      · exact mul_left_cancel₀ hN' e3
    calc γ1 = (gg γ1 h1.1 : PG F) := (hgg γ1 h1.1).1.symm
      _ = (gg γ2 h2.1 : PG F) := by rw [hgeq]
      _ = γ2 := (hgg γ2 h2.1).1
  have hmaps : f '' {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)} ⊆
      box ((N : ℝ) * max B 0) ×ˢ box ((N : ℝ) * max B 0) ×ˢ box ((N : ℝ) * max B 0) ×ˢ
        box ((N : ℝ) * max B 0 * C * |(z v0).1.im|) := by
    rintro _ ⟨γ, ⟨hgω, hnear⟩, rfl⟩
    obtain ⟨hgγ, hint, hdet⟩ := hgg γ hgω
    simp only [f, dif_pos hgω]
    generalize gg γ hgω = g at hgγ hint hdet ⊢
    have hE' : ∀ v, |(mkDat cc χ).r v g 1 0| ≤ B ∧ |(mkDat cc χ).r v g 0 0| ≤ B ∧ |(mkDat cc χ).r v g 1 1| ≤ B ∧
        |(mkDat cc χ).r v g 0 1| ≤ B * |(z v).1.im| := by
      intro v
      have hv := hnear v
      rw [← hgγ] at hv
      exact hBd ((mkDat cc χ).r v g) (z v) ((hz v).1.trans (le_max_left _ _)) (hz v).2.1
        (by rw [det_r]; exact (hdet v).2.trans (le_max_right _ _)) hv
    have hB3 : ∀ v i j, |(mkDat cc χ).r v g i j| ≤ B → v ((N : F) * g i j) ≤ (N : ℝ) * max B 0 := fun v i j h =>
      bnd v N (g i j) (h.trans (le_max_left _ _))
    have hB4 : ∀ v : InfinitePlace F, v ((N : F) * g 0 1) ≤ (N : ℝ) * max B 0 * C * |(z v0).1.im| := fun v => by
      have h1 : |(mkDat cc χ).r v g 0 1| ≤ max B 0 * (C * |(z v0).1.im|) :=
        (hE' v).2.2.2.trans (mul_le_mul (le_max_left _ _) ((hz v).2.2 v0) (abs_nonneg _) (le_max_right _ _))
      refine (bnd v N (g 0 1) h1).trans (le_of_eq ?_)
      ring
    exact ⟨⟨hint 1 0, fun v => hB3 v 1 0 (hE' v).1⟩, ⟨hint 0 0, fun v => hB3 v 0 0 (hE' v).2.1⟩,
      ⟨hint 1 1, fun v => hB3 v 1 1 (hE' v).2.2.1⟩, ⟨hint 0 1, hB4⟩⟩
  have hfin := (hCB _ ha).1.prod ((hCB _ ha).1.prod ((hCB _ ha).1.prod (hCB _ hR).1))
  refine ⟨Set.Finite.of_finite_image (hfin.subset hmaps) hinj, ?_⟩
  have hle := Set.ncard_le_ncard hmaps hfin
  rw [hinj.ncard_image, Set.ncard_prod, Set.ncard_prod, Set.ncard_prod] at hle
  have h1 : ((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) ≤ CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F)) :=
    (hCB _ ha).2
  have h4 : ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ) ≤
      CB * (1 + ((N : ℝ) * max B 0 * C * |(z v0).1.im|) ^ Fintype.card (InfinitePlace F)) := (hCB _ hR).2
  have hP : 0 ≤ ∏ v, |(z v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hprod : |(z v0).1.im| ^ Fintype.card (InfinitePlace F) ≤ C ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im| := by
    have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ => |(z v0).1.im|) (g := fun v => C * |(z v).1.im|)
      (fun _ _ => abs_nonneg _) (fun v _ => (hz v0).2.2 v)
    rwa [Finset.prod_const, Finset.card_univ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at this
  have hRd : ((N : ℝ) * max B 0 * C * |(z v0).1.im|) ^ Fintype.card (InfinitePlace F) ≤
      ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im| := by
    calc _ = ((N : ℝ) * max B 0 * C) ^ Fintype.card (InfinitePlace F) * |(z v0).1.im| ^ Fintype.card (InfinitePlace F) :=
          mul_pow _ _ _
      _ ≤ ((N : ℝ) * max B 0 * C) ^ Fintype.card (InfinitePlace F) * (C ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im|) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hX : 0 ≤ CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F)) := mul_nonneg hCB0 (by positivity)
  have hM : 0 ≤ ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F) := by positivity
  have h4' : ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ) ≤
      CB * ((1 + ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F)) * (1 + ∏ v, |(z v).1.im|)) :=
    h4.trans (mul_le_mul_of_nonneg_left (by nlinarith) hCB0)
  have hle' : (({γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)}.ncard : ℕ) : ℝ) ≤
      ((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) * (((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) *
        (((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) * ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ))) := by
    exact_mod_cast hle
  refine hle'.trans ((mul_le_mul h1 (mul_le_mul h1 (mul_le_mul h1 h4' (Nat.cast_nonneg _) hX) (by positivity) hX)
    (by positivity) hX).trans_eq (by ring))
