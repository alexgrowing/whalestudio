import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

namespace UnipotentNormalization

def up {F : Type} [Field F] (u t : F) (hu : u ≠ 0) : GL (Fin 2) F :=
  ⟨!![u, t; 0, 1], !![u⁻¹, -t * u⁻¹; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring⟩

theorem up_mem (hM : AMem) {F : Type} [Field F] [NumberField F] (u t : F) (hu : u ≠ 0)
    (h1 : IsIntegral ℤ u) (h2 : IsIntegral ℤ u⁻¹) (h3 : IsIntegral ℤ t) : jF F (up u t hu) ∈ K0 F := by
  have hI : ∀ g : GL (Fin 2) F, (∀ i j, IsIntegral ℤ (g.val i j)) → ∀ i j, (jF F g).val i j ∈ Ohat F := by
    intro g hg i j
    change algebraMap F (Af F) (g.val i j) ∈ Ohat F
    exact ((hM F).2.2.2.2.2.1 _).1 (hg i j)
  refine ((hM F).1 _).2 ⟨hI _ ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [up, h1, h3, isIntegral_zero, isIntegral_one]
  · rw [← map_inv]
    refine hI _ ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp [up, h2, isIntegral_zero, isIntegral_one, h3.mul h2]

theorem ht01 {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem ht_inv {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (h2 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ γ x, D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x)
    (h3 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ a : F, a ≠ 0 → ∀ x, D.hf (a • s) x = D.hf s x * ∏ v, D.σ v a ^ 2)
    (b : GL (Fin 2) F) (hb : b 1 0 = 0) (z : X I) (x : Gf) :
    D.Ht ![0, 1] (D.act b z) (D.j b * x) = D.Ht ![0, 1] z x := by
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  have hdb : b.val.det = b 0 0 * b 1 1 := by
    rw [Matrix.det_fin_two]; simp [hb]
  have hdet : b.val.det ≠ 0 := b.det_ne_zero
  have hd : b 1 1 ≠ 0 := fun e => hdet (by rw [hdb, e, mul_zero])
  have hv : (![0, 1] : Fin 2 → F) ᵥ* b.val = b 1 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb]
  have key := h2 _ hs b x
  rw [hv, h3 _ hs _ hd] at key
  have him : ∀ v, ((D.act b z v).1).im = D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im := by
    intro v
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    simp only [Dat.act, coe_smul]
    rw [im_div, det_eq]
    simp [den, Dat.r, hb, Complex.normSq_ofReal]
    field_simp
  rw [ht01, ht01]
  simp_rw [him]
  have hpd : ∏ v, |D.σ v b.val.det| ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => abs_ne_zero.2 ((map_ne_zero _).2 hdet)
  apply mul_right_cancel₀ hpd
  have e : (∏ v, |D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im|) * ∏ v, D.σ v (b 1 1) ^ 2 =
      (∏ v, |(z v).1.im|) * ∏ v, |D.σ v b.val.det| := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    rw [hdb, map_mul, abs_mul, abs_mul, abs_div, ← sq_abs (D.σ v (b 1 1))]
    have : |D.σ v (b 1 1)| ≠ 0 := abs_ne_zero.2 hσ
    field_simp
  rw [mul_assoc, key]
  linear_combination D.hf ![0, 1] x * e

theorem act_up {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ) (χ : Hc c →* ℂˣ)
    (u t : F) (hu : u ≠ 0) (z : X (InfinitePlace F)) (v : InfinitePlace F) :
    (((mkDat c χ).act (up u t hu) z) v).1 = (sg v u : ℂ) * (z v).1 + (sg v t : ℂ) := by
  simp [Dat.act, coe_smul, num, den, Dat.r, up, mkDat]

theorem low {ι : Type} [Fintype ι] (y : ι → ℝ) {C c₀ M : ℝ} (hC : 0 < C) (hM : 0 < M)
    (hy : ∀ v v', |y v| ≤ C * |y v'|) (h : c₀ ≤ (∏ v, |y v|) * M) (v : ι) : min 1 (c₀ / M) / C ≤ |y v| := by
  rw [div_le_iff₀ hC, mul_comm]
  have ha : 0 ≤ C * |y v| := by positivity
  rcases le_or_gt 1 (C * |y v|) with h1 | h1
  · exact (min_le_left _ _).trans h1
  · have : Nonempty ι := ⟨v⟩
    have hp : ∏ v', |y v'| ≤ (C * |y v|) ^ Fintype.card ι := by
      rw [← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun v' _ => hy v' v
    have hpow := pow_le_of_le_one ha h1.le (Fintype.card_ne_zero (α := ι))
    have hcm : c₀ / M ≤ C * |y v| := by
      rw [div_le_iff₀ hM]
      exact h.trans (mul_le_mul_of_nonneg_right (hp.trans hpow) hM.le)
    exact (min_le_right _ _).trans hcm

end UnipotentNormalization

open UnipotentNormalization in
theorem dNormal : AMem → ABnfH → AOrb → AUnit → ATrans → DHt → DMul → DNormal := by
  intro hM hB hO hU hT hH hMu F _ _ _ c hc χ c₀ hc₀
  classical
  obtain ⟨S0, hS0⟩ := hB F c hc
  choose S' hS' using fun x1 : GF F => hO F c hc x1
  obtain ⟨CU, hCU, hU'⟩ := hU F
  obtain ⟨CT, hCT, hT'⟩ := hT F
  obtain ⟨-, h2, h3⟩ := hH F c hc χ
  obtain ⟨hm, -⟩ := hMu F c hc χ
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  set S := S0.biUnion S' with hSdef
  set M : ℝ := 1 + ∑ x' ∈ S, |(mkDat c χ).hf ![0, 1] x'| with hMdef
  have hM0 : 0 < M := by positivity
  have hMS : ∀ x' ∈ S, (mkDat c χ).hf ![0, 1] x' ≤ M := fun x' hx' =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun x' => |(mkDat c χ).hf ![0, 1] x'|)
      (fun _ _ => abs_nonneg _) hx').trans (le_add_of_nonneg_left zero_le_one))
  refine ⟨S, max CU CT, min 1 (c₀ / M) / CU, by positivity, fun z x hz => ?_⟩
  obtain ⟨b1, hb1, x1, hx1, h1, hh1, e1⟩ := hS0 x
  obtain ⟨u, hu0, hui, hui', hu⟩ := hU' (fun v => (((mkDat c χ).act b1 z) v).1.im) (fun v => (((mkDat c χ).act b1 z) v).2)
  obtain ⟨t, hti, ht⟩ := hT' (fun v => sg v u * (((mkDat c χ).act b1 z) v).1.re)
  obtain ⟨x', hx', h2', hh2, e2⟩ := hS' x1 _ (up_mem hM u t hu0 hui hui' hti)
  have hb : (up u t hu0 * b1) 1 0 = 0 := by
    simp [up, Matrix.mul_apply, Fin.sum_univ_two, hb1]
  have hact : (mkDat c χ).act (up u t hu0 * b1) z = (mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z) := by
    funext v; simp only [Dat.act, map_mul, mul_smul]
  have hj : (mkDat c χ).j (up u t hu0 * b1) * x = x' * (h2' * h1) := by
    change jF F (up u t hu0 * b1) * x = _
    rw [map_mul, mul_assoc, e1, ← mul_assoc, e2, mul_assoc]
  have hH' : h2' * h1 ∈ (mkDat c χ).H := Subgroup.mem_sup_left (mul_mem hh2 hh1)
  have hx'S : x' ∈ S := Finset.mem_biUnion.2 ⟨x1, hx1, hx'⟩
  refine ⟨up u t hu0 * b1, hb, ⟨x', hx'S, h2' * h1, hH', hj⟩, ?_⟩
  have e := ht_inv (mkDat c χ) h2 h3 _ hb z x
  rw [← e, hj, hact, ht01, hm _ hs _ _ hH'] at hz
  rw [hact]
  have hre : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.re =
      sg v u * (((mkDat c χ).act b1 z) v).1.re + sg v t := by
    intro v; rw [act_up]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im =
      sg v u * (((mkDat c χ).act b1 z) v).1.im := by
    intro v; rw [act_up]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hy : ∀ v v', |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im| ≤
      CU * |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v').1.im| := by
    intro v v'; rw [him, him]; exact hu v v'
  have hprod : c₀ ≤ (∏ v, |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im|) * M :=
    hz.trans (mul_le_mul_of_nonneg_left (hMS x' hx'S) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
  intro v
  refine ⟨?_, low _ hCU hM0 hy hprod v, fun v' => ?_⟩
  · rw [hre]; exact (ht v).trans (le_max_right _ _)
  · exact (hy v v').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

end UpperTheory.Esk
