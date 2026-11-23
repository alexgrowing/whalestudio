import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostCond

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.thmHV :
    PointHV → ∀ (K : BConst) (Ct : ℝ), 0 < Ct → ThmHV K Ct := by
  intro hP K Ct hCt ψ
  obtain ⟨C, r₁, r₂, hr₁, hr₂, hmain⟩ := hP ψ (fun l => Nat.log l (K.Rl l (Lchi ψ l)) + 3)
  refine ⟨(C : ℝ), r₁, r₂, hr₁, hr₂, ?_⟩
  intro eps A1 heps _
  have hJ : 0 < Jchi K Ct eps ψ := BConst.J_pos K hCt heps _ _ _
  refine ⟨(2 : ℝ) ^ Jchi K Ct eps ψ, ?_⟩
  intro e t hadm X hX q d hpair hq hd hlist _ Y hwin x hYx hxY
  obtain ⟨⟨hXY, hYX⟩, hwin'⟩ := hwin
  have hXY' : X ^ (1 / Jchi K Ct eps ψ) ≤ Y := hXY
  have h1 : ((2 : ℝ) ^ Jchi K Ct eps ψ) ^ (1 / Jchi K Ct eps ψ) ≤ X ^ (1 / Jchi K Ct eps ψ) :=
    Real.rpow_le_rpow (by positivity) hX (by positivity)
  rw [one_div, Real.rpow_rpow_inv (by norm_num) hJ.ne'] at h1
  rw [one_div] at hXY'
  have hx2 : (2 : ℝ) ≤ x := by linarith
  obtain ⟨he2, -, ht2, htx⟩ := hadm x hx2
  have hxX : x ≤ X := le_trans hxY hYX
  have htX : (t x : ℝ) ≤ X ^ Ct := le_trans htx (Real.rpow_le_rpow (by linarith) hxX hCt.le)
  intro E _ _ _ hE
  have hB := hwin' x hYx hxY
  have hq' : 2 * t x + 1 < q := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < q by linarith)
  have hd' : 2 * t x + 1 < d := by exact_mod_cast (show (2 * (t x : ℝ) + 1) < d by linarith)
  have hbig : Host.Big ⟨ψ, e x, q, d, he2, hpair⟩ (t x) := by
    refine ⟨hq', hd', ?_⟩
    intro y hy
    apply hlist y
    simp only [Host.q, Host.o, List.mem_cons, List.not_mem_nil] at hy ⊢
    tauto
  have key := hmain ⟨ψ, e x, q, d, he2, hpair⟩ rfl
    (hlist r₁ (by simp)).1 (hlist r₁ (by simp)).2 (hlist r₂ (by simp)).1 (hlist r₂ (by simp)).2
    (t x) ht2 hbig (Real.exp (x ^ (4 * eps / 5))) (Real.exp_pos _).le
    (fun l hl _ => hB.2 l hl) E hE
  rw [hostCond ⟨ψ, e x, q, d, he2, hpair⟩ E hE]
  simpa [Real.rpow_natCast] using key
