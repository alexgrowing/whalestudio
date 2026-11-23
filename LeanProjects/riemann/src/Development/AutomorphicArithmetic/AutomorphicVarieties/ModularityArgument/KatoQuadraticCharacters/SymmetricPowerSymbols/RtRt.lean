import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtOfDif
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.KumCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SgDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Square

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem rt_rt {M : ℕ} (x : Row M) (γ δ : SL(2, ℤ)) (h : γ * δ = 1) : rt (rt x γ) δ = x := by
  unfold rt
  rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]
  simp

theorem pDist : PDist := by
  unfold PDist
  intro Ω _ _ _ ε X m c d k M _ _ hm hc hd hc6 hd6 hLv t w' w hsec hsym' hsym
  obtain ⟨hL, hcL, hdL⟩ := hLv
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  haveI : NeZero (k * M) := ⟨hL.ne'⟩
  have hcM : c.Coprime M := (Nat.coprime_mul_iff_right.mp hcL).2
  have hdM : d.Coprime M := (Nat.coprime_mul_iff_right.mp hdL).2
  obtain ⟨hAslR, hAgal, -⟩ := admB Ω ε X
  obtain ⟨hgrM, hokM, -, hup⟩ := rowB Ω M hM
  obtain ⟨-, -, -, hokdn, hgrdn, hrtdn, hsurj⟩ := hup k hk
  obtain ⟨hgrL, hokL, -⟩ := rowB Ω (k * M) hL
  have hinvM : ∀ (s : Gal(Ω/ℚ)) (x : Row M), gr M s (gr M s⁻¹ x) = x := by
    intro s x
    rw [← (hgrM s s⁻¹ x).1, mul_inv_cancel, (hgrM 1 1 x).2]
  have hinvL : ∀ (s : Gal(Ω/ℚ)) (x : Row (k * M)), gr (k * M) s (gr (k * M) s⁻¹ x) = x := by
    intro s x
    rw [← (hgrL s s⁻¹ x).1, mul_inv_cancel, (hgrL 1 1 x).2]
  have hnz : ∀ (x' : Row (k * M)) (x : Row M), dn k M x' = x → x ≠ 0 → x' ≠ 0 := by
    rintro x' x rfl hx rfl
    apply hx
    funext i
    simp [dn]
  have sgc := sgB Ω ε X c (k * M) hc hc6 hL hcL
  have sgd := sgB Ω ε X d (k * M) hd hd6 hL hdL
  have sgcM := sgB Ω ε X c M hc hc6 hM hcM
  have sgdM := sgB Ω ε X d M hd hd6 hM hdM
  have key : ∀ x y : Row M, Ok x y →
      (Finset.univ.filter (fun x' => dn k M x' = x)).Nonempty ∧
      (Finset.univ.filter (fun y' => dn k M y' = y)).Nonempty ∧
      ∀ x' ∈ Finset.univ.filter (fun x' => dn k M x' = x),
        ∀ y' ∈ Finset.univ.filter (fun y' => dn k M y' = y),
          IsPt X m (sg X c (k * M) x') (sg X d (k * M) y')
            (t (sg X c (k * M) x') (sg X d (k * M) y')) := by
    intro x y h
    obtain ⟨x₀, hx₀⟩ := hsurj x
    obtain ⟨y₀, hy₀⟩ := hsurj y
    refine ⟨⟨x₀, by simp [hx₀]⟩, ⟨y₀, by simp [hy₀]⟩, ?_⟩
    intro x' hx' y' hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' hy'
    obtain ⟨hx0, hy0, -⟩ := hokL x' y' (hokdn x' y' (by rw [hx', hy']; exact h))
    exact (hsec _ _ (sgc x' hx0).1 (sgd y' hy0).1).1
  have hex : ∀ x y : Row M, ∃ R : Pt X m, Ok x y →
      IsSum X m (Finset.univ.filter (fun x' => dn k M x' = x))
        (Finset.univ.filter (fun y' => dn k M y' = y))
        (fun x' y' => t (sg X c (k * M) x') (sg X d (k * M) y')) R := by
    intro x y
    by_cases h : Ok x y
    · obtain ⟨R, hR⟩ := (sumB Ω ε X m hm _ _ _ _ (sg X c (k * M)) (sg X d (k * M)) _
        (key x y h).1 (key x y h).2.1 (key x y h).2.2).1
      exact ⟨R, fun _ => hR⟩
    · exact ⟨t (sg X c M x) (sg X d M y), fun h' => absurd h' h⟩
  choose Qs hQs using hex
  have hQpt : ∀ x y : Row M, Ok x y → IsPt X m (sg X c M x) (sg X d M y) (Qs x y) := by
    intro x y h
    obtain ⟨hx0, hy0, -⟩ := hokM x y h
    have hp := (sumB Ω ε X m hm _ _ _ _ (sg X c (k * M)) (sg X d (k * M)) _
      (key x y h).1 (key x y h).2.1 (key x y h).2.2).2 _ (hQs x y h)
    rwa [sgDist Ω ε X c k M hc hc6 hcL x hx0, sgDist Ω ε X d k M hd hd6 hdL y hy0] at hp
  have hfibgr : ∀ (s : Gal(Ω/ℚ)) (z : Row M),
      Set.BijOn (gr (k * M) s⁻¹) ↑(Finset.univ.filter (fun x' => dn k M x' = z))
        ↑(Finset.univ.filter (fun x' => dn k M x' = gr M s⁻¹ z)) := by
    intro s z
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      rw [hgrdn, hi]
    · intro i _ j _ hij
      rw [← hinvL s i, hij, hinvL]
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      refine ⟨gr (k * M) s j, ?_, ?_⟩
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        rw [hgrdn, hj, hinvM]
      · have h1 := hinvL s⁻¹ j
        rwa [inv_inv] at h1
  have hQmv : ∀ (s : Gal(Ω/ℚ)) (x y : Row M), Ok x y →
      Mv X m (X.gal s) s (Qs (gr M s⁻¹ x) (gr M s⁻¹ y)) (Qs x y) (pushD X k M (w' s) x y) := by
    intro s x y h
    have h1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hokM x y h).2.2.1 s⁻¹
    obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
    have hu : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = x),
        sg X c (k * M) i = X.gal s (sg X c (k * M) (gr (k * M) s⁻¹ i)) := by
      intro i hi
      have hm' := (hfibgr s x).1 hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      rw [(sgc _ (hnz _ _ hm' hx1)).2.2.1 s, hinvL]
    have hv : ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = y),
        sg X d (k * M) j = X.gal s (sg X d (k * M) (gr (k * M) s⁻¹ j)) := by
      intro j hj
      have hm' := (hfibgr s y).1 hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      rw [(sgd _ (hnz _ _ hm' hy1)).2.2.1 s, hinvL]
    have hf : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = x),
        ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = y),
          Mv X m (X.gal s) s (t (sg X c (k * M) (gr (k * M) s⁻¹ i)) (sg X d (k * M) (gr (k * M) s⁻¹ j)))
            (t (sg X c (k * M) i) (sg X d (k * M) j)) (w' s i j) := by
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact (hsym' s i j (hokdn i j (by rw [hi, hj]; exact h))).2
    exact sumMv Ω ε X m hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ (gr (k * M) s⁻¹) (gr (k * M) s⁻¹)
      (X.gal s) s (hAgal s) (key _ _ h1).1 (key _ _ h1).2.1 (hfibgr s x) (hfibgr s y)
      (key _ _ h1).2.2 (key x y h).2.2 hu hv (hQs _ _ h1) (hQs x y h) (fun i j => w' s i j) hf
  have hfibrt : ∀ (γ : SL(2, ℤ)) (z : Row M),
      Set.BijOn (fun i : Row (k * M) => rt i γ⁻¹) ↑(Finset.univ.filter (fun x' => dn k M x' = rt z γ))
        ↑(Finset.univ.filter (fun x' => dn k M x' = z)) := by
    intro γ z
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      rw [hrtdn, hi, rt_rt _ _ _ (mul_inv_cancel γ)]
    · intro i _ j _ hij
      have hij' : rt (rt i γ⁻¹) γ = rt (rt j γ⁻¹) γ := by
        simp only at hij
        rw [hij]
      rwa [rt_rt _ _ _ (inv_mul_cancel γ), rt_rt _ _ _ (inv_mul_cancel γ)] at hij'
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj
      refine ⟨rt j γ, ?_, ?_⟩
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        rw [hrtdn, hj]
      · exact rt_rt _ _ _ (mul_inv_cancel γ)
  have hQsl : ∀ (γ : SL(2, ℤ)) (x y : Row M), Ok x y →
      Mv X m (slR X (ofSL γ)) 1 (Qs x y) (Qs (rt x γ) (rt y γ)) 1 := by
    intro γ x y h
    have h1 : Ok (rt x γ) (rt y γ) := (hokM x y h).2.2.2 γ
    obtain ⟨hx0, hy0, -⟩ := hokM _ _ h
    have hu : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = rt x γ),
        sg X c (k * M) i = slR X (ofSL γ) (sg X c (k * M) (rt i γ⁻¹)) := by
      intro i hi
      have hm' := (hfibrt γ x).1 hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      have e1 := (sgc _ (hnz _ _ hm' hx0)).2.1 γ
      rw [rt_rt _ _ _ (inv_mul_cancel γ)] at e1
      exact e1.symm
    have hv : ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = rt y γ),
        sg X d (k * M) j = slR X (ofSL γ) (sg X d (k * M) (rt j γ⁻¹)) := by
      intro j hj
      have hm' := (hfibrt γ y).1 hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm'
      have e1 := (sgd _ (hnz _ _ hm' hy0)).2.1 γ
      rw [rt_rt _ _ _ (inv_mul_cancel γ)] at e1
      exact e1.symm
    have hf : ∀ i ∈ Finset.univ.filter (fun x' => dn k M x' = rt x γ),
        ∀ j ∈ Finset.univ.filter (fun y' => dn k M y' = rt y γ),
          Mv X m (slR X (ofSL γ)) 1 (t (sg X c (k * M) (rt i γ⁻¹)) (sg X d (k * M) (rt j γ⁻¹)))
            (t (sg X c (k * M) i) (sg X d (k * M) j)) ((fun _ _ => (1 : X.Kˣ)) i j) := by
      intro i hi j hj
      have hi' := (hfibrt γ x).1 hi
      have hj' := (hfibrt γ y).1 hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi' hj'
      have hi0 := hnz _ _ hi' hx0
      have hj0 := hnz _ _ hj' hy0
      have e := ((hsec _ _ (sgc _ hi0).1 (sgd _ hj0).1).2 γ)
      rw [(sgc _ hi0).2.1 γ, (sgd _ hj0).2.1 γ, rt_rt _ _ _ (inv_mul_cancel γ),
        rt_rt _ _ _ (inv_mul_cancel γ)] at e
      exact e
    have e := sumMv Ω ε X m hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun i : Row (k * M) => rt i γ⁻¹) (fun i : Row (k * M) => rt i γ⁻¹)
      (slR X (ofSL γ)) 1 (hAslR _) (key x y h).1 (key x y h).2.1 (hfibrt γ x) (hfibrt γ y)
      (key x y h).2.2 (key _ _ h1).2.2 hu hv (hQs x y h) (hQs _ _ h1) (fun _ _ => (1 : X.Kˣ)) hf
    simpa only [Finset.prod_const_one] using e
  obtain ⟨a, hcob, ha⟩ := cmp Ω ε X m M hm hM (sg X c M) (sg X d M) Qs
    (fun x y => t (sg X c M x) (sg X d M y)) (fun s => pushD X k M (w' s)) w
    (fun x y h => by
      obtain ⟨hx0, hy0, -⟩ := hokM x y h
      exact ⟨hQpt x y h, (hsec _ _ (sgcM x hx0).1 (sgdM y hy0).1).1⟩)
    (fun s x y h => by
      have h1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hokM x y h).2.2.1 s⁻¹
      obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
      refine ⟨?_, ?_, hQmv s x y h, (hsym s x y h).2⟩
      · rw [(sgcM _ hx1).2.2.1 s, hinvM]
      · rw [(sgdM _ hy1).2.2.1 s, hinvM])
  refine ⟨a, fun x y h => ⟨(ha x y h).1, fun γ => ?_⟩, hcob⟩
  obtain ⟨hx0, hy0, -⟩ := hokM x y h
  have hT : Mv X m (slR X (ofSL γ)) 1 (t (sg X c M x) (sg X d M y))
      (t (sg X c M (rt x γ)) (sg X d M (rt y γ))) 1 := by
    have e := (hsec _ _ (sgcM x hx0).1 (sgdM y hy0).1).2 γ
    rwa [(sgcM x hx0).2.1 γ, (sgdM y hy0).2.1 γ] at e
  exact (ha x y h).2 (slR X (ofSL γ)) (rt x γ) (rt y γ) (hAslR _) ((hokM x y h).2.2.2 γ)
    ((sgcM x hx0).2.1 γ) ((sgdM y hy0).2.1 γ) (hQsl γ x y h) hT

end UpperTheory.V.Z.Kato.Sym

end
