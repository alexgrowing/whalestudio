import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem isHomogeneous_multiset_prod_map {σ : Type*} (φ : ℕ → MvPolynomial σ ℤ)
    (hφ : ∀ b, (φ b).IsHomogeneous b) (t : Multiset ℕ) : ((t.map φ).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (hφ a).mul ih

theorem isHomogeneous_hsymm (N a : ℕ) : (hsymm (Fin N) ℤ a).IsHomogeneous a := by
  have h : ∀ t : Multiset (Fin N),
      ((t.map X).prod : MvPolynomial (Fin N) ℤ).IsHomogeneous (Multiset.card t) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one (Fin N) ℤ
    | cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
      exact (isHomogeneous_X ℤ b).mul ih
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  simpa [s.2] using h s.1

theorem FlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hSeg : HsymmPairFlagIndependence.Statement) (hSym : SymmetricSpanHsymm.Statement) :
    FlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 m G hGm hGsym Gs Hs hGs hHs Q hQ
  classical

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (Fin.append x u i - Fin.append x' u' i)
      (Fin.append f f₂ i) (Fin.append g g₂ i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact hF1.vertical i
    · simp only [Fin.append_right]
      exact hF2.vertical i
  have hind : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As Bs, A.IsHomogeneous m →
      IsPairExpansion m A As → IsPairExpansion m A Bs →
      pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) As Q =
        pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
          (Fin.append g g₂) Bs Q :=
    fun A As Bs hA h1 h2 => hExp O ϖ hϖ K ι _ d hV (N + N) _ _ _ _ hvert m A hA As Bs h1 h2 Q hQ

  let ex : MvPolynomial (Fin (N + N)) ℤ → Fin (N + N) → MvPolynomial (Fin (N + N) ⊕ Fin (N + N)) ℤ :=
    fun A => Classical.choose (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  have hex : ∀ A, IsPairExpansion m (homogeneousComponent m A) (ex A) :=
    fun A => Classical.choose_spec (exists_isPairExpansion (homogeneousComponent_isHomogeneous m A))
  let pn : MvPolynomial (Fin (N + N)) ℤ →+ ℤ := AddMonoidHom.mk'
    (fun A => pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
      (Fin.append g g₂) (ex A) Q)
    (by
      intro A B'
      have h2 : IsPairExpansion m (homogeneousComponent m (A + B')) (ex A + ex B') := by
        rw [map_add]
        exact isPairExpansion_add (hex A) (hex B')
      rw [hind _ _ _ (homogeneousComponent_isHomogeneous m _) (hex (A + B')) h2]
      exact map_add (pairNumHom (pointIdeal O y) (Fin.append x u) (Fin.append x' u')
        (Fin.append f f₂) (Fin.append g g₂) Q) (ex A) (ex B'))
  have pn_eq : ∀ (A : MvPolynomial (Fin (N + N)) ℤ) As, A.IsHomogeneous m →
      IsPairExpansion m A As →
      pn A = pairNum (pointIdeal O y) (Fin.append x u) (Fin.append x' u') (Fin.append f f₂)
        (Fin.append g g₂) As Q := by
    intro A As hA h
    have h1 := hex A
    rw [homogeneousComponent_eq_self hA] at h1
    exact hind A _ _ hA h1 h

  have seg : ∀ (a r : ℕ) (R : MvPolynomial (Fin (N + N)) ℤ), R.IsHomogeneous r → a + r = m →
      pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R) =
        pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R) := by
    intro a r R hR har
    have hH : (hsymmTimes N (N + N) a R).IsHomogeneous (a + r) :=
      (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
    obtain ⟨As, hAs⟩ := exists_isPairExpansion hH
    have key := hSeg O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' v v' x x' u u' f g f₂ g₂ hF1 hF2
      (N + N) _ _ _ _ hvert a r R hR As As hAs hAs Q (by rw [har]; exact hQ)
    let σx : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.castAdd N) id
    let σu : Fin (N + (N + N)) → Fin (N + N) := Fin.append (Fin.natAdd N) id
    have cx : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σx = Fin.append a₁ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σx, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have cu : ∀ {α : Type} (a₁ a₂ : Fin N → α),
        Fin.append a₁ a₂ ∘ σu = Fin.append a₂ (Fin.append a₁ a₂) := by
      intro α a₁ a₂
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [σu, Function.comp_apply, Fin.append_left, Fin.append_right, id_eq]
    have rx : rename σx (hsymmTimes N (N + N) a R) =
        rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σx ∘ Fin.castAdd (N + N) = Fin.castAdd N := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_left]
      have e2 : σx ∘ Fin.natAdd N = id := by
        funext i
        simp only [σx, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have ru : rename σu (hsymmTimes N (N + N) a R) =
        rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) * R := by
      have e1 : σu ∘ Fin.castAdd (N + N) = Fin.natAdd N := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_left]
      have e2 : σu ∘ Fin.natAdd N = id := by
        funext i
        simp only [σu, Function.comp_apply, Fin.append_right, id_eq]
      simp only [hsymmTimes, map_mul, rename_rename, e1, e2, rename_id, AlgHom.id_apply]
    have hpx := isPairExpansion_push σx hAs
    have hpu := isPairExpansion_push σu hAs
    rw [rx, har] at hpx
    rw [ru, har] at hpu
    rw [pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpx,
      pn_eq _ _ (har ▸ ((isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR)) hpu,
      pairNum_pushExpansion, pairNum_pushExpansion, cx, cx, cx, cx, cu, cu, cu, cu]
    exact key

  have hX : ∀ b, (rename (Fin.castAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have hU : ∀ b, (rename (Fin.natAdd N) (hsymm (Fin N) ℤ b) :
      MvPolynomial (Fin (N + N)) ℤ).IsHomogeneous b :=
    fun b => (isHomogeneous_hsymm N b).rename_isHomogeneous
  have tele : ∀ (t : Multiset ℕ) (s : ℕ) (S : MvPolynomial (Fin (N + N)) ℤ), S.IsHomogeneous s →
      s + t.sum = m →
      pn (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) =
        pn (S * (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intros; rfl
    | cons a t ih =>
      intro s S hS hst
      rw [Multiset.sum_cons] at hst
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have hpX := isHomogeneous_multiset_prod_map _ hX t
      calc pn (S * (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod))
          = pn (rename (Fin.castAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_left_comm]
        _ = pn (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (S * (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod)) :=
            seg a (s + t.sum) _ (hS.mul hpX) (by omega)
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.castAdd N) (hsymm (Fin N) ℤ b)).prod) := by
            congr 1
            ring
        _ = pn ((S * rename (Fin.natAdd N) (hsymm (Fin N) ℤ a)) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod) :=
            ih (s + a) _ (hS.mul (hU a)) (by omega)
        _ = pn (S * (rename (Fin.natAdd N) (hsymm (Fin N) ℤ a) *
              (t.map fun b => rename (Fin.natAdd N) (hsymm (Fin N) ℤ b)).prod)) := by
            rw [mul_assoc]

  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hSym N m G hGm hGsym)
  have hren : ∀ (φ : Fin N → Fin (N + N)), rename φ G =
      ∑ μ, c μ • (μ.parts.map fun b => rename φ (hsymm (Fin N) ℤ b)).prod := by
    intro φ
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_zsmul, hsymmPart, map_multiset_prod, Multiset.map_map]
    rfl
  have hLHS : pairNum (pointIdeal O y) x x' f g Gs Q = pn (rename (Fin.castAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.castAdd N) hGs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_left]
  have hRHS : pairNum (pointIdeal O y) u u' f₂ g₂ Hs Q = pn (rename (Fin.natAdd N) G) := by
    rw [pn_eq _ _ hGm.rename_isHomogeneous (isPairExpansion_push (Fin.natAdd N) hHs),
      pairNum_pushExpansion]
    simp only [Function.comp_def, Fin.append_right]
  rw [hLHS, hRHS, hren, hren, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  have h := tele μ.parts 0 1 (isHomogeneous_one _ _) (by rw [μ.parts_sum, zero_add])
  simpa only [one_mul] using h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
