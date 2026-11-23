import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.EOmZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.Cancel

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.dgPt :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d k M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → 0 < k →
        ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∃ Q : Row M → Row M → Pt X m, ∀ x y, Ok x y →
          IsPt X m (X.sl (dg k) (sg X c M x)) (X.sl (dg k) (sg X d M y)) (Q x y) ∧
          (∀ s, Mv X m (X.gal s) s (Q (gr M s⁻¹ x) (gr M s⁻¹ y)) (Q x y) (slU X (dg k) (w s x y))) ∧
          ∀ γ γ' : SL(2, ℤ), !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1] →
            Mv X m (slR X (ofSL γ)) 1 (Q x y) (Q (rt x γ') (rt y γ')) 1 := by
  intro Ω _ _ _ ε X m c d k M hm hc hd hc6 hd6 hL hk t w hsec hsym
  obtain ⟨hM, hcM, hdM⟩ := hL
  have hA := admB Ω ε X
  have hG := galDg Ω ε X k hk
  have hR := rowB Ω M hM
  have hSc := sgB Ω ε X c M hc hc6 hM hcM
  have hSd := sgB Ω ε X d M hd hd6 hM hdM
  have hE := mvEx Ω ε X m hm
  have hcyc : cyc m (1 : Gal(Ω/ℚ)) = 1 := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
  have hτ : admitted X (slR X (dg k)) 1 := hA.1 (dg k)
  have hex : ∀ x y : Row M, ∃ Q : Pt X m, Ok x y →
      IsPt X m (X.sl (dg k) (sg X c M x)) (X.sl (dg k) (sg X d M y)) Q ∧
        Mv X m (slR X (dg k)) 1 (t (sg X c M x) (sg X d M y)) Q 1 := by
    intro x y
    by_cases h : Ok x y
    · obtain ⟨hx, hy, -, -⟩ := hR.2.1 x y h
      have hP := (hsec _ _ (hSc x hx).1 (hSd y hy).1).1
      obtain ⟨Q, hQ⟩ := (hE _ 1 hτ _ _ _ hP).2.1
      exact ⟨Q, fun _ => hQ⟩
    · exact ⟨t (sg X c M x) (sg X d M y), fun h' => absurd h' h⟩
  choose Q hQ using hex
  refine ⟨Q, fun x y hxy => ⟨(hQ x y hxy).1, ?_, ?_⟩⟩
  · intro s
    have hxy' : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hR.2.1 x y hxy).2.2.1 s⁻¹
    obtain ⟨hx, hy, -, -⟩ := hR.2.1 x y hxy
    obtain ⟨hx', hy', -, -⟩ := hR.2.1 _ _ hxy'
    have ex : gr M s (gr M s⁻¹ x) = x := by
      rw [← (hR.1 s s⁻¹ x).1, mul_inv_cancel, (hR.1 1 1 x).2]
    have ey : gr M s (gr M s⁻¹ y) = y := by
      rw [← (hR.1 s s⁻¹ y).1, mul_inv_cancel, (hR.1 1 1 y).2]
    have gu : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
      rw [(hSc _ hx').2.2.1 s, ex]
    have gv : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
      rw [(hSd _ hy').2.2.1 s, ey]
    have hP' := (hsec _ _ (hSc _ hx').1 (hSd _ hy').1).1
    have hP := (hsec _ _ (hSc x hx).1 (hSd y hy).1).1
    obtain ⟨-, hmv⟩ := hsym s x y hxy
    obtain ⟨hQ'1, hQ'2⟩ := hQ _ _ hxy'
    obtain ⟨hQ1, hQ2⟩ := hQ x y hxy
    have hPg : IsPt X m (X.gal s (sg X c M (gr M s⁻¹ x))) (X.gal s (sg X d M (gr M s⁻¹ y)))
        (t (sg X c M x) (sg X d M y)) := by
      rw [gu, gv]; exact hP
    have hQg : IsPt X m (X.sl (dg k) (X.gal s (sg X c M (gr M s⁻¹ x))))
        (X.sl (dg k) (X.gal s (sg X d M (gr M s⁻¹ y)))) (Q x y) := by
      rw [gu, gv]; exact hQ1
    have hcomp := mvComp Ω ε X m hm (X.gal s) (slR X (dg k)) s 1 (hA.2.1 s) hτ _ _ _ _ _
      hP' hPg hQg _ _ hmv hQ2
    have heq : (X.gal s).trans (slR X (dg k)) = (slR X (dg k)).trans (X.gal s) := by
      ext f
      exact (hG.1 s f).symm
    rw [heq, one_mul] at hcomp
    have hc2 : Mv X m ((slR X (dg k)).trans (X.gal s)) (s * 1)
        (t (sg X c M (gr M s⁻¹ x)) (sg X d M (gr M s⁻¹ y))) (Q x y)
        ((unU X (slR X (dg k))) (w s x y) ^ (cyc m (1 : Gal(Ω/ℚ))).val * 1) := by
      rw [mul_one]; exact hcomp
    have hR' : IsPt X m (X.gal s (X.sl (dg k) (sg X c M (gr M s⁻¹ x))))
        (X.gal s (X.sl (dg k) (sg X d M (gr M s⁻¹ y)))) (Q x y) := by
      rw [hG.1 s, hG.1 s, gu, gv]; exact hQ1
    have hres := PC.cancel Ω ε X m hm (slR X (dg k)) (X.gal s) 1 s hτ (hA.2.1 s) _ _ _ _ _
      hP' hQ'1 hR' _ hQ'2 hc2
    refine ((hE (X.gal s) s (hA.2.1 s) _ _ _ hQ'1).2.2.2 _ hR' _ _ hres).mpr ?_
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · haveI : Fact (1 < m) := ⟨h1⟩
      refine ⟨1, ?_⟩
      rw [hcyc, ZMod.val_one, pow_one, mul_one, one_pow, mul_one]
      rfl
    · obtain rfl : m = 1 := by omega
      refine ⟨((unU X (slR X (dg k))) (w s x y) ^ (cyc 1 (1 : Gal(Ω/ℚ))).val * 1)⁻¹ * slU X (dg k) (w s x y), ?_⟩
      rw [pow_one, mul_inv_cancel_left]
  · intro γ γ' hγ
    obtain ⟨hx, hy, -, hrt⟩ := hR.2.1 x y hxy
    have hxy'' := hrt γ'
    obtain ⟨hx'', hy'', -, -⟩ := hR.2.1 _ _ hxy''
    have ux : sg X c M (rt x γ') = X.sl (ofSL γ') (sg X c M x) := ((hSc x hx).2.1 γ').symm
    have vy : sg X d M (rt y γ') = X.sl (ofSL γ') (sg X d M y) := ((hSd y hy).2.1 γ').symm
    have hP := hsec _ _ (hSc x hx).1 (hSd y hy).1
    have h1 := hP.2 γ'
    rw [← ux, ← vy] at h1
    have hP'' : IsPt X m (X.sl (ofSL γ') (sg X c M x)) (X.sl (ofSL γ') (sg X d M y))
        (t (sg X c M (rt x γ')) (sg X d M (rt y γ'))) := by
      rw [← ux, ← vy]; exact (hsec _ _ (hSc _ hx'').1 (hSd _ hy'').1).1
    obtain ⟨hQ1, hQ2⟩ := hQ x y hxy
    obtain ⟨hQ''1, hQ''2⟩ := hQ _ _ hxy''
    have hQ''g : IsPt X m (X.sl (dg k) (X.sl (ofSL γ') (sg X c M x)))
        (X.sl (dg k) (X.sl (ofSL γ') (sg X d M y))) (Q (rt x γ') (rt y γ')) := by
      rw [← ux, ← vy]; exact hQ''1
    have hcomp := mvComp Ω ε X m hm (slR X (ofSL γ')) (slR X (dg k)) 1 1 (hA.1 _) hτ _ _ _ _ _
      hP.1 hP'' hQ''g _ _ h1 hQ''2
    have heq : (slR X (ofSL γ')).trans (slR X (dg k)) = (slR X (dg k)).trans (slR X (ofSL γ)) := by
      ext f
      exact (hG.2.1 γ γ' hγ f).symm
    rw [heq, map_one, one_pow, mul_one, mul_one] at hcomp
    have hR' : IsPt X m (X.sl (ofSL γ) (X.sl (dg k) (sg X c M x)))
        (X.sl (ofSL γ) (X.sl (dg k) (sg X d M y))) (Q (rt x γ') (rt y γ')) := by
      rw [hG.2.1 γ γ' hγ, hG.2.1 γ γ' hγ, ← ux, ← vy]; exact hQ''1
    exact PC.cancel Ω ε X m hm (slR X (dg k)) (slR X (ofSL γ)) 1 1 hτ (hA.1 _) _ _ _ _ _
      hP.1 hQ1 hR' 1 hQ2 (by rw [mul_one]; exact hcomp)
