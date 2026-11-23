import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.coc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∀ s s' x y, Ok x y → Cgr m (w (s * s') x y) (w s x y * tw X m M s (w s') x y) := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw s s' x y hxy
  unfold Lv at hL
  unfold IsSec at ht
  unfold IsSymb at hw
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := admB Ω ε X
  set x1 := gr M s⁻¹ x
  set y1 := gr M s⁻¹ y
  have hxy1 : Ok x1 y1 := (hok x y hxy).2.2.1 s⁻¹
  have hxy2 : Ok (gr M s'⁻¹ x1) (gr M s'⁻¹ y1) := (hok x1 y1 hxy1).2.2.1 s'⁻¹
  have ex : gr M (s * s')⁻¹ x = gr M s'⁻¹ x1 := by rw [mul_inv_rev, (hgr _ _ _).1]
  have ey : gr M (s * s')⁻¹ y = gr M s'⁻¹ y1 := by rw [mul_inv_rev, (hgr _ _ _).1]
  have w1 := (hw s' x1 y1 hxy1).2
  have w2 := (hw s x y hxy).2
  have w3 := (hw (s * s') x y hxy).2
  rw [ex, ey] at w3
  have pt : ∀ a b : Row M, Ok a b → IsPt X m (sg X c M a) (sg X d M b) (t (sg X c M a) (sg X d M b)) := by
    intro a b hab
    exact (ht _ _ (sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).1 (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).1).1
  have gs : ∀ (r : Gal(Ω/ℚ)) (a b : Row M), Ok a b → (X.gal r) (sg X c M a) = sg X c M (gr M r a) ∧ (X.gal r) (sg X d M b) = sg X d M (gr M r b) := by
    intro r a b hab
    exact ⟨(sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).2.2.1 r, (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).2.2.1 r⟩
  have inv1 : ∀ (r : Gal(Ω/ℚ)) (a : Row M), gr M r (gr M r⁻¹ a) = a := by
    intro r a
    rw [← (hgr _ _ _).1, mul_inv_cancel, (hgr 1 1 a).2]
  have q1 : IsPt X m ((X.gal s') (sg X c M (gr M s'⁻¹ x1))) ((X.gal s') (sg X d M (gr M s'⁻¹ y1))) (t (sg X c M x1) (sg X d M y1)) := by
    rw [(gs s' _ _ hxy2).1, (gs s' _ _ hxy2).2, inv1, inv1]
    exact pt _ _ hxy1
  have q2 : IsPt X m ((X.gal s) ((X.gal s') (sg X c M (gr M s'⁻¹ x1)))) ((X.gal s) ((X.gal s') (sg X d M (gr M s'⁻¹ y1)))) (t (sg X c M x) (sg X d M y)) := by
    rw [(gs s' _ _ hxy2).1, (gs s' _ _ hxy2).2, inv1, inv1, (gs s _ _ hxy1).1, (gs s _ _ hxy1).2, inv1, inv1]
    exact pt _ _ hxy
  have comp := mvComp Ω ε X m hm (X.gal s') (X.gal s) s' s (hadm s') (hadm s) _ _ _ _ _ (pt _ _ hxy2) q1 q2 _ _ w1 w2
  have eg : (X.gal s').trans (X.gal s) = X.gal (s * s') := by
    ext f
    rw [gal_mul_apply]
    rfl
  rw [eg] at comp
  have u := ((mvEx Ω ε X m hm (X.gal (s * s')) (s * s') (hadm _) _ _ _ (pt _ _ hxy2)).2.2.2 _ ?_ _ _ comp).1 w3
  · unfold tw
    rw [mul_comm (w s x y)]
    exact u
  · rw [gal_mul_apply, gal_mul_apply]
    exact q2
