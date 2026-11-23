import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CastVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Square

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

theorem pRed : PRed := by
  unfold PRed
  intro Ω _ _ _ ε X k m c d M hk hm hc hd hc6 hd6 hLv t' t w' w hsec' hsec hsym' hsym
  obtain ⟨hM, hcM, hdM⟩ := hLv
  have hkm : 0 < k * m := Nat.mul_pos hk hm
  obtain ⟨hAslR, hAgal, -⟩ := admB Ω ε X
  obtain ⟨hgrM, hokM, -⟩ := rowB Ω M hM
  obtain ⟨hred, hredmv⟩ := redB Ω ε X k m hk hm
  have hinvM : ∀ (s : Gal(Ω/ℚ)) (x : Row M), gr M s (gr M s⁻¹ x) = x := by
    intro s x
    rw [← (hgrM s s⁻¹ x).1, mul_inv_cancel, (hgrM 1 1 x).2]
  have sgc := sgB Ω ε X c M hc hc6 hM hcM
  have sgd := sgB Ω ε X d M hd hd6 hM hdM
  obtain ⟨a, hcob, ha⟩ := cmp Ω ε X m M hm hM (sg X c M) (sg X d M)
    (fun x y => Pt.red k m (t' (sg X c M x) (sg X d M y)))
    (fun x y => t (sg X c M x) (sg X d M y)) w' w
    (fun x y h => by
      obtain ⟨hx0, hy0, -⟩ := hokM x y h
      exact ⟨hred _ _ _ (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).1,
        (hsec _ _ (sgc x hx0).1 (sgd y hy0).1).1⟩)
    (fun s x y h => by
      have h1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hokM x y h).2.2.1 s⁻¹
      obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
      obtain ⟨hx0, hy0, -⟩ := hokM x y h
      have ex : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
        rw [(sgc _ hx1).2.2.1 s, hinvM]
      have ey : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
        rw [(sgd _ hy1).2.2.1 s, hinvM]
      refine ⟨ex, ey, ?_, (hsym s x y h).2⟩
      refine hredmv (X.gal s) s (hAgal s) _ _ _ _
        (hsec' _ _ (sgc _ hx1).1 (sgd _ hy1).1).1 ?_ _ (hsym' s x y h).2
      rw [ex, ey]
      exact (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).1)
  refine ⟨a, fun x y h => ⟨(ha x y h).1, fun γ => ?_⟩, hcob⟩
  obtain ⟨hx0, hy0, -⟩ := hokM x y h
  have h1 : Ok (rt x γ) (rt y γ) := (hokM x y h).2.2.2 γ
  obtain ⟨hx1, hy1, -⟩ := hokM _ _ h1
  have hT : Mv X m (slR X (ofSL γ)) 1 (t (sg X c M x) (sg X d M y))
      (t (sg X c M (rt x γ)) (sg X d M (rt y γ))) 1 := by
    have e := (hsec _ _ (sgc x hx0).1 (sgd y hy0).1).2 γ
    rwa [(sgc x hx0).2.1 γ, (sgd y hy0).2.1 γ] at e
  have hR : Mv X m (slR X (ofSL γ)) 1 (Pt.red k m (t' (sg X c M x) (sg X d M y)))
      (Pt.red k m (t' (sg X c M (rt x γ)) (sg X d M (rt y γ)))) 1 := by
    have e := (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).2 γ
    rw [(sgc x hx0).2.1 γ, (sgd y hy0).2.1 γ] at e
    refine hredmv _ 1 (hAslR _) _ _ _ _ (hsec' _ _ (sgc x hx0).1 (sgd y hy0).1).1 ?_ _ e
    have e1 : slR X (ofSL γ) (sg X c M x) = sg X c M (rt x γ) := (sgc x hx0).2.1 γ
    have e2 : slR X (ofSL γ) (sg X d M y) = sg X d M (rt y γ) := (sgd y hy0).2.1 γ
    rw [e1, e2]
    exact (hsec' _ _ (sgc _ hx1).1 (sgd _ hy1).1).1
  exact (ha x y h).2 (slR X (ofSL γ)) (rt x γ) (rt y γ) (hAslR _) h1
    ((sgc x hx0).2.1 γ) ((sgd y hy0).2.1 γ) hR hT

end UpperTheory.V.Z.Kato.Sym

end
