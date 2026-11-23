import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

theorem pLev : PLev := by
  unfold PLev
  intro Ω _ _ _ ε X m c d k M hm hc hd hc6 hd6 hlv t w' w ht hw' hw
  obtain ⟨hkM, hck, hdk⟩ := hlv
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hkM)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkM)
  obtain ⟨-, hgal, -, -, -, -, -, hUn⟩ := admB Ω ε X
  obtain ⟨hgr, hok, -, hup⟩ := rowB Ω M hM
  obtain ⟨-, hokK, -, -⟩ := rowB Ω (k * M) hkM
  obtain ⟨hupQ, hupOk, hupgr, -⟩ := hup k hk
  have hsgup : ∀ e : ℕ, 1 < e → e.Coprime 6 → e.Coprime (k * M) → ∀ z : Row M, z ≠ 0 →
      up k M z ≠ 0 → sg X e (k * M) (up k M z) = sg X e M z := by
    intro e he he6 hek z hz hz'
    have hem : e.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hek
    rw [← (sgB Ω ε X e (k * M) he he6 hkM hek (up k M z) hz').2.2.2 (toQ M z)
      (fun i => ⟨0, by simp [hupQ z]⟩)]
    exact (sgB Ω ε X e M he he6 hM hem z hz).2.2.2 (toQ M z) (fun i => ⟨0, by simp⟩)
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hck
  have hdM : d.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hdk
  unfold Coh Eqv CobBy
  refine ⟨fun _ _ => (1 : X.Kˣ), ?_, ?_⟩
  · intro x y _
    refine ⟨(hUn m).1, fun γ => ⟨1, by simp [slU]⟩⟩
  · intro s x y hxy
    have hxy1 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hok x y hxy).2.2.1 s⁻¹
    have hupxy := hupOk x y hxy
    have hupxy1 := hupOk _ _ hxy1
    have hx := (hok x y hxy).1
    have hy := (hok x y hxy).2.1
    have hx1 := (hok _ _ hxy1).1
    have hy1 := (hok _ _ hxy1).2.1
    have hux := (hokK _ _ hupxy).1
    have huy := (hokK _ _ hupxy).2.1
    have hux1 := (hokK _ _ hupxy1).1
    have huy1 := (hokK _ _ hupxy1).2.1
    obtain ⟨-, hwMv⟩ := hw s x y hxy
    obtain ⟨-, hw'Mv⟩ := hw' s (up k M x) (up k M y) hupxy
    rw [hupgr s⁻¹ x, hupgr s⁻¹ y, hsgup c hc hc6 hck _ hx1 hux1, hsgup d hd hd6 hdk _ hy1 huy1,
      hsgup c hc hc6 hck _ hx hux, hsgup d hd hd6 hdk _ hy huy] at hw'Mv
    have hgx : ∀ z : Row M, gr M s (gr M s⁻¹ z) = z := by
      intro z
      rw [← (hgr s s⁻¹ z).1, mul_inv_cancel, (hgr 1 1 z).2]
    have hτu : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by
      rw [(sgB Ω ε X c M hc hc6 hM hcM _ hx1).2.2.1 s, hgx]
    have hτv : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by
      rw [(sgB Ω ε X d M hd hd6 hM hdM _ hy1).2.2.1 s, hgx]
    have hP := (ht (sg X c M (gr M s⁻¹ x)) (sg X d M (gr M s⁻¹ y))
      (sgB Ω ε X c M hc hc6 hM hcM _ hx1).1 (sgB Ω ε X d M hd hd6 hM hdM _ hy1).1).1
    have hQ := (ht (sg X c M x) (sg X d M y)
      (sgB Ω ε X c M hc hc6 hM hcM _ hx).1 (sgB Ω ε X d M hd hd6 hM hdM _ hy).1).1
    have key := (mvEx Ω ε X m hm (X.gal s) s (hgal s) _ _ _ hP).2.2.2 _
      (by rw [hτu, hτv]; exact hQ) _ (w' s (up k M x) (up k M y)) hwMv
    have htw : tw X m M s (fun _ _ => (1 : X.Kˣ)) x y = 1 := by simp [tw]
    rw [htw, mul_one, div_one]
    exact key.1 hw'Mv

end UpperTheory.V.Z.Kato.Sym

end
