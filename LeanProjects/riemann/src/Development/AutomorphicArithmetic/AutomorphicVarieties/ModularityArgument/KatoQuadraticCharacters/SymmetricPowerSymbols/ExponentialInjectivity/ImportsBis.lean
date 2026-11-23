import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvNear
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.GalNear

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.loc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∃ T : Finset Ω, ∀ s s', (∀ z ∈ T, s z = s' z) → ∀ x y, Ok x y → Cgr m (w s x y) (w s' x y) := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw
  unfold Lv at hL
  unfold IsSec at ht
  unfold IsSymb at hw
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := admB Ω ε X
  classical
  haveI : NeZero M := ⟨by omega⟩
  have pt : ∀ a b : Row M, Ok a b → IsPt X m (sg X c M a) (sg X d M b) (t (sg X c M a) (sg X d M b)) := by
    intro a b hab
    exact (ht _ _ (sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).1 (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).1).1
  have loc : ∀ a b : Row M, ∃ T : Finset Ω, ∀ r : Gal(Ω/ℚ), (∀ z ∈ T, r z = z) → Ok a b →
      (X.gal r) (sg X c M a) = sg X c M a ∧ (X.gal r) (sg X d M b) = sg X d M b ∧
      Mv X m (X.gal r) r (t (sg X c M a) (sg X d M b)) (t (sg X c M a) (sg X d M b)) 1 := by
    intro a b
    by_cases hab : Ok a b
    · obtain ⟨T1, h1⟩ := PC.galNear Ω ε X (sg X c M a)
      obtain ⟨T2, h2⟩ := PC.galNear Ω ε X (sg X d M b)
      obtain ⟨S, hS⟩ := mvNear Ω ε X m hm _ _ _ (pt a b hab)
      let Tf : X.K → Finset Ω := fun f => Classical.choose (PC.galNear Ω ε X f)
      refine ⟨T1 ∪ T2 ∪ S.biUnion Tf, fun r hr _ => ⟨h1 r (fun z hz => hr z (by simp [hz])), h2 r (fun z hz => hr z (by simp [hz])), ?_⟩⟩
      refine hS _ r (hadm r) (fun f hf => ?_)
      exact Classical.choose_spec (PC.galNear Ω ε X f) r (fun z hz => hr z (by simp only [Finset.mem_union, Finset.mem_biUnion]; exact Or.inr ⟨f, hf, hz⟩))
    · exact ⟨∅, fun r _ h => absurd h hab⟩
  let G : Row M × Row M → Finset Ω := fun p => Classical.choose (loc p.1 p.2)
  refine ⟨Finset.univ.biUnion G, ?_⟩
  intro s s' hss x y hxy
  set r := s'⁻¹ * s
  set a := gr M s⁻¹ x
  set b := gr M s⁻¹ y
  have hab : Ok a b := (hok x y hxy).2.2.1 s⁻¹
  have hr : ∀ z ∈ G (a, b), r z = z := by
    intro z hz
    have := hss z (Finset.mem_biUnion.2 ⟨(a, b), Finset.mem_univ _, hz⟩)
    show s'⁻¹ (s z) = z
    rw [this]
    exact s'.symm_apply_apply z
  obtain ⟨fa, fb, fm⟩ := Classical.choose_spec (loc a b) r hr hab
  have hsr : s' * r = s := by simp [r]
  have hrs : r * s⁻¹ = s'⁻¹ := by simp [r]
  have inv1 : ∀ (q : Gal(Ω/ℚ)) (e : Row M), gr M q (gr M q⁻¹ e) = e := by
    intro q e
    rw [← (hgr _ _ _).1, mul_inv_cancel, (hgr 1 1 e).2]
  have sa := sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1
  have sb := sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1
  have ex : sg X c M (gr M s'⁻¹ x) = sg X c M a := by
    rw [← hrs, (hgr _ _ _).1, ← sa.2.2.1 r, fa]
  have ey : sg X d M (gr M s'⁻¹ y) = sg X d M b := by
    rw [← hrs, (hgr _ _ _).1, ← sb.2.2.1 r, fb]
  have ws' := (hw s' x y hxy).2
  rw [ex, ey] at ws'
  have ws := (hw s x y hxy).2
  have gx : (X.gal s) (sg X c M a) = sg X c M x := by rw [sa.2.2.1 s, inv1]
  have gy : (X.gal s) (sg X d M b) = sg X d M y := by rw [sb.2.2.1 s, inv1]
  have q1 : IsPt X m ((X.gal r) (sg X c M a)) ((X.gal r) (sg X d M b)) (t (sg X c M a) (sg X d M b)) := by
    rw [fa, fb]
    exact pt a b hab
  have q2 : IsPt X m ((X.gal s') ((X.gal r) (sg X c M a))) ((X.gal s') ((X.gal r) (sg X d M b))) (t (sg X c M x) (sg X d M y)) := by
    rw [← gal_mul_apply, ← gal_mul_apply, hsr, gx, gy]
    exact pt x y hxy
  have comp := mvComp Ω ε X m hm (X.gal r) (X.gal s') r s' (hadm r) (hadm s') _ _ _ _ _ (pt a b hab) q1 q2 _ _ fm ws'
  rw [map_one, one_pow, one_mul] at comp
  have eg : (X.gal r).trans (X.gal s') = X.gal s := by
    ext f
    rw [← hsr, gal_mul_apply]
    rfl
  rw [eg, hsr] at comp
  have q3 : IsPt X m ((X.gal s) (sg X c M a)) ((X.gal s) (sg X d M b)) (t (sg X c M x) (sg X d M y)) := by
    rw [gx, gy]
    exact pt x y hxy
  exact ((mvEx Ω ε X m hm (X.gal s) s (hadm s) _ _ _ (pt a b hab)).2.2.2 _ q3 _ _ comp).1 ws
