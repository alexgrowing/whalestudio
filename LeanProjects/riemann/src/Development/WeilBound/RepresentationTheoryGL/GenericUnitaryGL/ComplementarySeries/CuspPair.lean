import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotientStatement
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg Zc

namespace PositivityTheory.RgGu.NR

namespace CuspPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem key {x y : IrrGL k} (hx : x.IsCusp) (hy : y.IsCusp) {N : ℕ} (hd : ∑ a, (![x, y] a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V)
    (hτ : IsSubquotient τ (prodIrr ![x, y] hd)) (u : Fin 2 → IrrGL k) (hu : ∑ a, (u a).1 = N)
    (hpos : ∀ a, 0 < (u a).1) (hj : 1 ≤ jm u hu τ) : u = ![x, y] ∨ u = ![y, x] := by
  have hxc : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hj' := GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient u hu τ _ (isSmooth_prodIrr ![x, y] hd) hτ
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.CuspPairSub.exists_equiv_of_jm_ne_zero ![x, y] u hd hu hxc hpos
    (ENat.one_le_iff_ne_zero.1 (hj.trans hj'))
  have hee : e 0 ≠ e 1 := fun h => by simpa using e.injective h
  have k2 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  rcases k2 _ _ hee with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
  · exact Or.inr (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))

end CuspPair

open CuspPair in

theorem cuspPairIrr_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h : GlobalTheory.BZSeg.NuPair k) : GlobalTheory.BZSeg.CuspPairIrr k := by
  intro x y N hd hx hy h1 h2
  by_contra hred
  obtain ⟨ψ, hc, hψ⟩ := exists_continuous_addChar_ne_one k
  obtain ⟨τ, hτ, hg⟩ := GlobalTheory.T.reducible_cuspidal_pair_nongeneric_subquotient k (PositivityTheory.rg.gu.whit.whitRankIrr k) ψ hc hψ x y N hd hx hy hred
  have hng : ¬ IsGeneric τ.ρ := fun hG => hg ((isGeneric_iff_isGenericFor hc hψ τ.ρ).1 hG)
  obtain ⟨α, β, β', hd1, hd2, hα, hβ, hββ, j1, j2⟩ := h N τ.V τ.ρ τ.smooth τ.irr hng
  have hp1 : ∀ a, 0 < (![α, β] a).1 := Fin.forall_fin_two.2 ⟨hα, hβ⟩
  have hp2 : ∀ a, 0 < (![β', α.nu 1] a).1 := Fin.forall_fin_two.2 ⟨hββ ▸ hβ, hα⟩
  have c1 := key hx hy hd τ.ρ hτ _ hd1 hp1 j1
  have c2 := key hx hy hd τ.ρ hτ _ hd2 hp2 j2
  have e0 : ∀ {a b c d : IrrGL k}, ![a, b] = ![c, d] → a = c ∧ b = d := fun h =>
    ⟨congrFun h 0, congrFun h 1⟩
  rcases c1 with c1 | c1 <;> obtain ⟨rfl, -⟩ := e0 c1
  · rcases c2 with c2 | c2 <;> obtain ⟨-, h3⟩ := e0 c2
    · exact h1 h3.symm
    · exact GlobalTheory.CompanionTheory.CuspPairSub.nu_one_ne hx.1 h3
  · rcases c2 with c2 | c2 <;> obtain ⟨-, h3⟩ := e0 c2
    · exact GlobalTheory.CompanionTheory.CuspPairSub.nu_one_ne hy.1 h3
    · exact h2 h3.symm

end PositivityTheory.RgGu.NR

end
