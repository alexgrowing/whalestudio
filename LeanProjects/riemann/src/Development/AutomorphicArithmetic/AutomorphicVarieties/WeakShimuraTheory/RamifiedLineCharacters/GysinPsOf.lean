import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CoefFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupRaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.OpenKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupSwap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SuppMMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.DataAl
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.RootCharactersNeOneAtBasepoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupEx (P : CohomologyHyp) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (T : Tower D) (hT : T.Fit) (k : Type) [Field k] (a : c.O →+* k) (ha : ∀ x ∈ maximalIdeal c.O, a x = 0)
    (W : Finset ℕ) (hW : ∀ w ∈ W, w.Prime ∧ T.Splits w) (w w' : ℤ × ℤ) (h1 : a ((T.fr W).rt w T.g0) ≠ 1)
    (h2 : a ((T.fr W).rt (w + w') T.g0) ≠ 1) (J : Type) [Finite J] (y : J → G T.F Ω → k)
    (hy : ∀ j, (T.fr W).Coc a w' (y j) ∧ y j T.g0 = 0) :
    ∃ W' : Finset ℕ, W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (∀ j, (T.fr W').Coc a w' (y j)) ∧
      ∃ (x : G T.F Ω → k) (m : T.ι → k), (T.fr W').Coc a w x ∧ x T.g0 = 0 ∧ (T.fr W').LocTriv a w x m ∧ (∃ g, x g ≠ 0) ∧
        ∀ j, ∃ z, (T.fr W').Cup a w w' x (y j) z m ∧ z T.g0 = 0 := by
  obtain ⟨hc, hf⟩ := Gys.coefFacts c k a ha
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨N', hN, x, m, hx, hm, ⟨g, g1, g2⟩, hz⟩ := Gys.cupRaw (T.fr W) a l hf (ok W) _ (Gys.gysT P D T hD W hW) w w' J y
    fun j => (hy j).1
  have hs := hN.sub
  obtain ⟨W', s1, s2, rfl⟩ := hN
  have hy' : ∀ j, (T.fr W').Coc a w' (y j) := fun j => ⟨(hy j).1.lc, (hy j).1.coc, fun g hg => (hy j).1.kill g (hs hg)⟩
  obtain ⟨x', m', b1, b2, b3, b4, b5⟩ := Gys.cupNorm (T.fr W') a (ok W') w w' h1 h2 J y (fun j => ⟨hy' j, (hy j).2⟩) x m hx hm hz
  exact ⟨W', s1, s2, hy', x', m', b1, b2, b3, ⟨g, (b4 g g1).symm ▸ g2⟩, b5⟩

theorem UpperTheory.V.Ws.Gys.mu_of {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)
    {p : PD Φ.ι Γ R} (hp : Φ.IsRes a p) (h : ∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) :
    ∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v ∧ ∀ i, a (Φ.χ i s) = 1 :=
  fun v s hs => ⟨h v s hs, fun i => (hp.res.char v s (h v s hs) i).symm.trans (hp.pair.mu v s hs i)⟩

theorem UpperTheory.V.Ws.Gys.gysinPs_of :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → Supp nM p.r →
      ∃ (W' : Finset ℕ) (s : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ s.In qQ ∧ s.SameAl p ∧ Ent s.r (-wPs) := by
  intro P Ω _ _ _ l _ c D T hT k _ a ha W hW p hp hs
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨-, r2, r3⟩ := Gys.rootCharacters_ne_one_at_basepoint (T.fr W) a (ok W)
  obtain ⟨x, x1, x2, x3, x4⟩ := Gys.dataAl (T.fr W) a p hp hs
  obtain ⟨W', s1, s2, hx, y, n, y1, y2, y3, ⟨g, hg⟩, hz⟩ := Gys.cupEx P D T hT k a ha W hW (-wPs) (-wAl) r2
    (by rw [add_comm]; exact r3) Unit (fun _ => x) fun _ => ⟨x1, x2⟩
  obtain ⟨z, z1, z2⟩ := hz ()
  have hmu := Gys.mu_of (T.fr W) a hp fun v s hs => hs.1
  obtain ⟨s, a1, a2, a3, a4, a5, -⟩ := Gys.ob (T.fr W') a (ok W') hmu x y (y * x - z) _ n (hx ()) x2 x3 y1 y2 y3
    (Gys.cupSwap (T.fr W') a _ _ y x z n _ y1 y3 (hx ()) x3 z1) (by
      show y T.g0 * x T.g0 - z T.g0 = 0
      rw [y2, z2, zero_mul, sub_zero])
  exact ⟨W', s, s1, s2, a1, a2, ⟨fun g => (a3 g).trans (x4 g).symm, a4⟩, g, 2, 0, by decide,
    a5 g ▸ mul_ne_zero hg (((T.fr W').χ 0 g).isUnit.map a).ne_zero⟩
