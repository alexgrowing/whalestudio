import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SplitEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PadicHomUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ResExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.KapPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetPush

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpr : p.Prime := CharP.char_is_prime K p
  by_cases h : p = l
  · subst h
    exact hp
  · exfalso
    have hu : IsUnit (p : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out hpr).2 (Ne.symm h)
    have hu' := hu.map f
    rw [map_natCast, CharP.cast_eq_zero] at hu'
    exact not_isUnit_zero hu'

theorem UpperTheory.V.Pa.Det.onePt :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {q : ℕ} (sg : Fin q → F.G₀), (∀ a, ((mat x.ρ (sg a)).charpoly.map (algebraMap x.A (FractionRing x.A))).Separable) → Detects k (Set.range sg) → ∃ d : ℕ, d ≠ 0 ∧ ∀ D, d ∣ D → D ≠ 0 → ∃ (x' : NP F n) (j : x.A →+* x'.A) (k' : Kap x') (al : Fin q → Fin n → x'.A), x.Ext x' j ∧ Nat.card x'.K = l ^ D ∧ Detects k' (Set.range sg) ∧ ∀ a, Function.Injective (al a) ∧ (mat x'.ρ (sg a)).charpoly = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ F n x k q sg hsep hdet
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  have hmat : ∀ (y y' : NP F n) (j : y.A →+* y'.A), y.Ext y' j → ∀ g, mat y'.ρ g = (mat y.ρ g).map j := by
    intro y y' j h g
    rw [h.2.2.2.1]
    rfl
  obtain ⟨A1, _, _, _, _, j1, al1, hj1i, hj1l, hj1f, hal1⟩ :=
    Det.splitEx l (n := n) (fun a => (mat x.ρ (sg a)).charpoly)
      (fun a => ⟨Matrix.charpoly_monic _, by simp [Matrix.charpoly_natDegree_eq_dim], hsep a⟩)
  obtain ⟨x1, J1, e1, hE1, he1, -⟩ := Det.extEx x A1 j1 hj1i hj1l hj1f
  haveI : CharP x1.K l := charP_of_padic (algebraMap ℤ_[l] x1.K)
  haveI := Fintype.ofFinite x1.K
  obtain ⟨d, -, hcard⟩ := FiniteField.card x1.K l
  refine ⟨(d : ℕ), d.ne_zero, ?_⟩
  intro D hdD hD0
  obtain ⟨A2, _, _, _, _, j2, hj2i, hj2l, hj2f, hres2, -⟩ :=
    Det.resExt l (K := x1.K) d D (by rw [Nat.card_eq_fintype_card]; exact hcard) hdD hD0
  obtain ⟨x2, J2, e2, hE2, -, hc2⟩ := Det.extEx x1 A2 j2 hj2i hj2l hj2f
  have hE := Det.extTrans x x1 x2 J1 J2 hE1 hE2
  obtain ⟨k', e, hk, -⟩ := Det.kapPush x x2 _ hE k
  refine ⟨x2, J2.comp J1, k', fun a b => J2 (e1.symm (al1 a b)), hE.1, by rw [hc2, hres2],
    Det.detPush x x2 _ hE k k' e hk _ hdet, fun a => ⟨?_, ?_⟩⟩
  · exact hE2.1.1.comp (e1.symm.injective.comp (hal1 a).1)
  · have h1 : J1 = (e1.symm : A1 →+* x1.A).comp j1 := by
      refine RingHom.ext fun t => ?_
      simp [← he1 t]
    have key : Polynomial.map J1 (mat x.ρ (sg a)).charpoly =
        ∏ b, (Polynomial.X - Polynomial.C (e1.symm (al1 a b))) := by
      rw [h1, ← Polynomial.map_map, (hal1 a).2, Polynomial.map_prod]
      simp
    rw [hmat x x2 _ hE.1, Matrix.charpoly_map, ← Polynomial.map_map, key, Polynomial.map_prod]
    simp
