import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafKumCut

def LeafTwist : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nonempty (Prim q B) →
  ∀ n i j : ℤ, Nonempty (Ht q (sp B) n i ≃+ Ht q (sp B) n j)

def EtaleFirstCohomologyMultiplicativeGroupPicard : Prop := Hyps → DivisorPicardCompatibility

def LeafKumSeq : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ (a : Additive (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) →+ Ht q (sp B) 1 1)
    (b : Ht q (sp B) 1 1 →+ H ℤ (sp B) Gm 1), Function.Exact a b

theorem prim_of_isAlgClosed (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k)) :
    Nonempty (Prim q k) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)))
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem finite_of_exact {A M N : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup N] [Finite A]
    (a : A →+ M) (b : M →+ N) (h : Function.Exact a b) (hb : Finite b.range) : Finite M := by
  have hK : Finite b.ker := by
    have : (b.ker : Set M) = Set.range a := by ext x; exact h x
    have hf : (Set.range a).Finite := Set.finite_range a
    rw [← this] at hf
    exact hf.to_subtype
  have hQ : Finite (M ⧸ b.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange b).symm.toEquiv
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup b.ker
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  have : Nonempty (M ⧸ b.ker) := ⟨0⟩
  exact Nat.mul_ne_zero (Nat.card_pos).ne' (Nat.card_pos).ne'

theorem goal_of (hT : LeafTwist) (hG : EtaleFirstCohomologyMultiplicativeGroupPicard) (hS : LeafKumSeq) : LeafKum := by
  intro hy q _ k B _ _ _ _ hq hU hP i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨ζ⟩ := prim_of_isAlgClosed q k hq
  obtain ⟨e⟩ := hT hy q B ⟨ζ.map (algebraMap k B)⟩ 1 i 1
  obtain ⟨a, b, hab⟩ := hS hy q B hqB
  obtain ⟨E⟩ := hG hy B
  have hr : Finite b.range := by
    refine Finite.of_injective (β := {c : CommRing.Pic B // c ^ q = 1})
      (fun y => ⟨Additive.toMul (E y.1), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      have h0 : q • x = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]
      have : q • E y.1 = 0 := by rw [← hx, ← map_nsmul, ← map_nsmul, h0, map_zero, map_zero]
      rw [← toMul_nsmul, this, toMul_zero]
    · intro y z h
      apply Subtype.ext
      apply E.injective
      apply Additive.toMul.injective
      exact congrArg Subtype.val h
  have : Finite (Ht q (sp B) 1 1) := finite_of_exact a b hab hr
  exact Finite.of_equiv _ e.symm.toEquiv

end LateralTheory.E.LeafKumCut
