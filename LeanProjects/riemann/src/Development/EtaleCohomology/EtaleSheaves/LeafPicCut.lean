import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open nonZeroDivisors

namespace LateralTheory.E.LeafPicCut

def sel (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (FractionRing B)ˣ :=
  (powMonoidHom q : (FractionalIdeal B⁰ (FractionRing B))ˣ →* _).range.comap (toPrincipalIdeal B (FractionRing B))

abbrev selPow (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (sel B q) :=
  (powMonoidHom q : (FractionRing B)ˣ →* (FractionRing B)ˣ).range.subgroupOf (sel B q)

abbrev selQ (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Type := sel B q ⧸ selPow B q

def LeafTorsPrime : Prop := ∀ (G : Type) [CommGroup G] (q : ℕ), q ≠ 0 →
  (∀ p : ℕ, p.Prime → p ∣ q → Finite {x : G // x ^ p = 1}) → Finite {x : G // x ^ q = 1}

def LeafSelPic : Prop := ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (q : ℕ) [NeZero q],
  Finite (selQ B q) → Finite {c : ClassGroup B // c ^ q = 1}

def LeafBound : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ∃ V : Submodule k (FractionRing B), FiniteDimensional k V ∧
  ∀ f ∈ sel B q, ∃ g ∈ sel B q, (g : FractionRing B) ∈ V ∧ ∃ u : (FractionRing B)ˣ, f = g * u ^ q

def LeafRigid : Prop := LateralTheory.E.E4.Hyps → ∀ (q : ℕ) [NeZero q], q.Prime → ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
  [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) →
  ∀ V : Submodule k (FractionRing B), FiniteDimensional k V →
  Set.Finite ((QuotientGroup.mk : sel B q → selQ B q) '' {f | ((f : (FractionRing B)ˣ) : FractionRing B) ∈ V})

theorem goal_of (hT : LeafTorsPrime) (hS : LeafSelPic) (hB : LeafBound) (hR : LeafRigid) : LateralTheory.E.E4.LeafPic := by
  intro hH q _ k B _ _ _ _ _ _ hq
  have key : Finite {c : ClassGroup B // c ^ q = 1} := by
    apply hT (ClassGroup B) q (NeZero.ne q)
    intro p hp hpq
    have : NeZero p := ⟨hp.ne_zero⟩
    have hpk : IsUnit (p : k) := by
      obtain ⟨m, rfl⟩ := hpq
      push_cast at hq
      exact isUnit_of_mul_isUnit_left hq
    apply hS B p
    obtain ⟨V, hV, hb⟩ := hB p k B
    have hfin := hR hH p hp k B hpk V hV
    refine Set.finite_univ_iff.mp (hfin.subset ?_)
    rintro x -
    induction x using QuotientGroup.induction_on with
    | H f =>
      obtain ⟨g, hg, hgV, u, hu⟩ := hb f f.2
      refine ⟨⟨g, hg⟩, hgV, ?_⟩
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      refine ⟨u, ?_⟩
      simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, hu]
      group
  exact Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1)
    (ClassGroup.equivPic B).toEquiv (fun c => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))

end LateralTheory.E.LeafPicCut
