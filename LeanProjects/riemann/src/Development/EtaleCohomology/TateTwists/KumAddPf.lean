import Development.EtaleCohomology.TateTwists.EtaleKummerClassSpecificationOfExistenceNaturali

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsKumCoc (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ)
    (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) : Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
    ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_uniq : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γ → IsKumCoc q u γ' → CohomologyClass.mk γ = CohomologyClass.mk γ'

def kum_mul_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γu γv : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γu → IsKumCoc q v γv →
      ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
        IsKumCoc q (u * v) γ ∧ CohomologyClass.mk γ = CohomologyClass.mk γu + CohomologyClass.mk γv

def kum_pow_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q (u ^ q) γ ∧ CohomologyClass.mk γ = 0

theorem kum_add_of (he : kum_exists) (hu : kum_uniq) (hm : kum_mul_coc) (hp : kum_pow_coc) : kum_add := by
  intro q _ X u v hq
  obtain ⟨γu, eu, ku⟩ := kum_spec_of_exists he q X u hq
  obtain ⟨γv, ev', kv⟩ := kum_spec_of_exists he q X v hq
  obtain ⟨γuv, euv, kuv⟩ := kum_spec_of_exists he q X (u * v) hq
  obtain ⟨γp, epw, kpw⟩ := kum_spec_of_exists he q X (u ^ q) hq
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ, hsum⟩ := hm q X u v hq γu γv ku kv
    rw [← euv, ← eu, ← ev', ← hsum]
    exact hu q X (u * v) hq γuv γ kuv hγ
  · obtain ⟨γ, hγ, h0⟩ := hp q X u hq
    rw [← epw, ← h0]
    exact hu q X (u ^ q) hq γp γ kpw hγ

end LateralTheory.EtaleFoundations
