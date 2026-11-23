import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

structure QuadAt (p : ℕ) (s : ℤˣ) (S : Finset ℕ) (η : G ℚ Ω →* ℤˣ) : Prop where
  prime : p.Prime
  nm : p ∉ S
  opn : IsOpen (η.ker : Set (G ℚ Ω))
  idx : η.ker.index = 2
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (p : Ω) < 1 → Ine (F := ℚ) A ≤ η.ker
  ram : ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∃ g ∈ Ine (F := ℚ) A, η g = -1
  cc : ∀ σ : G ℚ Ω, IsCC σ → η σ = s
  split : ∀ q ∈ S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := ℚ) A ≤ η.ker

structure Kap (D : Raw Ω c) (κ : G ℚ Ω →* c.Oˣ) : Prop where
  opn : IsOpen (κ.ker : Set (G ℚ Ω))
  pow : ∃ j : ℕ, κ ^ l ^ j = 1
  unrS : ∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ κ.ker
  unrL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ κ.ker
  kb : ∀ A, Raw.Away {l} A → ∀ g ∈ Ine (F := ℚ) A, Raw.bar D.Psi g = 1 → κ g = 1 → D.ψ g = 1
  kc : ∃ m : ℕ, l.Coprime m ∧ ∀ g, cycZ ℚ Ω l g = 1 → κ g = 1 → D.ψ g ^ m = 1

structure Set2 (D : Raw Ω c) where
  κ : G ℚ Ω →* c.Oˣ
  p₃ : ℕ
  p : ℕ
  p' : ℕ
  φ : G ℚ Ω →* ℤˣ
  η : G ℚ Ω →* ℤˣ
  η' : G ℚ Ω →* ℤˣ
  kap : Kap D κ
  hφ : QuadAt p₃ 1 D.S φ
  hη : QuadAt p (-1) (insert p₃ D.S) η
  hη' : QuadAt p' (-1) (insert p (insert p₃ D.S)) η'
  psi_cc : ∀ σ : G ℚ Ω, IsCC σ → D.Psi σ = 1
  ord : ∃ n : ℕ, D.ξ ^ 2 ^ n = 1
  xi : ∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker
  ev : ∃ t, D.om t = 1 ∧ κ t = 1 ∧ Raw.bar D.Psi t = -1
  bigL : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    ∃ g ∈ Dec (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1
  big2 : ∀ A : ValuationSubring Ω, A.valuation (2 : Ω) < 1 →
    ∃ g ∈ Ine (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1

namespace Set2

variable {D : Raw Ω c} (X : Set2 D)

def H : Subgroup (G ℚ Ω) :=
  ((Units.map (residue c.O).toMonoidHom).comp D.Psi).eqLocus
    ((Units.map (Int.castRingHom (ResidueField c.O)).toMonoidHom).comp X.φ) ⊓ X.η.eqLocus X.η' ⊓ X.κ.ker

theorem mem_H {g : G ℚ Ω} :
    g ∈ X.H ↔ Raw.bar D.Psi g = ((X.φ g : ℤ) : ResidueField c.O) ∧ X.η g = X.η' g ∧ X.κ g = 1 :=
  ⟨fun h => ⟨congrArg Units.val h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨Units.ext h.1, h.2.1⟩, h.2.2⟩⟩

structure Elts (a u t : G ℚ Ω) : Prop where
  a_mem : a ∈ X.H ⊓ X.η.ker
  a_xi : Raw.bar D.ξ a = -1
  a_psi : Raw.bar D.Psi a = 1
  a_om : Raw.bar D.om a = -1
  u_mem : u ∈ X.H ⊓ X.η.ker
  u_xi : Raw.bar D.ξ u ^ 4 ≠ 1
  u_psi : Raw.bar D.Psi u = 1
  u_om : D.om u = 1
  t_mem : t ∈ X.H ⊓ X.η.ker
  t_xi : Raw.bar D.ξ t ^ 2 ≠ 1
  t_psi : Raw.bar D.Psi t = -1
  t_om : D.om t = 1

def On (T : Tower D) : Prop := T.F.fixingSubgroup = X.H ∧ T.K.fixingSubgroup = X.η.ker

end Set2

theorem resQ_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup :=
  (F.mem_fixingSubgroup_iff _).2 fun x hx => g.commutes ⟨x, hx⟩

theorem exists_resQ {F : IntermediateField ℚ Ω} {g : G ℚ Ω} (hg : g ∈ F.fixingSubgroup) : ∃ s : G F Ω, resQ F s = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => (F.mem_fixingSubgroup_iff g).1 hg x.1 x.2, rfl⟩

theorem resQ_Dec (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (g : G F Ω) :
    g ∈ Dec (F := F) A ↔ resQ F g ∈ Dec (F := ℚ) A := Iff.rfl

theorem resQ_Ine (F : IntermediateField ℚ Ω) [NumberField F] (A : ValuationSubring Ω) (g : G F Ω) :
    g ∈ Ine (F := F) A ↔ resQ F g ∈ Ine (F := ℚ) A := Iff.rfl

theorem resQ_cyc (F : IntermediateField ℚ Ω) [NumberField F] (g : G F Ω) : cycZ ℚ Ω l (resQ F g) = cycZ F Ω l g := rfl

end UpperTheory.V.Ws

end
