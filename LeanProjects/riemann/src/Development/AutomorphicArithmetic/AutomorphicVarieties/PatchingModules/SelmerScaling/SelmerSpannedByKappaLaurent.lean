import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

def ired {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (N : Submodule B A) : Ideal B :=
  Ideal.span {b | ∃ x ∈ N, ∃ y ∈ N, x * y = algebraMap B A b}

def BndF {A Fr G : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace G] (t : A) (φ : G → Fr) : Prop :=
  ∃ (s : ℕ) (φ' : G → A), AdicCont (Ideal.span {t}) φ' ∧ ∀ g, algebraMap A Fr (φ' g) = algebraMap A Fr t ^ s * φ g

def BndM {A Fr G : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace G] {n : ℕ} (t : A)
    (z : G → Matrix (Fin n) (Fin n) Fr) : Prop := ∀ i j, BndF t fun g => z g i j

def BndD {A Fr G : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace G] {n e : ℕ} (t : A)
    (z : G → Matrix (Fin n) (Fin n) (DD Fr e)) : Prop :=
  ∀ i j, (BndF t fun g => (z g i j).a) ∧ (∀ k, BndF t fun g => (z g i j).ep k) ∧ (∀ k, BndF t fun g => (z g i j).ep' k) ∧
    BndF t fun g => (z g i j).eta

def DD.Rel {X : Type} [CommRing X] {a g : ℕ} (c : Fin a → Fin g → X) (u : DD X a) (v : DD X g) : Prop :=
  u.a = v.a ∧ u.eta = v.eta ∧ (∀ k, u.ep k = ∑ j, c k j * v.ep j) ∧ ∀ j, v.ep' j = ∑ k, c k j * u.ep' k

section F

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} {x : NP G0.frame n} (k : Kap x)

abbrev NP.Fr {F : GFrame l} (x : NP F n) : Type := FractionRing x.A

variable (x) in

def BdP (X : Type) [CommRing X] [Algebra x.A X] := Bd G.frame (fun g => x.ρX X (h.p₀ g)) (Ev x.A X n x.a)

def kapF (j : Fin k.g) (γ : G.G₀) : Matrix (Fin n) (Fin n) x.Fr := (k.κ j (h.p₀ γ)).map (algebraMap x.A x.Fr)

def SelmerRankBoundLaurent (D0 : ℕ) : Prop :=
  ∀ (e : ℕ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g)), (∀ i, z i ∈ Sel1 h x.Fr k ∧ BndD x.t (z i)) →
    (∀ c : Fin e → x.Fr, ∑ i, c i • z i ∈ Bd1 h x.Fr k → c = 0) → e ≤ D0

def Lifts (z : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr) : Prop :=
  ∃ Ψ ∈ Sel2 h x.Fr k, BndD x.t Ψ ∧ ∀ j γ a b, (Ψ γ a b).ep' j = z j γ a b

def EvenCocyclesLiftLaurent : Prop :=
  ∀ z : Fin (k.g + 1) → Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr, (∀ i j, z i j ∈ SelP h x x.Fr ∧ BndM x.t (z i j)) →
    ∃ c : Fin (k.g + 1) → x.Fr, c ≠ 0 ∧ Lifts h k (∑ i, c i • z i)

def SelmerSpannedByKappaLaurent : Prop :=
  ∀ z ∈ SelM h x x.Fr, BndM x.t z → ∃ c : Fin k.g → x.Fr, z - ∑ j, c j • kapF h k j ∈ BdM h x x.Fr

end F

structure Ctx (l : ℕ) [Fact l.Prime] : Type 1 where
  odd : l ≠ 2
  L : Loc
  G : Glob l L
  G0 : Glob l L
  h : G.Hom G0
  n : ℕ
  x : NP G0.frame n
  k : Kap x
  O : Type
  [o1 : CommRing O]
  [o2 : IsDomain O]
  [o3 : IsDiscreteValuationRing O]
  [o4 : IsCoef l O]
  [o5 : Algebra ℤ_[l] O]
  [o6 : Algebra O x.K]
  r : Resid G.frame O n
  B : Type
  [b1 : CommRing B]
  [b2 : Algebra O B]
  [b3 : IsCO O B]
  u : Pair r B
  P : OoPt h x u
  Bh : Type
  [c1 : CommRing Bh]
  [c2 : IsLocalRing Bh]
  [c3 : Algebra B Bh]
  cpl : IsCplAt B (RingHom.ker P.f) Bh
  rF : Bh →+* x.Fr
  rF_f : ∀ b, rF (algebraMap B Bh b) = algebraMap x.A _ (P.f b)
  rF_ker : RingHom.ker rF = maximalIdeal Bh
  U : URep h x u.D P.ker Bh rF (G.frame.eps O B)
  OO : Type
  [d1 : CommRing OO]
  [d2 : IsDomain OO]
  [d3 : IsDiscreteValuationRing OO]
  [d4 : IsAdicComplete (maximalIdeal OO) OO]
  [d5 : Algebra OO Bh]
  [d6 : IsCO OO Bh]
  oo_A : ∀ a : x.A, ∃ (o : OO) (b : B), algebraMap OO Bh o = algebraMap B Bh b ∧ P.f b = a
  oo_O : ∀ c : O, ∃ o : OO, algebraMap OO Bh o = algebraMap B Bh (algebraMap O B c)
  ordinaryPointSection : ∃ o : OO, algebraMap OO Bh o = algebraMap B Bh P.s
  oo_surj : Function.Surjective (rF.comp (algebraMap OO Bh))

attribute [instance] Ctx.o1 Ctx.o2 Ctx.o3 Ctx.o4 Ctx.o5 Ctx.o6 Ctx.b1 Ctx.b2 Ctx.b3 Ctx.c1 Ctx.c2 Ctx.c3 Ctx.d1 Ctx.d2 Ctx.d3
  Ctx.d4 Ctx.d5 Ctx.d6

namespace Ctx

variable {l : ℕ} [Fact l.Prime] (S : Ctx l)

abbrev F : Type := S.x.Fr

abbrev ρ (X : Type) [CommRing X] [Algebra S.x.A X] (g : S.G.G₀) : Matrix (Fin S.n) (Fin S.n) X := S.x.ρX X (S.h.p₀ g)

theorem exists_pr (a : S.U.AA) : ∃ b : S.Bh, a - algebraMap S.Bh S.U.AA b ∈ S.U.N := by
  have : a ∈ (1 : Submodule S.Bh S.U.AA) ⊔ S.U.N := by rw [S.U.compl.sup_eq_top]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
  obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hy
  exact ⟨b, by simpa using hz⟩

def pr0 (a : S.U.AA) : S.Bh := (S.exists_pr a).choose

def pr1 (a : S.U.AA) : S.U.N := ⟨a - algebraMap S.Bh S.U.AA (S.pr0 a), (S.exists_pr a).choose_spec⟩

def J2 : Ideal S.Bh := (maximalIdeal S.OO).map (algebraMap S.OO S.Bh) ⊔ maximalIdeal S.Bh ^ 2 ⊔ ired S.U.N

def Tp : Submodule S.F (S.Bh →+ S.F) where
  carrier := {α | (∀ b b', α (b * b') = S.rF b * α b' + S.rF b' * α b) ∧ (∀ o, α (algebraMap S.OO S.Bh o) = 0) ∧
    ∀ b ∈ ired S.U.N, α b = 0}
  add_mem' := by
    rintro α β ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun b b' => ?_, fun o => by simp [a2, b2], fun b hb => by simp [a3 b hb, b3 b hb]⟩
    simp only [AddMonoidHom.add_apply, a1, b1]; ring
  zero_mem' := ⟨by simp, by simp, by simp⟩
  smul_mem' := by
    rintro c α ⟨a1, a2, a3⟩
    refine ⟨fun b b' => ?_, fun o => by simp [a2], fun b hb => by simp [a3 b hb]⟩
    simp only [AddMonoidHom.smul_apply, a1, smul_eq_mul]; ring

def La : Submodule S.F (S.U.N →+ S.F) where
  carrier := {μ | ∀ (b : S.Bh) y, μ (b • y) = S.rF b * μ y}
  add_mem' := fun {α β} a b c y => by simp only [AddMonoidHom.add_apply, a c y, b c y]; ring
  zero_mem' := by simp
  smul_mem' := fun c α a b y => by simp only [AddMonoidHom.smul_apply, a b y, smul_eq_mul]; ring

def Ph : Submodule S.F (S.U.N →+ S.F) where
  carrier := {Φ | (∀ (o : S.OO) y, Φ (algebraMap S.OO S.Bh o • y) = S.rF (algebraMap S.OO S.Bh o) * Φ y) ∧
    ∀ b ∈ S.J2, ∀ y, Φ (b • y) = 0}
  add_mem' := by
    rintro α β ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨fun o y => by simp only [AddMonoidHom.add_apply, a1, b1]; ring, fun b hb y => by simp [a2 b hb, b2 b hb]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro c α ⟨a1, a2⟩
    exact ⟨fun o y => by simp only [AddMonoidHom.smul_apply, a1, smul_eq_mul]; ring, fun b hb y => by simp [a2 b hb]⟩

def alC (α : S.Bh →+ S.F) (g : S.G.G₀) : Matrix (Fin S.n) (Fin S.n) S.F :=
  (S.U.vr g).map (fun a => α (S.pr0 a)) * S.ρ S.F g⁻¹

def laC (μ : S.U.N →+ S.F) (g : S.G.G₀) : Matrix (Fin S.n) (Fin S.n) S.F :=
  (S.U.vr g).map (fun a => μ (S.pr1 a)) * S.ρ S.F g⁻¹

structure Test (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R) : Prop where
  fin : Module.Finite S.F R
  nil : ∃ N : ℕ, RingHom.ker e ^ N = ⊥
  res : ∀ a, e (θ a) = S.rF (S.pr0 a)
  oo : ∀ o : S.OO, θ (algebraMap S.Bh S.U.AA (algebraMap S.OO S.Bh o)) = algebraMap S.F R (S.rF (algebraMap S.OO S.Bh o))

def DualM (m : Fin S.k.g → S.U.N) : Prop :=
  ∀ μ ∈ S.La, S.laC μ - ∑ j, μ (m j) • kapF S.h S.k j ∈ BdM S.h S.x S.F

def Pres (D0 : ℕ) : Prop :=
  ∃ (X : Fin D0 → S.Bh) (m : Fin S.k.g → S.U.N) (c : Fin S.k.g × Fin S.k.g → Fin D0 → S.OO),
    (∀ a, X a ∈ maximalIdeal S.Bh) ∧ Submodule.span S.Bh (Set.range m) = ⊤ ∧
    LinearIndependent (ResidueField S.OO) (fun p a => residue S.OO (c p a)) ∧
    maximalIdeal S.Bh ≤ Ideal.span (Set.range X) ⊔ S.J2 ∧
    ∀ i, ∑ j, (∑ a, algebraMap S.OO S.Bh (c (i, j) a) * X a) • m j ∈ S.J2 • (⊤ : Submodule S.Bh S.U.N)

end Ctx

end UpperTheory.V.Pa
