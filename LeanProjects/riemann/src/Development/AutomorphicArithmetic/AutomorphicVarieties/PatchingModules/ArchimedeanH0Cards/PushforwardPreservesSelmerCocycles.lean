import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
import ReciprocityTheory.Hypotheses.GalCoh

noncomputable section

open ReciprocityTheory.Gal

namespace UpperTheory.V.Pa.B2

structure Pl (Γ : Type) [Group Γ] [TopologicalSpace Γ] : Type 1 where
  ι : Type
  [fin : Fintype ι]
  G : ι → Type
  [grp : ∀ w, Group (G w)]
  [top : ∀ w, TopologicalSpace (G w)]
  [tgrp : ∀ w, IsTopologicalGroup (G w)]
  φ : ∀ w, G w →* Γ
  cont : ∀ w, Continuous (φ w)
  J : ∀ w, Subgroup (G w)

attribute [instance] Pl.fin Pl.grp Pl.top Pl.tgrp

structure FRep (A G : Type) [CommRing A] [Group G] [TopologicalSpace G] : Type 1 where
  X : Type
  [add : AddCommGroup X]
  [mod : Module A X]
  [fin : Finite X]
  [top : TopologicalSpace X]
  [disc : DiscreteTopology X]
  ρ : Representation A G X
  cont : ContAction ρ

attribute [instance] FRep.add FRep.mod FRep.fin FRep.top FRep.disc

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ]

structure Dat (A : Type) [CommRing A] (P : Pl Γ) : Type 1 where
  M : FRep A Γ
  Q : ∀ w, FRep A (P.G w)
  π : ∀ w, M.X →ₗ[A] (Q w).X
  surj : ∀ w, Function.Surjective (π w)
  equiv : ∀ w g m, π w (M.ρ (P.φ w g) m) = (Q w).ρ g (π w m)

namespace Dat

variable {P : Pl Γ} (D : Dat A P)

abbrev C2 : Type := (Γ × Γ → D.M.X) × ∀ w, P.G w → (D.Q w).X

def selmerSecondCocycles : Submodule A D.C2 where
  carrier := {p | p.1 ∈ Z2 D.M.ρ ∧ ∀ w, Continuous (p.2 w) ∧
    ∀ g h, D.π w (p.1 (P.φ w g, P.φ w h)) = d1 (D.Q w).ρ (p.2 w) (g, h)}
  zero_mem' := ⟨zero_mem _, fun w => ⟨continuous_const, fun g h => by simp⟩⟩
  add_mem' := by
    rintro p q ⟨a1, a2⟩ ⟨b1, b2⟩
    refine ⟨add_mem a1 b1, fun w => ⟨(a2 w).1.add (b2 w).1, fun g h => ?_⟩⟩
    have e : (p + q).2 w = p.2 w + q.2 w := rfl
    rw [e, map_add, Prod.fst_add, Pi.add_apply, map_add, (a2 w).2, (b2 w).2, Pi.add_apply]
  smul_mem' := by
    rintro c p ⟨a1, a2⟩
    refine ⟨Submodule.smul_mem _ c a1, fun w => ⟨(a2 w).1.const_smul c, fun g h => ?_⟩⟩
    have e : (c • p).2 w = c • p.2 w := rfl
    rw [e, map_smul, Prod.smul_fst, Pi.smul_apply, map_smul, (a2 w).2, Pi.smul_apply]

def abelian₂ (w : P.ι) : Submodule A (P.G w → (D.Q w).X) where
  carrier := {y | y ∈ Z1 (D.Q w).ρ ∧ ∃ Y, ∀ g ∈ P.J w, y g = (D.Q w).ρ g Y - Y}
  zero_mem' := ⟨zero_mem _, 0, fun g _ => by simp⟩
  add_mem' := by
    rintro y y' ⟨a, Y, hY⟩ ⟨b, Y', hY'⟩
    exact ⟨add_mem a b, Y + Y', fun g hg => by rw [Pi.add_apply, hY g hg, hY' g hg, map_add]; abel⟩
  smul_mem' := by
    rintro c y ⟨a, Y, hY⟩
    exact ⟨Submodule.smul_mem _ c a, c • Y, fun g hg => by rw [Pi.smul_apply, hY g hg, map_smul, smul_sub]⟩

def selmerSecondCoboundaries : Submodule A D.C2 where
  carrier := {p | ∃ x : Γ → D.M.X, Continuous x ∧ p.1 = d1 D.M.ρ x ∧
    ∀ w, (p.2 w - fun g => D.π w (x (P.φ w g))) ∈ D.abelian₂ w}
  zero_mem' := ⟨0, continuous_const, by simp, fun w => by
    convert (D.abelian₂ w).zero_mem using 1; funext g; simp⟩
  add_mem' := by
    rintro p q ⟨x, a1, a2, a3⟩ ⟨x', b1, b2, b3⟩
    refine ⟨x + x', a1.add b1, by rw [Prod.fst_add, a2, b2, map_add], fun w => ?_⟩
    convert add_mem (a3 w) (b3 w) using 1
    funext g; simp; abel
  smul_mem' := by
    rintro c p ⟨x, a1, a2, a3⟩
    refine ⟨c • x, a1.const_smul c, by rw [Prod.smul_fst, a2, map_smul], fun w => ?_⟩
    convert (D.abelian₂ w).smul_mem c (a3 w) using 1
    funext g; simp [smul_sub]

abbrev H2LocalConditions : Type := D.selmerSecondCocycles ⧸ D.selmerSecondCoboundaries.comap D.selmerSecondCocycles.subtype

def loc1 (w : P.ι) : H1 D.M.ρ →ₗ[A] H1 (D.Q w).ρ :=
  pairH1DecompositionMap D.M.ρ (D.Q w).ρ (P.φ w) (P.cont w) (D.π w) continuous_of_discreteTopology (D.equiv w)

def loc2 : H2 D.M.ρ →ₗ[A] ∀ w, H2 (D.Q w).ρ :=
  LinearMap.pi fun w => compatiblePairH2 D.M.ρ (D.Q w).ρ (P.φ w) (P.cont w) (D.π w) continuous_of_discreteTopology (D.equiv w)

def Sel : Submodule A (H1 D.M.ρ) := ⨅ w, (H1ur (D.Q w).ρ (P.J w)).comap (D.loc1 w)

abbrev Ck2 : Type := (∀ w, H2 (D.Q w).ρ) ⧸ LinearMap.range D.loc2

structure Hom (D D' : Dat A P) where
  f : D.M.X →ₗ[A] D'.M.X
  fq : ∀ w, (D.Q w).X →ₗ[A] (D'.Q w).X
  equiv : ∀ g m, f (D.M.ρ g m) = D'.M.ρ g (f m)
  comm : ∀ w m, fq w (D.π w m) = D'.π w (f m)

variable {D} {D' D'' : Dat A P}

theorem Hom.equivq (u : Hom D D') (w : P.ι) (g : P.G w) (m : (D.Q w).X) :
    u.fq w ((D.Q w).ρ g m) = (D'.Q w).ρ g (u.fq w m) := by
  obtain ⟨m, rfl⟩ := D.surj w m
  rw [← D.equiv, u.comm, u.comm, u.equiv, D'.equiv]

def Hom.c2 (u : Hom D D') : D.C2 →ₗ[A] D'.C2 where
  toFun p := (fun s => u.f (p.1 s), fun w g => u.fq w (p.2 w g))
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

theorem Hom.lineCoeffQuadratic_mem (u : Hom D D') {p : D.C2} (hp : p ∈ D.selmerSecondCocycles) : u.c2 p ∈ D'.selmerSecondCocycles := by
  obtain ⟨⟨hc, hcoc⟩, hloc⟩ := hp
  refine ⟨⟨(continuous_of_discreteTopology (f := u.f)).comp hc, fun g h k => ?_⟩,
    fun w => ⟨(continuous_of_discreteTopology (f := u.fq w)).comp (hloc w).1, fun g h => ?_⟩⟩
  · show D'.M.ρ g (u.f (p.1 (h, k))) - u.f (p.1 (g * h, k)) + u.f (p.1 (g, h * k)) - u.f (p.1 (g, h)) = 0
    rw [← u.equiv, ← map_sub, ← map_add, ← map_sub, hcoc, map_zero]
  · show D'.π w (u.f (p.1 (P.φ w g, P.φ w h))) =
      (D'.Q w).ρ g (u.fq w (p.2 w h)) - u.fq w (p.2 w (g * h)) + u.fq w (p.2 w g)
    rw [← u.comm, (hloc w).2]
    show u.fq w ((D.Q w).ρ g (p.2 w h) - p.2 w (g * h) + p.2 w g) = _
    rw [map_add, map_sub, u.equivq]

theorem Hom.lam_mem (u : Hom D D') (w : P.ι) {y} (hy : y ∈ D.abelian₂ w) : (fun g => u.fq w (y g)) ∈ D'.abelian₂ w := by
  obtain ⟨⟨hc, hcoc⟩, Y, hY⟩ := hy
  refine ⟨⟨(continuous_of_discreteTopology (f := u.fq w)).comp hc, fun g h => ?_⟩, u.fq w Y, fun g hg => ?_⟩
  · show u.fq w (y (g * h)) = u.fq w (y g) + (D'.Q w).ρ g (u.fq w (y h))
    rw [hcoc, map_add, u.equivq]
  · show u.fq w (y g) = (D'.Q w).ρ g (u.fq w Y) - u.fq w Y
    rw [hY g hg, map_sub, u.equivq]

def Hom.h2 (u : Hom D D') : D.H2LocalConditions →ₗ[A] D'.H2LocalConditions :=
  Submodule.mapQ _ _ (u.c2.restrict fun _ hp => u.lineCoeffQuadratic_mem hp) (by
    rintro p ⟨x, a1, a2, a3⟩
    refine ⟨fun g => u.f (x g), continuous_of_discreteTopology.comp a1, ?_, fun w => ?_⟩
    · funext s
      have e : p.1.1 s = d1 D.M.ρ x s := congrFun a2 s
      show u.f (p.1.1 s) = _
      obtain ⟨g, h⟩ := s
      rw [e]; simp [u.equiv]
    · convert u.lam_mem w (a3 w) using 1
      funext g
      show u.fq w (p.1.2 w g) - D'.π w (u.f _) = u.fq w (p.1.2 w g - D.π w _)
      rw [map_sub, u.comm])

structure SES (f : Hom D' D) (g : Hom D D'') : Prop where
  inj : Function.Injective f.f
  ex : Function.Exact f.f g.f
  surj : Function.Surjective g.f
  injq : ∀ w, Function.Injective (f.fq w)
  exq : ∀ w, Function.Exact (f.fq w) (g.fq w)

def ofSub (P : Pl Γ) (M : FRep A Γ) (N : P.ι → Submodule A M.X)
    (hN : ∀ w g, N w ≤ (N w).comap (M.ρ (P.φ w g))) : Dat A P where
  M := M
  Q w :=
    { X := M.X ⧸ N w
      fin := Finite.of_surjective _ (N w).mkQ_surjective
      top := ⊥
      disc := by letI : TopologicalSpace (M.X ⧸ N w) := ⊥; exact ⟨rfl⟩
      ρ := Representation.quotient (M.ρ.comp (P.φ w)) (N w) (hN w)
      cont := by
        letI : TopologicalSpace (M.X ⧸ N w) := ⊥
        haveI : DiscreteTopology (M.X ⧸ N w) := ⟨rfl⟩
        refine continuous_prod_of_discrete_right.2 fun q => ?_
        obtain ⟨m, rfl⟩ := (N w).mkQ_surjective q
        exact (continuous_of_discreteTopology (f := (N w).mkQ)).comp
          (M.cont.comp ((P.cont w).prodMk continuous_const)) }
  π w := (N w).mkQ
  surj w := (N w).mkQ_surjective
  equiv _ _ _ := rfl

end Dat

def plOf {l : ℕ} [Fact l.Prime] {L : Loc} (G : Glob l L) : Pl G.Γ where
  ι := L.Vl ⊕ L.St
  G w := Sum.rec (motive := fun _ => Type) L.Gv L.Gu w
  grp w := Sum.rec (motive := fun w => Group (Sum.rec (motive := fun _ => Type) L.Gv L.Gu w)) L.gv L.gu w
  top w := Sum.rec (motive := fun w => TopologicalSpace (Sum.rec (motive := fun _ => Type) L.Gv L.Gu w)) L.tv L.tu w
  tgrp w := by cases w; exacts [L.tgv _, L.tgu _]
  φ w := match w with
    | .inl v => G.η.ker.subtype.comp (G.φ v)
    | .inr u => G.η.ker.subtype.comp (G.φu u)
  cont w := by
    cases w
    exacts [continuous_subtype_val.comp (G.φ_cont _), continuous_subtype_val.comp (G.φu_cont _)]
  J w := match w with
    | .inl _ => ⊤
    | .inr u => L.Ju u

section Ax

variable (l : ℕ) (G : Type) [Group G] [TopologicalSpace G]

def FinH : Prop :=
  ∀ (A : Type) [CommRing A] (M : FRep A G), (∀ m : M.X, l • m = 0) → Finite (H1 M.ρ) ∧ Finite (H2 M.ρ)

def SecondCohomologyRightExactModL : Prop :=
  ∀ (A : Type) [CommRing A] (M M' : FRep A G), (∀ m : M.X, l • m = 0) →
    ∀ (u : M.X →ₗ[A] M'.X) (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m)), Function.Surjective u →
      Function.Surjective (mapH2 M.ρ M'.ρ u continuous_of_discreteTopology hu)

def LocE (d : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] (M : FRep A G), (∀ m : M.X, l • m = 0) →
    Nat.card (H1 M.ρ) = Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ d

variable {G}

def UrAx (J : Subgroup G) : Prop :=
  ∀ (A : Type) [CommRing A] (M : FRep A G), (∀ m : M.X, l • m = 0) → (∀ g ∈ J, ∀ m, M.ρ g m = m) →
    Nat.card (H0 M.ρ) ≤ Nat.card (H1ur M.ρ J) ∧
    ∀ (M' : FRep A G) (u : M.X →ₗ[A] M'.X), (∀ g m, u (M.ρ g m) = M'.ρ g (u m)) → Function.Surjective u →
      ∀ y' ∈ Z1 M'.ρ, (∀ g ∈ J, y' g = 0) → ∃ y ∈ Z1 M.ρ, (∀ g ∈ J, y g = 0) ∧ ∀ g, u (y g) = y' g

end Ax

structure CohAx {l : ℕ} [Fact l.Prime] {L : Loc} (G : Glob l L) (d : ℕ) (dv : L.Vl → ℕ) : Prop where
  sum : ∑ v, dv v = d
  fin : FinH l G.Γ
  finV : ∀ v, FinH l (L.Gv v)
  finU : ∀ u, FinH l (L.Gu u)
  onto : SecondCohomologyRightExactModL l G.Γ
  ge : ∃ c : Fin d → G.Γ, (∀ i, G.η (c i) = -1 ∧ c i * c i = 1) ∧
    ∀ (A : Type) [CommRing A] (M : FRep A G.Γ), (∀ m : M.X, l • m = 0) →
      Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ d =
        Nat.card (H1 M.ρ) * ∏ i, Nat.card {m : M.X // M.ρ (c i) m = m}
  leV : ∀ v, LocE l (L.Gv v) (dv v)
  leU : ∀ u, LocE l (L.Gu u) 0
  ur : ∀ u, UrAx l (L.Ju u)
  ck : ∀ (A : Type) [CommRing A] (D : Dat A (plOf G)), (∀ m : D.M.X, l • m = 0) →
    Nat.card D.Ck2 ≤ Nat.card {f : D.M.X →+ ZMod l // ∀ g m,
      f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m}

end UpperTheory.V.Pa.B2
