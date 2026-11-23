import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp

namespace UpperTheory.V.Th

abbrev Om (O : Type) [CommRing O] [IsLocalRing O] (m : ℕ) : Type := O ⧸ maximalIdeal O ^ m

def IsDer {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module O X] (x : R →ₐ[O] O)
    (δ : R →ₗ[O] X) : Prop := ∀ a b, δ (a * b) = x a • δ b + x b • δ a

def twoPowerModulus {R G : Type} [CommRing R] [Group G] {n : ℕ} (E : ℕ) (ph ta : G) (u : Fin n → R) (i : Fin n) (y : R) : MonoidAlgebra R G :=
  (List.ofFn fun k => if k = i then 1 else MonoidAlgebra.single ph (1 : R) - MonoidAlgebra.single 1 (u k)).prod ^ (E + 1) *
    (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y)

variable {l : ℕ} [Fact l.Prime]

structure Pt (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) where
  ρ : F.G₀ →* GL (Fin n) O
  cont : ∀ i j, AdicCont (maximalIdeal O) fun g => mat ρ g i j
  P : GL (Fin n) O
  sgn : (P : Matrix (Fin n) (Fin n) O)ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) O)ᵀ = -P
  form : F.IsForm O n ρ P
  span : ∃ c : O, c ≠ 0 ∧ ∀ Z : Matrix (Fin n) (Fin n) O, c • Z ∈ Submodule.span O (Set.range (mat ρ))
  ine : ∀ u, ∀ g ∈ F.Iu u, ρ g = 1
  ψ : ∀ v, Fin n → F.Gv v →* Oˣ
  w : F.Vl → GL (Fin n) O
  tri : ∀ v g, (∀ i j, j < i → ((w v)⁻¹ * ρ (F.φ v g) * w v : GL (Fin n) O) i j = 0) ∧
    ∀ i, ((w v)⁻¹ * ρ (F.φ v g) * w v : GL (Fin n) O) i i = (ψ v i g : O)
  reg : ∀ v, ∃ g, Function.Injective fun i => ψ v i g
  N1 : ∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps O O).comp (F.φ v)

section Pt

variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}

def red (m : ℕ) (Z : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) (Om O m) := Z.map (Ideal.Quotient.mk _)

def Pt.N4 {F : GFrame l} (y : Pt F O n) (D : Subgroup F.G₀) : Prop :=
  ∀ Z : Matrix (Fin n) (Fin n) O, (∀ g ∈ D, ((F.eps O O g : Oˣ) : O) • (mat y.ρ g * Z) = Z * mat y.ρ g) → Z = 0

variable {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) (y : Pt G0.frame O n) (m : ℕ)

def Pt.ρm (g : G.G₀) : Matrix (Fin n) (Fin n) (Om O m) := red m (mat y.ρ (h.p₀ g))

def Sel : Set (G.G₀ → Matrix (Fin n) (Fin n) (Om O m)) :=
  {z | IsLocallyConstant z ∧ (∀ g g', z (g * g') = z g + y.ρm h m g * z g' * y.ρm h m g⁻¹) ∧
    (∀ g, red m y.P * z (G.frame.conj g) = -((z g)ᵀ * red m y.P)) ∧ (∀ u, ∀ g ∈ G.frame.Iu u, z g = 0) ∧
    ∀ v, ∃ Y, LocAt G.frame (y.ρm h m) (fun v => red m (y.w v)) (fun v => red m ((y.w v)⁻¹ : GL (Fin n) O)) z v Y}

def trFun (z : G.G₀ → Matrix (Fin n) (Fin n) (Om O m)) (g : G.G₀) : Om O m := (z g * y.ρm h m g).trace

variable (T : TWGrp G0)

def Eig (al : Fin T.q → Fin n → O) : Prop :=
  ∀ j, Function.Injective (al j) ∧ (mat y.ρ (T.sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))

def B1 (D0 : ℕ) : Prop :=
  ∃ C : ℕ, ∀ m, ∀ᶠ N in atTop, (trFun (T.h N) y m '' Sel (T.h N) y m).Finite ∧
    (trFun (T.h N) y m '' Sel (T.h N) y m).ncard ≤ Nat.card (ResidueField O) ^ (m * D0 + C)

end Pt

section Mod

variable {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
  (b : TWBase u J Empty D) (x : B →ₐ[O] O)

def wtSub : Submodule (abelian₂ O Empty D) b.M := RingHom.ker (x.comp b.lam) • ⊤

def Et : Prop := ∃ t : B, x t ≠ 0 ∧ ∀ a : B, x a = 0 → ∀ m : b.M, (t * a) • m ∈ wtSub b x

def CtrlH : Prop :=
  ∀ t ∈ Algebra.adjoin O {a : B | ∃ i g, a = u.D.lam i (MonoidAlgebra.single g 1)}, ∀ k : ℕ,
    (∀ m : b.M, t ^ k • m ∈ wtSub b x) → ∀ m : b.M, t • m ∈ wtSub b x

variable {b} {G : Glob l L} {h : G.Hom G0} {q N : ℕ} (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ)

structure OpRelX : Prop where
  two : TwoMaps (M := b.M) A.β.toRingHom (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)) A.actw
    (fEl Nq fun j i => MvPolynomial.X (j, i))
  rel2 : ∀ j i, A.act1 (fEl Nq (uV A.R) ^ E * (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr
    (twoPowerModulus E (ph j) (ta j) (uV A.R j) i (yV A.R j i))) = 0

variable (b) in

def OpAt (T : TWGrp G0) : Prop :=
  ∃ E : ℕ, ∀ N, ∃ A : OpMod b (T.h N) T.q N, OpRelX A (T.Nq N) (T.ph N) (T.ta N) E

end Mod

def Coc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n), l ≠ 2 → 1 ≤ n →
    ∃ c : O, c ≠ 0 ∧ ∀ (G : Glob l L) (h : G.Hom G0) (rN : Resid G.frame O n) (R : Type) [CommRing R] [Algebra O R] [IsCO O R]
      (p : Pair rN R) (x : R →ₐ[O] O), (∀ w, rN.Ip w = G.frame.Iu w) →
      p.Maps x.toRingHom (GDet.ofRep (mat (y.ρ.comp h.p₀))) y.ψ → ∀ (m : ℕ) (δ : R →ₗ[O] Om O m), IsDer x δ →
      ∃ z ∈ Sel h y m, ∀ g, trFun h y m z g = c • δ (p.D.tr (MonoidAlgebra.single g 1))

def TrPsi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    [Algebra ℤ_[l] O] (y : Pt G0.frame O n), 1 ≤ n →
    ∃ c : O, c ≠ 0 ∧ ∀ (G : Glob l L) (h : G.Hom G0) (rN : Resid G.frame O n) (R : Type) [CommRing R] [Algebra O R] [IsCO O R]
      (p : Pair rN R) (x : R →ₐ[O] O), p.Maps x.toRingHom (GDet.ofRep (mat (y.ρ.comp h.p₀))) y.ψ →
      ∀ (X : Type) [AddCommGroup X] [Module O X] (δ : R →ₗ[O] X), IsDer x δ →
      (∀ g, δ (p.D.tr (MonoidAlgebra.single g 1)) = 0) → ∀ v i g, c • δ (p.ψ v i g : Rˣ) = 0

def Split : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (y : Pt G0.frame O n) (x : B →ₐ[O] O)
    (al : Fin T.q → Fin n → O) (E : ℕ), 1 ≤ n → GenBy O (pairVals u) →
    u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → J ≤ RingHom.ker x → Et b x →
    (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → Eig y T al →
    ∃ c : O, c ≠ 0 ∧ ∀ m, ∀ᶠ N in atTop, ∀ A : OpMod b (T.h N) T.q N, OpRelX A (T.Nq N) (T.ph N) (T.ta N) E →
      ∃ α : Fin T.q → Fin n → O, ∀ a : Fin D ⊕ Fin T.q × Fin n, ∃ δ : A.R →ₗ[O] Om O m, IsDer (x.comp A.β) δ ∧
        (∀ k, δ (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = if a = .inl k then algebraMap O _ c else 0) ∧
        ∀ j i, δ (A.p.D.tr (twoPowerModulus E (T.ph N j) (T.ta N j) (fun k => algebraMap O A.R (α j k)) i 0)) =
          if a = .inr (j, i) then algebraMap O _ c else 0

def EtOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (y : Pt G0.frame O n) (x : B →ₐ[O] O),
    1 ≤ n → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → GenBy O (pairVals u) → CtrlH b x → Et b x

def Count : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (y : Pt G0.frame O n) (x : B →ₐ[O] O)
    (al : Fin T.q → Fin n → O), l ≠ 2 → 1 ≤ n → Adapted T (r := r) → OpAt b T → GenBy O (pairVals u) →
    u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → J ≤ RingHom.ker x → Et b x →
    (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → Eig y T al → B1 y T (D + n * T.q) →
    ∀ δ : B →ₗ[O] O, IsDer x δ → (∀ k, δ (u.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : Bˣ) = 0) →
      ∀ g, δ (u.D.tr (MonoidAlgebra.single g 1)) = 0

section Bar

variable (F : GFrame l) {n : ℕ} (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O (Qbar l)]
  (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l))

def DetQ (S : Set F.G₀) : Prop :=
  ∀ z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l), Continuous z →
    (∀ g g', z (g * g') = z g + ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) • (mat ρ g * z g' * mat ρ g⁻¹)) →
    (∀ g, (P : Matrix (Fin n) (Fin n) (Qbar l)) * z (F.conj g) = (z g)ᵀ * P) →
    (∀ σ ∈ S, ∀ k : ℕ, (z σ * mat ρ σ ^ k).trace = 0) →
    ∃ Y, ∀ g, z g = ((F.eps O (Qbar l) g : (Qbar l)ˣ) : Qbar l) • (mat ρ g * Y * mat ρ g⁻¹) - Y

def RegDet : Prop :=
  ∃ (q : ℕ) (sg : Fin q → F.G₀), (∀ j, sg j ∈ F.G' ∧ (mat ρ (sg j)).charpoly.Separable) ∧ DetQ F O ρ P (Set.range sg)

structure IsOrdCoc (I : F.St → Subgroup F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ)
    (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) : Prop where
  cont : Continuous z
  coc : ∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹
  pol : ∀ g, (P : Matrix (Fin n) (Fin n) (Qbar l)) * z (F.conj g) = -((z g)ᵀ * P)
  ine : ∀ u, ∀ g ∈ I u, z g = 0
  ord : ∀ v, ∃ (w : GL (Fin n) (Qbar l)) (Y : Matrix (Fin n) (Fin n) (Qbar l)), ∀ g : F.Gv v,
    (∀ i j, j < i → (w⁻¹ * ρ (F.φ v g) * w : GL (Fin n) (Qbar l)) i j = 0) ∧
    (∀ i, (w⁻¹ * ρ (F.φ v g) * w : GL (Fin n) (Qbar l)) i i = (ψ v i g : Qbar l)) ∧
    (∀ i j, j < i → (((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
      (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) (Qbar l))) i j = 0) ∧
    (g ∈ F.Iv v → ∀ i, (((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
      (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) (Qbar l))) i i = 0)

end Bar

section Ar

variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev}

def LevAt {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r}
    {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D) : Prop :=
  ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
    (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
    V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
    (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.Classical

variable {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)

def barPt (x : B.B →ₐ[c.O] c.O) : B.Pt := (Algebra.ofId c.O (Qbar l)).comp x

def LevelX (J : Ideal B.B) : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)), LevAt b ∧ (∀ k, b.wt.γ k ∈ V0.frame.Iv (b.wt.v k)) ∧
    ∀ (x : B.B →ₐ[c.O] c.O) (h : s.Wt n), (barPt B x).Arith h → CtrlH b x

end Ar

def HidaX : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → ∀ (c : Coef l) (n : ℕ), 1 ≤ n →
    ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ), ∃ J : Ideal B.B, B.PT ι J ∧ LevelX B J

def HasOp : Prop :=
  LocP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ)
    (b : TWBase (pairOf B.u) J Empty D), LevAt b → ∀ T : TWGrp (globOf r V0), TWPl r T → OpAt b T

def ordinaryHeckeAlgebraIntegral : Prop :=
  CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V0.frame c.O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T)
    (y : Pt (globOf r V0).frame c.O n) (al : Fin T.q → Fin n → c.O), V0.S' = s.S → LocCFT s → 1 ≤ n →
    (∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → y.N4 V0.frame.D0 → Eig y T al →
    DetQ (globOf r V0).frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ)
      (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) (Set.range T.sg) →
    B1 y T (n * Module.finrank ℚ (Lp L) + n * T.q)

def CoreO : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V0.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B)
    (y : Pt (globOf r V0).frame c.O n) (x : B.B →ₐ[c.O] c.O) (h : s.Wt n) (q : ℕ) (sg : Fin q → V0.frame.G₀)
    (al : Fin q → Fin n → c.O), V0.S' = s.S → 1 ≤ n → LevelX B J → J ≤ RingHom.ker x → (barPt B x).Arith h →
    B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → y.N4 V0.frame.D0 →
    (∀ j, sg j ∈ V0.frame.G' ∧ Function.Injective (al j) ∧
      (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) →
    DetQ (globOf r V0).frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ)
      (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) (Set.range sg) →
    ∀ δ : B.B →ₗ[c.O] c.O, IsDer x δ → (∀ v i, ∀ g ∈ V0.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) →
      ∀ g, δ (B.u.D.tr (MonoidAlgebra.single g 1)) = 0

def OrdVan : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
    (x : B.Pt) (h : s.Wt n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), V.S' = s.S → 1 ≤ n →
    r.V0ok → x.Arith h → x.D = GDet.ofRep (mat ρ) → Continuous ρ → Af.IsAutCsd ι (ρ.comp V.pr) →
    Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → V.frame.IsForm c.O n ρ P → (∀ g ∈ V.frame.I0, ρ g = 1) →
    (∀ v : Vl l L, (∀ i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) ∨
      Af.PotCrysAt (F := L) (ρ.comp V.pr) (s.A v)) →
    (∀ (v : Vl l L) i j, i < j → x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    RegDet V.frame c.O ρ P → ∀ z, IsOrdCoc V.frame ρ P r.Ip x.psi z → ∃ Y, ∀ g, z g = dY V.frame (mat ρ) Y g

end UpperTheory.V.Th
