import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions.N

namespace Formalism.MainNotions.EmbeddingTypes

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.TruncatedSeriesCountingIdentities (Decl CoefExt locC)

section Rank

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def FilCount : Prop :=
  ∀ (τ : K →ₐ[Qp] LL) (J : Finset ℤ), (∀ a, a ∉ J → multV PD ρ τ a = 0) →
    (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0) =
      ∑ a ∈ J.filter (· < 0), multV PD ρ τ a

end Rank

section Row

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def powB (L : Lattice (O := O) ρ) (n : ℕ) : Submodule O (G → V) :=
  (latticeFiniteCocycles PD L).map ((((PD.p : ℕ) : O) ^ n) • (LinearMap.id : (G → V) →ₗ[O] (G → V))) ⊔ latticeCoboundaries L

def lenModPow (L : Lattice (O := O) ρ) (n : ℕ) : ℕ∞ :=
  Module.length O (↥(latticeFiniteCocycles PD L) ⧸ (powB PD L n).comap (latticeFiniteCocycles PD L).subtype)

omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  [Module Qp V] [IsScalarTower Qp LL V] in

def lenInvD (L : Lattice (O := O) ρ) : ℕ∞ :=
  Module.length O ↥(Representation.invariants (repD L))

end Row

variable {D : D7}

open Classical

section TypeSign

variable {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

def EmbTypeUc (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  (∀ x : D.host.E, ∃ y : D.what₂.LL,
      Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x)) ∧
  ∃ φ ∈ D.host.cmType,
    ∀ (x : D.host.E) (y : D.what₂.LL),
      Br.toLLK (D.nbr i w hw) (D.nd.embK i y) = τ₀ (Br.cEw D.nbr i w hw x) →
        D.what₂.embLL y = starRingEnd ℂ (φ x)

def EmbTypeUe (ep : Bool) (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) : Prop :=
  if ep then Br.EmbTypeU D.nbr i w hw τ₀ else EmbTypeUc τ₀

variable (i w hw) in

def PlTypeUe (ep : Bool) : Prop := ∀ τ₀, EmbTypeUe (i := i) (w := w) (hw := hw) ep τ₀

end TypeSign

section AtW

variable {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : CoefExt D i w hw)

def EmbU (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) : Prop :=
  ∃ τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw,
    EmbTypeUe ep τ₀ ∧ ∀ x, τ x = C.inc (τ₀ x)

def IsStd {k : ℕ} {M : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1}
    (L : Lattice (O := ↥(OL C.LL)) (matRep M)) : Prop :=
  ∀ v, v ∈ L.T ↔ ∀ j, v j ∈ Set.range (algebraMap ↥(OL C.LL) ↥C.LL.1)

end AtW

def ShapeJumps (k m t : ℕ) (sgn : ℤ) (C L : Finset ℤ) (μ : ℤ → ℤ) : Prop :=
  (∃ s S η : ℚ, 0 < s ∧ 0 < S ∧ 0 < η ∧
    (∀ a ∈ C, s ≤ ((sgn * a : ℤ) : ℚ) ∧ ((sgn * a : ℤ) : ℚ) ≤ s + S) ∧ ∀ a ∈ L, |(a : ℚ)| ≤ η) ∧
  C.card = k - 1 ∧ L.card = m ∧ Disjoint C L ∧ Disjoint C (Finset.Ico 0 (t : ℤ)) ∧
  Disjoint L (Finset.Ico 0 (t : ℤ)) ∧ (-1 : ℤ) ∉ C ∪ L ∧ (t : ℤ) ∉ C ∪ L ∧
  ∀ a, μ a = if a ∈ C ∪ L ∪ Finset.Ico 0 (t : ℤ) then 1 else 0

section Pt

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : Decl D i) (ep : Bool)

def hypL : Prop :=
  2 ≤ D.nd.l i ∧ (D.host.cls (D.nd.l i) = PrimeClass.splitK ∨ D.nd.l i ∈ D.host.small) ∧
    (D.nd.l i ∉ D.host.small → ∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧
    D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1

def RowsAreConj : Prop := ∀ v, v ∈ dc.row ↔ ∃ u ∈ dc.col, IsConjPl D.host u v

def hypDecl : Prop :=
  (∀ v (hv : v ∈ placesOver D.host.E (D.nd.l i)), v ∈ dc.col ↔ PlTypeUe i v hv ep) ∧
    RowsAreConj i dc

def admG2 : Prop :=
  D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw),
    (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rO D.nd i r x)))) ∧
    (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r x)))) ∧
    ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ Cl Lo : Finset ℤ,
      ∀ x, ShapeJumps D.R.k D.R.m D.R.t (if EmbU C ep τ then 1 else -1) Cl Lo
        (multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r x))) τ)

def ambBlock : Prop :=
  π ∈ D.nd.Z i → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
    (∀ a, multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r π))) τ a =
      multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) τ a +
        ∑ c ∈ Finset.Icc 1 D.R.t,
          multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (chiRatO D.nd i c))) τ a) ∧
    ∀ c ∈ Finset.Icc 1 D.R.t, ∀ a,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0

def G5at (S : IdempotentChoiceData D.nd i) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.E), (v ∈ D.nd.S i ∨ v ∈ D.nd.Q i) →
    TameGen D.nd (D.nd.plOm.1 v) (D.nd.gam0 i v) ∧
    ((v ∈ D.nd.Q i ∨ v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) →
      ∀ x, (∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        (rO D.nd i r x γ - 1) *
          (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0) ∧
        ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
          ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ u,
            e ((mapM (toK D.nd i) (rO D.nd i r x) γ).mulVec u) =
              ((e u).1, toK D.nd i ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (e u).2)) ∧
    ((∃ k, v ∈ placesOver D.host.E (D.host.g k)) →
      ∃ P : Polynomial (D.nd.T i),
        (∀ x, ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
          aeval (rO D.nd i r x (D.nd.gam0 i v)) (P.map (evT D.nd i x)) *
            (rO D.nd i r x γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) = 0) ∧
        IsUnit (P.eval (algebraMap (D.nd.O i) (D.nd.T i) (D.nd.zeta i v)))) ∧
    (v ∈ D.nd.S i →
      (∀ c : Fin D.R.t, ∀ φ : (S.X' → MatN D.nd i) →ₗ[D.nd.O i] KmodO (D.nd.O i),
        (∀ a, InR' D.nd r S a → ∀ y, InY D.nd r S y → φ (a * y) = S.ψχ c a • φ y) →
        ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), φ (yg D.nd r S γ) = 0) ∧
      ∀ a : ℤ,
        Subsingleton ↥(H0 ((rhoBarTw D.nd ρ π a).comp (decS D.nd v))) ∧
        Subsingleton (H1 ((rhoBarTw D.nd ρ π a).comp (decS D.nd v))) ∧
        Subsingleton (H2 ((rhoBarTw D.nd ρ π a).comp (decS D.nd v))))

def admG5 : Prop := π ∈ D.nd.Z i → ∀ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S → G5at i r ρ π S

def ColumnH0Vanishing : Prop :=
  π ∈ D.nd.Z i →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    ∀ C : CoefExt D i w hw, H0V (matRep (locC C (WpO D.nd i ρ π))) = ⊥

def admBK : Prop := TruncatedSeriesCountingIdentities.admBK i ∧ LargeLevelLemmas.BlochKatoAnnihilators i

def LiftExponentColumn (e' : ℕ) : Prop := TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc (fun _ => e')

def LiftExponentDualPlaces (e' : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ C : CoefExt D i w hw, C.IsGood →
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : D.nd.X i => ⇑(locC C (rDuO D.nd i r x))) e'

def H0ColumnLengthBound (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) : Prop :=
  π ∈ D.nd.Z i →
  ∀ u ∈ dc.col, ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    IsConjPl D.host u w → ∀ C : CoefExt D i w hw, C.IsGood →
    ∀ L2 : Lattice (O := ↥(OL C.LL)) (matRep (locC C (T2O D.nd i ρ π))), IsStd C L2 →
      lenInvD L2 ≤ (D.R.r : ℕ∞) * (c0 u : ℕ∞) * lenOl (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL))

def admTB (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ C : CoefExt D i w hw, C.IsGood →
    TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (Br.inert D.nbr i w hw)
      (fun τ => {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r π))) τ a}) D.R.t cB

def UnramifiedTrivialH1f : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    ∀ C : CoefExt D i w hw,
    UnrTriv (Br.PD D.loc D.nbr i w hw) (LL := ↥C.LL.1) (Br.inert D.nbr i w hw)

def ambDual : Prop :=
  π ∈ D.nd.Z i →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ (C : CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ),
    multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) τ a =
      multV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) τ (-a - 1)

def ambT2 : Prop :=
  π ∈ D.nd.Z i →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ C : CoefExt D i w hw,
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) ∧
      IsDR (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) ∧
      H0V (matRep (locC C (T2O D.nd i ρ π))) = ⊥

def ambW : Prop :=
  π ∈ D.nd.Z i →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    ∀ C : CoefExt D i w hw, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π)))

def ambFil : Prop :=
  (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    ∀ (C : CoefExt D i w hw) (x : D.nd.X i),
    FilCount (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r x)))) ∧
  (π ∈ D.nd.Z i →
    (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
      ∀ C : CoefExt D i w hw,
      FilCount (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π)))) ∧
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
      ∀ C : CoefExt D i w hw,
      FilCount (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))))

def H1fFiniteRankTorsion : Prop :=
  π ∈ D.nd.Z i →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ (C : CoefExt D i w hw)
      (L2 : Lattice (O := ↥(OL C.LL)) (matRep (locC C (T2O D.nd i ρ π)))), IsStd C L2 → ∀ n : ℕ,
      lenModPow (Br.PD D.loc D.nbr i w hw) L2 n ≤
        (n : ℕ∞) * (finrank ↥C.LL.1
            (FiniteCohomology (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π)))) : ℕ∞) *
          lenOl (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) + lenInvD L2

def ambSub : Prop :=
  D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ (C : CoefExt D i w hw) (A : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)),
    IsSubOfSums A.ρ (fun x : D.nd.X i => ⇑(locC C (rTwO D.nd i r x))) →
      IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ ∧
      ∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) A.ρ τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (locC C (rTwO D.nd i r π))) τ a}

def ambCont : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : CoefExt D i w hw),
    (∀ x v, Continuous fun g => matRep (locC C (rTwO D.nd i r x)) g v) ∧
    (π ∈ D.nd.Z i →
      (∀ v, Continuous fun g => matRep (locC C (WpO D.nd i ρ π)) g v) ∧
      ∀ v, Continuous fun g => matRep (locC C (T2O D.nd i ρ π)) g v)

def ambTypeD : Prop :=
  ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)),
    PlTypeUe i u hu ep →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      IsConjPl D.host u w → ∀ τ₀, ¬ EmbTypeUe (i := i) (w := w) (hw := hw) ep τ₀

def admitted (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : Prop :=
  TruncatedSeriesCountingIdentities.admG1 i r ∧ admG2 i r ep ∧ TruncatedSeriesCountingIdentities.admG3 i r ρ π ∧ TruncatedSeriesCountingIdentities.admG4 i r ∧ admG5 i r ρ π ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions i ∧
    TruncatedSeriesCountingIdentities.admG6 i r ∧ ColumnH0Vanishing i ρ π dc ∧ LargeLevelLemmas.adm51 i r ρ π ∧ LargeLevelLemmas.CharpolyCoeffsLemmaFamily i r ∧ LargeLevelLemmas.SpanQuotientLemma i r ρ π ∧
    admBK i ∧ LiftExponentColumn i r dc e' ∧ LiftExponentDualPlaces i r dc e' ∧ H0ColumnLengthBound i ρ π dc c0 ∧
    admTB i r π dc cB ∧ UnramifiedTrivialH1f i dc ∧
    TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage i ∧
    TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i ∧ TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i ∧ TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i ∧ TruncatedSeriesCountingIdentities.admH2 i ∧ LargeLevelLemmas.tateH1FinitenessAtPlacesOver i ∧ TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i ∧
    ambBlock i r ρ π ∧ ambDual i ρ π dc ∧ ambT2 i ρ π dc ∧ ambW i ρ π dc ∧ ambFil i r ρ π dc ∧
    H1fFiniteRankTorsion i ρ π dc ∧ ambSub i r π dc ∧ ambCont i r ρ π ∧ ambTypeD i ep

def JumpConditions : Prop :=
  ∀ u (hu : u ∈ dc.col),
    Br.jW D.loc D.nbr i u ((dc.cover u).1 (Or.inr hu)) ρ π ≤ locDeg D.host.E u * D.R.m

def rowNum (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (u : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  (locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * (e' : ℚ) + (D.R.r : ℚ) * (c0 u : ℚ)

def ColengthRowPlaceBound (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) : Prop :=
  ∀ u ∈ dc.col, ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    IsConjPl D.host u w → ∀ C : CoefExt D i w hw, C.IsGood →
    RowAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : D.nd.X i => ⇑(locC C (rDuO D.nd i r x)))
      ⇑(locC C (T2O D.nd i ρ π)) (rowNum e' c0 u)

def boundSplit (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : ℚ :=
  (∑ u ∈ dc.col, ((e' : ℚ) + (locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * ((e' : ℚ) + D.nd.vdel i) +
      2 * D.nd.vdel i + Br.h0W i u ρ π +
      (locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * (e' : ℚ) + (D.R.r : ℚ) * (c0 u : ℚ))) +
    Br.sPi D.loc D.nbr i ρ π +
    (∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e) +
    (padicValNat (D.nd.l i) (hE D.host) : ℚ) +
    (D.R.t : ℚ) * (∑ w ∈ dc.row, ((locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
    4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
    (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col +
    (D.R.t : ℚ) * (∑ v ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}))

def ShaBoundTheoremB (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : Prop :=
  Br.sFin D.loc D.nbr i ρ π →
    (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
    (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → D.nd.vcc i π ≤ boundSplit i ρ π dc e' c0 cB

def aux₃ (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : Prop :=
  hypL i → hypDecl i dc ep → π ∈ D.nd.Z i →
    JumpConditions i ρ π dc ∧ ColengthRowPlaceBound i r ρ π dc e' c0 ∧ ShaBoundTheoremB i ρ π dc e' c0 cB

end Pt

def Stmt (D : D7) : Prop :=
  ∀ (ep : Bool) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : Decl D i)
    (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → admitted i r ρ π dc ep e' c0 cB → aux₃ i r ρ π dc ep e' c0 cB

end Formalism.MainNotions.EmbeddingTypes
