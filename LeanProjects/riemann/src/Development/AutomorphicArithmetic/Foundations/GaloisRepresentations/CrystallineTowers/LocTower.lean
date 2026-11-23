import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrystallinePeriodsOfSmooth
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC TensorProduct
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst CrystallineSemistableComparison UpperTheory.Gal.Int.Geo
open GlobalTheory.GalV (HTower Htot hop galV galTot pullTot IsCorrOp)

namespace UpperTheory.Gal.Seam

def kOf {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) : E →+* ↥Bw.Kw.1 :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E

def mod {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {L : Type} [Field L] {H : HTower ↥K} {θ : H.Γ → L}
    (C : Cover H θ ↥(OK l K)) : Model l K := ⟨C.Y, C.p⟩

def toMod {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {L : Type} [Field L] {H : HTower ↥K} {θ : H.Γ → L}
    (C : Cover H θ ↥(OK l K)) : H.geomZ (PadicAlgCl l) ⟶ GlobalTheory.Et.geom (PadicAlgCl l) (mod C).q :=
  GlobalTheory.Et.geomMap (PadicAlgCl l) H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _)

def HopEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero Ω] (H : HTower k),
  Nice H → ∀ g, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g)

def NiceBc : Prop := ∀ (k K : Type) [Field k] [Field K] (τ : k →+* K) (H : HTower k), Nice H → Nice (bcAlong H τ)

def LocTower : Prop := ∀ (l : ℕ) [Fact l.Prime] (k K Ω Ω' : Type) [Field k] [CharZero k] [Field K] [Field Ω] [Field Ω'] [Algebra k Ω]
  [IsAlgClosure k Ω] [Algebra K Ω'] [IsAlgClosed Ω'] (τ : k →+* K) (j : Ω →+* Ω'), (∀ x, j (algebraMap k Ω x) = algebraMap K Ω' (τ x)) →
  ∀ (H : HTower k), Nice H → ∀ (L : Type) [Field L] [Algebra ℚ_[l] L] (θ : H.Γ → L) (d : ℕ) (ρ₀ : (Ω ≃ₐ[k] Ω) →* GL (Fin d) L),
    IsMat l H Ω L θ ρ₀ → ∃ ρ₁ : (Ω' ≃ₐ[K] Ω') →* GL (Fin d) L, IsMat l (bcAlong H τ) Ω' L θ ρ₁ ∧
      ∀ σ σ', (∀ x, σ' (j x) = j (σ x)) → ρ₁ σ' = ρ₀ σ

def BcCover : Prop := ∀ (k K O O' L : Type) [Field k] [Field K] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O' K] [Field L]
  (τ : k →+* K) (φ : O →+* O'), (∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x)) →
  ∀ (H : HTower k) (θ : H.Γ → L) (C : Cover H θ O), ∃ (C' : Cover (bcAlong H τ) θ O') (u : C'.Y ⟶ C.Y),
    IsPullback u C'.p C.p (Spec.map (CommRingCat.ofHom φ)) ∧
    C'.π ≫ u = pullback.fst H.q (Spec.map (CommRingCat.ofHom τ)) ≫ C.π ∧ (C.Onto → C'.Onto) ∧ (C.Good → C'.Good) ∧
    ∀ g (T : Scheme.{0}) (s t : T ⟶ C.Y) (m : ℕ), t ≫ C.p = s ≫ C.p → C.Lies g s t m →
      ∀ (T' : Scheme.{0}) (v : T' ⟶ T) (s' t' : T' ⟶ C'.Y), IsPullback v s' s u → t' ≫ u = v ≫ t → t' ≫ C'.p = s' ≫ C'.p →
        C'.Lies g s' t' m

def IntMap : Prop := ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
  (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
  ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw →
    ∃ φ : Ow w →+* ↥(OK l Bw.Kw.1), (∀ x, algebraMap ↥(OK l Bw.Kw.1) ↥Bw.Kw.1 (φ x) = kOf Bw (algebraMap (Ow w) E x)) ∧
      ∀ ϖ, Irreducible ϖ → Irreducible (φ ϖ)

def PieceIn : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (L : Type) [Field L] [Algebra ℚ_[l] L]
  (H : HTower ↥K) (θ : H.Γ → L), Nice H → ∀ C : Cover H θ ↥(OK l K), C.Onto →
    Function.Injective ((pullTot l (sch.map (toMod C))).baseChange L) ∧
    piece l H (PadicAlgCl l) L θ ≤ LinearMap.range ((pullTot l (sch.map (toMod C))).baseChange L) ∧
    ∀ σ, galTot l (PadicAlgCl l) H.q σ ∘ₗ pullTot l (sch.map (toMod C)) =
      pullTot l (sch.map (toMod C)) ∘ₗ galTot l (PadicAlgCl l) (mod C).q σ

def NegVan : Prop := ∀ (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ), n < 0 → Subsingleton (HQ l (sch.obj X) n 0)

def GoodOf : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K),
  Smooth M.p → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.p → M.Good

def MatIn : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : HTower ↥K.1) (θ : H.Γ → Om l), Nice H →
  ∀ C : Cover H θ ↥(OK l K.1), C.Onto → ∀ (d : ℕ) (ρ₁ : (PadicAlgCl l ≃ₐ[↥K.1] PadicAlgCl l) →* GL (Fin d) (Om l)),
    IsMat l H (PadicAlgCl l) (Om l) θ ρ₁ → ∃ (N : ℕ) (a : Fin N → ℕ) (b : ∀ n : Fin N, Module.Basis (Fin (a n)) ℚ_[l] ((mod C).V n))
      (M : Matrix (Σ n, Fin (a n)) (Fin d) (Om l)), Function.Injective M.mulVec ∧ ∀ σ : ↥(GK K),
        (Matrix.blockDiagonal' fun n : Fin N => (mod C).mat n (b n) σ).map (algebraMap ℚ_[l] (Om l)) * M =
          M * (ρ₁ (IntermediateField.fixingSubgroupEquiv K.1 σ) : Matrix (Fin d) (Fin d) (Om l))

def SubAdm : Prop := ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
  ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (N d : ℕ) (a : Fin N → ℕ)
    (R : ∀ n, ↥(GK Bw.Kw) → Matrix (Fin (a n)) (Fin (a n)) ℚ_[l]) (r : ↥Gw →* GL (Fin d) (Om l)),
    (∀ n, R n 1 = 1 ∧ (∀ σ σ', R n (σ * σ') = R n σ * R n σ') ∧ IsAdmP P (GK Bw.Kw) (R n)) →
    ∀ M : Matrix (Σ n, Fin (a n)) (Fin d) (Om l), Function.Injective M.mulVec →
    (∀ g : ↥Gw, (Matrix.blockDiagonal' fun n => R n (Bw.e g)).map (algebraMap ℚ_[l] (Om l)) * M =
      M * (r g : Matrix (Fin d) (Fin d) (Om l))) → IsCrysAt P Bw r

def GrCrys : Prop := ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
  ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (d : ℕ) (r₀ r : ↥Gw →* GL (Fin d) (Om l)),
    IsGr r₀ r → IsCrysAt P Bw r₀ → IsCrysAt P Bw r

end UpperTheory.Gal.Seam
