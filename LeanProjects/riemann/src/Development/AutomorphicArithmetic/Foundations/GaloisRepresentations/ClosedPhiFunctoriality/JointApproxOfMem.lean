import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

def JointApprox {k Γ : Type} [NormedField k] [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k))
    (p : (Γ →* GL (Fin a) k) → k) (θ : k) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C ∧
    (∀ g : Γ, ‖trc r g - ∑ ρ ∈ s, c ρ * trc ρ g‖ ≤ ε) ∧ ‖θ - ∑ ρ ∈ s, c ρ * p ρ‖ ≤ ε

theorem JointApprox.lin {k Γ : Type} [NormedField k] [Group Γ] {a : ℕ} {r : Γ →* GL (Fin a) k} {C : Set (Γ →* GL (Fin a) k)}
    {p : (Γ →* GL (Fin a) k) → k} {θ : k} (h : JointApprox r C p θ) : LinApprox r C := fun ε hε => by
  obtain ⟨s, c, hs, h1, -⟩ := h ε hε
  exact ⟨s, c, hs, h1⟩

variable {l : ℕ} [Fact l.Prime]

def wdTr (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (g : ↥(Weil h)) : Om l :=
  ι.symm (-((wdAt P ι Bw h hj r).charPol g).nextCoeff)

def ClosedPhi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ)
    (a : ℕ), 1 ≤ a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw)
      (J : (E →+* Om l) → Multiset ℤ) (r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l)), Continuous r → IsSSRep r →
    ∀ (C : Set (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l))) (g : ↥(Weil h)), deg g ≤ 0 → ∀ θ : Om l,
      JointApprox r C (fun ρ => wdTr P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype) g) θ →
      (∀ ρ ∈ C, Continuous ρ ∧ GlobalTheory.GalOfCusp.IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧ IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Om l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
      wdTr P ι Bw h hj (r.comp (Dec (F := E) A).subtype) g = θ

def PolyOfTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : ℕ) (X Y : WD h), X.unr → Y.unr →
    X.lpDim = a → Y.lpDim = a → ∀ F : ↥(Weil h), deg F = -1 →
    (∀ j : ℕ, 1 ≤ j → j ≤ a → (X.charPol (F ^ j)).nextCoeff = (Y.charPol (F ^ j)).nextCoeff) →
    ∀ g : ↥(Weil h), X.charPol g = Y.charPol g

abbrev iA (l : ℕ) [Fact l.Prime] : Ainf l →+* Per.Acris l := algebraMap (Ainf l) (Per.Acris l)

abbrev iB (l : ℕ) [Fact l.Prime] : Per.Acris l →+* Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l)

def zC (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* Per.Acris l := (iA l).comp (Per.zA l)

def fI (l : ℕ) [Fact l.Prime] : Ainf l →+* Per.Acris l := (iA l).comp WittVector.frobenius

variable {K : FinExt l}

def uC (bk : BK K) : Per.Acris l := ((iA l).comp bk.ev) X

def fA (bk : BK K) : bk.S →+* Per.Acris l := ((iA l).comp bk.ev).comp (frobS l bk.a)

def f0 (bk : BK K) : bk.S →+* Per.Acris l := (fA bk).comp ((PowerSeries.C).comp PowerSeries.constantCoeff)

structure IsSecQ (bk : BK K) (N k : ℕ) {d : ℕ} (A : Matrix (Fin d) (Fin d) bk.S) (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) : Prop where
  mul : Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))
  mod : ∀ i j, uC bk ∣ (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j
  mod' : ∀ i j, uC bk ∣ (Q' - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j
  frob : fA bk bk.E ^ N • (Q * A.map (f0 bk)) = f0 bk bk.E ^ N • (A.map (fA bk) * Q.map (phiA l))

structure IsPerU {d : ℕ} (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) : Prop where
  unit : IsUnit U
  inv : ∀ g : ↥(GK K), (ρ g).val.map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U

def IsOp {d : ℕ} (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (n : ℕ) (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)) : Prop :=
  ∃ U, IsPerU ρ U ∧ V * U = s • U.map ⇑(Per.φB l ^ n)

def FixUr (K : FinExt l) (n : ℕ) : Prop := ∀ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 → (frobUr l ^ n) c = c

def IsTr {B : Type} [CommRing B] (u : ↥(MaximalUnramifiedExtension l) →+* B) (s : B) {n : Type} [Fintype n] (v : n → B) (t : n → Om l) (p : Om l) : Prop :=
  ∀ lam : Om l →ₗ[↥(MaximalUnramifiedExtension l)] ↥(MaximalUnramifiedExtension l), ∑ i, v i * u (lam (t i)) = s * u (lam p)

def uB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l :=
  T.eB.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)

abbrev OB (P : LocPrime l) : Type := Om l ⊗[↥(MaximalUnramifiedExtension l)] Bst P

def IsCoord (P : LocPrime l) (L : FinExt l) {a : ℕ} (ψ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)) : Prop :=
  ∀ (v : Fin a → ↥L.1) (b : Bst P) (i : Fin a), ψ (v ⊗ₜ b) i = ((v i : ↥L.1) : Om l) ⊗ₜ b

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
