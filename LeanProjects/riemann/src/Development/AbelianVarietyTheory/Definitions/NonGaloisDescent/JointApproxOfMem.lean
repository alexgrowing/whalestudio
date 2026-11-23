import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong TensorProduct

namespace GlobalTheory.CongPhi

def phiSum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x : WD h) (σ : Weil h) (n : ℕ) : ℂ :=
  ((x.charPol σ).roots.map (· ^ n)).sum

def JointApprox {k Γ : Type} [NormedField k] [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k))
    (S : ℕ → k) (s : (Γ →* GL (Fin a) k) → ℕ → k) : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ (t : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k),
    (t : Set (Γ →* GL (Fin a) k)) ⊆ C ∧ (∀ g : Γ, ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ ≤ ε) ∧
      ∀ j ≤ n, ‖S j - ∑ ρ ∈ t, c ρ * s ρ j‖ ≤ ε

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def IsPhiD (T : ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ) ≃ₗ[LL] ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ)) : Prop :=
  ∀ x, ((T x : ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ)) : V ⊗[Qp] B) = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := V) x

open Classical in

def phiTr (m : ℤ) : LL :=
  if h : ∃ T, IsPhiD PD ρ T then
    LinearMap.trace LL _ ((h.choose ^ ((Module.finrank Qp K₀ : ℤ) * m) : ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ) ≃ₗ[LL] ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ)) :
      ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ) →ₗ[LL] ↥(Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ))
  else 0

open Classical in

def phiLetter (m : ℤ) : LL := phiTr PD ρ m / (Module.finrank Qp K₀ : LL)

end Local

section Om

variable {l : ℕ} [Fact l.Prime]

def matRep {K : FinExt l} (L : FinExt l) {a : ℕ} (r' : ↥(GK K) →* GL (Fin a) ↥L.1) :
    Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥L.1 ≃ₐ[↥L.1] _) : _ →* _).comp ((Units.coeHom _).comp r')

def IsMod {K : FinExt l} {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) :
    Prop :=
  ∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ g).val i j

def CrysLe (P : LocPrime l) (K : FinExt l) {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (N : ℕ) : Prop :=
  ∃ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1), IsMod ρ L r' ∧ Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (matRep L r') ∧
    Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD K) (matRep L r') ≤ Formalism.WeaklyAdmissibleFiltrations.FilV (P.PD K) (LL := ↥L.1) (V := Fin a → ↥L.1) (-(N : ℤ)) ∧
    Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD K) (matRep L r') ⊓ Formalism.WeaklyAdmissibleFiltrations.FilV (P.PD K) (LL := ↥L.1) (V := Fin a → ↥L.1) ((N : ℤ) + 1) = ⊥

open Classical in

def phiOm (P : LocPrime l) (K : FinExt l) {a : ℕ} (ρ : ↥(GK K) →* GL (Fin a) (Om l)) (m : ℤ) : Om l :=
  if h : ∃ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1), IsMod ρ L r' then
    ((phiLetter (P.PD K) (matRep h.choose h.choose_spec.choose) m : ↥h.choose.1) : Om l)
  else 0

end Om

def ClosedPhi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A w),
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
      (hBw : Pst.Induces Bw),
    ∀ (J : (E →+* Qbar l) → Multiset ℤ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r →
    ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)),
      (∀ ρ ∈ C, Continuous ρ ∧ IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
    ∀ (σ : Weil hA) (S : ℕ → Qbar l),
      JointApprox r C S (fun ρ n => ι.symm (phiSum (wdAt P ι Bw hA hBw (ρ.comp (Dec (F := E) A).subtype)) σ n)) →
      ∀ n : ℕ, phiSum (wdAt P ι Bw hA hBw (r.comp (Dec (F := E) A).subtype)) σ n = ι (S n)

end GlobalTheory.CongPhi

end
