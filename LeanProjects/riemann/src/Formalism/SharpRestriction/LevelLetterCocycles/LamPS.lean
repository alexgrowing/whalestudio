import Formalism.SharpRestriction.LevelLetterCocycles.LocalFormOfThreeInputs

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def letS (c : ZMod n) : Submodule O (W.DD T) :=
  LinearMap.ker ((((letE c : LetA O n) • LinearMap.id - LinearMap.id :
    W.DD T →ₗ[LetA O n] W.DD T)).restrictScalars O)

def DelS : Submodule O (W.DD T) :=
  ⨅ δ ∈ W.DelF, LinearMap.ker (W.γD T δ - LinearMap.id)

def NcS (c : ZMod n) : Submodule O (W.DD T) :=
  (W.N T).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def PcS (c : ZMod n) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  ((Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).comap (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (Eπ ^ h'))).restrictScalars O ⊓
    DelS W T ⊓ letS W T c

def PiNS (π' : LetA O n) (k : ℕ) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ k)).restrictScalars O ⊓ DelS W T

def InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  LamPS W T Eπ h' c ⊓ (PiNS W T π' k).comap (W.γD T W.gamK - LinearMap.id)

abbrev JcQ (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Type :=
  ↥(InvS W T π' Eπ h' M c) ⧸ (PiNS W T π' M).comap (InvS W T π' Eπ h' M c).subtype

abbrev IcQ (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Type :=
  ↥(InvS W T π' Eπ h' 1 c) ⧸ (PiNS W T π' 1).comap (InvS W T π' Eπ h' 1 c).subtype

abbrev LcQ (π' : LetA O n) (c : ZMod n) : Type :=
  ↥(NcS W T (c - 1)) ⧸ (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype

def JCl (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Set (G → T.V) :=
  {κ | ∃ hκ : κ ∈ latticeCocycles T.L, ∃ w ∈ InvS W T π' Eπ h' M c, ∃ z ∈ PiNS W T π' M,
    ∃ hwz : (w, z) ∈ W.wachCocyclesDelta T,
      Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) = W.clK T ⟨(w, z), hwz⟩}

def JZ (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Submodule O (G → T.V) :=
  Submodule.span O (JCl W T π' Eπ h' M c)

end Local

section Record

variable {l : ℕ} [Fact l.Prime]

abbrev eK (K : FinExt l) : ℕ := finrank ↥(K0 K) ↥K.1

abbrev sK (l : ℕ) [Fact l.Prime] (K : FinExt l) : ℕ := (l - 1) / eK K

abbrev MK (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' : ℕ) : ℕ := ⌈(4 * h' : ℝ) / (sK l K : ℝ)⌉₊

abbrev y2K (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' S η : ℕ) : ℕ :=
  2 * sigA l (sK l K) h' + kapA l (eK K) h' S + rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)

def HypN (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, JumpsInV (P.PD K) T₂.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧ (∀ τ, b τ + S ≤ h') ∧ 1 ≤ h' ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

end Record

end Formalism.MainNotions.N.Ln34

end
