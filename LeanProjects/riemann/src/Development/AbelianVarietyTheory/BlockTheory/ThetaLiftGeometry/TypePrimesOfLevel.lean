import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable (E n SG) in

def unipLevel : Subgroup (GLG E n SG) :=
  Subgroup.pi Set.univ fun w : SG => uniUT n (𝓞 E ⧸ w.1.asIdeal) n []

def SameClass (d d' : DecoSet E n ST SG) : Prop :=
  ∃ (γ : UF E n) (h : GLG E n SG), h ∈ unipLevel E n SG ∧ ((γ, h) : UF E n × GLG E n SG) • d = d'

def classStab (d : DecoSet E n ST SG) : Subgroup (UF E n) :=
  (MulAction.stabilizer (UF E n × GLG E n SG) d ⊓ (⊤ : Subgroup (UF E n)).prod (unipLevel E n SG)).map
    (MonoidHom.fst (UF E n) (GLG E n SG))

def IsReps {ι : Type} (rep : ι → DecoSet E n ST SG) : Prop :=
  ∀ d : DecoSet E n ST SG, ∃! c, SameClass (rep c) d

def IsStabOf {G : Type} [Group G] (j : G →* UF E n) (d : DecoSet E n ST SG) : Prop :=
  Function.Injective j ∧ j.range = classStab d

end Generic

variable (D : D7)

def conjInt : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

def condE : ℕ := D.host.QS * D.host.q * D.host.d

def TypeGenTie (πg : Fin 2 → 𝓞 D.host.E) : Prop :=
  ∀ i, (πg i : D.host.E) ∈ D.host.K ∧ πg i * conjInt D (πg i) = (D.host.g i : 𝓞 D.host.E) ∧
    ((condE D : ℕ) : 𝓞 D.host.E) ∣ πg i - 1

def LevelGenTie (πT : D.what₂.Word → 𝓞 D.host.E) : Prop :=
  ∀ u, (πT u : D.host.E) ∈ D.host.K ∧ πT u * conjInt D (πT u) = ((D.mem u).A.T : 𝓞 D.host.E) ∧
    ((condE D * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E) ∣ πT u - 1

open Classical in

def typePrimes (πg : Fin 2 → 𝓞 D.host.E) : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
  divs (conjInt D (πg 0)) ∪ divs (conjInt D (πg 1))

abbrev ColPt (πg : Fin 2 → 𝓞 D.host.E) (π : 𝓞 D.host.E) : Type :=
  letI := D.host.cmStar; DecoSet D.host.E (D.R.N 0) (divs π) (typePrimes D πg)

abbrev UCol : Type := ↥(@UF D.host.E _ D.host.cmStar (D.R.N 0))

def ClassTie (πg : Fin 2 → 𝓞 D.host.E) (πT : D.what₂.Word → 𝓞 D.host.E)
    (rep : ∀ u μ, (D.chTw u μ).cls 0 → ColPt D πg (πT u)) : Prop :=
  letI := D.host.cmStar
  ∀ u μ, IsReps (rep u μ)

def StabTie (πg : Fin 2 → 𝓞 D.host.E) (πT : D.what₂.Word → 𝓞 D.host.E)
    (rep : ∀ u μ, (D.chTw u μ).cls 0 → ColPt D πg (πT u))
    (j : ∀ u μ (c : (D.chTw u μ).cls 0), (D.chTw u μ).stab 0 c →* UCol D) : Prop :=
  letI := D.host.cmStar
  ∀ u μ c, IsStabOf (j u μ c) (rep u μ c)

def TypePrimesLarge : Prop := ∀ i, 2 * D.R.f * D.R.k + 1 < D.host.g i

def ColumnStabTrivial_at (_Dx : DivX D) (_Tw : TwForms D) (_E : KerEnt D _Dx _Tw)
    (πg : Fin 2 → 𝓞 D.host.E) (πT : D.what₂.Word → 𝓞 D.host.E)
    (rep : ∀ u μ, (D.chTw u μ).cls 0 → ColPt D πg (πT u))
    (j : ∀ u μ (c : (D.chTw u μ).cls 0), (D.chTw u μ).stab 0 c →* UCol D) : Prop :=
  TypePrimesLarge D → TypeGenTie D πg → LevelGenTie D πT → ClassTie D πg πT rep → StabTie D πg πT rep j →
    ∀ (u : D.what₂.Word) (μ : D.what₂.Tup),
      (D.chTw u μ).StabZero ∧ ∀ c, (D.chTw u μ).wt 0 c = 1

end GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers

end
