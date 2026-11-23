import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SatakeDualWeyl.DefsCS

noncomputable section

namespace Formalism.MainNotions.Gaps.LG

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lbVec (k : ℕ) (pz : 𝓞 E) (i : Fin k) : Fin k → E :=
  Pi.single i (if i.1 = 0 then (pz : E) else 1)

def LbOf (k : ℕ) (pz : 𝓞 E) : Submodule (𝓞 E) (Fin k → E) :=
  Submodule.span (𝓞 E) (Set.range (lbVec k pz))

structure SplitAt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E) where
  φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F
  sig : ∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)
  alg : ∀ c : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] c) = (c, c)
  int : ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F
  ori : Valued.v (φ (a ⊗ₜ[F] (1 : v.adicCompletion F))).1 < 1

structure Par (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) where
  σ : E →ₐ[F] E
  J : Matrix (Fin k) (Fin k) E
  gp : Fin 2 → ℕ
  T : ℕ
  pz : 𝓞 E
  a : Fin 2 → E

namespace Par

variable {k : ℕ} (P : Par F E k)

def Lb : Submodule (𝓞 E) (Fin k → E) := LbOf k P.pz

def Ld : Submodule (𝓞 E) (Fin k → E) := Submodule.span (𝓞 E) (dualSet (P.σ : E →+* E) P.J P.Lb)

def LbV (v : HeightOneSpectrum (𝓞 F)) : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) P.Lb

def LdV (v : HeightOneSpectrum (𝓞 F)) : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) P.Ld

def pzV (v : HeightOneSpectrum (𝓞 F)) : intV E v :=
  ⟨((P.pz : 𝓞 E) : E) ⊗ₜ[F] (1 : v.adicCompletion F), Subring.subset_closure (Or.inl ⟨⟨_, ⟨P.pz, rfl⟩⟩, rfl⟩)⟩

def fKer (v : HeightOneSpectrum (𝓞 F)) : Submodule (intV E v) (P.LdV v) :=
  (P.LbV v).comap (P.LdV v).subtype ⊔ LinearMap.range (P.pzV v • (LinearMap.id : P.LdV v →ₗ[intV E v] P.LdV v))

abbrev fM (v : HeightOneSpectrum (𝓞 F)) : Type := P.LdV v ⧸ P.fKer v

def fT (v : HeightOneSpectrum (𝓞 F)) : P.LdV v →ₗ[intV E v] P.fM v := (P.fKer v).mkQ

abbrev Splits : Type :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (P.gp i : 𝓞 F) ∈ v.asIdeal → SplitAt P.σ v (P.a i)

def iwPre (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) :
    Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)) :=
  UPts P.σ P.J (v.adicCompletion F) ⊓ (iwU F k v).comap (bc ((RingHom.fst _ _).comp φ.toRingHom))

open Classical in

def Uloc (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)) :=
  if (P.T : 𝓞 F) ∈ v.asIdeal then levelVL P.σ P.J v P.Lb ⊓ stabFun _ (P.fT v)
  else if h0 : (P.gp 0 : 𝓞 F) ∈ v.asIdeal then P.iwPre v (S 0 v h0).φ
  else if h1 : (P.gp 1 : 𝓞 F) ∈ v.asIdeal then P.iwPre v (S 1 v h1).φ
  else levelVL P.σ P.J v P.Lb

abbrev GA : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := UPts P.σ P.J (FiniteAdeleRing (𝓞 F) F)

def U (S : P.Splits) : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  P.GA ⊓ ⨅ v : HeightOneSpectrum (𝓞 F), (P.Uloc S v).comap (bc (prV (E := E) v))

abbrev Cls (S : P.Splits) : Type :=
  ClassSet ((ratPts P.σ P.J (FiniteAdeleRing (𝓞 F) F)).subgroupOf P.GA) ((P.U S).subgroupOf P.GA)

structure LbOK (d : ℕ) : Prop where
  fin : Module.Finite (𝓞 E) P.Lb
  span : Submodule.span E (P.Lb : Set (Fin k → E)) = ⊤
  int : ∀ x ∈ P.Lb, x ∈ dualSet (P.σ : E →+* E) P.J P.Lb
  dual : ∀ y ∈ dualSet (P.σ : E →+* E) P.J P.Lb, (P.T : E) • y ∈ P.Lb
  index : P.Lb.toAddSubgroup.relIndex P.Ld.toAddSubgroup = P.T ^ d

def FMCard : Prop := ∀ v : HeightOneSpectrum (𝓞 F), (P.T : 𝓞 F) ∈ v.asIdeal → Nat.card (P.fM v) = P.T

def IwLe : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (P.gp i : 𝓞 F) ∈ v.asIdeal → ∀ s : SplitAt P.σ v (P.a i),
    P.iwPre v s.φ ≤ levelVL P.σ P.J v P.Lb

def UCompact : Prop :=
  ∀ S : P.Splits, letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsCompact (P.U S : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))

def UOpen : Prop :=
  ∀ S : P.Splits, letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : P.GA | (x : GL _ _) ∈ P.U S}

def ClsFinite : Prop := ∀ S : P.Splits, Finite (P.Cls S)

def StabTriv : Prop :=
  ∀ (S : P.Splits) (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), y ∈ P.GA →
    ∀ γ : GL (Fin k) E, γ ∈ UJ (P.σ : E →+* E) P.J →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ (P.U S).map (MulAut.conj y).toMonoidHom → γ = 1

end Par

end Gen

section HostPar

variable {R : Ranks} (H : Host R)

structure LevHyp (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) : Prop where
  T_prime : T.Prime
  pz_K : (pz : H.E) ∈ H.K
  pz_norm : (pz : H.E) * H.conj (pz : H.E) = (T : H.E)
  pz_cong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}
  piG_K : ∀ i, (piG i : H.E) ∈ H.K
  piG_norm : ∀ i, (piG i : H.E) * H.conj (piG i : H.E) = (H.g i : H.E)
  g_split : ∀ i, {v : HeightOneSpectrum (𝓞 H.E) | ((H.g i : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E

def hostPar (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) : Par H.F H.E R.k where
  σ := Examples₂.conjF H
  J := 1
  gp := H.g
  T := T
  pz := pz
  a := fun i => H.conj (piG i : H.E)

end HostPar

abbrev PlT {R : Ranks} (H : Host R) (T : ℕ) : Type := {v : HeightOneSpectrum (𝓞 H.F) // (T : 𝓞 H.F) ∈ v.asIdeal}

def FactSplitG : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 H.F)), (H.g i : 𝓞 H.F) ∈ v.asIdeal →
      Nonempty (SplitAt (Examples₂.conjF H) v (H.conj (piG i : H.E)))

def FactLb : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    (hostPar H T pz piG).LbOK (2 * R.f)

def FactFMCard : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    (hostPar H T pz piG).FMCard

def FactIwLe : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    (hostPar H T pz piG).IwLe

def FactUCompact : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    (hostPar H T pz piG).UCompact

def FactUOpen : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    (hostPar H T pz piG).UOpen

def FactClsFinite : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    (hostPar H T pz piG).ClsFinite

def FactStabTriv : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    (hostPar H T pz piG).StabTriv

def FactTNeG : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    ∀ i, T ≠ H.g i

def FactPlacesT : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    Nonempty (Fin R.f ≃ PlT H T)

def FactTau : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    ∀ w : HeightOneSpectrum (𝓞 H.E), (T : 𝓞 H.E) ∈ w.asIdeal →
      ∃ e : PlT H T ≃ ↥(R.Psi), ∀ (v : PlT H T) (x : 𝓞 H.F),
        x ∈ v.1.asIdeal ↔ w.valuation H.E (H.sigmaOf (e v : R.GG) (algebraMap H.F H.E (x : H.F))) < 1

end Formalism.MainNotions.Gaps.LG

end
