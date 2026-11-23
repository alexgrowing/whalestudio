import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CcKPrimitive

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.GH

def IsRoot {L : Type} [Field L] (x : L) : Prop := ∃ m : ℕ, 0 < m ∧ x ^ m = 1

structure CMData0 {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    {I : Type} (φ : I → L →+* ℂ) : Prop where
  real : IsTotallyReal F
  cplx : IsTotallyComplex L
  rank : Module.finrank F L = 2
  ne : c ≠ 1
  bij : Function.Bijective fun i => InfinitePlace.mk (φ i)

theorem CMData0.of_cmData {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]
    {c : L ≃ₐ[F] L} {I : Type} {φ : I → L →+* ℂ} (h : CMData F c φ) : CMData0 F c φ :=
  ⟨h.real, h.cplx, h.rank, h.ne, h.bij⟩

theorem cmData0_negTwo : CMData0 ℚ negTwoConj (fun w : InfinitePlace NegTwoField => w.embedding) :=
  CMData0.of_cmData cmData_negTwo

variable {e : ℕ} (H : GHost e)

instance psiFintype : Fintype H.Psi := Fintype.ofFinite _

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

def embPsi (g : H.Psi) : H.E →+* ℂ := H.emb (g : H.GG)

def IsConjPl (w w' : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → (x ∈ w.asIdeal ↔ y ∈ w'.asIdeal)

def IsSplitPl (v : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∃ x : 𝓞 H.E, x ∈ v.asIdeal ∧ ∀ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y ∉ v.asIdeal

def WtOK (a : H.Psi → ℤ) : Prop := ∀ ζ : H.E, IsRoot ζ → ∏ τ, embPsi H τ ζ ^ a τ = 1

def WtOKQ (a : H.Psi → ℚ) : Prop := ∃ z : H.Psi → ℤ, (∀ τ, a τ = z τ) ∧ WtOK H z

theorem wtOK_zero : WtOK H 0 := fun _ _ => by simp

structure IsClsF (ξ : HChar H.E) : Prop where
  unitary : ξ.IsUnitary
  unr : ∀ v, ξ.UnrAt v
  inf : ∀ k, ξ.inf k = 1
  triv : ξ.TrivOn H.F

structure IsEtaT (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta H.F
  inf : χ.HasInf (embPsi H) (fun _ => 1)

def EtaTExists : Prop := ∃ χ : HChar H.E, IsEtaT H χ

structure IsChiPsi (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  triv : χ.TrivOn H.F
  inf : χ.HasInf (embPsi H) (fun _ => 2)

structure PiBar where
  pb : Fin 2 → HeightOneSpectrum (𝓞 H.K)
  pb_over : ∀ k, ((H.g k : ℕ) : 𝓞 H.K) ∈ (pb k).asIdeal

def PiBar.Div {H : GHost e} (P : PiBar H) (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  w.under (𝓞 H.K) = P.pb k

structure Omg where
  om : ∀ k : Fin 2, (ZMod (H.g k))ˣ →* ℂˣ
  gen : ∀ k, Function.Injective (om k)

variable {H}

structure IsMu0 (P : PiBar H) (W : Omg H) (a : H.Psi → ℚ) (j : ℕ) (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn H.F
  inf : χ.HasInfQ (embPsi H) (fun τ => -a τ)
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (b : ℕ) (hb : b.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (b : H.E) → χ.locK w x = (W.om k (ZMod.unitOfCoprime b hb) ^ (2 * (j + 1)))⁻¹

def Mu0Exists (P : PiBar H) (W : Omg H) (a : H.Psi → ℚ) (j : ℕ) : Prop := ∃ χ : HChar H.E, IsMu0 P W a j χ

structure IsDelta (p : ℕ) (χ : HChar H.E) : Prop where
  fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  unr : ∀ v, ¬ OverP H p v → χ.UnrAt v
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → χ.loc v x ^ n = 1) ↔ 15 ∣ n

def DeltaExists (p : ℕ) : Prop := ∃ χ : HChar H.E, IsDelta (H := H) p χ

structure IsPsi (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E) : Prop where
  ord : ∃ a : ℕ, χ.OrderDvd (l ^ a)
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  ram : ∀ v, χ.UnrAt v ↔ v ∉ Q
  atl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1
  split : ∀ v ∈ Q, IsSplitPl H v

def SplitsCompletely (Q : Finset (HeightOneSpectrum (𝓞 H.E))) : Prop :=
  ∀ v ∈ Q, ∀ p : ℕ, p.Prime → OverP H p v → ∀ v' : HeightOneSpectrum (𝓞 H.E), OverP H p v' →
    Ideal.absNorm v'.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v'.asIdeal ^ 2

variable (H)

def congG : Set (Ideles H.E) :=
  {a | a ∈ unitIdl H.E ∧ ∀ k v, OverP H (H.g k) v → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v - 1) < 1}

def KD : Subgroup (Ideles H.E) :=
  Subgroup.closure (congG H ∪ {a | ∃ v k, a = locF H.F v k})

abbrev DtT : Type := Ideles H.E ⧸ KD H

open Classical in

def tildeD (χ : HChar H.E) : DtT H →* ℂˣ :=
  if h : KD H ≤ (χ.1.comp (finPartI H.E)).ker then QuotientGroup.lift (KD H) (χ.1.comp (finPartI H.E)) h else 1

def muTilT {m : ℕ} (mu : Fin m → HChar H.E) (j : ℕ) : DtT H →* ℂˣ :=
  if h : 1 ≤ j ∧ j ≤ m then tildeD H (mu ⟨j - 1, by omega⟩) else 1

def UOT : Subgroup (DtT H) := (unitIdl H.E).map (QuotientGroup.mk' (KD H))

def IsRationalUnitaryDeterminantMap (f : (letI := H.cmStar; unitary H.E) →* DtT H) : Prop :=
  letI := H.cmStar
  ∀ (k : H.Eˣ) (z : unitary H.E), (z : H.E) * H.conj (k : H.E) = k → QuotientGroup.mk (diagUnits H.E k) = f z

open Classical in

def e1T : (letI := H.cmStar; unitary H.E) →* DtT H := if h : ∃ f, IsRationalUnitaryDeterminantMap H f then h.choose else 1

def relDetT (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : DtT H ⧸ UOT H :=
  QuotientGroup.mk (QuotientGroup.mk (∏ᶠ w : HeightOneSpectrum (𝓞 H.E),
    localIdele H.E w (atFin w (unif w)) ^ (ordSub w (detSub M') - ordSub w (detSub M)).toNat))

def IsTwist (S : Set ℕ) (ξ : HChar H.E) : Prop :=
  (∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n) ∧ ξ.TrivOn H.F ∧ (∀ v, ξ.TameAt v) ∧
    ∀ v, ¬ ξ.UnrAt v → IsSplitPl H v ∧ (Ideal.absNorm v.asIdeal).Prime ∧
      ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ Ideal.absNorm v.asIdeal ∉ S

structure HFrame {m : ℕ} (a : Fin m → H.Psi → ℚ) where
  P : PiBar H
  W : Omg H
  mu0 : Fin m → HChar H.E
  eta : HChar H.E
  chiPsi : HChar H.E
  del : HChar H.E
  del' : HChar H.E
  isMu0 : ∀ j, IsMu0 P W (a j) j.1 (mu0 j)
  isEta : IsEtaT H eta
  isChi : IsChiPsi H chiPsi
  isDel : IsDelta (H := H) H.pde del
  isDel' : IsDelta (H := H) H.pde' del'

end GlobalTheory.GH
