import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.GradedCompletionLemmas

noncomputable section

open MvPowerSeries

namespace Formalism.MainNotions.GradedPowerSeriesLemmas

section Graded

variable (O : Type) [CommRing O] {a : ℕ} (wt : Fin a → ℤ)

def W : Fin a → Formalism.BasicNotions.V1.Wt 1 := fun v _ => wt v

def cj (j : ℤ) : Formalism.BasicNotions.V1.Wt 1 := fun _ => j

def mwt (n : Fin a →₀ ℕ) : ℤ := n.sum fun v k => (k : ℤ) * wt v

abbrev Pring : Subalgebra O (MvPowerSeries (Fin a) O) := Formalism.MainNotions.UnusedSlot38.Psub O (W wt)

abbrev PT : Type := ↥(Pring O wt)

variable {O wt}

def IsHom (j : ℤ) (f : PT O wt) : Prop :=
  (f : MvPowerSeries (Fin a) O) ∈ Formalism.MainNotions.UnusedSlot38.Pj O (W wt) (cj j)

def PjP (j : ℤ) : Submodule O (PT O wt) :=
  (Formalism.MainNotions.UnusedSlot38.Pj O (W wt) (cj j)).comap (Pring O wt).val.toLinearMap

def comp (j : ℤ) (f : MvPowerSeries (Fin a) O) : MvPowerSeries (Fin a) O :=
  Formalism.MainNotions.UnusedSlot38.comp (W wt) (cj j) f

theorem X_mem (v : Fin a) : (X v : MvPowerSeries (Fin a) O) ∈ Pring O wt :=
  Formalism.MainNotions.UnusedSlot38.Pj_le_P (W wt) (W wt v) (Formalism.MainNotions.UnusedSlot38.X_mem_Pj (W wt) v)

def Xv (v : Fin a) : PT O wt := ⟨X v, X_mem v⟩

def cc : PT O wt →+* O := (constantCoeff (σ := Fin a) (R := O)).comp (Pring O wt).val.toRingHom

variable (𝔓 : Ideal (PT O wt))

abbrev AT : Type := PT O wt ⧸ 𝔓

def mkA : PT O wt →ₐ[O] AT 𝔓 := Ideal.Quotient.mkₐ O 𝔓

def Aj (j : ℤ) : Submodule O (AT 𝔓) := (PjP (O := O) (wt := wt) j).map (mkA 𝔓).toLinearMap

def mA : Ideal (AT 𝔓) := Ideal.map (mkA 𝔓) (RingHom.ker (cc (O := O) (wt := wt)))

def Wj (j : ℤ) : Submodule O (mA 𝔓).Cotangent :=
  Submodule.span O {c | ∃ g : mA 𝔓, (g : AT 𝔓) ∈ Aj 𝔓 j ∧ c = (mA 𝔓).toCotangent g}

def dSet {ι : Type} (F : ι → PT O wt) : Set (mA 𝔓).Cotangent :=
  {c | ∃ i, ∃ g : mA 𝔓, (g : AT 𝔓) = mkA 𝔓 (F i) ∧ c = (mA 𝔓).toCotangent g}

def SpansRat {M : Type} [AddCommGroup M] [Module O M] (s : Set M) (W : Submodule O M) : Prop :=
  Submodule.span O s ≤ W ∧ ∀ w ∈ W, ∃ c : O, c ≠ 0 ∧ c • w ∈ Submodule.span O s

def LinIndepRat {ι : Type} [Fintype ι] (F : ι → PT O wt) : Prop :=
  ∀ (g : ι → mA 𝔓), (∀ i, (g i : AT 𝔓) = mkA 𝔓 (F i)) →
    ∀ c : ι → O, (∃ t : O, t ≠ 0 ∧ t • ∑ i, c i • (mA 𝔓).toCotangent (g i) = 0) → ∀ i, c i = 0

abbrev Tors : Submodule O (mA 𝔓).Cotangent := Submodule.torsion O (mA 𝔓).Cotangent

def PiLat : Submodule O ((mA 𝔓).Cotangent ⧸ Tors 𝔓) :=
  Submodule.span O {q | ∃ g : mA 𝔓, (g : AT 𝔓) ∈ Aj 𝔓 (-1) ∧ q = (Tors 𝔓).mkQ ((mA 𝔓).toCotangent g)}

def spanF {ι : Type} (F : ι → PT O wt) : Submodule O ((mA 𝔓).Cotangent ⧸ Tors 𝔓) :=
  Submodule.span O {q | ∃ i, ∃ g : mA 𝔓, (g : AT 𝔓) = mkA 𝔓 (F i) ∧
    q = (Tors 𝔓).mkQ ((mA 𝔓).toCotangent g)}

def VPrime {ι : Type} (F : ι → PT O wt) : ℕ∞ :=
  Module.length O (↥(PiLat 𝔓) ⧸ (spanF 𝔓 F).comap (PiLat 𝔓).subtype)

variable {r s r' s' m : ℕ}
  (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
  (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt)

def IS : Ideal (PT O wt) :=
  𝔓 ⊔ Ideal.span (Set.range F ∪ Set.range G ∪ Set.range E1 ∪ Set.range E2 ∪ Set.range Z)

abbrev ST : Type := PT O wt ⧸ IS 𝔓 F G E1 E2 Z

def mkS : PT O wt →ₐ[O] ST 𝔓 F G E1 E2 Z := Ideal.Quotient.mkₐ O _

def Sj (j : ℤ) : Submodule O (ST 𝔓 F G E1 E2 Z) :=
  (PjP (O := O) (wt := wt) j).map (mkS 𝔓 F G E1 E2 Z).toLinearMap

end Graded

section Points

variable {O : Type} [CommRing O] [IsDomain O] {a : ℕ} {wt : Fin a → ℤ}

abbrev Ebar (O : Type) [CommRing O] [IsDomain O] : Type := AlgebraicClosure (FractionRing O)

variable {R : Type} [CommRing R] [Algebra O R] (mk : PT O wt →ₐ[O] R)

def Fixed (ξ : R →ₐ[O] Ebar O) : Prop :=
  ∀ (t : (Ebar O)ˣ) (j : ℤ) (f : PT O wt), IsHom j f → ξ (mk f) = (t : Ebar O) ^ j * ξ (mk f)

def SameOrbit (ξ ξ' : R →ₐ[O] Ebar O) : Prop :=
  ∃ t : (Ebar O)ˣ, ∀ (j : ℤ) (f : PT O wt), IsHom j f → ξ' (mk f) = (t : Ebar O) ^ j * ξ (mk f)

def IsNotBasePoint (ξ : R →ₐ[O] Ebar O) : Prop :=
  ∃ f : PT O wt, ξ (mk f) ≠ algebraMap O (Ebar O) (cc f)

def NegZero (ξ : R →ₐ[O] Ebar O) : Prop := ∀ v, wt v < 0 → ξ (mk (Xv v)) = 0

def PosZero (ξ : R →ₐ[O] Ebar O) : Prop := ∀ v, 0 < wt v → ξ (mk (Xv v)) = 0

def NegNZ (ξ : R →ₐ[O] Ebar O) : Prop := ∃ v, wt v < 0 ∧ ξ (mk (Xv v)) ≠ 0

def PosNZ (ξ : R →ₐ[O] Ebar O) : Prop := ∃ v, 0 < wt v ∧ ξ (mk (Xv v)) ≠ 0

def SameD (ξ ξ₁ : R →ₐ[O] Ebar O) : Prop := ∀ v, wt v = 0 → ξ (mk (Xv v)) = ξ₁ (mk (Xv v))

def Both (ξ : R →ₐ[O] Ebar O) : Prop := NegNZ mk ξ ∧ PosNZ mk ξ

def xiE (ξ : R →ₐ[O] Ebar O) : TensorProduct O (Ebar O) R →ₐ[Ebar O] Ebar O :=
  Algebra.TensorProduct.lift (AlgHom.id (Ebar O) (Ebar O)) ξ (fun _ _ => Commute.all _ _)

variable [IsDiscreteValuationRing O]

def vE (x : Ebar O) : ℚ :=
  (((IsDiscreteValuationRing.addVal O) ((minpoly O x).coeff 0)).toNat : ℚ) /
    ((minpoly O x).natDegree : ℚ)

end Points

section Hyp

variable {O : Type} [CommRing O] [IsDomain O] {a : ℕ} {wt : Fin a → ℤ}
  (𝔓 : Ideal (PT O wt)) {r s r' s' m : ℕ}
  (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
  (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt)

def DataM : Prop :=
  (∀ v, -2 ≤ wt v ∧ wt v ≤ 2) ∧
  (∀ f ∈ 𝔓, ∀ j, ∃ g ∈ 𝔓, (g : MvPowerSeries (Fin a) O) = comp (wt := wt) j f) ∧
  𝔓.IsPrime ∧ Module.Flat O (AT 𝔓) ∧
  (∀ f ∈ 𝔓, cc f = 0) ∧
  (∀ i, IsHom (-1) (F i)) ∧ (∀ i, IsHom (-2) (G i)) ∧ (∀ i, IsHom 1 (E1 i)) ∧
  (∀ i, IsHom 2 (E2 i)) ∧ (∀ i, IsHom 0 (Z i) ∧ cc (Z i) = 0)

def M1 (rp sp l : ℕ) : Prop :=
  (∃ _ : (Ideal.map (algebraMap (AT 𝔓) (Localization.Away (algebraMap O (AT 𝔓) (l : O))))
      (mA 𝔓)).IsPrime,
    IsRegularLocalRing (Localization.AtPrime (Ideal.map (algebraMap (AT 𝔓)
      (Localization.Away (algebraMap O (AT 𝔓) (l : O)))) (mA 𝔓)))) ∧
  1 ≤ r ∧
  Module.finrank O (Wj 𝔓 (-1)) = r ∧ Module.finrank O (Wj 𝔓 (-2)) = s ∧
  Module.finrank O (Wj 𝔓 1) = rp + 1 ∧ Module.finrank O (Wj 𝔓 2) = sp + 1 ∧
  Module.finrank O (Wj 𝔓 0) = m ∧
  SpansRat (dSet 𝔓 F) (Wj 𝔓 (-1)) ∧
  SpansRat (dSet 𝔓 G) (Wj 𝔓 (-2)) ∧ LinIndepRat 𝔓 G ∧
  SpansRat (dSet 𝔓 Z) (Wj 𝔓 0) ∧ LinIndepRat 𝔓 Z

def M2 : Prop := Module.Finite O (Sj 𝔓 F G E1 E2 Z 0)

def M3 : Prop :=
  ∀ x₁ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Fixed (mkS 𝔓 F G E1 E2 Z) x₁ →
    IsNotBasePoint (mkS 𝔓 F G E1 E2 Z) x₁ →
    (¬ ∃ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, NegZero (mkS 𝔓 F G E1 E2 Z) ξ ∧
        PosNZ (mkS 𝔓 F G E1 E2 Z) ξ ∧ SameD (mkS 𝔓 F G E1 E2 Z) ξ x₁) ∨
    (¬ ∃ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, PosZero (mkS 𝔓 F G E1 E2 Z) ξ ∧
        NegNZ (mkS 𝔓 F G E1 E2 Z) ξ ∧ SameD (mkS 𝔓 F G E1 E2 Z) ξ x₁)

def M4 : Prop :=
  ∀ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Both (mkS 𝔓 F G E1 E2 Z) ξ →
    IsRegularLocalRing
      (@Localization.AtPrime _ _ (RingHom.ker (xiE ξ).toRingHom) (RingHom.ker_isPrime _)) ∧
    ringKrullDim
      (@Localization.AtPrime _ _ (RingHom.ker (xiE ξ).toRingHom) (RingHom.ker_isPrime _)) = 1

def M5 (a₀ : PT O wt) : Prop :=
  IsHom 0 a₀ ∧ cc a₀ = 0 ∧
  ∀ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Both (mkS 𝔓 F G E1 E2 Z) ξ →
    ξ (mkS 𝔓 F G E1 E2 Z a₀) ≠ 0

def IsDerS {M : Type} [AddCommGroup M] [Module O M] (D : ST 𝔓 F G E1 E2 Z →ₗ[O] M) : Prop :=
  ∀ f g : PT O wt, D (mkS 𝔓 F G E1 E2 Z (f * g)) =
    cc f • D (mkS 𝔓 F G E1 E2 Z g) + cc g • D (mkS 𝔓 F G E1 E2 Z f)

def IsDerA (D : AT 𝔓 →ₗ[O] O) : Prop :=
  ∀ f g : PT O wt, D (mkA 𝔓 (f * g)) = cc f * D (mkA 𝔓 g) + cc g * D (mkA 𝔓 f)

end Hyp

section Bridge

variable {O : Type} [CommRing O] {a : ℕ} (wt : Fin a → ℤ) (Jh : Ideal (MvPowerSeries (Fin a) O))

def PofJ : Ideal (PT O wt) := Jh.comap (Pring O wt).val

def toA : PT O wt →ₐ[O] Formalism.MainNotions.UnusedSlot38.Asub (W wt) Jh :=
  ((Formalism.MainNotions.UnusedSlot38.mk Jh).comp (Pring O wt).val).codRestrict _ (fun f => ⟨f, f.2, rfl⟩)

theorem toA_surj : Function.Surjective (toA wt Jh) := by
  rintro ⟨y, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem ker_toA : RingHom.ker (toA wt Jh) = PofJ wt Jh := by
  ext f
  rw [RingHom.mem_ker, Subtype.ext_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

def equivA : AT (PofJ wt Jh) ≃ₐ[O] Formalism.MainNotions.UnusedSlot38.Asub (W wt) Jh :=
  (Ideal.quotientEquivAlgOfEq O (ker_toA wt Jh).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toA_surj wt Jh))

end Bridge

def IsOl (O : Type) [CommRing O] (l : ℕ) : Prop := Formalism.MainNotions.UnusedSlot38.IsCoeff O l ∧ Irreducible (l : O)

def LemmaM : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), IsOl O l →
  ∀ (a : ℕ) (wt : Fin a → ℤ) (𝔓 : Ideal (PT O wt)) (r s r' s' m : ℕ)
    (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
    (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt) (a₀ : PT O wt),
  DataM 𝔓 F G E1 E2 Z → M1 𝔓 F G Z r' s' l → M2 𝔓 F G E1 E2 Z → M3 𝔓 F G E1 E2 Z →
  M4 𝔓 F G E1 E2 Z → M5 𝔓 F G E1 E2 Z a₀ →
  ∃ T : Finset (ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O),
    (∀ τ ∈ T, Both (mkS 𝔓 F G E1 E2 Z) τ) ∧
    (∀ ξ : ST 𝔓 F G E1 E2 Z →ₐ[O] Ebar O, Both (mkS 𝔓 F G E1 E2 Z) ξ →
      ∃! τ, τ ∈ T ∧ SameOrbit (mkS 𝔓 F G E1 E2 Z) τ ξ) ∧
    ∃ V' : ℕ, VPrime 𝔓 F = V' ∧ (V' : ℚ) ≤ 2 * ∑ τ ∈ T, vE (τ (mkS 𝔓 F G E1 E2 Z a₀))

def LemmaM' : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), IsOl O l →
  ∀ (a : ℕ) (wt : Fin a → ℤ) (𝔓 : Ideal (PT O wt)) (r s r' s' m : ℕ)
    (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
    (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt),
  DataM 𝔓 F G E1 E2 Z →
  ∀ (MM : Type) [AddCommGroup MM] [Module O MM] [Finite MM] (k₀ : ℕ), 1 ≤ k₀ →
  ∀ φ : MM →+ (ST 𝔓 F G E1 E2 Z →ₗ[O] O ⧸ Ideal.span {(l : O) ^ k₀}),
    Function.Injective φ →
    (∀ x : MM, IsDerS 𝔓 F G E1 E2 Z (φ x) ∧
      (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → φ x (mkS 𝔓 F G E1 E2 Z f) = 0) ∧
      ∃ Dt : AT 𝔓 →ₗ[O] O, IsDerA 𝔓 Dt ∧
        (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → Dt (mkA 𝔓 f) = 0) ∧
        ∀ f : PT O wt, Ideal.Quotient.mk _ (Dt (mkA 𝔓 f)) = φ x (mkS 𝔓 F G E1 E2 Z f)) →
    Module.length O MM ≤ VPrime 𝔓 F

def LemmaM'fg : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), IsOl O l →
  ∀ (a : ℕ) (wt : Fin a → ℤ) (𝔓 : Ideal (PT O wt)) (r s r' s' m : ℕ)
    (F : Fin (r + 1) → PT O wt) (G : Fin s → PT O wt) (E1 : Fin r' → PT O wt)
    (E2 : Fin s' → PT O wt) (Z : Fin m → PT O wt),
  DataM 𝔓 F G E1 E2 Z →
  ∀ (MM : Type) [AddCommGroup MM] [Module O MM] [Module.Finite O MM] (k₀ : ℕ), 1 ≤ k₀ →
  ∀ φ : MM →+ (ST 𝔓 F G E1 E2 Z →ₗ[O] O ⧸ Ideal.span {(l : O) ^ k₀}),
    Function.Injective φ →
    (∀ x : MM, IsDerS 𝔓 F G E1 E2 Z (φ x) ∧
      (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → φ x (mkS 𝔓 F G E1 E2 Z f) = 0) ∧
      ∃ Dt : AT 𝔓 →ₗ[O] O, IsDerA 𝔓 Dt ∧
        (∀ j : ℤ, j ≠ -1 → ∀ f, IsHom j f → Dt (mkA 𝔓 f) = 0) ∧
        ∀ f : PT O wt, Ideal.Quotient.mk _ (Dt (mkA 𝔓 f)) = φ x (mkS 𝔓 F G E1 E2 Z f)) →
    IsFiniteLength O MM ∧ Module.length O MM ≤ VPrime 𝔓 F

set_option linter.unusedVariables false in

def adm1 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := Formalism.MainNotions.UnusedSlot38.FiniteTypeRingPart

def admitted (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := adm1 D V

set_option linter.unusedVariables false in

def Conclusion1 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := LemmaM
set_option linter.unusedVariables false in

def Conclusion2 (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := LemmaM'
set_option linter.unusedVariables false in

def LemmaMPrimeFinitelyGenerated (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := LemmaM'fg

def Conclusion₂ (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := Conclusion1 D V ∧ Conclusion2 D V

def Stmt (D : Formalism.BasicNotions.D7) (V : Formalism.BasicNotions.VData D) : Prop := admitted D V → Conclusion₂ D V

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (VF : ∀ x (i : Fm.Ix x), Formalism.BasicNotions.VData (Fm.D x i))

def OrbitValuationBound : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion₂ (Fm.D x i) (VF x i)

def AdmF : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, admitted (Fm.D x i) (VF x i)

def KudlaFamilyStatement : Prop := AdmF Fm VF → OrbitValuationBound Fm VF

end Family

end Formalism.MainNotions.GradedPowerSeriesLemmas
