import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfApply

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)

namespace UpperTheory.Gal.Wt

def ExpBasic : Prop :=
  (∀ (s t : ℤ) (f g : Circle → ℂ), f ∈ ExpLe s → g ∈ ExpLe t → (fun z => f z * g z) ∈ ExpLe (s + t)) ∧
  (∀ (s t : ℤ) (f g : Circle → ℂ), f ∈ ExpGe s → g ∈ ExpGe t → (fun z => f z * g z) ∈ ExpGe (s + t)) ∧
  (∀ s t : ℤ, s ≤ t → ExpLe s ≤ ExpLe t ∧ ExpGe t ≤ ExpGe s) ∧
  (∀ (c : ℂ) (m : ℤ), (fun z : Circle => c * (z : ℂ) ^ m) ∈ ExpLe m ∧ (fun z : Circle => c * (z : ℂ) ^ m) ∈ ExpGe m) ∧
  (∀ c : ℂ, (fun _ : Circle => c) ∈ ExpLe 0 ∧ (fun _ : Circle => c) ∈ ExpGe 0) ∧
  (∀ (s : ℤ) (f : Circle → ℂ), (f ∈ ExpLe s → (fun z => f z⁻¹) ∈ ExpGe (-s)) ∧ (f ∈ ExpGe s → (fun z => f z⁻¹) ∈ ExpLe (-s)))

def ExpDisj : Prop := ∀ (s t : ℤ) (f : Circle → ℂ), s < t → f ∈ ExpLe s → f ∈ ExpGe t → f = 0

def EvLem : Prop :=
  ∀ (M X Z : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ev : X → M →ₗ[ℂ] ℂ),
    (∀ m, (∀ x, ev x m = 0) → m = 0) → ∀ (T : Submodule ℂ (Z → ℂ)) (Φ : Z → M), (∀ x, (fun z => ev x (Φ z)) ∈ T) →
    ∀ L : M →ₗ[ℂ] ℂ, (fun z => L (Φ z)) ∈ T

def PevExp : Prop :=
  ∀ (a k : ℕ) (P : MvPolynomial (Fin a × Fin a) ℂ) (A B : GL (Fin a) ℂ),
    (fun z => pev P (A * (tor a k z * B))) ∈ ExpLe P.totalDegree ∧ (fun z => pev P (A * (tor a k z * B))) ∈ ExpGe 0

def Dom : Prop :=
  ∀ (a : ℕ) (κ : DomWeight a), ∀ f ∈ nablaSq ℂ a κ, ∀ m ∈ f.support, ∀ k : ℕ,
    (∑ i : Fin a with i.val < k, Formalism.GradedWeylDivisibility.rowDeg m i) ≤ ∑ i : Fin a with i.val < k, κ.natW i

def SqExp : Prop :=
  ∀ (a k : ℕ) (κ : DomWeight a) (w : nablaSq ℂ a κ) (L : nablaSq ℂ a κ →ₗ[ℂ] ℂ),
    (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ ExpLe (psum κ k) ∧
    (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ ExpGe (-((a * κ.detShift.natAbs : ℕ) : ℤ))

def TopUp : Prop := ∀ (a : ℕ) (κ : DomWeight a) (b : GL (Fin a) ℂ), IsUp b → sqRep ℂ a κ b (top κ) = chi κ b • top κ

def TorFacts : Prop :=
  ∀ (a k : ℕ) (z : Circle), IsUp (tor a k z) ∧ (∃ u : Matrix.unitaryGroup (Fin a) ℂ, unitaryIncl a u = tor a k z) ∧
    (∀ κ : DomWeight a, chi κ (tor a k z) = (z : ℂ) ^ psum κ k) ∧
    Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (tor a k z) = tor a k z⁻¹

def QR : Prop := ∀ (a : ℕ) (y : GL (Fin a) ℂ), ∃ (u : Matrix.unitaryGroup (Fin a) ℂ) (b : GL (Fin a) ℂ), IsUp b ∧ y = unitaryIncl a u * b

def WtBd : Prop :=
  ∀ (a k : ℕ) (κ : DomWeight a) (s : ℤ),
    (∀ A : Set (nablaSq ℂ a κ), (∃ w ∈ A, w ≠ 0) → (∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∀ w ∈ A, sqRep ℂ a κ (unitaryIncl a u) w ∈ A) →
      (∀ w ∈ A, ∀ L : nablaSq ℂ a κ →ₗ[ℂ] ℂ, (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ ExpLe s) → psum κ k ≤ s) ∧
    ∀ w : nablaSq ℂ a κ, w ≠ 0 → (∀ L : nablaSq ℂ a κ →ₗ[ℂ] ℂ, (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ ExpGe s) → s ≤ psum κ k

def WExp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (W : Wt E a), ∃ d : ℕ, ∀ (k : ℕ) (x : Circle → infU E a), IsCirc τ k x →
    ∀ (v : W.Sp) (L : W.Sp →ₗ[ℂ] ℂ), (fun z => L (W.rep (x z) v)) ∈ ExpLe d ∧ (fun z => L (W.rep (x z) v)) ∈ ExpGe (-d)

def RFinEx : Prop :=
  ∀ a : ℕ, (∀ (ν : DomWeight a) (X : GL (Fin a) ℂ), RFin fun n => delta ν (X * n)) ∧ ∀ P : MvPolynomial (Fin a × Fin a) ℂ, RFin (pev P)

def DeltaNear : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ν : DomWeight a) (h : GL (Fin a) ℂ), IntGL ι h → ‖ι.symm (delta ν h)‖ ≤ 1 ∧
    ∀ ε : ℝ, 0 ≤ ε → NearOne ι ε h → ‖ι.symm (delta ν h - 1)‖ ≤ ε

def AutCrit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C → ∀ φ : UA E a → ℂ, (∀ γ ∈ ratU E a, ∀ g, φ (γ * g) = φ g) →
    (∀ c ∈ C, ∀ g, φ (g * c) = φ g) → (∀ g, Continuous fun x : infU E a => φ (g * x)) →
    ∀ S : Submodule ℂ (UA E a → ℂ), FiniteDimensional ℂ S → (∀ x ∈ infU E a, RU E a x φ ∈ S) → IsAutFormU φ

def AutMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ ψ : UA E a → ℂ), IsAutFormU φ → IsAutFormU ψ → IsAutFormU fun g => φ g * ψ g

def NrmAut : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (C : Subgroup (UA E a)), IsLevel C → ∀ n : UA E a → GL (Fin a) ℂ, IsNrm τ C n →
    ∀ p : GL (Fin a) ℂ → ℂ, RFin p → (∀ y, IsAutFormU fun g => p (n g * y)) ∧
      ∃ S : Submodule ℂ (UA E a → ℂ), FiniteDimensional ℂ S ∧ ∀ y, (fun g => p (n g * y)) ∈ S

def FamOfA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (C : Subgroup (UA E a)), IsLevel C → ∀ n : UA E a → GL (Fin a) ℂ, IsNrm τ C n →
    ∀ (W : Wt E a) (ν : DomWeight a) (Q : Type) [Fintype Q] (f : Q → algForms W) (P : Q → MvPolynomial (Fin a × Fin a) ℂ)
      (X : Q → GL (Fin a) ℂ), (∀ y₁ y₂ v, IsAutFormU (famOf n ν f P X y₁ y₂ v)) ∧
      ∃ S : Submodule ℂ (UA E a → ℂ), FiniteDimensional ℂ S ∧ ∀ y₁ y₂ v, famOf n ν f P X y₁ y₂ v ∈ S

def FamOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (C : Subgroup (UA E a)), IsLevel C → ∀ n : UA E a → GL (Fin a) ℂ, IsNrm τ C n →
    ∀ (W : Wt E a) (Q : Type) [Fintype Q] (f : Q → algForms W), (∀ q, f q ∈ fixedBy W C) →
    ∀ (P : Q → MvPolynomial (Fin a × Fin a) ℂ), ∃ d : ℕ, ∀ (ν : DomWeight a) (X : Q → GL (Fin a) ℂ), Fam τ W C ν d (famOf n ν f P X)

def SumRep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (S : Submodule ℂ (UA E a → ℂ)), FiniteDimensional ℂ S → (∀ φ ∈ S, IsAutFormU φ) →
    ∃ t : Finset (Submodule ℂ (UA E a → ℂ)), (∀ U ∈ t, IsAutRepU U) ∧ sSupIndep (t : Set (Submodule ℂ (UA E a → ℂ))) ∧
      S ≤ sSup (t : Set (Submodule ℂ (UA E a → ℂ)))

def FamProj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (W : Wt E a) (K : Subgroup (UA E a)) (ν : DomWeight a) (d : ℕ) (B : GL (Fin a) ℂ → GL (Fin a) ℂ → W.Sp →ₗ[ℂ] (UA E a → ℂ)), Fam τ W K ν d B →
    ∃ (t : Finset (Submodule ℂ (UA E a → ℂ))) (F : Submodule ℂ (UA E a → ℂ) → GL (Fin a) ℂ → GL (Fin a) ℂ → W.Sp →ₗ[ℂ] (UA E a → ℂ)),
      (∀ U ∈ t, IsAutRepU U ∧ Fam τ W K ν d (F U) ∧ ∀ y₁ y₂ v, F U y₁ y₂ v ∈ U) ∧ ∀ y₁ y₂ v, ∑ U ∈ t, F U y₁ y₂ v = B y₁ y₂ v

def FamOff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (W : Wt E a) (K : Subgroup (UA E a)) (ν : DomWeight a) (d : ℕ) (B : GL (Fin a) ℂ → GL (Fin a) ℂ → W.Sp →ₗ[ℂ] (UA E a → ℂ)), Fam τ W K ν d B →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ y₁ y₂ v, B y₁ y₂ v ∈ U) → (∃ y₁ y₂ v, B y₁ y₂ v ≠ 0) →
    ∀ τ' : E →+* ℂ, InfinitePlace.mk τ' ≠ InfinitePlace.mk τ → HasWeightAt U τ' (W.at τ')

def EmbProj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ κ : DomWeight a, HasWeightAt U τ κ →
    ∀ u ∈ U, u ≠ 0 → ∃ p : (UA E a → ℂ) →ₗ[ℂ] nablaSq ℂ a κ, p u ≠ 0 ∧
      ∀ x ∈ embU a τ, ∀ y ∈ U, p (RU E a x y) = sqRep ℂ a κ (cEmb τ x) (p y)

def FamSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (W : Wt E a) (K : Subgroup (UA E a)) (ν : DomWeight a) (d : ℕ) (B : GL (Fin a) ℂ → GL (Fin a) ℂ → W.Sp →ₗ[ℂ] (UA E a → ℂ)), Fam τ W K ν d B →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ y₁ y₂ v, B y₁ y₂ v ∈ U) → (∃ y₁ y₂ v, B y₁ y₂ v ≠ 0) →
    ∀ κ : DomWeight a, HasWeightAt U τ κ → ∀ k : ℕ, psum κ k ≤ psum ν k + d ∧ psum ν k - d ≤ psum κ k

def FamWt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (τ : E →+* ℂ) (W : Wt E a) (K : Subgroup (UA E a)) (ν : DomWeight a) (d : ℕ) (B : GL (Fin a) ℂ → GL (Fin a) ℂ → W.Sp →ₗ[ℂ] (UA E a → ℂ)), Fam τ W K ν d B →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ y₁ y₂ v, B y₁ y₂ v ∈ U) → (∃ y₁ y₂ v, B y₁ y₂ v ≠ 0) →
    ∃ mu : (E →+* ℂ) → DomWeight a, OfType mu K U ∧ (∀ τ', InfinitePlace.mk τ' ≠ InfinitePlace.mk τ → mu τ' = W.at τ') ∧
      ∀ i, |(mu τ).w i - ν.w i| ≤ ((2 * d : ℕ) : ℤ)

def NeatLev : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ∀ a : ℕ, 1 ≤ a → ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (v' : HeightOneSpectrum (𝓞 E)), IsSplitAt v' → Apart v' w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → (∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' a → x ∈ K) →
    ∀ (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))), IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) →
    ∀ (W : Wt E a) (f : algForms W), f ∈ UpperTheory.Gal.Gen.fixedBy W (K ⊓ Kv.comap (cLoc v')) →
    ∃ C : Subgroup (UA E a), IsLevel C ∧ K ≤ C ∧
      (∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c ∈ C, ∀ x ∈ infU E a, γ * g = g * c * x → c = 1) ∧
      (∀ c ∈ C, cLoc v' c ∈ GlobalTheory.LFun.KGL v' a) ∧ f ∈ fixedBy W (C ⊓ Kv.comap (cLoc v'))

def EllC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), C ≤ finU E a →
    (∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c ∈ C, ∀ x ∈ infU E a, γ * g = g * c * x → c = 1) → ∃ ℓ : UA E a → C, IsEll C ℓ

def Twist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C → ∀ ℓ : UA E a → C, IsEll C ℓ → ∀ (W : Wt E a) (f : algForms W) (c : C),
    ∃ F ∈ fixedBy W C, ∀ v g, F.1 v g = f.1 v (g * ((ℓ g)⁻¹ * c : C))

def TwistBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (C : Subgroup (UA E a)), IsLevel C → ∀ ℓ : UA E a → C, IsEll C ℓ → ∀ (W : Wt E a) (f : algForms W)
    (X : Type) (b : UA E a → X → W.Sp), (∀ F : algForms W, ∃ R : ℝ, ∀ g i, ‖ι.symm (F.1 (b g i) g)‖ ≤ R) →
    ∃ R : ℝ, 0 < R ∧ ∀ (c : C) g i, ‖ι.symm (f.1 (b g i) (g * ((ℓ g)⁻¹ * c : C)))‖ ≤ R

def Kap0 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (v' : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ), GlobalTheory.CongL.OverPl ι τ v' →
    ∃ κ : UA E a →* GL (Fin a) ℂ, (∀ γ ∈ ratU E a, κ γ = cEmb τ γ) ∧ (∀ x ∈ infU E a, κ x = 1) ∧ (∀ g, κ g = 1 ↔ cLoc v' g = 1) ∧
      (∀ i j, Continuous fun g => ι.symm ((κ g : Matrix (Fin a) (Fin a) ℂ) i j)) ∧
      ∀ g, cLoc v' g ∈ GlobalTheory.LFun.KGL v' a → IntGL ι (κ g)

def Kapl : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (Y : Set k), IsCompact Y → ∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 1 →
    ∃ p : Polynomial k, (∀ x ∈ Y, ‖p.eval x‖ ≤ 1) ∧ (∀ x ∈ Y, δ ≤ ‖x‖ → ‖p.eval x‖ ≤ ε) ∧ ∀ x, ‖x‖ ≤ δ * ε → ‖p.eval x - 1‖ ≤ ε

def KaplFin : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (s : Finset k) (δ ε : ℝ), 0 < δ → 0 < ε → ε ≤ 1 → (∀ c ∈ s, δ ≤ ‖c‖) →
    ∃ p : Polynomial k, (∀ x, ‖x‖ ≤ δ → ‖p.eval x‖ ≤ 1) ∧ (∀ c ∈ s, ∀ x, ‖x - c‖ ≤ ‖c‖ / 2 → ‖p.eval x‖ ≤ ε) ∧
      ∀ x, ‖x‖ ≤ δ * ε → ‖p.eval x - 1‖ ≤ ε

def SepPoly : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (σ : Type) [Fintype σ] (Z₁ Z₂ : Set (σ → k)), IsCompact Z₁ → IsCompact Z₂ →
    Disjoint Z₁ Z₂ → ∀ ε : ℝ, 0 < ε → ∃ P : MvPolynomial σ k, (∀ z ∈ Z₁, ‖MvPolynomial.eval z P - 1‖ ≤ ε) ∧
      ∀ z ∈ Z₂, ‖MvPolynomial.eval z P‖ ≤ ε

def NearSub : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (φ : Γ →* GL (Fin a) ℂ),
    (∀ i j, Continuous fun g => ι.symm ((φ g : Matrix (Fin a) (Fin a) ℂ) i j)) → (∀ g, IntGL ι (φ g)) → ∀ ε : ℝ, 0 < ε →
    ∃ H : Subgroup Γ, IsOpen (H : Set Γ) ∧ ∀ g, g ∈ H ↔ NearOne ι ε (φ g)

def Pieces : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (φ : Γ →* GL (Fin a) ℂ),
    (∀ i j, Continuous fun g => ι.symm ((φ g : Matrix (Fin a) (Fin a) ℂ) i j)) → (∀ g, IntGL ι (φ g)) →
    ∀ Γ' : Subgroup Γ, IsOpen (Γ' : Set Γ) → φ.ker ≤ Γ' → ∀ ε : ℝ, 0 < ε →
    ∃ (Q : Type) (_ : Fintype Q) (c : Q → Γ) (P : Q → MvPolynomial (Fin a × Fin a) ℂ), ∀ g, ∃ q₀, (c q₀)⁻¹ * g ∈ Γ' ∧
      NearOne ι ε (φ ((c q₀)⁻¹ * g)) ∧ ‖ι.symm (pev (P q₀) (φ g) - 1)‖ ≤ ε ∧ ∀ q, q ≠ q₀ → ‖ι.symm (pev (P q) (φ g))‖ ≤ ε

def FamEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (v' : HeightOneSpectrum (𝓞 E)), IsSplitAt v' → Apart v' w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → (∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' a → x ∈ K) →
    ∀ (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))), IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) →
    ∀ (W : Wt E a) (f : algForms W), f ∈ UpperTheory.Gal.Gen.fixedBy W (K ⊓ Kv.comap (cLoc v')) →
    ∀ τ : E →+* ℂ, GlobalTheory.CongL.OverPl ι τ v' → ∀ (X : Type) (b : UA E a → X → W.Sp),
    (∀ F : algForms W, ∃ R : ℝ, ∀ g i, ‖ι.symm (F.1 (b g i) g)‖ ≤ R) → ∀ ε : ℝ, 0 < ε →
    ∃ (d : ℕ) (M : UA E a → GL (Fin a) ℂ), (∀ g, ∀ h ∈ finU E a, cLoc v' h = 1 → M (g * h) = M g) ∧
      ∀ ν : DomWeight a, ∃ B : GL (Fin a) ℂ → GL (Fin a) ℂ → W.Sp →ₗ[ℂ] (UA E a → ℂ), Fam τ W K ν d B ∧
        ∀ g i, ‖ι.symm (f.1 (b g i) g - B (M g) (M g) (b g i) g)‖ ≤ ε

end UpperTheory.Gal.Wt

end
