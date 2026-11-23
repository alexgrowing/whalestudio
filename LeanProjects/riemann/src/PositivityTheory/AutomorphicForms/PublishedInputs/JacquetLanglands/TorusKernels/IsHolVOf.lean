import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

variable {F : Type} [Field F] [NumberField F]

def jF (F : Type) [Field F] [NumberField F] : GL (Fin 2) F →* GF F := Matrix.GeneralLinearGroup.map (algebraMap F (Af F))

def nF (s : Fin 2 → F) (x : GF F) : ℝ :=
  ∏ᶠ w : Pl F, max ‖pLoc F w (((fun i => algebraMap F (Af F) (s i)) ᵥ* x.val) 0)‖ ‖pLoc F w (((fun i => algebraMap F (Af F) (s i)) ᵥ* x.val) 1)‖

theorem jF_center {γ : GL (Fin 2) F} (h : γ ∈ Subgroup.center (GL (Fin 2) F)) : ∃ z, jF F γ = zc F z := by
  obtain ⟨h1, h2, h3⟩ := center_entries h
  have h0 : γ 0 0 ≠ 0 := fun e => γ.det_ne_zero (by rw [Matrix.det_fin_two, e, h1]; simp)
  refine ⟨ratU F (Units.mk0 _ h0), Units.ext (Matrix.ext fun i j => ?_)⟩
  change algebraMap F (Af F) (γ i j) = Matrix.scalar (Fin 2) (algebraMap F (Af F) (γ 0 0)) i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, ← h3]

theorem zc_center (z : (Af F)ˣ) : zc F z ∈ Subgroup.center (GF F) :=
  Subgroup.mem_center_iff.2 fun g => Units.ext (Matrix.scalar_commute (n := Fin 2) (z : Af F) (fun _ => Commute.all _ _) g.val).symm.eq

variable [IsTotallyReal F]

def mkDat (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) : Dat F (InfinitePlace F) (GF F) where
  σ v := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)
  j := jF F
  H := Hc c
  χ := χ
  hf s x := absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2
  cenH γ h := by
    obtain ⟨z, hz⟩ := jF_center h
    rw [hz]
    exact Subgroup.mem_sup_right ⟨z, rfl⟩
  cenC γ h := by
    obtain ⟨z, hz⟩ := jF_center h
    rw [hz]
    exact zc_center z

def IsChi (c : Pl F → ℕ) (ω : HChar F) (χ : Hc c →* ℂˣ) : Prop :=
  ∀ h : Hc c, (∃ k ∈ Kc c, ∃ z, (h : GF F) = k * zc F z) ∧ ∀ k ∈ Kc c, ∀ z, (h : GF F) = k * zc F z → χ h = ω.1 (finId F z)

structure IsHolV (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2) : Prop where
  aut : TR.IsAutForm φ
  level : ∀ w, φ ∈ Hi.fixd (locSm F w) (K1 w (c w))
  cent : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g
  wt : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ
  low : ∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)

theorem isHolV_of {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} {φ : TR.Sm F 2} (h : IsHol k c ω φ) : IsHolV (fun _ => k) c ω φ :=
  ⟨h.aut, h.level, h.cent, h.wt, h.low⟩

def gv (v : InfinitePlace F) : GL (Fin 2) (TR.Rinf F) →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v)

def Rel (k : InfinitePlace F → ℕ) (f : X (InfinitePlace F) × GF F → ℂ) (φ : GA F 2 → ℂ) : Prop :=
  ∀ (g : GL (Fin 2) (TR.Rinf F)) (x : GF F), φ (TR.infGL F 2 g * finGL F 2 x) * ∏ v, j1 (k v) (gv v g) iP = f (fun v => gv v g • iP, x)

def Sgn (k : InfinitePlace F → ℕ) (ω : HChar F) : Prop := ∀ v, ((ω.locInf v (-1) : ℂˣ) : ℂ) = (-1) ^ k v

structure IsReps (c : Pl F → ℕ) (W : List (Pl F)) {ι : Type} [Fintype ι] (a : ι → GF F) : Prop where
  act : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V), ∀ x ∈ Hi.fixd ρ (Kc c),
    ∑ i, ρ (a i) x ∈ Hi.fixd ρ (Kc c) ∧ ∑ i, ρ (a i) x = (W.map fun w => Uop w (ρ.comp (locGL F 2 w)) (c w)).prod x
  det : ∀ i, absF (Matrix.GeneralLinearGroup.det (a i)) = (W.map fun w => (normV w : ℝ)⁻¹).prod
  loc : ∀ i w, c w ≠ 0 → ∃ u : w.adicCompletionIntegers F, Matrix.GeneralLinearGroup.map (pLoc F w) (a i) =
    aff (atFin w (unif w) ^ (open Classical in W.count w)) (u : w.adicCompletion F)

def AllA (p : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Dat F (InfinitePlace F) (GF F) → Prop) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ χ : Hc c →* ℂˣ, p F (mkDat c χ)

def DCount : Prop := AllA fun F _ _ _ D => Countable D.Om ∧ ∀ a : GF F, {ω : GF F ⧸ D.H | ∃ h ∈ D.H, ω = ((h * a : GF F) : GF F ⧸ D.H)}.Finite

def DHt : Prop := AllA fun F _ _ _ D => (∀ s, s ≠ 0 → ∀ x, 0 < D.hf s x) ∧
  (∀ s, s ≠ 0 → ∀ γ x, D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x) ∧
  (∀ s, s ≠ 0 → ∀ a : F, a ≠ 0 → ∀ x, D.hf (a • s) x = D.hf s x * ∏ v, D.σ v a ^ 2)

def DMul : Prop := AllA fun _ _ _ _ D => (∀ s, s ≠ 0 → ∀ x, ∀ h ∈ D.H, D.hf s (x * h) = D.hf s x) ∧
  ∀ a, ∃ C, ∀ s, s ≠ 0 → ∀ x, D.hf s (x * a) ≤ C * D.hf s x

def DProd : Prop := AllA fun F _ _ _ D =>
  ∀ s s' : Fin 2 → F, s 0 * s' 1 - s 1 * s' 0 ≠ 0 → ∀ x, D.hf s x * D.hf s' x ≤ ∏ v, D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2

def DMink : Prop := AllA fun _ _ _ _ D => ∃ c₀, 0 < c₀ ∧ ∀ z x, ∃ s, s ≠ 0 ∧ c₀ ≤ D.Ht s z x

def DNormal : Prop := AllA fun F _ _ _ D => ∀ c₀, 0 < c₀ → ∃ (S : Finset (GF F)) (C c : ℝ), 0 < c ∧ ∀ z x, c₀ ≤ D.Ht ![0, 1] z x →
  ∃ b : GL (Fin 2) F, b 1 0 = 0 ∧ (∃ x' ∈ S, ∃ h ∈ D.H, D.j b * x = x' * h) ∧ Sg C c (D.act b z)

def DScale : Prop := AllA fun F _ _ _ D => ∀ ω : D.Om, ∃ (N : ℕ) (C : ℝ), N ≠ 0 ∧ 0 < C ∧ ∀ γ : PG F, γ • ω = ω →
  ∃ g : GL (Fin 2) F, (g : PG F) = γ ∧ (∀ i j, IsIntegral ℤ ((N : F) * g i j)) ∧ ∀ v, C⁻¹ ≤ |D.σ v g.val.det| ∧ |D.σ v g.val.det| ≤ C

def DBox : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
  {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R}.Finite ∧
    ({t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R}.ncard : ℝ) ≤ C * (1 + R ^ Fintype.card (InfinitePlace F))

def DEntry : Prop := ∀ δ C c : ℝ, 0 < δ → 0 < c → ∃ B : ℝ, ∀ (g : GL (Fin 2) ℝ) (z : P), |z.1.re| ≤ C → c ≤ |z.1.im| → |g.val.det| ≤ C →
  δ ≤ kap z (g • z) → |g 1 0| ≤ B ∧ |g 0 0| ≤ B ∧ |g 1 1| ≤ B ∧ |g 0 1| ≤ B * |z.1.im|

def DCnt : Prop := AllA fun F _ _ _ D => ∀ (ω : D.Om) (δ C c : ℝ), 0 < δ → 0 < c → ∃ C' : ℝ, ∀ z : D.Xs, Sg C c z →
  {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)}.Finite ∧
    ({γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)}.ncard : ℝ) ≤ C' * (1 + ∏ v, |(z v).1.im|)

def DTwo : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ) (χ : Hc c →* ℂˣ), (∃ u, c u ≠ 0 ∧ normV u = 2) →
  ∀ (ω : (mkDat c χ).Om) (S : Subgroup (PG F)), S ≤ MulAction.stabilizer (PG F) ω → Finite S → ∃ n, Nat.card S = 2 ^ n

def DReps : Prop := ∀ (F : Type) [Field F] [NumberField F] (c : Pl F → ℕ) (W : List (Pl F)), ∃ (n : ℕ) (a : Fin n → GF F), IsReps c W a

def DGood : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ) (ω : HChar F) (χ : Hc c →* ℂˣ), IsChi c ω χ →
  ∀ (W : List (Pl F)) (n : ℕ) (a : Fin n → GF F), IsReps c W a → (mkDat c χ).Good a ∧ ((∃ w ∈ W, c w ≠ 0) → (mkDat c χ).Reg a)

open Classical in

def nz {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (k₀ : ℕ) (t : InfinitePlace F → ℕ) (w : Pl F) : ℂ :=
  (((normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1) : ℝ) : ℂ) * ∏ v, if D.pl v = w then (l : ℂ) ^ t v else 1

def GCh : Prop := ∀ (ν : Valuation ℂ ℝ≥0) (τ δ : ℂ), ν τ ≤ 1 → ν δ ≤ 1 → ∀ n, ν (ch τ δ (n + 1)) ≤ 1 ∧ ν (ch τ δ (n + 1) - τ ^ n) ≤ ν δ

def GUnit : Prop := ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (v : InfinitePlace F)
  (x : (D.pl v).adicCompletion F), Valued.v x = 1 → ∀ N t : ℕ, (l - 1) * l ^ N ∣ t → nu ι (D.em v x ^ t - 1) ≤ nu ι l ^ N

def GMod : Prop := ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (z : (Af F)ˣ),
  0 < absF z ∧ nu ι ((absF z : ℂ) * ∏ v, D.ea v (z : Af F)) = 1

open Classical in

def GTerm : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι)
  (c : Pl F → ℕ) (χ : Hc c →* ℂˣ), (∀ v, c (D.pl v) = 1) → ∀ k₀ : ℕ, 2 ≤ k₀ → ∀ (N : ℕ) (t : InfinitePlace F → ℕ), (∀ v, (l - 1) * l ^ N ∣ t v) →
  ∀ (W : List (Pl F)) (r : ℕ), 1 ≤ r → (∀ v, r ≤ W.count (D.pl v)) → ∀ (n : ℕ) (a : Fin n → GF F), IsReps c W a →
  ∀ (γ : GL (Fin 2) F) (x : GF F) (i : Fin n), (mkDat c χ).TotEll γ → x⁻¹ * (jF F γ)⁻¹ * x * a i ∈ Hc c →
    nu ι ((W.map (nz D k₀ 0)).prod * (mkDat c χ).orb (fun _ => k₀) γ) ≤ 1 ∧
    nu ι ((W.map (nz D k₀ t)).prod * (mkDat c χ).orb (fun v => k₀ + 2 * t v) γ) ≤ 1 ∧
    nu ι ((W.map (nz D k₀ 0)).prod * (mkDat c χ).orb (fun _ => k₀) γ - (W.map (nz D k₀ t)).prod * (mkDat c χ).orb (fun v => k₀ + 2 * t v) γ) ≤
      max (nu ι l ^ N) (nu ι l ^ r)

def H0 : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2),
  IsHolV k c ω φ → φ ≠ 0 → Sgn k ω ∧ φ ∈ Hi.fixd (TR.finRep F 2) (Kc c) ∧ ∃ χ, IsChi c ω χ

def H0b : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
  (χ : Hc c →* ℂˣ), IsOfFinOrder ω → IsChi c ω χ → (∃ m, 0 < m ∧ ∀ h, χ h ^ m = 1) ∧ (Sgn k ω → (mkDat c χ).Compat k ∧
    ∀ u : (TR.Rinf F)ˣ, ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (u.val v) : ℝ) : ℂ) ^ k v)

def HRel : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ),
  (∀ f : X (InfinitePlace F) × GF F → ℂ, ∃ φ, Rel k f φ) ∧ (∀ f φ φ', Rel k f φ → Rel k f φ' → φ = φ') ∧ (∀ f f' φ, Rel k f φ → Rel k f' φ → f = f') ∧
  (∀ f f' φ φ' (s : ℂ), Rel k f φ → Rel k f' φ' → Rel k (f + s • f') (φ + s • φ')) ∧ Rel k 0 0 ∧
  ∀ (n : ℕ) (a : Fin n → GF F) f (φ : TR.Sm F 2), Rel k f φ.1 → Rel k (Dat.Op a f) (∑ i, TR.finRep F 2 (a i) φ).1

def H1a : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2),
  IsOfFinOrder ω → IsHolV k c ω φ → ∃ f, Rel k f φ.1

def H1b : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2),
  IsOfFinOrder ω → IsHolV k c ω φ → ∀ f, Rel k f φ.1 → ∀ x, SepHol fun z => f (z, x)

def H1c : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2),
  IsOfFinOrder ω → IsHolV k c ω φ → TR.IsCuspForm φ → ∃ C, ∀ g, ‖φ.1 g‖ ≤ C

def H1 : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
  (χ : Hc c →* ℂˣ), IsOfFinOrder ω → IsChi c ω χ → ∀ φ : TR.Sm F 2, IsHolV k c ω φ → TR.IsCuspForm φ → ∃ f, (mkDat c χ).IsForm k f ∧ Rel k f φ.1

def AllF (p : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (InfinitePlace F → ℕ) → (Pl F → ℕ) → HChar F → (GA F 2 → ℂ) → Prop) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ (ω : HChar F)
    (χ : Hc c →* ℂˣ), IsOfFinOrder ω → IsChi c ω χ → Sgn k ω → (∀ v, 1 ≤ k v) → ∀ f φ, (mkDat c χ).IsForm k f → Rel k f φ → p F k c ω φ

def H2a : Prop := AllF fun F _ _ _ _ c ω φ => (∀ γ g, φ (ratGL F 2 γ * g) = φ g) ∧ (∀ u ∈ Kc c, ∀ g, φ (g * finGL F 2 u) = φ g) ∧
  (∀ (z : Ideles F) g, φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g) ∧ ∃ C, ∀ g, ‖φ g‖ ≤ C

def H2b : Prop := AllF fun F _ _ _ _ _ _ φ => φ ∈ TR.Sm F 2

def H2c : Prop := AllF fun F _ _ _ k _ _ φ => ∀ h : φ ∈ TR.Sm F 2, ∀ v,
  TR.Eop v 0 1 ⟨φ, h⟩ - TR.Eop v 1 0 ⟨φ, h⟩ = (Complex.I * k v) • (⟨φ, h⟩ : TR.Sm F 2) ∧
  TR.Eop v 0 0 ⟨φ, h⟩ - TR.Eop v 1 1 ⟨φ, h⟩ = Complex.I • (TR.Eop v 0 1 ⟨φ, h⟩ + TR.Eop v 1 0 (⟨φ, h⟩ : TR.Sm F 2))

def H2d : Prop := AllF fun F _ _ _ k c ω φ => ∃ h : φ ∈ TR.Sm F 2, IsHolV k c ω ⟨φ, h⟩

def H2e : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2),
  IsOfFinOrder ω → (∀ v, 1 ≤ k v) → IsHolV k c ω φ → (∃ C, ∀ g, ‖φ.1 g‖ ≤ C) → TR.IsCuspForm φ

def HCap : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
  ∀ φ : TR.Sm F 2, IsHolV k c ω φ → TR.lie F 2 (TR.oneL F 2) φ = 0 ∧
    ∀ v (u : ℂ), TR.cap v u φ = ((u + ((k v : ℂ) - 1) / 2) * (u - ((k v : ℂ) - 1) / 2)) • φ

def HFinC : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite →
  ∀ ω : HChar F, IsOfFinOrder ω → FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F 2 | IsHolV k c ω φ ∧ TR.IsCuspForm φ})

def HFin : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite →
  ∀ (ω : HChar F) (χ : Hc c →* ℂˣ), IsOfFinOrder ω → IsChi c ω χ → Sgn k ω → (∀ v, 1 ≤ k v) →
    FiniteDimensional ℂ (Submodule.span ℂ {f | (mkDat c χ).IsForm k f})

def HRep : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), 2 ≤ k → ∀ (t : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ (lam : Pl F → ℂ), IsHolV (fun v => k + 2 * t v) c ω φ → φ ≠ 0 → (∀ w, hk k w (c w) φ = lam w • φ) → TR.IsCuspForm φ →
    ∃ π : TR.CuspSub F 2, π.IsRegAlg ∧ (∃ χ : HChar F, π.Polarized χ) ∧
      (∀ v, π.HasInfChar v (infOf ![(t v : ℤ), 1 - (k : ℤ) - t v])) ∧ (∀ w, HasU w (π.locRep w) (c w) (lam w)) ∧
      ∀ w, c w = 0 → ∃ B, π.HasSat w B ∧ ((algSat 2 (normV w) B).map fun b => Polynomial.X - C b).prod =
        Polynomial.X ^ 2 - C (lam w) * Polynomial.X + C ((ω.val w : ℂˣ) * (normV w : ℂ) ^ (k - 1))

def TrCong : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (D : LDat F ι)
    (k₀ : ℕ), 4 ≤ k₀ → ∀ c : Pl F → ℕ, {w | c w ≠ 0}.Finite → (∀ v, c (D.pl v) = 1) → (∃ u, c u ≠ 0 ∧ normV u = 2) →
    ∀ (ω : HChar F) (χ : Hc c →* ℂˣ), IsOfFinOrder ω → IsChi c ω χ → Sgn (fun _ => k₀) ω →
    ∀ (N : ℕ) (t : InfinitePlace F → ℕ), (∀ v, (l - 1) * l ^ N ∣ t v) →
    ∀ (W : List (Pl F)) (r : ℕ), 1 ≤ r → (∀ v, r ≤ (open Classical in W.count (D.pl v))) → ∀ (n : ℕ) (a : Fin n → GF F), IsReps c W a →
    ∀ (h : ∀ f ∈ (mkDat c χ).M fun _ => k₀, Dat.Op a f ∈ (mkDat c χ).M fun _ => k₀)
      (h' : ∀ f ∈ (mkDat c χ).M fun v => k₀ + 2 * t v, Dat.Op a f ∈ (mkDat c χ).M fun v => k₀ + 2 * t v),
    nu ι ((W.map (nz D k₀ 0)).prod * LinearMap.trace ℂ _ ((Dat.Op a).restrict h)) ≤ 1 ∧
    nu ι ((W.map (nz D k₀ t)).prod * LinearMap.trace ℂ _ ((Dat.Op a).restrict h')) ≤ 1 ∧
    nu ι ((W.map (nz D k₀ 0)).prod * LinearMap.trace ℂ _ ((Dat.Op a).restrict h) -
      (W.map (nz D k₀ t)).prod * LinearMap.trace ℂ _ ((Dat.Op a).restrict h')) ≤ max (nu ι l ^ N) (nu ι l ^ r)

def DAx : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (c : Pl F → ℕ), {w | c w ≠ 0}.Finite →
  ∀ χ : Hc c →* ℂˣ, (∃ m, 0 < m ∧ ∀ h, χ h ^ m = 1) → (mkDat c χ).Ax

open Classical in

def HolWC : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (D : LDat F ι)
    (k₀ : ℕ), 4 ≤ k₀ → ∀ c : Pl F → ℕ, {w | c w ≠ 0}.Finite → (∀ v, c (D.pl v) = 1) → (∃ u, c u ≠ 0 ∧ normV u = 2) →
    ∀ ω : HChar F, IsOfFinOrder ω → ∀ φ lam, IsEigHol k₀ c ω φ lam → TR.IsCuspForm φ → (∀ v, nu ι (lam (D.pl v)) = 1) →
    ∀ (S : Set (InfinitePlace F)) (B : ℕ), ∃ t ≥ B, l - 1 ∣ t ∧ ∃ (φ' : TR.Sm F 2) (lam' : Pl F → ℂ),
      IsHolV (fun v => k₀ + 2 * (if v ∈ S then t else 0)) c ω φ' ∧ φ' ≠ 0 ∧ TR.IsCuspForm φ' ∧ (∀ w, hk k₀ w (c w) φ' = lam' w • φ') ∧
      ∀ w, nu ι ((∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) * lam' w - lam w) < 1

open Classical in

def PropMV : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    2 ≤ Module.finrank ℚ F → SplitL F l →
    ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ), IsOpen (ξ.ker : Set (G F Ω)) → (∀ c, IsConjEl c → ξ c = -1) →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ ξ.ker) →
    (∃ (u : Pl F) (A : ValuationSubring Ω), normV u = 2 ∧ IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ ξ.ker) →
    ∀ P : Set (Pl F),
    (∃ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    (∃ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
    ∃ k t : ℕ, 2 ≤ k ∧ 2 ≤ t ∧ l - 1 ∣ k ∧ l - 1 ∣ t ∧ ∃ c a π r,
      OrdForm ι ξ (-(k : ℤ)) c (fun w => if w ∈ P then ![(t : ℤ), -(k : ℤ) - t] else ![0, -(k : ℤ)]) a π r ∧ ResSum r ![1, ξ] ∧
      ∀ (w : Pl F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
        (w ∈ P → a w = (ξ σ⁻¹ : (Qbar l)ˣ)) ∧ (w ∉ P → a w = 1)

end UpperTheory.Esk
