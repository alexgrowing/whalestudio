import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Definitions.Divisors.GenTyL

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def FramedX {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) {J : Type} (t : J → (UA E a →₀ ℂ)) : Prop :=
  ∃ (X : Type) (b : UA E a → X → W.Sp), (∀ f : algForms W, ∃ R : ℝ, ∀ g i, ‖ι.symm (f.1 (b g i) g)‖ ≤ R) ∧
    (∀ f : algForms W, (∀ g i, f.1 (b g i) g = 0) → f = 0) ∧
    ∀ (F : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R : ℝ), (∀ g i, ‖ι.symm (F (b g i) g)‖ ≤ R) →
      ∀ j g i, ‖ι.symm (opOf (RU E a) (t j) (F (b g i)) g)‖ ≤ R

theorem Framed.framedX {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {W : Wt E a} {J : Type} {t : J → (UA E a →₀ ℂ)}
    (h : Framed ι W t) : FramedX ι W t := by
  obtain ⟨d, b, h⟩ := h
  exact ⟨Fin d, b, h⟩

def DenomLe (l d : ℕ) (g : UA E a) : Prop :=
  ∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
    IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
    IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
      Matrix (Fin a) (Fin a) (u.adicCompletion E)))

def IntW {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU E a ∧ ∃ d : ℕ, DenomLe l d g ∧ ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * wtSize lam)

theorem intW_of {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {lam : (E →+* ℂ) → DomWeight a} {w₀ : HeightOneSpectrum (𝓞 E)}
    {f : UA E a →₀ ℂ} (h : IsIntegralOpW ι lam w₀ f) : IntW ι lam f :=
  fun g hg => ⟨(h g hg).1, (h g hg).2.2⟩

def CoefLe {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type} (R : ℝ) (x : MvPolynomial σ ℂ) : Prop :=
  ∀ m, ‖ι.symm (MvPolynomial.coeff m x)‖ ≤ R

def ToPolyX : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)), K ≤ finU E a → ∀ (lam : (E →+* ℂ) → DomWeight a)
    (P : Submodule ℂ (UA E a → ℂ) → Prop), Dense ι (Wt.ofFam lam) K P → ∀ (J : Type) (t : J → (UA E a →₀ ℂ))
    (η : Submodule ℂ (UA E a → ℂ) → J → ℂ), FramedX ι (Wt.ofFam lam) t → ActsBy K t η → ∀ U, OfType lam K U →
      PolyApprox (fun j => ι.symm (η U j)) {θ | ∃ U', OfType lam K U' ∧ P U' ∧ θ = fun j => ι.symm (η U' j)}

def Kappa : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ),
    ∃ κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ), (∀ γ ∈ ratU E n, κ γ = cAll γ) ∧ (∀ x ∈ infU E n, κ x = 1) ∧
      ∀ (g : UA E n) (d : ℕ), DenomLe l d g → ∀ v i j,
        ‖ι.symm (((κ g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d ∧
        ‖ι.symm ((((κ g v)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ (l : ℝ) ^ d

def DenomBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ∀ (n : ℕ) (Z : Set (UA E n)), IsCompact Z →
    ∃ d : ℕ, ∀ g ∈ Z, DenomLe l d g

def DegLe : Prop :=
  ∀ (T : Type) [Fintype T] (n : ℕ) (lam : T → DomWeight n), ∀ x ∈ Formalism.L2.DIV.VV ℂ lam,
    x.totalDegree ≤ ∑ τ, ∑ i, (lam τ).natW i

def BlockBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (T : Type) (n : ℕ) (A : T → Matrix (Fin n) (Fin n) ℂ) (R : ℝ), 1 ≤ R →
    (∀ τ i j, ‖ι.symm (A τ i j)‖ ≤ R) → ∀ (D : ℕ) (x : MvPolynomial (T × Fin n × Fin n) ℂ), x.totalDegree ≤ D → CoefLe ι 1 x →
    CoefLe ι (R ^ D) (Formalism.GradedWeylDivisibility.blockAct ℂ A x)

def DetBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (T : Type) [Fintype T] (n : ℕ) (lam : T → DomWeight n) (A : T → GL (Fin n) ℂ) (R : ℝ),
    1 ≤ R → (∀ τ i j, ‖ι.symm (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ R ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ R) →
    ‖ι.symm (Formalism.L2.DIV.detTwK lam A)‖ ≤ R ^ (∑ τ, n * (lam τ).detShift.natAbs)

def SizeLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a),
    (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs ≤ a * wtSize W.at

def RhoBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a)
    (A : InfinitePlace E → GL (Fin a) ℂ) (R : ℝ), 1 ≤ R →
    (∀ τ i j, ‖ι.symm (((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ R ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ R) →
    ∀ x : W.Sp, CoefLe ι 1 x.1 → CoefLe ι (R ^ (a * wtSize W.at)) (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1

def LatFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (σ : Type) (V : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V],
    (∀ φ : V →ₗ[ℂ] ℂ, ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) (x : V), CoefLe ι R x.1 → ‖ι.symm (φ x)‖ ≤ M * R) ∧
    ∀ x : V, ∃ c : ℂ, c ≠ 0 ∧ CoefLe ι 1 (c • x).1

def LevelEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a) (f : algForms W),
    ∃ C : Subgroup (UA E a), IsLevel C ∧ f ∈ fixedBy W C

def FrameW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (W : Wt E a) (J : Type)
    (t : J → (UA E a →₀ ℂ)), (∀ j, IntW ι W.at (t j)) → FramedX ι W t

def ScaleW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ), (∀ g ∈ f.support, g ∈ finU E a) → ∃ c : ℂ, c ≠ 0 ∧ IntW ι lam (c • f)

def HypOf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (K : Subgroup (UA E a)), IsCompact (K : Set (UA E a)) →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w a → x ∈ K) → HypAt K w

def MaxCpt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (H : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (Z : Set (GL (Fin a) (w.adicCompletion E))), IsCompact Z → (H : Set (GL (Fin a) (w.adicCompletion E))) ⊆ Z →
    GlobalTheory.LFun.KGL w a ≤ H → H ≤ GlobalTheory.LFun.KGL w a

def PowNhds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a N : ℕ), N ≠ 0 →
    ∀ V ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), (fun x => x ^ N) '' V ∈ nhds (1 : GL (Fin a) (w.adicCompletion E))

def KerOpen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (J : Subgroup (GL (Fin a) (w.adicCompletion E))),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → ∀ (A : Type) [Group A] [Finite A] (θ : J →* A),
    ∃ N : Set (GL (Fin a) (w.adicCompletion E)), IsOpen N ∧ 1 ∈ N ∧ ∀ x : J, x.1 ∈ N → θ x = 1

def TyStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)), IsSplitAt w₀ → ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (W : Wt E a)
    (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
    ∀ (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), ∀ f ∈ fixedBy W (lev K w₀ J),
      ∃ G ∈ part W K (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ HasTypeVec w₀ K J θ χ U),
        ∃ e : UA E a → ℂ, (∀ g, ‖ι.symm (e g)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ m) ∧ ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g

def TwistPart : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a))
    (W : Wt E a) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (A : Type) [Group A] (θ : J →* A) (χ : A →* ℂˣ)
    (hC : ∀ c ∈ lev K w₀ J, cLoc w₀ c ∈ J), (∀ k ∈ K, cLoc w₀ k = 1) → ∀ F : algForms W,
    (∀ c (hc : c ∈ lev K w₀ J) v g, F.1 v (g * c) = ((χ (θ ⟨cLoc w₀ c, hC c hc⟩) : ℂˣ) : ℂ) * F.1 v g) →
    F ∈ part W K fun U => HasTypeVec w₀ K J θ χ U

def CharSum : Prop :=
  ∀ (N : ℕ) [NeZero N], ∃ (s : Finset (Multiplicative (ZMod N) →* ℂˣ)), (∀ χ ∈ s, χ ≠ 1) ∧
    ∀ x : Multiplicative (ZMod N), 1 + ∑ χ ∈ s, ((χ x : ℂˣ) : ℂ) = 0 ∨ 1 + ∑ χ ∈ s, ((χ x : ℂˣ) : ℂ) = N

def GenW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ), GenData w₀ K S Φ →
    ∀ P : Submodule ℂ (UA E a → ℂ) → Prop, Dense ι (Wt.ofFam lam) K P →
    ∀ (J : Type) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ), (∀ j, IntW ι lam (t j)) →
      ActsBy K t η → ∀ U, OfType lam K U →
        PolyApprox (fun j => ι.symm (η U j))
          {θ | ∃ U', OfType lam K U' ∧ P U' ∧ (∀ w ∈ S, GenAt w (Φ w) U') ∧ θ = fun j => ι.symm (η U' j)}

def DiscEx : Prop :=
  ∀ a : ℕ, ∃ D : MvPolynomial (Fin a) ℤ, D.IsSymmetric ∧ D.IsHomogeneous D.totalDegree ∧ D ≠ 0 ∧
    ∀ (k : Type) [Field k] (z : Fin a → k), MvPolynomial.aeval z D ≠ 0 → Function.Injective z ∧
      ∀ m : Fin a → ℕ, ∑ i, m i = a → ∏ i, z i ^ m i = ∏ i, z i → m = fun _ => 1

def DiscEx2 : Prop :=
  ∀ a n : ℕ, ∃ D : MvPolynomial (Fin a) ℤ, D.IsSymmetric ∧ D.IsHomogeneous D.totalDegree ∧ D ≠ 0 ∧
    ∀ (k : Type) [Field k] (z : Fin a → k), MvPolynomial.aeval z D ≠ 0 →
      (∀ i j, i ≠ j → ∀ c, 1 ≤ c → c ≤ n → z i ^ c ≠ z j ^ c) ∧ (∀ i j k', ¬ (i = j ∧ k' = j) → z i * z k' ≠ z j ^ 2)

end UpperTheory.Gal.Gen

end
