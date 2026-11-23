import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import GroundTheory.AutomorphicForms.FourierWhittaker
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

namespace UpperTheory.V.Af.Smo

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

def IsY (m : ℕ) (p : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i : Fin n, m ≤ i.val → p i i = 1 ∧ ∀ j, j < i → p i j = 0

def supN (p : Matrix (Fin n) (Fin n) R) : R := ∑ i, ∑ j, if i.val + 1 = j.val then p i j else 0

def colM (m : Fin n) (u : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  1 + Matrix.of fun i j => if i ≤ m ∧ j.val = m.val + 1 then u i else 0

def rowM (m : Fin n) (ξ : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = m ∧ j ≤ m then ξ j else (1 : Matrix (Fin n) (Fin n) R) i j

def dotLe (m : Fin n) (ξ u : Fin n → R) : R := ∑ j, if j ≤ m then ξ j * u j else 0

def IsWh (ψ : R → ℂ) (W : GL (Fin n) R → ℂ) : Prop :=
  ∀ ν : GL (Fin n) R, IsY 0 ν.val → ∀ g, W (ν * g) = ψ (supN ν.val) * W g

end Alg

def ColConj : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (m : Fin n), m.val + 1 < n → ∀ p : GL (Fin n) R, IsY (m.val + 1) p.val →
    ∀ u : Fin n → R, ∃ ν : GL (Fin n) R, IsY 0 ν.val ∧ supN ν.val = dotLe m (p.val m) u ∧ p.val * colM m u = ν.val * p.val

def RowStep : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (m : Fin n) (p s : GL (Fin n) R), IsY (m.val + 1) p.val → s.val = rowM m (p.val m) →
    IsY m.val (p * s⁻¹).val

def SchOfClosed : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (A : Set (X → ℂ)),
    (∀ f ∈ A, (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ Differentiable ℝ f ∧ (∀ v, (fun x => fderiv ℝ f x v) ∈ A) ∧
      ∀ l : X →L[ℝ] ℝ, (fun x => (l x : ℂ) * f x) ∈ A) →
    ∀ f ∈ A, ∃ F : 𝓢(X, ℂ), ⇑F = f

section Part

variable {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def pft (G : V × M → ℂ) (z : V × M) : ℂ := 𝓕 (fun ξ => G (ξ, z.2)) z.1

end Part

def SchTensor : Prop :=
  ∀ (V M : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup M] [NormedSpace ℝ M]
    [FiniteDimensional ℝ M] (h : V → ℂ), ContDiff ℝ ∞ h → HasCompactSupport h → ∀ α : 𝓢(M, ℂ),
    ∃ G : 𝓢(V × M, ℂ), ∀ ξ y, G (ξ, y) = h ξ * α y

def SchTw : Prop :=
  ∀ (V M : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup M] [NormedSpace ℝ M]
    [FiniteDimensional ℝ M] (A : V →L[ℝ] M →L[ℝ] M) (e : V), ∃ h : V → ℂ, h e = 1 ∧
      (∀ ξ, h ξ ≠ 0 → ∀ y, y + A (ξ - e) y = 0 → y = 0) ∧
      ∀ α : 𝓢(M, ℂ), ∃ G : 𝓢(V × M, ℂ), ∀ ξ y, G (ξ, y) = h ξ * α (y + A (ξ - e) y)

def PftDeriv : Prop :=
  ∀ (V M : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] (G : 𝓢(V × M, ℂ)),
    Differentiable ℝ (pft G) ∧ ∀ v, ∃ G' : 𝓢(V × M, ℂ), (fun z => fderiv ℝ (pft G) z v) = pft G'

def PftMul : Prop :=
  ∀ (V M : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] (G : 𝓢(V × M, ℂ)),
    (∃ C : ℝ, ∀ z, ‖pft G z‖ ≤ C) ∧
      ∀ l : V × M →L[ℝ] ℝ, ∃ G' : 𝓢(V × M, ℂ), (fun z => (l z : ℂ) * pft G z) = pft G'

def PftSch : Prop :=
  ∀ (V M : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] (G : 𝓢(V × M, ℂ)),
    ∃ K : 𝓢(V × M, ℂ), ⇑K = pft G

theorem pftSch_of (h0 : SchOfClosed) (h1 : PftDeriv) (h2 : PftMul) : PftSch := by
  intro V M _ _ _ _ _ _ _ _ G
  refine h0 (V × M) (Set.range fun G : 𝓢(V × M, ℂ) => pft G) ?_ _ ⟨G, rfl⟩
  rintro _ ⟨G, rfl⟩
  exact ⟨(h2 V M G).1, (h1 V M G).1, fun v => ((h1 V M G).2 v).imp fun _ => Eq.symm,
    fun l => ((h2 V M G).2 l).imp fun _ => Eq.symm⟩

def BetaSch : Prop :=
  ∀ (V M : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] (B : V →L[ℝ] M →L[ℝ] M),
    (∀ u x, B u (B u x) = 0) → ∀ K : 𝓢(V × M, ℂ), ∃ (K' : 𝓢(V × M, ℂ)) (β : 𝓢(M, ℂ)),
      (∀ u x, K' (u, x) = K (u, x - B u x)) ∧ ∀ x, β x = ∫ u, K' (u, x)

def BetaInt : Prop :=
  ∀ (V M : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) [μ.IsAddHaarMeasure] (B : V →L[ℝ] M →L[ℝ] M), (∀ u x, B u (B u x) = 0) →
    ∀ G K K' : 𝓢(V × M, ℂ), ⇑K = pft G → (∀ u x, K' (u, x) = K (u, x - B u x)) →
    ∀ (w : M → ℂ) (η : V), Measurable w → (∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) →
      (∀ u x, w (x + B u x) = (𝐞 ⟪η, u⟫ : ℂ) * w x) →
      ∫ x, w x * (∫ u, K' (u, x)) ∂μ = ∫ x, w x * G (η, x) ∂μ

section Glob

variable (E : Type) [Field E] [NumberField E]

def psiA : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)

def psiF : AddChar (Af E) ℂ := (psiA E).compAddMonoidHom (sFin E : Af E →+ Ad E)

variable {E} in

def psiL (w : HeightOneSpectrum (𝓞 E)) : AddChar (w.adicCompletion E) ℂ :=
  (psiF E).compAddMonoidHom (sLoc E w : w.adicCompletion E →+ Af E)

def psiR (x : Rinf E) : ℂ := (𝐞 (-∑ v, x v) : ℂ)

end Glob

def ArchStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (m : Fin n), m.val + 1 < n →
    ∃ h : (Fin n → Rinf E) → ℂ, h ((1 : Matrix (Fin n) (Fin n) (Rinf E)) m) = 1 ∧ (∀ ξ, h ξ ≠ 0 → IsUnit (rowM m ξ)) ∧
      ∀ α : 𝓢(Lie E n, ℂ), ∃ β : 𝓢(Lie E n, ℂ), ∀ (w : Lie E n → ℂ) (ξ : Fin n → Rinf E), Measurable w →
        (∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) → (∀ u x, w (lmul (toL (colM m u)) x) = psiR E (dotLe m ξ u) * w x) →
        ∫ x, w x * β x = h ξ * ∫ x, w x * α (lmul (toL (rowM m ξ)) x)

def LinChange : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∃ c : GL (Fin n) (Rinf E) → ℂ, c 1 = 1 ∧
    ∀ (s : GL (Fin n) (Rinf E)) (f : Lie E n → ℂ), ∫ x, f (lmul (toL s.val) x) = c s * ∫ x, f x

def ArchKir : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ), m < n → ∃ H : GL (Fin n) (Rinf E) → ℂ, H 1 = 1 ∧
    ∀ α : 𝓢(Lie E n, ℂ), ∃ β : 𝓢(Lie E n, ℂ), ∀ w : Lie E n → ℂ, Measurable w → (∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) →
      (∀ ν : GL (Fin n) (Rinf E), IsY 0 ν.val → ∀ x, w (lmul (toL ν.val) x) = psiR E (supN ν.val) * w x) →
      ∀ p : GL (Fin n) (Rinf E), IsY m p.val → ∫ x, w (lmul (toL p.val) x) * β x = H p * ∫ x, w x * α x

def comb {G : Type} [Group G] (c : G →₀ ℂ) (W : G → ℂ) (g : G) : ℂ := c.sum fun x z => z * W (g * x)

theorem exists_comb_comb {G : Type} [Group G] (c₁ c₀ : G →₀ ℂ) : ∃ c : G →₀ ℂ,
    (∀ x ∈ c.support, ∃ a ∈ c₁.support, ∃ b ∈ c₀.support, x = a * b) ∧
      ∀ W g, comb c W g = comb c₁ (comb c₀ W) g := by
  classical
  refine ⟨c₁.sum fun a z => c₀.sum fun b z' => Finsupp.single (a * b) (z * z'), fun x hx => ?_, fun W g => ?_⟩
  · obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
    obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
    exact ⟨a, ha, b, hb, Finset.mem_singleton.1 (Finsupp.support_single_subset hx)⟩
  · unfold comb
    rw [Finsupp.sum_sum_index (by simp) (by intros; ring)]
    refine Finsupp.sum_congr fun a _ => ?_
    rw [Finsupp.sum_sum_index (by simp) (by intros; ring), Finsupp.mul_sum]
    refine Finsupp.sum_congr fun b _ => ?_
    rw [Finsupp.sum_single_index (by simp), mul_assoc, mul_assoc]

def AvgChar : Prop :=
  ∀ (A : Type) [AddCommGroup A] (L₀ L : AddSubgroup A), L₀ ≤ L → L₀.relIndex L ≠ 0 →
    ∃ T : Finset A, T.Nonempty ∧ (∀ t ∈ T, t ∈ L) ∧ ∀ χ : AddChar A ℂ, (∀ x ∈ L₀, χ x = 1) → (∃ x ∈ L, χ x ≠ 1) →
      ∑ t ∈ T, χ t = 0

def LocDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), ψ ≠ 1 →
    ∀ V ∈ 𝓝 (0 : w.adicCompletion E), ∃ L : AddSubgroup (w.adicCompletion E),
      IsOpen (L : Set (w.adicCompletion E)) ∧ IsCompact (L : Set (w.adicCompletion E)) ∧
      ∀ x, (∀ y ∈ L, ψ (x * y) = 1) → x ∈ V

def LocStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ),
    (∀ᶠ x in 𝓝 (0 : w.adicCompletion E), ψ x = 1) → ψ ≠ 1 → ∀ (n : ℕ) (m : Fin n), m.val + 1 < n →
    ∀ U : OpenSubgroup (GL (Fin n) (w.adicCompletion E)),
    ∃ (c : GL (Fin n) (w.adicCompletion E) →₀ ℂ) (h : (Fin n → w.adicCompletion E) → ℂ),
      h ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) m) = 1 ∧ (∀ ξ, h ξ ≠ 0 → ∃ s ∈ U, s.val = rowM m ξ) ∧
      ∀ W : GL (Fin n) (w.adicCompletion E) → ℂ, (∀ g, ∀ u ∈ U, W (g * u) = W g) → ∀ p ξ,
        (∀ u (t : GL (Fin n) (w.adicCompletion E)), t.val = colM m u → W (p * t) = ψ (dotLe m ξ u) * W p) →
        comb c W p = h ξ * W p

def LocKir : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ),
    (∀ᶠ x in 𝓝 (0 : w.adicCompletion E), ψ x = 1) → ψ ≠ 1 → ∀ n m : ℕ, m < n →
    ∀ U : OpenSubgroup (GL (Fin n) (w.adicCompletion E)),
    ∃ (c : GL (Fin n) (w.adicCompletion E) →₀ ℂ) (H : GL (Fin n) (w.adicCompletion E) → ℂ), H 1 = 1 ∧
      ∀ W : GL (Fin n) (w.adicCompletion E) → ℂ, IsWh ψ W → (∀ g, ∀ u ∈ U, W (g * u) = W g) →
        ∀ p, IsY m p.val → comb c W p = H p * W 1

section Glob

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

abbrev cmp (w : HeightOneSpectrum (𝓞 E)) : GL (Fin n) (Af E) →* GL (Fin n) (w.adicCompletion E) :=
  GeneralLinearGroup.map (pLoc E w)

def SuppIn (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin n) (Af E)) : Prop := ∀ w ∉ S, cmp w k = 1

def Away (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin n) (Af E)) : Prop := ∀ w ∈ S, cmp w k = 1

def InKS (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin n) (Af E)) : Prop :=
  Away S k ∧ ∀ w, cmp w k ∈ GlobalTheory.LFun.KGL w n

theorem cmp_ext {k k' : GL (Fin n) (Af E)} (h : ∀ w, cmp w k = cmp w k') : k = k' := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  refine DFunLike.ext _ _ fun w => ?_
  exact congrArg (fun x : GL (Fin n) (w.adicCompletion E) => x i j) (h w)

def GoodAt (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ) : Prop :=
  (∀ x ∈ Formalism.UG.Ov E w, ψ x = 1) ∧ ∀ ϖ, Formalism.UG.IsUnifV E w ϖ → ∃ x, ϖ * x ∈ Formalism.UG.Ov E w ∧ ψ x ≠ 1

structure Eig (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (W : GL (Fin n) (w.adicCompletion E) → ℂ) : Prop where
  card : B.card = n
  inv : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w n, W (g * k) = W g
  eig : ∀ ϖ, Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, ∀ g,
    ∑ᶠ c : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n,
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * W (g * c.out) = GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n B j * W g

def EigAt (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (f : GA E n → ℂ) : Prop :=
  ∀ g, Eig w B fun y => f (g * finGL E n (locGL E n w y))

structure Nice (f : GA E n → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C
  left : IsLeftInvariant f
  cusp : AutomorphicForm.IsCuspidal f
  level : ∃ V : OpenSubgroup (GL (Fin n) (Af E)), ∀ g, ∀ v ∈ V, f (g * finGL E n v) = f g

def fop (c : GL (Fin n) (Af E) →₀ ℂ) (f : GA E n → ℂ) (g : GA E n) : ℂ := c.sum fun x z => z * f (g * finGL E n x)

def Orth (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure] (φ φ' : cuspForms E n) : Prop :=
  ∀ g g', ∫ q, starRingEnd ℂ (quotTr φ g q) * quotTr φ' g' q
    ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0

variable [IsTotallyReal E]

def conv (f : GA E n → ℂ) (α : Lie E n → ℂ) (g : GA E n) : ℂ := ∫ x, chart f g x * α x

def InPS (S : Finset (HeightOneSpectrum (𝓞 E))) (p : GA E n) : Prop :=
  IsY (n - 1) p.val ∧ SuppIn S (GeneralLinearGroup.map (pFin E) p)

def Cen (π : CuspSub E n) : Prop := ∀ φ ∈ π.V, TR.lie E n (oneL E n) φ = 0

def SameSat (π π' : CuspSub E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ π'.HasSat w B

end Glob

def PsiLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    (∀ w : HeightOneSpectrum (𝓞 E), (∀ᶠ x in 𝓝 (0 : w.adicCompletion E), psiL w x = 1) ∧ psiL w ≠ 1) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, GoodAt w (psiL w)

def PsiInf : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (x : Rinf E), psiA E (sInf E x) = psiR E x

def EmbY : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n m : ℕ),
    (∀ w (y : GL (Fin n) (HeightOneSpectrum.adicCompletion E w)), IsY m y.val →
      IsY m (locGL E n w y).val ∧ supN (locGL E n w y).val = sLoc E w (supN y.val)) ∧
    (∀ y : GL (Fin n) (Af E), IsY m y.val → IsY m (finGL E n y).val ∧ supN (finGL E n y).val = sFin E (supN y.val)) ∧
    (∀ y : GL (Fin n) (Rinf E), IsY m y.val → IsY m (infGL E n y).val ∧ supN (infGL E n y).val = sInf E (supN y.val)) ∧
    ∀ w, Continuous (locGL E n w)

def FinKir : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ), 1 ≤ n → ∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
    (U : OpenSubgroup (GL (Fin n) (Af E))), ∃ (c : GL (Fin n) (Af E) →₀ ℂ) (H : GL (Fin n) (Af E) → ℂ), H 1 = 1 ∧
      (∀ x ∈ c.support, SuppIn S x) ∧ ∀ W : GL (Fin n) (Af E) → ℂ,
        (∀ ν, SuppIn S ν → IsY 0 ν.val → ∀ g, SuppIn S g → W (ν * g) = psiF E (supN ν.val) * W g) →
        (∀ g, SuppIn S g → ∀ u ∈ U, SuppIn S u → W (g * u) = W g) →
        ∀ p, SuppIn S p → IsY (n - 1) p.val → comb c W p = H p * W 1

def SphZero : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ),
    GoodAt w ψ → ∀ (B : Multiset ℂˣ) (W : GL (Fin n) (w.adicCompletion E) → ℂ), IsWh ψ W → Eig w B W → W 1 = 0 → W = 0

def AwayInd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (P : GL (Fin n) (Af E) → Prop),
    (∀ k, InKS S k → P k) → (∀ w ∉ S, ∀ k, Away S k → cmp w k = 1 → P k → ∀ y, P (k * locGL E n w y)) →
    ∀ k, Away S k → P k

def LevelS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (V : OpenSubgroup (GL (Fin n) (Af E))),
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ k, InKS S k → k ∈ V

def DenseAway : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    Dense {x : GA E n | ∃ γ k, Away S k ∧ x = ratGL E n γ * finGL E n k}

def WhBasic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (f : GA E n → ℂ), Nice f →
    Continuous (whittaker f) ∧ (∃ C : ℝ, ∀ g, ‖whittaker f g‖ ≤ C) ∧ IsWh (psiA E) (whittaker f)

def WhLin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (f : GA E n → ℂ), Nice f →
    (∀ c, Nice (fop c f) ∧ whittaker (fop c f) = fop c (whittaker f)) ∧
    ∀ f', Nice f' → Nice (f - f') ∧ whittaker (f - f') = whittaker f - whittaker f'

def ChartCont : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (f : GA E n → ℂ), Continuous f →
    ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) ∧ ∀ g, Measurable (chart f g)

def ConvCont : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (f : GA E n → ℂ), Continuous f →
    (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) → ∀ α : 𝓢(Lie E n, ℂ), Continuous (conv f α) ∧ ∃ C : ℝ, ∀ g, ‖conv f α g‖ ≤ C

def ConvFub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (f : GA E n → ℂ), Continuous f →
    (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) → ∀ (α : 𝓢(Lie E n, ℂ)) (X : Type) [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (u : X → GA E n) (a : X → ℂ),
    Continuous u → Continuous a → (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → ∀ g,
      ∫ x, conv f α (u x * g) * a x ∂ν = conv (fun g' => ∫ x, f (u x * g') * a x ∂ν) α g

def ConvNice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (f : GA E n → ℂ), Nice f → ∀ α : 𝓢(Lie E n, ℂ),
    Nice (conv f α) ∧ whittaker (conv f α) = conv (whittaker f) α

def SeedConv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (W : GA E n → ℂ), Continuous W →
    ∀ y, W (infGL E n y) ≠ 0 → ∃ α : 𝓢(Lie E n, ℂ), conv W α 1 = 1

def InjP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ f : GA E n → ℂ, Nice f → ∀ X : Set (GA E n),
    (∀ γ : GL (Fin n) E, IsY (n - 1) γ.val → ∀ g ∈ X, ratGL E n γ * g ∈ X) → (∀ g ∈ X, whittaker f g = 0) →
    ∀ g ∈ X, f g = 0

def EigOfSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ), π.HasSat w B → ∀ φ ∈ π.V,
    (∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w n, φ.1 (g * finGL E n (locGL E n w k)) = φ.1 g) → EigAt w B φ.1

def EigMap : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (f : GA E n → ℂ), EigAt w B f →
    (Nice f → EigAt w B (whittaker f)) ∧ (Nice f → ∀ α : 𝓢(Lie E n, ℂ), EigAt w B (conv f α)) ∧
    ∀ f', EigAt w B f' → EigAt w B (f - f')

def KillP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ), 1 ≤ n → ∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
    (U : OpenSubgroup (GL (Fin n) (Af E))), ∃ (c : GL (Fin n) (Af E) →₀ ℂ) (H : GA E n → ℂ), H 1 = 1 ∧
      (∀ x ∈ c.support, SuppIn S x) ∧ ∀ α : 𝓢(Lie E n, ℂ), ∃ β : 𝓢(Lie E n, ℂ), ∀ W : GA E n → ℂ, Continuous W →
        (∃ C : ℝ, ∀ g, ‖W g‖ ≤ C) → IsWh (psiA E) W → (∀ g, ∀ u ∈ U, W (g * finGL E n u) = W g) →
        ∀ p, InPS S p → conv (fop c W) β p = H p * conv W α 1

def SphAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (W : GA E n → ℂ), IsWh (psiA E) W →
    (∀ w ∉ S, GoodAt w (psiL w) ∧ EigAt w (B w) W) → (∀ g k, InKS S k → W (g * finGL E n k) = W g) →
    ∀ p : GA E n, SuppIn S (GeneralLinearGroup.map (pFin E) p) → W p = 0 → ∀ k, Away S k → W (p * finGL E n k) = 0

def Vanish : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ), 1 ≤ n → ∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
    (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (f : GA E n → ℂ), Nice f →
    (∀ w ∉ S, GoodAt w (psiL w) ∧ EigAt w (B w) f) → (∀ g k, InKS S k → f (g * finGL E n k) = f g) →
    (∀ p, InPS S p → whittaker f p = 0) → f = 0

def Seed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (π : CuspSub E n), Cen π →
    (∀ φ ∈ π.V, Nice φ.1) ∧ ∃ φ ∈ π.V, ∃ α : 𝓢(Lie E n, ℂ), conv (whittaker φ.1) α 1 = 1

def SetUp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (π π' : CuspSub E n), SameSat π π' →
    ∀ φ ∈ π.V, ∀ φ' ∈ π'.V, ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ),
      (∀ w ∉ S, GoodAt w (psiL w) ∧ π.HasSat w (B w) ∧ π'.HasSat w (B w)) ∧
      (∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g) ∧ ∀ g k, InKS S k → φ'.1 (g * finGL E n k) = φ'.1 g

def Pair : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ), 1 ≤ n → ∀ π π' : CuspSub E n, Cen π → Cen π' →
    SameSat π π' → ∃ φ ∈ π.V, ∃ φ' ∈ π'.V, ∃ β β' : 𝓢(Lie E n, ℂ), conv φ.1 β = conv φ'.1 β' ∧ conv φ.1 β ≠ 0

def InnerZero : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure]
    (π π' : CuspSub E n), Cen π → Cen π' → ¬ π.Iso π' → ∀ φ ∈ Fb.carrier π, ∀ φ' ∈ Fb.carrier π',
    inner ℂ (CuspidalSpectrum.cuspToL2 μ φ) (CuspidalSpectrum.cuspToL2 μ φ') = 0

def OrthTr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure]
    (U U' : Submodule ℂ (cuspForms E n)), U ≤ centralCuspForms E n → U' ≤ centralCuspForms E n → Fb.Stab U → Fb.Stab U' →
    (∀ φ ∈ U, ∀ φ' ∈ U', inner ℂ (CuspidalSpectrum.cuspToL2 μ φ) (CuspidalSpectrum.cuspToL2 μ φ') = 0) →
    ∀ φ ∈ U, ∀ φ' ∈ U', Orth μ φ φ'

def OrthStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure]
    (f : GA E n → ℂ), Continuous f → (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) → IsLeftInvariant f →
    ∀ a : RightCosetSpace (Reduction.rationalGLOne E n) → ℂ, Continuous a → (∃ C : ℝ, ∀ q, ‖a q‖ ≤ C) →
    (∀ g (h : IsLeftInvariant fun x => f (x * g)), ∫ q, a q * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0) →
    ∀ (β : 𝓢(Lie E n, ℂ)) (h : IsLeftInvariant (conv f β)), ∫ q, a q * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ) = 0

def OrthConv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure]
    (φ φ' : cuspForms E n), φ ∈ centralCuspForms E n → φ' ∈ centralCuspForms E n → Orth μ φ φ' →
    ∀ β β' : 𝓢(Lie E n, ℂ), conv φ.1 β = conv φ'.1 β' → conv φ.1 β = 0

def CentLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ)
    (y : (w.adicCompletion E)ˣ), ∃ c : ℂ, ∀ W : GL (Fin n) (w.adicCompletion E) → ℂ, Eig w B W →
      ∀ g, W (g * GeneralLinearGroup.scalar (Fin n) y) = c * W g

def CentEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (f f' : GA E n → ℂ), Continuous f → Continuous f' →
    IsLeftInvariant f → IsLeftInvariant f' → (∀ w ∉ S, EigAt w (B w) f ∧ EigAt w (B w) f') →
    (∀ g k, InKS S k → f (g * finGL E n k) = f g) → (∀ g k, InKS S k → f' (g * finGL E n k) = f' g) →
    ∀ (z : (Ad E)ˣ) (g g' : GA E n),
      f (g * GeneralLinearGroup.scalar (Fin n) z) * f' g' = f g * f' (g' * GeneralLinearGroup.scalar (Fin n) z)

def CenSame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (π π' : CuspSub E n), SameSat π π' → Cen π → Cen π'

def TwistRed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ) (π π' : CuspSub E n) (χ : Formalism.L2.Host.HChar E),
    (SameSat π π' → SameSat (π.twist χ) (π'.twist χ)) ∧ ((π.twist χ).Iso (π'.twist χ) → π.Iso π')

theorem smo_of (h0 : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyReal E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
      ∃ χ, Cen (π.twist χ))
    (h1 : TwistRed) (h2 : CenSame) (h3 : Pair) (h4 : InnerZero) (h5 : OrthTr) (h6 : OrthConv) :
    Published.StrongMultOneReal := by
  intro E _ _ _ n hn π π' hs
  obtain ⟨χ, hc⟩ := h0 E n hn π
  refine (h1 E n π π' χ).2 ?_
  have hs' := (h1 E n π π' χ).1 hs
  generalize π.twist χ = π at hc hs'
  generalize π'.twist χ = π' at hs'
  have hc' := h2 E n π π' hs' hc
  by_contra hi
  obtain ⟨φ, hφ, φ', hφ', β, β', e, h⟩ := h3 E n hn π π' hc hc' hs'
  let μ : Measure (Reduction.normOneGL E n) := Measure.haar
  rw [← Fb.map_carrier] at hφ hφ'
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  obtain ⟨ψ', hψ', rfl⟩ := hφ'
  have l := Fb.carrier_le_central π hc
  have l' := Fb.carrier_le_central π' hc'
  exact h (h6 E n μ ψ ψ' (l hψ) (l' hψ') (h5 E n μ _ _ l l' (Fb.stab_carrier π) (Fb.stab_carrier π')
    (h4 E n μ π π' hc hc' hi) ψ hψ ψ' hψ') β β' e)

end UpperTheory.V.Af.Smo
