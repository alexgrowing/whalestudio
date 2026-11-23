import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

def re (x : A ℚ) : ℝ := TR.pInf ℚ x Rat.infinitePlace

def iy (y : ℝ) : (A ℚ)ˣ :=
  if h : y = 0 then 1 else TR.infId ℚ ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩

def rot (t : ℝ) : GL (Fin 2) (A ℚ) :=
  TR.infGL ℚ 2 (Matrix.SpecialLinearGroup.toGL ⟨!![fun _ => Real.cos t, fun _ => -Real.sin t; fun _ => Real.sin t, fun _ => Real.cos t], by
    rw [Matrix.det_fin_two_of]
    funext w
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.one_apply]
    nlinarith [Real.sin_sq_add_cos_sq t]⟩)

def ThR (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (g : GL (Fin 2) (A ℚ)) : ℂ :=
  ∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* g.val) j

def Bad (N : ℕ) (v : H.P ℚ) : Prop := (N : 𝓞 ℚ) ∈ v.asIdeal

def Dv (N : ℕ) (v : H.P ℚ) (x : A ℚ) : Prop := Valued.v (H.cp v x) ≤ Valued.v (N : H.Kv v)

def Lev (N : ℕ) (k : GL (Fin 2) (A ℚ)) : Prop :=
  (∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) ∧
    ∀ v, H.KAt v k ∧ ∀ i j, Dv N v (k.val i j - (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)

def ChOk (χ : HChar ℚ) (N : ℕ) : Prop := ∀ t ∈ UU, (∀ v, Dv N v ((t : A ℚ) - 1)) → χ.1 t = 1

def PhiN (N : ℕ) (p : MvPolynomial (Fin 2) ℂ) (x : Fin 2 → A ℚ) : ℂ :=
  if ∀ v, Dv N v (x 0) ∧ Dv N v (x 1 - 1) then
    MvPolynomial.eval (fun i => (re (x i) : ℂ)) p * Complex.exp (-(Real.pi : ℂ) * ((re (x 0) ^ 2 + re (x 1) ^ 2 : ℝ) : ℂ)) else 0

variable {E : Type} [Field E] [NumberField E]

def Wo (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (h : GL (Fin 2) (A E)) : ℂ :=
  ∫ u in FS2 ℚ, φ (nE D u * h) * ψ (u 1) ∂(adeleMeasurePi ℚ)

def Ir (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) : ℂ :=
  ∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M.μ ∂U.υ

def Zs (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (2 * s * t) * Ir M U χ φ Φ t

def Zu (D : Dat ℚ E) (M : Meas ℚ) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ) : ℂ :=
  ∫ k, ∫ y : IdeleGroup ℚ, Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) *
    ∫ z : IdeleGroup ℚ, (Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)
      ∂(ideleMeasure ℚ) ∂(ideleMeasure ℚ) ∂M.κ

def Mk (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (φ : GL (Fin 2) (A E) → ℂ) (p : MvPolynomial (Fin 2) ℂ) (s : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p *
    ∫ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)

structure admitted (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) : Prop where
  cont : Continuous φ
  left : ∀ γ g, φ (ratGL E 2 γ * g) = φ g
  cen : ∀ z g, φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * φ g
  zero : ∀ h, ∫ u in FS2 ℚ, φ (nE D u * h) ∂(adeleMeasurePi ℚ) = 0
  bdd : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B
  decay : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∀ r : ℕ,
    ∃ B : ℝ, ∀ b a, ∀ k ∈ C, c ≤ ab a → ‖φ (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ ^ r
  wdec : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧ ∀ r : ℕ, ∃ B : ℝ,
    ∀ y : (A ℚ)ˣ, ∀ k ∈ C, ‖Wo D φ (em E (aE y) * k)‖ ≤ B * ((1 + |re y|) ^ r)⁻¹ ∧ (Wo D φ (em E (aE y) * k) ≠ 0 → (y : A ℚ).2 ∈ K)

variable [IsTotallyComplex E]

structure Gd (D : Dat ℚ E) (P : CuspSub E 2) (L N : ℕ) (φ : GL (Fin 2) (A E) → ℂ) : Prop where
  pos : 0 < N
  dvd : L ∣ N
  same : ∀ v, Bad N v → Bad L v
  mem : φ ∈ Tr P
  pl : ∀ v, ¬ Bad N v → H.Gd D.δ v
  fix : ∀ w : H.P E, ¬ Bad N (w.under (𝓞 ℚ)) → H.Fix w φ ∧ ∃ B, (CG.mk P).HasSat w B ∧ EigAt w B φ
  lev : ∀ k, Lev N k → ∀ g, φ (g * em E k) = φ g
  supp : ∀ (y : (A ℚ)ˣ) x, Wo D φ (em E (aE y) * infGL E 2 x) ≠ 0 → ∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)
  tor : ∀ t ∈ UU, (∀ v, Dv L v ((t : A ℚ) - 1)) → ∀ (y : (A ℚ)ˣ) x,
    Wo D φ (em E (aE (y * t)) * infGL E 2 x) = Wo D φ (em E (aE y) * infGL E 2 x)

structure IsAs (P : CuspSub E 2) (χ : HChar ℚ) (N : ℕ) (a : ℕ → ℂ) : Prop where
  one : a 1 = 1
  mul : ∀ m n, m.Coprime n → a (m * n) = a m * a n
  bad : ∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0
  split : ∀ v, ¬ Bad N v → ∀ w w' : H.P E, w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → ∀ α β α' β' : ℂˣ,
    (CG.mk P).HasSat w {α, β} → (CG.mk P).HasSat w' {α', β'} →
    (PowerSeries.mk fun k => a (normV v ^ k)) * ((1 - PowerSeries.C ((α * α' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) *
      (1 - PowerSeries.C ((α * β' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) * (1 - PowerSeries.C ((β * α' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) *
      (1 - PowerSeries.C ((β * β' * χ.val v : ℂˣ) : ℂ) * PowerSeries.X)) = 1
  inert : ∀ v, ¬ Bad N v → ∀ w : H.P E, w.under (𝓞 ℚ) = v → normV w = normV v ^ 2 → ∀ α β : ℂˣ, (CG.mk P).HasSat w {α, β} →
    (PowerSeries.mk fun k => a (normV v ^ k)) * ((1 - PowerSeries.C ((α * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) *
      (1 - PowerSeries.C ((β * χ.val v : ℂˣ) : ℂ) * PowerSeries.X) * (1 - PowerSeries.X ^ 2)) = 1

def Unit1 (ω : HChar ℚ) : Prop := ∀ a, ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1

def Entire (a : ℕ → ℂ) : Prop := ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 4 < s.re → F s = LSeries a s

def AllA (p : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], Dat ℚ E → CuspSub E 2 → HChar ℚ → HChar ℚ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
    CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → p E D P ω χ

def TrAdm : Prop := AllA fun _ _ _ _ D P ω _ => ∀ φ ∈ Tr P, admitted D ω φ

def PerTr : Prop := AllA fun _ _ _ _ D P ω χ => (∀ φ ∈ Tr P, admitted D ω φ) → ∀ M U, NoPer M U χ P → ∀ φ ∈ Tr P, Per M U χ φ = 0

def Ent : Prop := AllA fun _ _ _ _ D _ ω χ => ∀ M U φ, admitted D ω φ → Per M U χ φ = 0 → ∀ Φ ∈ schwartzBruhatPi ℚ (Fin 2),
  Differentiable ℂ (Zs M U χ φ Φ)

def Unf : Prop := AllA fun _ _ _ _ D _ ω χ => ∀ M U, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, admitted D ω φ → ∀ Φ ∈ schwartzBruhatPi ℚ (Fin 2),
  ∀ s : ℂ, 4 < s.re → Zs M U χ φ Φ s = c * Zu D M χ φ Φ s

def PhiMem : Prop := ∀ N p, 0 < N → PhiN N p ∈ schwartzBruhatPi ℚ (Fin 2)

def Fac : Prop := AllA fun _ _ _ _ D P ω χ => ∀ M L N, ChOk χ L → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a →
  ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) → ∀ s : ℂ, 4 < s.re → LSeriesSummable a s →
    Zu D M χ φ (PhiN N p) s = c * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e)) * LSeries a s * Mk D χ 0 φ p s

def Shift : Prop := AllA fun E _ _ _ D P _ _ => ∀ L N φ, Gd D P L N φ → ∃ φ₀ φ₁ φ₂, Gd D P L N φ₀ ∧ Gd D P L N φ₁ ∧ Gd D P L N φ₂ ∧ ∀ y t : ℝ, y ≠ 0 →
  (y : ℂ) * Wo D φ (em E (aE (iy y) * rot t)) = (Real.sin t : ℂ) ^ 2 * Wo D φ₀ (em E (aE (iy y) * rot t)) +
    (Real.sin t : ℂ) * (Real.cos t : ℂ) * Wo D φ₁ (em E (aE (iy y) * rot t)) + (Real.cos t : ℂ) ^ 2 * Wo D φ₂ (em E (aE (iy y) * rot t))

def ShiftM : Prop := AllA fun _ _ _ _ D P _ χ => ∀ L N k φ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), Gd D P L N φ → p.IsHomogeneous (2 * e) →
  ∃ (n : ℕ) (f : Fin n → _) (q : Fin n → MvPolynomial (Fin 2) ℂ), (∀ i, Gd D P L N (f i) ∧ (q i).IsHomogeneous (2 * (e + k))) ∧
    ∀ s : ℂ, 4 < s.re → Mk D χ k φ p s = ∑ i, Mk D χ 0 (f i) (q i) s

def Hol : Prop := AllA fun _ _ _ _ D _ ω χ => ∀ k φ p, admitted D ω φ → DifferentiableOn ℂ (Mk D χ k φ p) {s | 1 - (k : ℝ) < s.re}

def NonZ : Prop := AllA fun _ _ _ _ D P ω χ => (∀ φ ∈ Tr P, admitted D ω φ) → ∀ L N φ, Gd D P L N φ → Wo D φ 1 ≠ 0 → ∀ (k : ℕ) (s : ℂ), 1 - (k : ℝ) < s.re →
  ∃ (φ' : _) (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), Gd D P L N φ' ∧ p.IsHomogeneous (2 * e) ∧ Mk D χ k φ' p s ≠ 0

def ExGd : Prop := AllA fun _ _ _ _ D P ω _ => (∀ φ ∈ Tr P, admitted D ω φ) → ∀ N₀, 0 < N₀ → ∃ L N φ, N₀ ∣ L ∧ Gd D P L N φ ∧ Wo D φ 1 ≠ 0

def ChEx : Prop := ∀ χ : HChar ℚ, ∃ N₀, 0 < N₀ ∧ ∀ N, N₀ ∣ N → ChOk χ N

def SatU : Prop := AllA fun E _ _ _ _ P _ _ => ∀ (w : H.P E) (α β : ℂˣ), (CG.mk P).HasSat w {α, β} →
  ‖(α * β : ℂ)‖ = 1 ∧ starRingEnd ℂ (α + β : ℂ) * (α * β) = α + β ∧ ‖(α : ℂ)‖ ^ 2 ≤ normV w

def AsEx : Prop := AllA fun _ _ _ _ D P _ χ => ∀ L N φ, Gd D P L N φ → ∃ a, IsAs P χ N a ∧ ∀ s : ℂ, 4 < s.re → LSeriesSummable a s

def Ext : Prop := AllA fun _ _ _ _ D P _ χ => ∀ M U, NoPer M U χ P → ∀ L N φ, ChOk χ L → Gd D P L N φ → Wo D φ 1 ≠ 0 →
  ∀ a, IsAs P χ N a → (∀ s : ℂ, 4 < s.re → LSeriesSummable a s) → Entire a

def Landau : Prop := ∀ b : ℕ → ℂ, (∀ n, 0 ≤ b n) → b 1 = 1 → (∀ s : ℂ, 4 < s.re → LSeriesSummable b s) → Entire b →
  {n | 1 ≤ b n}.Finite

def Lan : Prop := AllA fun E _ _ _ D P ω χ => ∀ η : HChar ℚ, χ = ω⁻¹ → ∀ L N φ, Gd D P L N φ →
  (∀ w : H.P E, ¬ Bad N (w.under (𝓞 ℚ)) → η.val (w.under (𝓞 ℚ)) = if normV w = normV (w.under (𝓞 ℚ)) then 1 else -1) →
  (∀ w w' : H.P E, ¬ Bad N (w.under (𝓞 ℚ)) → w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) → ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat w' B) →
  ChOk ω⁻¹ L → ChOk (ω * η)⁻¹ L → ∀ a a', IsAs P ω⁻¹ N a → IsAs P (ω * η)⁻¹ N a' → (∀ s : ℂ, 4 < s.re → LSeriesSummable a s) →
  (∀ s : ℂ, 4 < s.re → LSeriesSummable a' s) → Entire a → Entire a' → False

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
