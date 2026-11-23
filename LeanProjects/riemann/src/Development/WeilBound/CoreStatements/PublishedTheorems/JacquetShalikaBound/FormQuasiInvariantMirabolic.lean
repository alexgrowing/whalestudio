import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.CMMul

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace PositivityTheory.JacquetShalikaLocal

def ForF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F], Measure F → AddChar F ℂ → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] (ψ : AddChar F ℂ), PsiOK ψ → P F μ ψ

def ForR (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F], Measure F → AddChar F ℂ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V],
      Representation ℂ (GL (Fin n) F) V → Prop) : Prop :=
  ForF fun F _ _ _ _ _ μ ψ => ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V), Smooth ρ → P F μ ψ n V ρ

def L0 : Prop := ForF fun F _ _ _ _ _ μ ψ => Continuous ψ ∧ ∀ m : ℕ,
  (∀ M, IsCompact (lat F m M) ∧ IsOpen (lat F m M) ∧ MeasurableSet (lat F m M) ∧
    0 < (Measure.pi fun _ : Fin m => μ).real (lat F m M)) ∧
  ∀ (g : GL (Fin m) F) (A : Set (Fin m → F)) (f : (Fin m → F) → ℂ), MeasurableSet A →
    ∫ x in (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A, f x ∂(Measure.pi fun _ => μ) =
      ((Measures.modulus (g : Matrix (Fin m) (Fin m) F).det : ℝ) : ℂ) *
        ∫ x in A, f ((g : Matrix (Fin m) (Fin m) F) *ᵥ x) ∂(Measure.pi fun _ => μ)

open Classical in

def L1 : Prop := ForF fun F _ _ _ _ _ μ ψ => ∀ (m : ℕ) (y : Fin m → F),
  ∫ ξ in lat F m 0, ψ (ξ ⬝ᵥ y) ∂(Measure.pi fun _ => μ) =
    if ∀ i, y i ∈ 𝒪[F] then (((Measure.pi fun _ : Fin m => μ).real (lat F m 0) : ℝ) : ℂ) else 0

def L2 : Prop := ForF fun F _ _ _ _ _ μ ψ => ∀ (k c c' : ℕ) (f : (Fin (k + 1) → F) → ℂ),
  (∀ x y, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c' * t) → f (x + y) = f x) →
  (∀ h : GL (Fin (k + 1)) F, Div (c + 1) ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) →
    ∀ x, f ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) = f x) →
  ∀ g : GL (Fin (k + 1)) F, Div (c + 1) ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) →
    ∫ x in (fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0,
        ψ (-x (Fin.last k)) * f x ∂(Measure.pi fun _ => μ) =
      ∫ x in lat F (k + 1) (c + 1), ψ (-x (Fin.last k)) * f x ∂(Measure.pi fun _ => μ)

def L3 : Prop := ForR fun F _ _ _ _ _ μ ψ n V _ _ ρ => ∀ (k M : ℕ) (ξ : Fin (k + 1) → F) (u : V), ∃ w : V,
  (∀ l : V →ₗ[ℂ] ℂ, l w = ∫ x in lat F (k + 1) M, ψ (-(ξ ⬝ᵥ x)) * l (ρ (col n k x) u) ∂(Measure.pi fun _ => μ)) ∧
    ∀ y ∈ lat F (k + 1) M, ρ (col n k y) w = ψ (ξ ⬝ᵥ y) • w

def ColumnsMirabolic : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ n k : ℕ, k + 1 < n →
  (∀ x y : Fin (k + 1) → F, col n k (x + y) = col n k x * col n k y) ∧ col n k (0 : Fin (k + 1) → F) = 1 ∧
  (∀ x : Fin (k + 1) → F, inP (k + 1) (col n k x) ∧ inU k (col n k x) ∧
    (col n k x : Matrix (Fin n) (Fin n) F).det = 1 ∧ Whittaker.psiN ψ (col n k x) = ψ (x (Fin.last k))) ∧
  (∀ g : GL (Fin n) F, inP k g → inP (k + 1) g) ∧
  (∀ g : GL (Fin n) F, inP (k + 1) g → ∃ t : GL (Fin (k + 1)) F,
    (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det = (g : Matrix (Fin n) (Fin n) F).det ∧
    (∀ x, g * col n k x = col n k ((t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) * g) ∧
    (inP k g → ∀ x, ((t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) (Fin.last k) = x (Fin.last k))) ∧
  ∀ t : GL (Fin (k + 1)) F, ∃ g : GL (Fin n) F, inP (k + 1) g ∧
    (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det = (g : Matrix (Fin n) (Fin n) F).det ∧
    (∀ x, g * col n k x = col n k ((t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) * g) ∧
    ∀ c, Div c ((t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) → Div c ((g : Matrix (Fin n) (Fin n) F) - 1)

def ColumnsUnipotent : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ n k : ℕ, k + 1 < n →
  (∀ g : GL (Fin n) F, inU k g → ∃ (g' : GL (Fin n) F) (x : Fin (k + 1) → F), inU (k + 1) g' ∧ g = g' * col n k x ∧
    Whittaker.psiN ψ g = Whittaker.psiN ψ g' * ψ (x (Fin.last k))) ∧
  ∀ g : GL (Fin n) F, inU (k + 1) g → ∀ x : Fin (k + 1) → F, ∃ g' : GL (Fin n) F, inU (k + 1) g' ∧
    col n k x * g = g' * col n k x ∧ Whittaker.psiN ψ g' = Whittaker.psiN ψ g

def FormCoefficientStability : Prop := ForR fun F _ _ _ _ _ μ ψ n V _ _ ρ => ∀ (l : V →ₗ[ℂ] ℂ) (k : ℕ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
  k + 1 < n → Inv ρ ψ l (k + 1) B → ∀ u u', Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u)) ∧
    ∃ c : ℕ, ∀ g : GL (Fin (k + 1)) F,
      Div (c + 1) ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) →
      ∫ x in (fun x => (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0,
          ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u) ∂(Measure.pi fun _ => μ) =
        ∫ x in lat F (k + 1) (c + 1), ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u) ∂(Measure.pi fun _ => μ)

def StableAverageExists : Prop := ForR fun _ _ _ _ _ _ μ ψ n V _ _ ρ => ∀ (l : V →ₗ[ℂ] ℂ) (k : ℕ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
  k + 1 < n → Inv ρ ψ l (k + 1) B → ∃ B', Char μ ρ ψ k B B'

def FormHermitianPositive : Prop := ForR fun _ _ _ _ _ _ μ ψ n V _ _ ρ => ∀ (l : V →ₗ[ℂ] ℂ) (k : ℕ) (B B' : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
  k + 1 < n → Whit ρ ψ l → Inv ρ ψ l (k + 1) B → Char μ ρ ψ k B B' →
    (∀ u u', starRingEnd ℂ (B' u u') = B' u' u) ∧ (∀ u, 0 ≤ (B' u u).re) ∧ ∀ u, B' u u = 0 → l u = 0

def FormQuasiInvariantMirabolic : Prop := ForR fun F _ _ _ _ _ μ ψ n V _ _ ρ => ∀ (l : V →ₗ[ℂ] ℂ) (k : ℕ) (B B' : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
  k + 1 < n → Inv ρ ψ l (k + 1) B → Char μ ρ ψ k B B' → ∀ g, inP k g → ∀ u u', B' (ρ g u) (ρ g u') =
    (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - k) * B' u u'

def FormEquivariantColumn : Prop := ForR fun _ _ _ _ _ _ μ ψ n V _ _ ρ => ∀ (l : V →ₗ[ℂ] ℂ) (k : ℕ) (B B' : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
  k + 1 < n → Inv ρ ψ l (k + 1) B → Char μ ρ ψ k B B' → ∀ g, inU k g → ∀ u u',
    B' u' (ρ g u) = Whittaker.psiN ψ g * B' u' u

def L5 : Prop := ForR fun F _ _ _ _ _ μ ψ n V _ _ ρ => ∀ (l : V →ₗ[ℂ] ℂ) (B B' : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hn : 1 < n),
  Inv ρ ψ l 1 B → Char μ ρ ψ 0 B B' → ∀ v, (∀ g ∈ integralGL F n, ρ g v = v) → ∃ C : ℝ, ∀ T : ℕ,
    ∑ j ∈ Finset.range T, (qF F : ℝ) ^ (j * (n - 2)) *
      (B' (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v)
        (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v)).re ≤ C

def L6 : Prop := ForR fun F _ _ _ _ _ _ ψ n V _ _ ρ => ∀ (l : V →ₗ[ℂ] ℂ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hn : 1 < n),
  Whit ρ ψ l → Unit' ρ B → ∃ B', Inv ρ ψ l 0 B' ∧ ∀ v, (∀ g ∈ integralGL F n, ρ g v = v) → ∃ C : ℝ, ∀ T : ℕ,
    ∑ j ∈ Finset.range T, (qF F : ℝ) ^ (j * (n - 2)) *
      (B' (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v)
        (ρ (torusPow F n (Pi.single ⟨0, by omega⟩ (j : ℤ))) v)).re ≤ C

def L7 : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (ψ : AddChar F ℂ), PsiOK ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (v : V) (z : Fin n → ℂˣ), Heig ρ v z →
    ∀ l : V →ₗ[ℂ] ℂ, Whit ρ ψ l → ∀ g, l (ρ g v) = l v * sphericalWhittaker ψ z g

def L8 : Prop := ∀ (n : ℕ) (hn : 0 < n) (z : Fin n → ℂˣ),
  evalAt z (schur (Pi.single (⟨0, hn⟩ : Fin n) ((0 : ℕ) : ℤ))) = 1 ∧ ∀ j : ℕ, 1 ≤ j →
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r * (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, (z i : ℂ)) *
      evalAt z (schur (Pi.single (⟨0, hn⟩ : Fin n) ((j - r : ℕ) : ℤ))) = 0

def liftZP_newton : Prop := ∀ (n : ℕ) (β : Fin n → ℂ) (g : ℕ → ℂ), g 0 = 1 →
  (∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1),
    (-1) ^ r * (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, β i) * g (j - r) = 0) →
  Filter.Tendsto g Filter.atTop (nhds 0) → ∀ i, ‖β i‖ < 1

def ParameterUpperBound : Prop := ForR fun F _ _ _ _ _ _ ψ n V _ _ ρ => 1 < n → ∀ (l : V →ₗ[ℂ] ℂ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
  Whit ρ ψ l → Unit' ρ B → ∀ (v : V) (z : Fin n → ℂˣ), Heig ρ v z → (∃ g, l (ρ g v) ≠ 0) →
    ∀ i, ‖(z i : ℂ)‖ < Real.sqrt (qF F)

def liftZP_unit : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) F) V)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ), Unit' ρ B → ∀ (v : V) (z : Fin n → ℂˣ), v ≠ 0 → Heig ρ v z →
    ∀ r ≤ n, starRingEnd ℂ (evalAt z (esymmL n r)) * evalAt z (esymmL n n) = evalAt z (esymmL n (n - r))

def ParameterAbsoluteValues : Prop := ∀ (n : ℕ) (z : Fin n → ℂˣ),
  (∀ r ≤ n, starRingEnd ℂ (evalAt z (esymmL n r)) * evalAt z (esymmL n n) = evalAt z (esymmL n (n - r))) →
    ∀ i, ∃ j, ‖(z j : ℂ)‖ * ‖(z i : ℂ)‖ = 1

end PositivityTheory.JacquetShalikaLocal

end
