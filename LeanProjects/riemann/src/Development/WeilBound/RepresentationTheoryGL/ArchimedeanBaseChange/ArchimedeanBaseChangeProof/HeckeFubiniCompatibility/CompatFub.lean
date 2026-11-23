import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH HeckeM heckeAct Repro)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

def CompatEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure], ∃ ν : Measure (Hf E a b), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant ∧
    Compat D μa μb ν

def CompatFub : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure], Compat D μa μb ν →
  ∀ F : H E a b → ℂ, Continuous F → HasCompactSupport F →
    ∫ g, F g ∂D.μ = ∫ ya : InfinitePlace E → G a, ∫ yb : InfinitePlace E → G b, ∫ h : Hf E a b,
      F (infGL E a (Units.map (Matrix.piRingEquiv (n := Fin a) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
            (MulEquiv.piUnits.symm ya)) * finGL E a h.1,
          infGL E b (Units.map (Matrix.piRingEquiv (n := Fin b) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
            (MulEquiv.piUnits.symm yb)) * finGL E b h.2) ∂ν ∂(Measure.pi fun _ => μb) ∂(Measure.pi fun _ => μa)

def TensTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  (μa : Measure (G a)) [μa.IsHaarMeasure] (μb : Measure (G b)) [μb.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)), IsMults μa ka va T → IsMults μb kb vb T →
  IsFinM ψ → IsTestM (tens ka kb ψ) ∧ adjM (tens ka kb ψ) = tens (adjK ka) (adjK kb) (adjF ψ)

def TensMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka ka' : Kers Ma) (kb kb' : Kers Mb) va va' vb vb' (T T' : ℝ) (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)), Compat D μa μb ν →
  IsMults μa ka va T → IsMults μb kb vb T → IsMults μa ka' va' T' → IsMults μb kb' vb' T' → IsFinM ψ → IsFinM ψ' →
  IsFinM (mulF ν ψ ψ') ∧
    mulM D.μ (tens ka kb ψ) (tens ka' kb' ψ') = tens (convK μa ka ka') (convK μb kb kb') (mulF ν ψ ψ')

def TensTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b)
  (κ : Type) [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) (Ta : Ops Ma) (Tb : Ops Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
  (N : Matrix κ κ ℂ) (g : H E a b), F.trM (tens ka kb ψ) (opM Ta Tb N) g =
    (∏ v, phiOf (Ma v) (Ta v) (ka v) (gInf v g.1)) * (∏ v, phiOf (Mb v) (Tb v) (kb v) (gInf v g.2)) *
      ∑ x, ∑ y, ψ x y (hFin g) * N y x

def VCBridge : Prop := ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) (M : KMod n)
  (Tθ : M.V →L[ℂ] M.V) (k : Mat n → (M.V →L[ℂ] M.V)) val (T : ℝ), (∀ u, Tθ * M.ρ u = M.ρ u * Tθ) → IsMult μ M k val T →
  VCClause (phiOf M Tθ k) → VeryCusp (phiOf M Tθ k)

def Test2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (fa : InfinitePlace E → G a → ℂ) (fb : InfinitePlace E → G b → ℂ) (ψ : Hf E a b → ℂ) (R r : ℝ)
  (U : Subgroup (Hf E a b)), 0 ≤ R →
  (∀ v, Continuous (fa v) ∧ VeryCusp (fa v) ∧ ∀ y, fa v y ≠ 0 → lg y.val ≤ R) →
  (∀ v, Continuous (fb v) ∧ VeryCusp (fb v) ∧ ∀ y, fb v y ≠ 0 → lg y.val ≤ R) →
  HasCompactSupport ψ → IsOpen (U : Set (Hf E a b)) → (∀ u ∈ U, ∀ h, ψ (u * h) = ψ h ∧ ψ (h * u) = ψ h) →
  (∀ h, ψ h ≠ 0 → logSize (finGL E a h.1) ≤ r ∧ logSize (finGL E b h.2) ≤ r) →
  (∀ d x h₂, ψ (gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) ≠ 0 → IsRegD d) →
  (∀ d x h₁, ψ (h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) ≠ 0 → IsRegD d) →
  IsTest2 (fun g : H E a b => (∏ v, fa v (gInf v g.1)) * (∏ v, fb v (gInf v g.2)) * ψ (hFin g))
    (2 * Fintype.card (InfinitePlace E) * R + r)

def Repr {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (D : Dom E a b) {Ma : Mods E a} {Mb : Mods E b}
    {κ : Type} [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) (ψ : Matrix κ κ (Hf E a b → ℂ))
    (f : Io Ma Mb κ → H E a b → ℂ) : Prop :=
  (∀ i, Continuous (f i)) ∧ ∃ c : ℂ, c ≠ 0 ∧ PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f

def TypeOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a) (Mb : Mods E b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
    ∀ (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] (μa : Measure (G a)) (μb : Measure (G b))
      (κ : Type) [Fintype κ] (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ))
      (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (f : Io Ma Mb κ → H E a b → ℂ),
      IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
      (∀ x y, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ h, ψ x y ((u₁, u₂) * h) = ψ x y h) → Repr D ka kb ψ f → ∀ i, TypeH K₁ K₂ W₁ W₂ (f i)

def SmoothOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  (μa : Measure (G a)) [μa.IsHaarMeasure] (μb : Measure (G b)) [μb.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ] (D : Dom E a b)
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (U : Subgroup (Hf E a b))
  (f : Io Ma Mb κ → H E a b → ℂ), IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ → IsOpen (U : Set (Hf E a b)) →
  (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (u * h) = ψ x y h) → Repr D ka kb ψ f →
  (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)

def GrowthOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type)
  [Fintype ι] (Φ : Matrix ι ι (H E a b → ℂ)) (M : ℕ) (f : ι → H E a b → ℂ) (c : ℂ), IsTestM Φ → (∀ i, Continuous (f i)) →
  LeftInv f → WL2 D M f → c ≠ 0 → PositivityTheory.Rg.BcB.E.conv D.μ Φ f = c • f →
  ∃ C N : ℝ, ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))

def EigAll {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} (χa : InfinitePlace E → Inf a)
    (χb : InfinitePlace E → Inf b) (f : ι → H E a b → ℂ) : Prop :=
  (∀ i v g m₂, IsEig (χa v) (along v g fun x => f i (x, m₂))) ∧ ∀ i v g m₁, IsEig (χb v) (along v g fun x => f i (m₁, x))

def InfEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Sm E n)) (v : InfinitePlace E)
  (t : Bool → ℕ → ℂ), (∃ φ ∈ S, φ ≠ 0) →
  (∀ φ ∈ S, ∀ g s m, ∀ x ∈ GLs n, gel s m (along v g φ.1) x = t s m • along v g φ.1 x) →
  ∃ χ : Inf n, ∀ s m, GlobalTheory.Dec.gelfVal (χ s) m = t s m

def GelOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka : Kers Ma) (kb : Kers Mb) va vb (T : ℝ) (ψ : Matrix κ κ (Hf E a b → ℂ)) (f : Io Ma Mb κ → H E a b → ℂ) (c c' : ℂ)
  (v : InfinitePlace E) (g : ℝ → ℝ) (s : Bool) (m : ℕ), Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T →
  IsFinM ψ → IsBump g T →
  ((∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  (∀ i, Continuous (f i)) → c ≠ 0 → PositivityTheory.Rg.BcB.E.conv D.μ (tens ka kb ψ) f = c • f →
  (∀ k', IsKer μa (Ma v) [] g (ka v) → IsKer μa (Ma v) [(s, m)] g k' →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens (Function.update ka v k') kb ψ) f = c' • f →
    ∀ i y m₂, ∀ x ∈ GLs a, gel s m (along v y fun z => f i (z, m₂)) x = (c' / c) • along v y (fun z => f i (z, m₂)) x) ∧
  ∀ k', IsKer μb (Mb v) [] g (kb v) → IsKer μb (Mb v) [(s, m)] g k' →
    PositivityTheory.Rg.BcB.E.conv D.μ (tens ka (Function.update kb v k') ψ) f = c' • f →
    ∀ i y m₁, ∀ x ∈ GLs b, gel s m (along v y fun z => f i (m₁, z)) x = (c' / c) • along v y (fun z => f i (m₁, z)) x

def ActVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b)
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
  (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
  (Ma : Mods E a) (Mb : Mods E b) (κ : Type) [Fintype κ]
  (ka ka' : Kers Ma) (kb kb' : Kers Mb) va va' vb vb' (T T' : ℝ) (ψ ψ' : Matrix κ κ (Hf E a b → ℂ))
  (f : Io Ma Mb κ → H E a b → ℂ) χa χb, Compat D μa μb ν → IsMults μa ka va T → IsMults μb kb vb T → IsFinM ψ →
  Repr D ka kb ψ f →
  ((∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  EigAll χa χb f → IsMults μa ka' va' T' → IsMults μb kb' vb' T' → IsFinM ψ' →
  PositivityTheory.Rg.BcB.E.conv D.μ (tens ka' kb' ψ') f = (valA va' χa * valA vb' χb) • convF ν ψ' f

def FinHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure] (A κ : Type)
  [Fintype A] [Fintype κ] (ψ : Matrix κ κ (Hf E a b → ℂ)) (U : Subgroup (Hf E a b)), IsFinM ψ →
  IsOpen (U : Set (Hf E a b)) → IsCompact (U : Set (Hf E a b)) → (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (h * u) = ψ x y h) →
  ∃ h : HeckeM E a b (A × κ), (∀ i j, i.1 ≠ j.1 → h i j = 0) ∧ (∀ p q x y, h (p, x) (p, y) = h (q, x) (q, y)) ∧
    ∀ f : A × κ → H E a b → ℂ, (∀ i, ∀ u ∈ U, ∀ x, f i (x * finH u) = f i x) → convF ν ψ f = heckeAct h f

def AutOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) (f : ι → H E a b → ℂ)
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ))
  (W₂ : Submodule ℂ (Kinf E b → ℂ)) χa χb (C N : ℝ), IsOpen (K₁ : Set (GL (Fin a) (Af E))) →
  IsOpen (K₂ : Set (GL (Fin b) (Af E))) → FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → LeftInv f →
  (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) → (∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2))) → EigAll χa χb f →
  (∀ φ ∈ slices₁ f, IsAutForm φ) ∧ (∀ φ ∈ slices₂ f, IsAutForm φ) ∧
    (∀ τ, HasInfCharGL (Submodule.span ℂ (slices₁ f)) τ (mOf χa τ)) ∧
    ∀ τ, HasInfCharGL (Submodule.span ℂ (slices₂ f)) τ (mOf χb τ)

def InfConv : Prop := ∀ (n : ℕ) (x : ℕ → Fin n → ℂ) (y : Fin n → ℂ),
  (∀ m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (x k) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal y m))) → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ k in atTop, Multiset.Rel (fun p q => ‖p - q‖ ≤ ε) (Multiset.map (x k) Finset.univ.val) (Multiset.map y Finset.univ.val)

def ReproEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) (R : ℝ), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → Repro ν K W R

end PositivityTheory.Rg.BcB.CG

end
