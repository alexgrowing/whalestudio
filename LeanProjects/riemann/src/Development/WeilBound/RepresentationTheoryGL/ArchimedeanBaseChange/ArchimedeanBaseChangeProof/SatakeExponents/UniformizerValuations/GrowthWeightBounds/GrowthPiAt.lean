import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop
import Development.WeilBound.CoreStatements.PadicHodgeComparison.UniqueSaturation.DescentOffPrescribedPlaces
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.NoAccumS
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbLem

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

open PositivityTheory.Rg.BcB.Desc PositivityTheory.AutomorphicGaloisHodgeTate.D

namespace PositivityTheory.Rg.BcB.F.FrE

attribute [local instance] borelG borelF borelA borelH GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

section Pi

variable {a b : ℕ}

def piG (D : Dom E a b) (π : CuspSub E a) (ι : Type) [Fintype ι] : Submodule ℂ (Hs (ι := ι) D) :=
  (Submodule.span ℂ {f | ∀ i, ∃ ψ ∈ π.V, ∃ u : ℝ → ℂ, Continuous u ∧ HasCompactSupport u ∧
    (f i : H E a b → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * u (logAbs x.1.val.det)}).topologicalClosure

def TwTrG (μ : Measure (H E a b)) (π : CuspSub E a) (φ : H E a b → ℂ) (t : ℂ) : Prop :=
  ∃ L : π.V →ₗ[ℂ] π.V, (∀ (ψ : π.V) x, (L ψ).1.1 x = ∫ y, φ y * ψ.1.1 (thetaA E a (x * y.1)) ∂μ) ∧
    FiniteDimensional ℂ (LinearMap.range L) ∧
    t = LinearMap.trace ℂ (LinearMap.range L) (L.restrict fun x _ => LinearMap.mem_range_self L x)

def FinOnG (μ : Measure (H E a b)) (π : CuspSub E a) (φ : H E a b → ℂ) : Prop :=
  ∃ W : Submodule ℂ (Sm E a), W ≤ π.V ∧ FiniteDimensional ℂ W ∧ ∀ u : ℝ → ℂ, Continuous u → ∀ ψ ∈ π.V,
    ∃ ψ' ∈ W, ∀ x, ψ'.1 x = ∫ y, φ y * u (logAbs y.1.val.det) * ψ.1 (x * y.1) ∂μ

def GrowthPiAt (D : Dom E a b) (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (π : CuspSub E a) : Prop :=
  ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ)
    (r₀ r₁ ε : ℝ), IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOnG D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ →
    0 < ε → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ) (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E a b → ℂ)) (t : ℂ),
      IsTestM Φ → IsROp D Φ (T₁ * U * T₂) → (∀ f ∈ piG D π ι, U f ∈ piG D π ι) → (∀ f ∈ (piG D π ι)ᗮ, U f ∈ (piG D π ι)ᗮ) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → TwTrG D.μ π (trM Φ M) t →
      ‖ellSum2 μ₁ μ₂ (trM Φ M) - t / 2‖ ≤ C * (1 + k) ^ N * ‖U ∘L (piG D π ι)ᗮ.subtypeL‖ + C * ‖U‖ * ε ^ k

end Pi

structure Frame0 (hR : Rd.ReadLimit) (π : CuspSub E n) : Type 1 where
  lam : InfinitePlace E → DomWeight n
  hlam : ∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))
  μ : HChar E
  e : InfinitePlace E → ℤ
  hμ : IsMu μ e
  Sec : Set (Pl E)
  hSec : IsSection Sec
  d₀ : LocData E n
  ok₀ : d₀.Ok
  T₀ : d₀.T = ∅
  Bad₀ : d₀.Bad = ∅
  μloc : ∀ w, d₀.μ w = μ.loc w
  unif : ∀ w, IsUnifAt (d₀.ϖ w) ∧ IsUnifV E w (d₀.ϖ w : w.adicCompletion E)
  S₀ : ∀ w ∈ d₀.S₀, w ∈ Sec ∧ IsSplitAt w
  good : ∀ w ∈ Sec, w ∉ d₀.S₀ → w ∉ d₀.Bad → (∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w
  K'_lev : ∀ w ∈ d₀.S₀, IsLevel (MonoidHom.id _) (KL n w) ((d₀.K' w).subgroupOf (UL n w))
  τ : ∀ w : Pl E, SmIrr (GLw n w)
  hτ : ∀ w, π.IsLocComp w (τ w)
  τ_fix : ∀ w ∈ d₀.S₀, ∃ y ∈ fixed (τ w).ρ (d₀.K' w), y ≠ 0
  u₁ : ∀ a, GL (Fin a) E
  u₂ : ∀ a, GL (Fin (n - a)) E
  hu : ∀ a, IsTransl (u₁ a) ∧ IsTransl (u₂ a)
  C : Chain μ e lam
  A : ∀ i : C.ι, Arch E (C.a i) (n - C.a i) (C.l₁ i) (C.l₂ i) (C.μG (C.a i)) (C.μG (n - C.a i)) (C.νC (C.a i)) (C.νC (n - C.a i))
  K : ∀ w : Pl E, Subgroup (GLw n w)
  hK : F5.IsLevel K
  Kc : ∀ w, IsCompact (K w : Set (GLw n w))
  K_good : ∀ w : Pl E, (∀ u ∈ d₀.S₀ ∪ d₀.Bad, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) →
    K w = GlobalTheory.LFun.KGL w n
  K_bad : ∀ a (ha : a ≤ n), ∀ w ∈ d₀.S₀ ∪ d₀.Bad, ∀ m X, blk (Nat.add_sub_of_le ha) w m X ∈ K w →
    m ∈ d₀.L a w ∧ μ.loc w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1
  K_conj : ∀ a (ha : a ≤ n), ∀ w ∈ d₀.S₀ ∪ d₀.Bad, IsSplitAt w → ∀ u, ConjPl w u → ∀ m X, blk (Nat.add_sub_of_le ha) u m X ∈ K u →
    μ.loc u (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 ∧
      ∃ m' ∈ d₀.L a w, embW a u m.1 = embT a w m'.1 ∧ embW (n - a) u m.2 = embT (n - a) w m'.2
  i₀ : C.ι
  a₀ : C.a i₀ = n
  c₀ : C.c i₀ ≠ 0
  mid : ∀ i, i ≠ i₀ → 0 < C.a i ∧ C.a i < n
  lefM : (A i₀).Ma = fun v => lefE _ (C.l₁ i₀ v).w
  lefT : ∀ v, HEq ((A i₀).Ta v) (lefT _ (C.l₁ i₀ v).w)
  gp : GrowthPiAt (A i₀).D (C.μG (C.a i₀)) (C.μG (n - C.a i₀)) (a₀.symm ▸ π)
  L_fix : ∃ ψ ∈ (a₀.symm ▸ π : CuspSub E (C.a i₀)).V, ψ ≠ 0 ∧ ∀ k ∈ lev₁ Sec d₀ (C.a i₀), finRep E _ k ψ = ψ
  Wx₁ : Submodule ℂ (Kinf E (C.a i₀) → ℂ)
  Wx₂ : Submodule ℂ (Kinf E (n - C.a i₀) → ℂ)
  hWx : FiniteDimensional ℂ Wx₁ ∧ FiniteDimensional ℂ Wx₂ ∧ (fun _ => 1) ∈ Wx₁ ∧ (fun _ => 1) ∈ Wx₂
  pack : Rd.B.PackAt E _ _ (A i₀).Ma (A i₀).Mb Wx₁ Wx₂
  Ωx₁ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))
  Ωx₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))
  hΩx : KTypes E Ωx₁ ∧ KTypes E Ωx₂
  Θx₁ : Subgroup (GL (Fin (C.a i₀)) (Af E)) → Subgroup (GL (Fin (n - C.a i₀)) (Af E)) → ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))
  Θx₂ : Subgroup (GL (Fin (C.a i₀)) (Af E)) → Subgroup (GL (Fin (n - C.a i₀)) (Af E)) → ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))
  hx : ∀ (K₁ : Subgroup (GL (Fin (C.a i₀)) (Af E))) (K₂ : Subgroup (GL (Fin (n - C.a i₀)) (Af E))),
    IsOpen (K₁ : Set (GL (Fin (C.a i₀)) (Af E))) → IsOpen (K₂ : Set (GL (Fin (n - C.a i₀)) (Af E))) →
    Levels E (Θx₁ K₁ K₂) ∧ Levels E (Θx₂ K₁ K₂) ∧ SpectralAccumulation.LimAtS E _ _ Wx₁ Wx₂ Ωx₁ Ωx₂ K₁ K₂ (Θx₁ K₁ K₂) (Θx₂ K₁ K₂)
  W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)
  hW : ∀ N, FiniteDimensional ℂ (W N)
  W_join : ∀ (i : C.ι) (s₁ : Tr E (C.a i)) (s₂ : Tr E (n - C.a i)) Pa Pb (D : Pre E n), Ctx μ s₁ s₂ Pa Pb D →
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ rlΩ₁ hR E _ _ (A i).Ma (A i).Mb M ∪ {W' | i = i₀ ∧ W' ∈ Ωx₁ M}, HasType K' W' V) →
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K', ∃ W' ∈ rlΩ₂ hR E _ _ (A i).Ma (A i).Mb M ∪ {W' | i = i₀ ∧ W' ∈ Ωx₂ M}, HasType K' W' V) →
    ∀ j, HasKType (W (D.N j)) (D.V j)

namespace Frame0

variable {hR : Rd.ReadLimit} {π : CuspSub E n} (F₀ : Frame0 hR π)

abbrev π' : CuspSub E (F₀.C.a F₀.i₀) := F₀.a₀.symm ▸ π

structure Cand (d : LocData E n) (i : F₀.C.ι) (s₁ : Tr E (F₀.C.a i)) (s₂ : Tr E (n - F₀.C.a i)) (Pa : Pre E (F₀.C.a i))
    (Pb : Pre E (n - F₀.C.a i)) (D : Pre E n) : Prop where
  ctx : Ctx F₀.μ s₁ s₂ Pa Pb D
  leaves₁ : s₁.AllLeaves fun M V => M = 0 ∨ ∃ K' ∈ rlΘ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) M ∪
    {K' | i = F₀.i₀ ∧ K' ∈ F₀.Θx₁ (lev₁ F₀.Sec d (F₀.C.a F₀.i₀)) (lev₂ F₀.Sec d (F₀.C.a F₀.i₀)) M}, ∃ W' ∈ rlΩ₁ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb M ∪ {W' | i = F₀.i₀ ∧ W' ∈ F₀.Ωx₁ M}, HasType K' W' V
  leaves₂ : s₂.AllLeaves fun M V => M = 0 ∨ ∃ K' ∈ rlΘ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) M ∪
    {K' | i = F₀.i₀ ∧ K' ∈ F₀.Θx₂ (lev₁ F₀.Sec d (F₀.C.a F₀.i₀)) (lev₂ F₀.Sec d (F₀.C.a F₀.i₀)) M}, ∃ W' ∈ rlΩ₂ hR E _ _ (F₀.A i).Ma (F₀.A i).Mb M ∪ {W' | i = F₀.i₀ ∧ W' ∈ F₀.Ωx₂ M}, HasType K' W' V
  inf₁ : ∀ τ, HasInfCharGL s₁.space τ (mOf (F₀.A i).χa τ)
  inf₂ : ∀ τ, HasInfCharGL s₂.space τ (mOf (F₀.A i).χb τ)
  vec : ∃ G ∈ pairSpace s₁.space s₂.space, G ≠ 0 ∧ ∃ W₁ W₂, TypeH (lev₁ F₀.Sec d (F₀.C.a i)) (lev₂ F₀.Sec d (F₀.C.a i)) W₁ W₂ G

end Frame0

end PositivityTheory.Rg.BcB.F.FrE

end
