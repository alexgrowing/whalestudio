import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothCharCompNormU
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelStrongSupp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ArthurClozelLocalSC
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Unlinked (s : Multiset (IrrGL k)) : Prop := ∀ y ∈ s, ∀ z ∈ s, y ≠ z.nu 1

def PlainTor (x : IrrGL k) : Prop := ∃ s, HasSupport x.rep s ∧ (∀ y ∈ s, y.1 = 1) ∧ Unlinked s

def Plain (x : IrrGL k) : Prop := PlainTor x ∨ (x.IsCusp ∧ UpperTheory.Zero.LLC.GoodCusp x)

def chars {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) : Multiset (IrrGL k) :=
  Finset.univ.val.map fun j => IrrGL.ofChar (ξ j) (hξ j)

theorem unlinked_zero : Unlinked (0 : Multiset (IrrGL k)) := fun _ h => absurd h (Multiset.notMem_zero _)

example (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Plain (IrrGL.ofChar χ hχ) :=
  Or.inr ⟨IrrGL.isCusp_ofChar χ hχ, Or.inl rfl⟩

example (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ¬ Unlinked ({IrrGL.ofChar χ hχ, (IrrGL.ofChar χ hχ).nu 1} : Multiset (IrrGL k)) := fun h =>
  h ((IrrGL.ofChar χ hχ).nu 1) (by simp) (IrrGL.ofChar χ hχ) (by simp) rfl

example (ξ : Fin 1 → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) : chars ξ hξ = {IrrGL.ofChar (ξ 0) (hξ 0)} := by
  simp [chars]

end Classes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def satWD {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) : WD h :=
  (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2)

variable [IsCMField E]

def PlainAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ → Plain (IrrGL.of σ.ρ σ.smooth σ.irred)

example (π : CuspSub E 1) (w : HeightOneSpectrum (𝓞 E)) : PlainAt π w := fun σ _ => by
  refine Or.inr ⟨IrrGL.isCusp_of.2 ⟨one_pos, σ.smooth, fun s d e he => absurd ?_ he⟩, Or.inl rfl⟩
  rw [eq_bot_iff]
  intro u hu
  have h := congrArg Units.val (det_eq_one_of_mem_unipRad _ hu)
  rw [Subgroup.mem_bot]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h

example {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (B : Multiset ℂˣ) :
    satWD h 1 B = WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ)) := by
  rw [satWD, show (1 - ((1 : ℕ) : ℝ)) / 2 = 0 by norm_num, WD.lpTw_zero]

inductive Sph
  | unr | dR | crys | phi

def SphAt (c : Sph) (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ) : Prop :=
  match c with
  | .unr => ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)
  | .dR => ClauseAt .dR π ι r w
  | .crys => ClauseAt .crys π ι r w
  | .phi => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (satWD h a B).charPol g

def SphericalLevelCondition (s : Level) (c : Sph) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w →
    ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → SphAt c π ι r w B

def Core : Prop := Ex .csd ∧ ∀ c, SphericalLevelCondition .csd c

def CoreAll : Prop := Ex .all ∧ ∀ c, SphericalLevelCondition .all c

def CharLift {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M]
    (π : CuspSub K a) (P : CuspSub M a) : Prop :=
  IsLift π P ∧ ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal]
    (τ : SmIrr (GL (Fin a) (v.adicCompletion K))) (T : SmIrr (GL (Fin a) (u.adicCompletion M))), π.IsLocComp v τ → P.IsLocComp u T →
    ∀ (ξ : Fin a → ((v.adicCompletion K)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport τ.ρ (chars ξ hξ) →
      HasSupport T.ρ (chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j))

structure PropsU (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  weak : Weak π ι r

  pol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ

  isWeight : IsWeight π wt

  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    PlainAt π w → (wdOf h hl ι r).mono0 ∧ ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc →
      ∀ σ, π.IsLocComp w σ → wdOf h hl ι r = rc (algNorm σ)

  sizeAway : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    PlainAt π w → ∀ (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
      ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) / 2) < ‖z‖ ∧ ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) / 2)

  weights : ∀ (τ : E →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (ι.toRingHom.comp τ) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), PlainAt π w → GlobalTheory.NarrowPolarizedGalois.AboveN π ι r HT P h Bw hj

def RowU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), PropsU π χ ι r wt HT

def ToralGal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) σ,
      π.IsLocComp w σ →
    ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)),
      HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) →
    ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
      (wdOf h hl ι r).mono0 ∧ ∀ g : Weil h, (wdOf h hl ι r).charPol g = ∏ j, (X - C ((ξ j (a g) : ℂˣ) : ℂ))

def IneOf {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (g n : ℕ) [Fact g.Prime]
    (θ0 : (GaloisField g n)ˣ →* ℂˣ) (P : WD h) : Prop :=
  ∀ (E' : Type) [Field E'] [NumberField E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E' Ω]
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'), ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (red : 𝓞 E' →+* GaloisField g n), Function.Surjective red → RingHom.ker red = w'.asIdeal →
    ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : (GaloisField g n)ˣ), red x = z →
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
      P.inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) = ∏ j ∈ Finset.range n, (X - C ((θ0 (z ^ g ^ j) : ℂˣ) : ℂ))

def IsCuspOf (g n : ℕ) [Fact g.Prime] (θ0 : (GaloisField g n)ˣ →* ℂˣ) (τ : FDRep ℂ (Gn g n)) : Prop :=
  GlobalTheory.Published.IsRegularChar g n θ0 ∧ IsCusp τ.character ∧
    ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : (GaloisField g n)ˣ, aeval (z : GaloisField g n) (y : Mt g n).charpoly = 0 →
      τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ0 (z ^ g ^ j) : ℂˣ) : ℂ)

def DepthZeroIne : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ (θ0 : (GaloisField g n)ˣ →* ℂˣ) (τ : FDRep ℂ (Gn g n)), IsCuspOf g n θ0 τ →
    ∀ σ, π.IsLocComp w σ → GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      IneOf g n θ0 (wdOf h hl ι r)

def CyclicStrongAtCusp : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], IsCyclic (L ≃ₐ[K] L) →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal],
      (∀ u' : HeightOneSpectrum (𝓞 L), u'.under (𝓞 K) = v → u' = u) →
    ∀ (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n), UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : SmIrr (GL (Fin n) (u.adicCompletion L))),
      π.IsLocComp v τ → P.IsLocComp u T → (IrrGL.of τ.ρ τ.smooth τ.irred).IsCusp →
      letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
      ∃ t : u.adicCompletion L ≃ₐ[v.adicCompletion K] u.adicCompletion L,
        orderOf t = Module.finrank K L ∧ GlobalTheory.LBC.IsLBC t τ.ρ T.ρ

structure Inputs : Prop where

  js : GlobalTheory.Published.JacquetShalikaRigidity

  gk : GlobalTheory.Published.GelfandKazhdanDual

  adm : GlobalTheory.Published.IrreducibleAdmissibleGL

  len : GlobalTheory.Published.StandardFunctorsFiniteLength

  exh : GlobalTheory.Published.LanglandsExhaustionGL

  zel : GlobalTheory.Published.ZelevinskyPolynomialRing

  gen : GlobalTheory.Published.GenericUnitaryDualGL

  ac : GlobalTheory.Published.ArthurClozelStrongTC

  acs : GlobalTheory.Published.ArthurClozelStrongSupp

  loc : GlobalTheory.Published.ArthurClozelLocalSC

  hk : GlobalTheory.Published.HeckeLAdicCharacterAbove

  alg : GlobalTheory.Published.AlgebraicCharacterWD

  pst : GlobalTheory.Published.DeRhamPotSemistable

end GlobalTheory.RoadU

end
