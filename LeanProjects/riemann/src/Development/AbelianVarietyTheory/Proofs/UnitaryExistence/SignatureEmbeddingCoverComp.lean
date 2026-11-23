import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.XiDetCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.CoefChangeCompare
open scoped TensorProduct

section Lattices

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

def latHat0 (L0 : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ x i}

def finVec (v : Fin r → E) : Fin r → AdE F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

variable {F}

def gLat (L0 : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Set (Fin r → AdE F E) :=
  g.mulVec '' (latHat0 F L0 : Set (Fin r → AdE F E))

def latG (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat L0 g ∧ w = a • v}

def latGHat (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat L0 g, w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ a) * z i}

def InvSet (AA : Set E) : Prop :=
  ∃ (m : ℕ) (a b : Fin m → E), (∀ i, a i ∈ AA) ∧ (∀ i, ∀ x ∈ AA, ∃ o : 𝓞 E, b i * x = o) ∧ ∑ i, a i * b i = 1

variable (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)

def gLatS (g : Matrix (Fin r) (Fin r) (AdE F E)) : AddSubgroup (Fin r → AdE F E) :=
  (latHat0 F L0).map g.mulVecLin.toAddMonoidHom

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

end Lattices

section Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  [Fact (IsRealIn F E)] {r : ℕ}

def barU : (AdE F E)ˣ →* (AdE F E)ˣ := Units.map (conjA F : AdE F E →ₐ[F] AdE F E).toRingHom.toMonoidHom

def Reads (xi : (AdE F E)ˣ →* ℂˣ) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ x u : (AdE F E)ˣ, (x : AdE F E) = u * conjA F (x : AdE F E) → ((xi u : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)

def TrivFix (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1

def TrivRat (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1

theorem exists_extend {A M : Type} [CommGroup A] [CommGroup M] (Φ : A →* M) (hΦ : Function.Injective Φ) (χ : A →* ℂˣ) :
    ∃ κ : M →* ℂˣ, ∀ x, κ (Φ x) = χ x := by
  letI : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact Units.ne_zero _ hz.symm
    exact ⟨Additive.ofMul (Units.mk0 z hz0), Units.ext hz⟩
  letI : DivisibleBy (Additive ℂˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  exact ⟨MonoidHom.toAdditive.symm ρ, fun x => DFunLike.congr_fun hρ (Additive.ofMul x)⟩

end Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r rk : ℕ}
variable {𝔾 : Type} [Group 𝔾]

section First

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin rk) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin rk → E)) (AA : Set E)

def MarkedBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hr : rk = r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ}
    {lab : Fin g → E →+* ℂ} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) (h γ : 𝔾) : Prop :=
  γ ∈ Γ ∧
    ((U.X (dict h).1).Λ : Set (Fin r → E)) =
      (fun v : Fin rk → E => v ∘ Fin.cast hr.symm) '' (latG L0 AA (fin (γ * h)).1 : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ w ∈ latGHat L0 AA (fin (γ * h)).1,
        finVec F ((φ (dict h).1 (Fu.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (fin (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w

def ModelOf (gram : Matrix (Fin rk) (Fin rk) E) (xi0 : E) (hr : rk = r) (X : Data E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) gram).transpose ∧ X.ξ0 = -xi0

variable {Th : Type} (arch : Th → 𝔾 → Matrix (Fin rk) (Fin rk) ℂ)

open Classical in

def DictBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hr : rk = r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → Th) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((Fu.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (Fu.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (Fu.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = Fu.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fu.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : 𝔾, ∃ γ ∈ Γ,
      ((U.X (dict h).1).Λ : Set (Fin r → E)) =
        (fun v : Fin rk → E => v ∘ Fin.cast hr.symm) '' (latG L0 AA (fin (γ * h)).1 : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        ∃ w ∈ latGHat L0 AA (fin (γ * h)).1,
        finVec F ((φ (dict h).1 (Fu.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (fin (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (arch (th (dict h).1 τ) (γ * h)) * x₀ τ.1

def ValAtMark {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hr : rk = r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ}
    {lab : Fin g → E →+* ℂ} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) (c0 : ℂ) (xi : (AdE F E)ˣ →* ℂˣ)
    (f : Rul Xo c) : Prop :=
  ∀ h γ : 𝔾, MarkedBy Γ fin L0 AA U hr dict ι Fu ik φ h γ →
    rdU U f (dict h).1 (dict h).2 = c0 * ((xi (Matrix.GeneralLinearGroup.det (fin (γ * h))) : ℂˣ) : ℂ)

variable (gram : Matrix (Fin rk) (Fin rk) E) (xi0 : E) (IsInf : (E →+* ℂ) → Th → Prop)

def ValBody {c : Coeff l} (hr : rk = r) (σ0 : c.F →+* ℂ) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E))
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : Tup → (AdE F E)ˣ →* ℂˣ) (c0 : ℂ) : Prop :=
  ∀ t : Tup, IsUnf (U₂ t) ∧ (∀ k, ModelOf gram xi0 hr ((U₂ t).X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (Fu : FamilyUnif (dδ t).Xo₂ ((σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)).comp
          (IntermediateField.inclusion (dδ t).c₂.le).toRingHom)
        (fun j => relab (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) (e j).1))
      (ik : (U₂ t).Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] ((U₂ t).X k).Λ)
      (th : ∀ k, ((U₂ t).X k).Ψ → Th),
      (∀ k τ, IsInf τ.1 (th k τ)) ∧ DictBy Γ fin L0 AA arch (U₂ t) hr (dict₂ t) ι e Fu ik φ th x₀ ∧
      ValAtMark Γ fin L0 AA (U₂ t) hr (dict₂ t) ι Fu ik φ c0 (xi t) (dδ t).cδ

def ValFirst {c : Coeff l} (hr : rk = r) (σ0 : c.F →+* ℂ) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E))
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : Tup → (AdE F E)ˣ →* ℂˣ) : Prop :=
  ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ ValBody Γ fin L0 AA arch gram xi0 IsInf hr σ0 dδ U₂ dict₂ ι x₀ xi c0

end First

section Mark

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)

def embOf (k : U.Comp) : (Fu.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap

def LatTie (F : Type) [Field F] [NumberField F] [Algebra F E] (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)
    (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  InvSet AA ∧ LinearMap.range ι = latG L0 AA (1 : Matrix (Fin r) (Fin r) (AdE F E))

def RatTie (Gm : Matrix (Fin r) (Fin r) E) : Prop :=
  (∀ γ ∈ Γ, ∃ γ₀, IsUnitaryQ Gm γ₀ ∧ (fin γ).1 = γ₀.map (diagE F)) ∧
    ∀ γ₀, IsUnitaryQ Gm γ₀ → ∃ γ ∈ Γ, (fin γ).1 = γ₀.map (diagE F)

variable {L0 AA ι}

end Mark

section Value

variable [Fact (IsRealIn F E)]

def XiValAtC {c : Coeff l} (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) (f : Rul Xo c) : Prop :=
  ∀ (i : Fin Fu.n) (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h → AtClass l Gm ι (φ i) (Fu.t i) h → IsDetRootA h x →
    ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) ty P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → toC (evR Xo c f y) = c0 * ((ξ x : Circle) : ℂ)

variable (Xo) in

def XiValC (c : Coeff l) (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) (f : Rul Xo c) : Prop :=
  r = Dw.p + Dw.q ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)),
    AllMarked F Gm ξ0 ι Fu φ ∧ XiValAtC c0 Gm ι ξ σ Fu φ f

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) {L0 : Submodule (𝓞 E) (Fin r → E)} {AA : Set E}
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
  (ψ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E))

def FinTie (Gm : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ h : 𝔾, IsUnitaryA Gm (fin h).1 ∧ ∃ x, IsDetRootA (fin h).1 x

def OverPeriods : Prop :=
  ∀ h : 𝔾, ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (P : (Fu.Di (ik (dict h).1)).La →+ (Fin g → ℂ)),
    IsPeriod (Fu.Di (ik (dict h).1)) lab P ∧ (U.un (dict h).1 ⟨(dict h).2, hx⟩).x = Fu.u (ik (dict h).1) P

def Reaches (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ (i : Fin Fu.n) (gm : Matrix (Fin r) (Fin r) (AdE F E)), IsUnitaryA Gm gm → LatAt ι (ψ i) gm →
    MarkAt l ι (ψ i) (Fu.t i) gm → ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) lab P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → ∃ h : 𝔾, (fin h).1 = gm ∧ ik (dict h).1 = i ∧
        ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un (dict h).1 ⟨(dict h).2, hx⟩) y

variable {Γ fin U dict Fu ik φ ψ} {Gm : Matrix (Fin r) (Fin r) E} {xi : (AdE F E)ˣ →* ℂˣ} {ξ : (AdE F E)ˣ →* Circle}
  {c0 : ℂ} {f : Rul Xo c}

end Value

section Covers

variable [Fact (IsRealIn F E)] (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E))
  (AA : Set E) {Th : Type} (arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ) (IsInf : (E →+* ℂ) → Th → Prop)

def DictOnto {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Gm : Matrix (Fin r) (Fin r) E) : Prop :=
  (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) ∧ (∀ k, ∃ h, (dict h).1 = k) ∧
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → Th),
    (∀ k τ, IsInf τ.1 (th k τ)) → DictBy Γ fin L0 AA arch U rfl dict ι e Fu ik φ th x₀ →
      Function.Bijective ik ∧ ∀ ψ, (∀ k, ψ (ik k) = embOf U Fu ik φ k) → Reaches fin U dict Fu ik ψ Gm ι

variable {Γ fin L0 AA arch IsInf} {gram : Matrix (Fin r) (Fin r) E} {xi0 : E}

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} {dict : 𝔾 → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin Fu.n} {φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ} {th : ∀ k, (U.X k).Ψ → Th}

end One

variable {c : Coeff l} {σ0 : c.F →+* ℂ} {Tup : Type*} {dδ : Tup → DeltaDat Xo c n}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle} {c0 : ℂ}

end Covers

section Comparison₂

section Act

variable (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))

def actFirst (g : G) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
    levActR (Xo := Xo) (c := c) lev g' y y') g

def ActFirst : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g' y y')

variable {c} {c' : Coeff l} (hle : c.F ≤ c'.F)

end Act

variable (Γ : Subgroup 𝔾)

def adelFn {Comp : Type} {X : Comp → Data E r} (dict : 𝔾 → Σ k, Frame (X k).Ψ r) (mu : 𝔾 → ℂ) (P : FDSec X) : 𝔾 → ℂ :=
  fun g => mu g * P (dict g).1 (dict g).2

def jOnQ {Comp : Type} {X : Comp → Data E r} {C : Type} (rd : C → FDSec X) (dict : 𝔾 → Σ k, Frame (X k).Ψ r) (mu : 𝔾 → ℂ)
    (f : C) : Quotient (QuotientGroup.rightRel Γ) → ℂ := fun q => adelFn dict mu (rd f) q.out

variable (Xo) in

def IsSumDown (c : Coeff l) {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]
    (dδ : DeltaDat Xo c n) (w : Cl → (Fin n → LevQ Dw dδ.l₂) → c.F) (La : Cl → GenLat E n) (Nc : Cl → ℕ)
    (gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : Cl → Vs)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k],
    (∀ a : c.F, algebraMap dδ.c₂.F k (dδ.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y →
      ∃ vc : Cl → k, (∀ cl, ShortValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w cl q)) (La cl) 1 (Nc cl)
          (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (io (x cl))) y₂ (vc cl)) ∧
        evR Xo c f y = evR dδ.Xo₂ dδ.c₂ dδ.cδ y₂ *
          ∑ cl, algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) * vc cl

variable (Xo) in

def RowFirst (c : Coeff l) {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] {σ0 : c.F →+* ℂ} (U : Unf Xo c σ0 r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c.F) (ep : ∀ t, Cl' t → c.F) (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
    (LL : IntermediateField ℚ ℂ) (Cu : Submodule c.F (Rul Xo c)) (cst : U.Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cst k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z : G, z ∈ Subgroup.center G ∧
    ∀ t : Tup, ∃ ze : ℂ, ze ∈ LL ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      (∃ f ∈ Cu, IsSumDown Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f) ∧
      (∀ f ∈ sec Xo c a n, IsSumDown Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f →
        ∀ q : Quotient (QuotientGroup.rightRel Γ), ph * thAd t x q =
          ze * cst (dict q.out).1 * (lieFac Dw xr a : ℂ) * jOnQ Γ (rdU U) dict mu (act z f) q)

variable {c c' : Coeff l} (hle : c.F ≤ c'.F) {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

def TieFirst (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    (dict : 𝔾 → Σ k, Frame ((unifExt hle U σ0').X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c)
    (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F) (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
    (cst : (unifExt hle U σ0').Comp → ℂ) (ph : ℂ) : Prop :=
  LL ≤ c'.F ∧ CuspSums hle U ∧ ActSums hle act act' ∧
    RowFirst Xo Γ c' (unifExt hle U σ0') dict mu xr a act' dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unifExt hle U) a n) cst ph

variable (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
  (dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
  (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)] (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F)
  (La : ∀ t, Cl' t → GenLat E n) (Nc gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F)
  (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
  (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
  (cst : (U (sig0 c)).Comp → ℂ) (ph : ℂ)

end Comparison₂

section Whole

variable [Fact (IsRealIn F E)] {Γ : Subgroup 𝔾} {fin : 𝔾 →* GL (Fin r) (AdE F E)} {L0 : Submodule (𝓞 E) (Fin r → E)}
  {AA : Set E} {Th : Type} {arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ} {IsInf : (E →+* ℂ) → Th → Prop}
  {gram : Matrix (Fin r) (Fin r) E} {xi0 : E} {c c' : Coeff l} {hle : c.F ≤ c'.F} {Vs : Type} [AddCommGroup Vs]
  [Module c'.F Vs] {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
  {dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r} {mu : 𝔾 → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)} {Tup : Type*} {dδ : Tup → DeltaDat Xo c' n}
  {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)] {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F}
  {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F}
  {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop}
  {cst : (U (sig0 c)).Comp → ℂ} {ph : ℂ}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ ((sig0 c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle}

def CoverFirst (dδ : Tup → DeltaDat Xo c' n) : Prop :=
  ∀ t, (dδ t).IsLev ∧ (dδ t).l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab (dδ t).Xo₂ (dδ t).c₂ (dδ t).nab₂

end Whole

end GlobalTheory.XiDetCompare
