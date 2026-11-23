import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev OA (D : D7) : Subring (EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

abbrev inc (D : D7) : D.host.E →+* EAf D := Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)

abbrev cjA (D : D7) : EAf D →+* EAf D := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)

abbrev Lat (V : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)

def hat {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → EAf D) :=
  {y | y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ}

def hA (V : HSp D) (x y : Fin V.rank → EAf D) : EAf D :=
  Formalism.UG.hform (cjA D) (V.gram.map (inc D)) y x

def vA (V : HSp D) (z : V.V) : Fin V.rank → EAf D := fun i => inc D (Formalism.L2.Herm.crd V z i)

def mA (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) : Matrix (Fin Y.rank) (Fin X.rank) (EAf D) :=
  (frameMat Y X ι).map (inc D)

def IsPlIdem (w : Pl D.host.E) (e : EAf D) : Prop :=
  ∃ he : e ∈ OA D, e * e = e ∧ resS D.host.F w ⟨e, he⟩ = 1 ∧
    ∀ w' : Pl D.host.E, w' ≠ w → resS D.host.F w' ⟨e, he⟩ = 0

def InCmp {n : ℕ} (e : EAf D) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Fin n → EAf D) : Prop :=
  y ∈ hat Λ ∧ e • y = y

def IsSplitSet (S : Finset (Pl D.host.E)) : Prop := ∀ w ∈ S, ∀ w' ∈ S, ¬ IsConjPl w w'

def IsBasisAt (V : HSp D) (w : Pl D.host.E) (Λ : Lat V) {n : ℕ} (B : Matrix (Fin V.rank) (Fin n) (EAf D)) : Prop :=
  n = V.rank ∧ ∃ e, IsPlIdem w e ∧ e • B = B ∧
    ∀ y, InCmp e Λ y ↔ ∃ c : Fin n → OA D, y = B *ᵥ fun i => (c i : EAf D)

def IsVecBasisAt (V : HSp D) (w : Pl D.host.E) (B : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) : Prop :=
  ∃ e, IsPlIdem w e ∧ e • B = B ∧ ∃ C : Matrix (Fin V.rank) (Fin V.rank) (EAf D),
    B * C = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D))

def IsAdIsom (W Y : HSp D) (x : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)) : Prop :=
  Function.Bijective (x.mulVec : (Fin W.rank → EAf D) → (Fin Y.rank → EAf D)) ∧
    ∀ a b, hA Y (x *ᵥ a) (x *ᵥ b) = hA W a b

def IsTransport (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)) {n : ℕ}
    (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D))
    (x : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)) : Prop :=
  IsAdIsom W Y x ∧ (∀ a, a ∈ hat L ↔ x *ᵥ a ∈ hat Λ) ∧ ∀ w ∈ S, x * be w = be' w

def InStabAway (W : HSp D) (L : Lat W) (S : Finset (Pl D.host.E)) (k : GL (Fin W.rank) (EAf D)) : Prop :=
  k ∈ Formalism.UG.levelAfL D.sp.cm.sig W.gram L ∧
    ∀ w ∈ S, Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) (w.under (𝓞 D.host.F))) k = 1

def PlIdemSt (D : D7) : Prop := ∀ w : Pl D.host.E, ∃! e : EAf D, IsPlIdem w e

def TransportSt (D : D7) : Prop :=
  ∀ (W Y : HSp D), W.rank = Y.rank → ∀ (L : Lat W) (Λ : Lat Y), IsSelfDualC W L → IsSelfDualC Y Λ →
    ∀ S : Finset (Pl D.host.E), IsSplitSet S → ∀ (n : ℕ)
      (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)),
      (∀ w ∈ S, IsBasisAt W w L (be w)) → (∀ w ∈ S, IsBasisAt Y w Λ (be' w)) →
      (∃ x, IsTransport W Y L Λ S be be' x) ∧
      ∀ x, IsTransport W Y L Λ S be be' x → ∀ x',
        IsTransport W Y L Λ S be be' x' ↔
          ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D))

def CorrectionSt (D : D7) : Prop :=
  ∀ (Y Y' : HSp D) (io : Y.V ≃ₗ[D.host.E] Y'.V), HSpace.IsIsomEmb Y Y' io.toLinearMap →
    ∀ (Λ : Lat Y) (Λ' : Lat Y'), IsSelfDualC Y Λ → IsSelfDualC Y' Λ' →
    ∀ S : Finset (Pl D.host.E), IsSplitSet S → ∀ (n : ℕ)
      (be : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y'.rank) (Fin n) (EAf D)),
      (∀ w ∈ S, IsBasisAt Y w Λ (be w)) → (∀ w ∈ S, IsBasisAt Y' w Λ' (be' w)) →
      ∃ k ∈ GfC Y', IsTransport Y Y' Λ Λ' S be be'
        (HMul.hMul ((finE Y' k).1 : Matrix (Fin Y'.rank) (Fin Y'.rank) (EAf D)) (mA Y' Y io.toLinearMap))

def SplitGlueSt (D : D7) : Prop :=
  ∀ (V : HSp D) (Λ₀ : Lat V), IsSelfDualC V Λ₀ → ∀ S : Finset (Pl D.host.E), IsSplitSet S →
    ∀ B : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) (EAf D), (∀ w ∈ S, IsVecBasisAt V w (B w)) →
      ∃! Λ : Lat V, IsSelfDualC V Λ ∧ (∀ w ∈ S, IsBasisAt V w Λ (B w)) ∧
        ∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ S, w.under (𝓞 D.host.F) ≠ v) →
          Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ₀

def ImageSt (D : D7) : Prop :=
  ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ d ∈ GfC V,
    (∃ Λ' : Lat V, Submodule.IsLattice D.host.E Λ' ∧ Formalism.L2.Herm.Carries (finE V d) Λ Λ') ∧
    ∀ Λ' : Lat V, Submodule.IsLattice D.host.E Λ' → Formalism.L2.Herm.Carries (finE V d) Λ Λ' → IsSelfDualC V Λ'

def RationalSt (D : D7) : Prop :=
  ∀ W Y : HSp D, W.SigOK → Y.SigOK → W.rank = Y.rank → (∀ τ, W.sig τ = Y.sig τ) →
    ∃ φ : W.V ≃ₗ[D.host.E] Y.V, HSpace.IsIsomEmb W Y φ.toLinearMap

structure IsDec (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (c : D.host.E)
    (e f : Fin ρ → Y.V) : Prop where
  isom : HSpace.IsIsomEmb X Y ι
  a_le : a ≤ 1
  rank : Y.rank = X.rank + a + 2 * ρ
  z_norm : ∀ i, Y.hD (z i) (z i) = c
  z_X : ∀ i x, Y.hD (ι x) (z i) = 0
  ee : ∀ i j, Y.hD (e i) (e j) = 0
  ff : ∀ i j, Y.hD (f i) (f j) = 0
  ef : ∀ i j, Y.hD (e i) (f j) = if i = j then 1 else 0
  hyp_X : ∀ i x, Y.hD (ι x) (e i) = 0 ∧ Y.hD (ι x) (f i) = 0
  hyperbolicDecomp_hyp_orthogonal_line : ∀ i j, Y.hD (z j) (e i) = 0 ∧ Y.hD (z j) (f i) = 0

abbrev Tu (D : D7) (u : D.what₂.Word) : D.host.E := ((D.mem u).A.T : D.host.E)

def IsPi (u : D.what₂.Word) (π : 𝓞 D.host.E) : Prop :=
  (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * star (π : D.host.E) = Tu D u

def StdIsomSt (D : D7) : Prop :=
  ∀ u : D.what₂.Word, (∃ π, IsPi u π) ∧ ∀ π, IsPi u π → ∀ (s : ℤˣ) (a ρ : ℕ)
    (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Fin a → Y.V) (e f : Fin ρ → Y.V)
    (Y' X' : HSp D) (ι' : X'.V →ₗ[D.host.E] Y'.V) (z' : Fin a → Y'.V) (e' f' : Fin ρ → Y'.V),
    IsDec Y X ι z (((s : ℤ) : D.host.E) * Tu D u) e f → IsDec Y' X' ι' z' ((s : ℤ) : D.host.E) e' f' →
    X.SigOK → X'.SigOK → X.IsPosDef → X'.IsPosDef → X.rank = X'.rank →
    ∃ (φ : X.V ≃ₗ[D.host.E] X'.V) (io : Y.V ≃ₗ[D.host.E] Y'.V),
      HSpace.IsIsomEmb X X' φ.toLinearMap ∧ HSpace.IsIsomEmb Y Y' io.toLinearMap ∧
      (∀ x, io (ι x) = ι' (φ x)) ∧ (∀ i, io (z i) = (π : D.host.E) • z' i) ∧ ∀ i, io (e i) = e' i ∧ io (f i) = f' i

def RecordDecSt (D : D7) : Prop :=
  (∀ u, IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => D.zmOf u) (-Tu D u) D.sp.hypE D.sp.hypF) ∧
  ∃ z' : (D.sp.Y 0).V, IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => z') (-1) D.sp.hypE D.sp.hypF

section Flat

variable (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)

def flatSp : Submodule D.host.E Y.V := LinearMap.range ι ⊔ Submodule.span D.host.E {z}

def IsSDIn (U : Submodule D.host.E Y.V) (L : Submodule (𝓞 D.host.E) Y.V) : Prop :=
  L.FG ∧ Submodule.span D.host.E (L : Set Y.V) = U ∧
    ∀ y ∈ U, y ∈ L ↔ ∀ x ∈ L, Y.hD x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def IsPrim (L : Submodule (𝓞 D.host.E) Y.V) : Prop :=
  ∀ a : D.host.E, a • z ∈ L ↔ a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def capX (L : Submodule (𝓞 D.host.E) Y.V) : Lat X :=
  Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))

def IsBasePair (u : D.what₂.Word) (π : 𝓞 D.host.E) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D) : Prop :=
  Submodule.IsLattice D.host.E L₀ ∧
  (∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal →
    ∀ y, InCmp e L₀ y ↔ InCmp e (Formalism.L2.Herm.dualL D.sp.cm X L₀) y) ∧
  ∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → π ∈ w.asIdeal →
    e • f₀ w = f₀ w ∧ inc D (Tu D u) • f₀ w ∈ hat L₀ ∧ f₀ w ∉ hat L₀ ∧
    ∀ y, InCmp (cjA D e) L₀ y ↔
      cjA D e • y = y ∧ (∀ x, InCmp e L₀ x → hA X x y ∈ OA D) ∧ hA X (f₀ w) y ∈ OA D

def IsGlued (u : D.what₂.Word) (π : 𝓞 D.host.E) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D)
    (L : Submodule (𝓞 D.host.E) Y.V) : Prop :=
  L.FG ∧
  (∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal →
    ∀ y, InCmp e (Formalism.L2.Herm.crdLat Y L) y ↔
      ∃ x, InCmp e L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * e) • vA Y z) ∧
  ∀ (w : Pl D.host.E) (e : EAf D), IsPlIdem w e → π ∈ w.asIdeal →
    (∀ y, InCmp e (Formalism.L2.Herm.crdLat Y L) y ↔
      ∃ x, InCmp e L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * e) • vA Y z + mA Y X ι *ᵥ f₀ w)) ∧
    ∀ y, InCmp (cjA D e) (Formalism.L2.Herm.crdLat Y L) y ↔
      cjA D e • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp e (Formalism.L2.Herm.crdLat Y L) y' → hA Y y' y ∈ OA D

def lamN {ρ : ℕ} (e f : Fin ρ → Y.V) (L : Submodule (𝓞 D.host.E) Y.V)
    (nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) Y.V :=
  (⨆ i : Fin ρ, ((nn ^ (ρ - i.val) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E).map
      ((LinearMap.toSpanSingleton D.host.E Y.V (e i)).restrictScalars (𝓞 D.host.E))) ⊔ L ⊔
  ⨆ i : Fin ρ, (((nn ^ (ρ - i.val))⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E).map
      ((LinearMap.toSpanSingleton D.host.E Y.V (f i)).restrictScalars (𝓞 D.host.E))

end Flat

def IsLine (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (u : D.what₂.Word) : Prop :=
  HSpace.IsIsomEmb X Y ι ∧ (∀ x, Y.hD (ι x) z = 0) ∧ Y.hD z z = -Tu D u

def GluedSt (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D), IsBasePair X u π L₀ f₀ →
      (∃! L, IsGlued Y X ι z u π L₀ f₀ L) ∧
      ∀ L, IsGlued Y X ι z u π L₀ f₀ L → IsSDIn Y (flatSp Y X ι z) L ∧ IsPrim Y z L ∧ capX Y X ι L = L₀

def UngluedSt (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L →
      ∃ f₀, IsBasePair X u π (capX Y X ι L) f₀ ∧ IsGlued Y X ι z u π (capX Y X ι L) f₀ L

def IsCStable (nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Prop :=
  nn ≠ 0 ∧ ∀ x : D.host.E, x ∈ nn ↔ star x ∈ nn

def LamNSt (D : D7) : Prop :=
  (∀ (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V),
    IsDec Y X ι (fun _ : Fin 1 => z) (-Tu D u) e f → ∀ L, IsSDIn Y (flatSp Y X ι z) L →
      ∀ nn, IsCStable nn → IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (lamN Y e f L nn))) ∧
  IsCStable ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧
  IsCStable (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ *
    D.host.AA * D.host.AAbar)

def FrameSt (D : D7) : Prop :=
  (∀ (V : HSp D) (N : ℕ), ∃ β Λ, IsSDFrame V β Λ N) ∧
  ∀ (V : HSp D) (Λ : Lat V) (N c : ℕ), IsSelfDualC V Λ → 0 < N →
    (∀ x ∈ L0c D V, ((N ^ c : ℕ) : D.host.E) • x ∈ Λ) → (∀ x ∈ Λ, ((N ^ c : ℕ) : D.host.E) • x ∈ L0c D V) →
    ∀ S : Finset (Pl D.host.E), IsSplitSet S → ∀ be : Pl D.host.E → Matrix (Fin V.rank) (Fin V.rank) (EAf D),
      (∀ w ∈ S, IsBasisAt V w Λ (be w)) →
      ∃ β, IsSDFrame V β Λ N ∧ ∀ w ∈ S, ∀ e, IsPlIdem w e →
        e • (β.1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) = be w

def AdelicIsometries (D : D7) : Prop :=
  PlIdemSt D ∧ TransportSt D ∧ CorrectionSt D ∧ SplitGlueSt D ∧ ImageSt D ∧ RationalSt D ∧ StdIsomSt D ∧ RecordDecSt D ∧
    GluedSt D ∧ UngluedSt D ∧ LamNSt D ∧ FrameSt D

example (h : AdelicIsometries D) :
    (∀ j, ∃ β Λ, IsSDFrame (Yc D j) β Λ (D.host.g 0 * D.host.g 1)) ∧ (∃ β Λ, IsSDFrame D.sp.X' β Λ 1) ∧
      (∀ i, ∃ β Λ, IsSDFrame (Vc D i) β Λ 1) ∧ ∀ i, ∃ β Λ, IsSDFrame (Wc D i) β Λ 1 :=
  have hf := h.2.2.2.2.2.2.2.2.2.2.2.1
  ⟨fun _ => hf _ _, hf _ _, fun _ => hf _ _, fun _ => hf _ _⟩

example (V : HSp D) (L : Lat V) (S : Finset (Pl D.host.E)) {n : ℕ}
    (be : Pl D.host.E → Matrix (Fin V.rank) (Fin n) (EAf D)) : IsTransport V V L L S be be 1 := by
  refine ⟨⟨?_, fun a b => by simp⟩, fun a => by simp, fun w _ => by simp⟩
  have : ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)).mulVec) = id := by funext a; simp
  rw [this]; exact Function.bijective_id

end GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

end
