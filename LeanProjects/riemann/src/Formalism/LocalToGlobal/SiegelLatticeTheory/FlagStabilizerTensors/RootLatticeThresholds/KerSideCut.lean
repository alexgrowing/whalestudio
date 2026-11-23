import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfHypotheses

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.ProjRows Formalism.L2.SG.KerJoinS Formalism.IndefR.Cx Formalism.L2.Indef

namespace Formalism.L2.SG.KerSideCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Chain

theorem chainOpM_add' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (f g : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (f + g) = Formalism.ThetaLiftIndependence.chainOpM w Km m f + Formalism.ThetaLiftIndependence.chainOpM w Km m g := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.sum_add_distrib, smul_add, map_add]

theorem chainOpM_smul' {Rg : Type} [CommSemiring Rg] {ι : ℕ → Type} [∀ j, Fintype (ι j)]
    {M : ℕ → Type} [∀ j, AddCommMonoid (M j)] [∀ j, Module Rg (M j)]
    (w : ∀ j, ι j → Rg) (Km : ∀ j, ι j → ι (j + 1) → (M j →ₗ[Rg] M (j + 1))) (m : ℕ) (c : Rg) (f : ι 0 → M 0) :
    Formalism.ThetaLiftIndependence.chainOpM w Km m (c • f) = c • Formalism.ThetaLiftIndependence.chainOpM w Km m f := by
  induction m with
  | zero => first | rfl | simp [Formalism.ThetaLiftIndependence.chainOpM]
  | succ m ih =>
    simp only [Formalism.ThetaLiftIndependence.chainOpM, ih]
    funext t
    simp [Formalism.ThetaLiftIndependence.kerOpM, Finset.smul_sum, map_smul, smul_smul, mul_comm]

def colL {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) :
    (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls R.m → C.Y R.m → ℂ) where
  toFun := C.col
  map_add' f g := chainOpM_add' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m f g
  map_smul' c f := chainOpM_smul' (ι := C.cls) (M := fun j => C.Y j → ℂ) C.wt C.Kmap R.m c f

def perColL (D : D7) (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] D.what₂.Amb D.what₂.mu0 →ₗ[ℂ] ℂ :=
  ((D.mem u).P.period ∘ₗ (D.mem u).P.lowerMap ∘ₗ (D.mem u).P.evz ∘ₗ colL (D.mem u).C ∘ₗ
    (D.mem u).A.Mram.subtype ∘ₗ (D.eMu u).toLinearMap).compl₂ (D.eMt u).symm.toLinearMap

theorem perColL_apply (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F : D.what₂.Amb D.what₂.mu0) :
    perColL D u φ F = D.what₂.perCol u D.what₂.mu0 φ F := by
  rw [D.perCol_base_eq_PtilCol]
  simp only [perColL, LinearMap.compl₂_apply, LinearMap.comp_apply, PeriodMap.PtilCol, PeriodMap.Ptil]
  rfl

end Chain

section Read

variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₗ[ℂ] P.EE)

def ChainTie : Prop :=
  ∀ u (x : Fin ((fc P.zs).Dc.a (m u)) → K) (y : Fin ((fc P.zs).Df1.nV Bs.μ0) → K),
    D.what₂.perCol u D.what₂.mu0 ((cφ u).symm (cpt Bs.v0.embedding x)) (cF (cpt Bs.v0.embedding y)) =
      Bs.v0.embedding ((fc P.zs).Dc.Pt (m u) Bs.μ0 x y)

def GoodPartHasComplexCoordinates : Prop := D.what₂.V0 D.what₂.mu0 ≤ LinearMap.range cF

def RowTie : Prop :=
  (∀ F, eR F ∈ P.EEl true) ∧ (∀ e ∈ P.EEl true, ∃ F, eR F = e) ∧ (∃ c : ℝ, 0 < c ∧ ∀ F, ‖eR F‖ = c * ‖F‖) ∧
    ∀ y : Fin ((fc P.zs).Df1.nV Bs.μ0) → K,
      P.Θ Bs.μ0 (P.jR Bs.μ0 (eV Bs.μ0 y)) = eR (D.what₂.iota D.what₂.mu0 (cF (cpt Bs.v0.embedding y)))

def ColNorm : Prop :=
  ∀ u, ∃ c : ℝ, 0 < c ∧ ∀ φ : D.what₂.Mu u, Formalism.DivisionValues.fnorm ((fc P.zs).Dc.Xc (m u) Bs.v0) (cφ u φ) = c * ‖φ‖

def PairTie : Prop :=
  ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu X u hK),
    colDictL X (Tr u) hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
      ⟪sEE (eR F), (fc P.zs).Sp.Pu (m u) (cφ u φ)⟫_ℂ =
        κ * ⟪((conjHH X G (j F) : HHX X) : L2X X), PuFun X u hK (Dt u) T⟫_ℂ

end Read

end Formalism.L2.SG.KerSideCut
