import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.DoubleCosetMeasures.StatementV

noncomputable section

namespace Formalism.MainNotions.ZetaProductPairs

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Loc (D : D7) (T : ThetaX D) where

  gl1 : D.what₂.Word → T.Gf (D.sp.Y 0)

  glSym : D.what₂.Word → T.Gf (D.sp.Y 0)

  ArchDat : D.what₂.Word → Type
  ArchDat_ne : ∀ u, Nonempty (ArchDat u)

  ellT : ∀ u, ArchDat u → ℂ

  Au : ∀ u, ArchDat u → ℂ

  B0 : ∀ u, D.what₂.Mu u →ₗ[ℂ] D.what₂.EE →ₗ[ℂ] ℂ

  zeX : D.what₂.Word → D.what₂.Tup → ℂ

  zeta_at_base_tuple : ∀ u, zeX u D.what₂.mu0 = 1

  zeX_fin : ∀ u μ, ∃ n : ℕ, 0 < n ∧ zeX u μ ^ n = 1

variable {D : D7}

def FFTStable (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ φ ∈ (D.mem u).A.Mram, Formalism.MainNotions.product_first_zeroth_parts.FFall D u 0 φ ∈ (D.mem u).A.Mram

def FFTm (u : D.what₂.Word) (h : FFTStable D u) : Module.End ℂ (D.what₂.Mu u) :=
  (D.eMu u).symm.toLinearMap ∘ₗ (Formalism.MainNotions.product_first_zeroth_parts.FFall D u 0).restrict h ∘ₗ (D.eMu u).toLinearMap

def FFTScalarUnitary (u : D.what₂.Word) (h : FFTStable D u) : Prop :=
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x y : D.what₂.Mu u,
    inner ℂ (FFTm u h x) (FFTm u h y) = ((‖κ‖ ^ 2 : ℝ) : ℂ) * inner ℂ x y

def HeckeOperatorScalarUnitary (D : D7) : Prop := ∀ u : D.what₂.Word, ∃ h : FFTStable D u, FFTScalarUnitary u h

def diaAll (D : D7) (u : D.what₂.Word) (c : ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) :
    Formalism.MainNotions.product_first_zeroth_parts.Fn D u 0 →ₗ[ℂ] Formalism.MainNotions.product_first_zeroth_parts.Fn D u 0 :=
  (Finset.univ : Finset (D.mem u).A.vT).toList.foldr
    (fun v g => (Formalism.MainNotions.product_first_zeroth_parts.dia D u 0 v (c v)).comp g) LinearMap.id

def FFc (D : D7) (u : D.what₂.Word) (c : ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) :
    Formalism.MainNotions.product_first_zeroth_parts.Fn D u 0 →ₗ[ℂ] Formalism.MainNotions.product_first_zeroth_parts.Fn D u 0 :=
  diaAll D u c ∘ₗ Formalism.MainNotions.product_first_zeroth_parts.FFall D u 0

def FFStable (D : D7) (u : D.what₂.Word) :=
  {c : ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ //
    ∀ φ ∈ (D.mem u).A.Mram, FFc D u c φ ∈ (D.mem u).A.Mram}

def FFm (u : D.what₂.Word) (h : FFStable D u) : Module.End ℂ (D.what₂.Mu u) :=
  (D.eMu u).symm.toLinearMap ∘ₗ (FFc D u h.1).restrict h.2 ∘ₗ (D.eMu u).toLinearMap

def FFScalarUnitary (u : D.what₂.Word) (h : FFStable D u) : Prop :=
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x y : D.what₂.Mu u,
    inner ℂ (FFm u h x) (FFm u h y) = ((‖κ‖ ^ 2 : ℝ) : ℂ) * inner ℂ x y

def suPrimes (D : D7) (u : D.what₂.Word) : Finset ℕ :=
  insert (D.mem u).A.T (insert (D.host.g 0) (insert (D.host.g 1) (D.host.small ∪ (insert D.host.q
    (Ideal.absNorm D.host.ccK).primeFactors))))

def SuShape (D : D7) (u : D.what₂.Word) (s : ℂ) : Prop :=
  ∃ (e : ℕ → ℤ) (z : ℂ) (c : ℕ → ℂ), ‖z‖ = 1 ∧ (∀ j, c j ≠ 0) ∧
    s = ((∏ p ∈ suPrimes D u, ((p : ℝ) ^ ((e p : ℝ) / 2)) : ℝ) : ℂ) * z * (∏ j ∈ Finset.Icc 1 D.R.m, c j)⁻¹

theorem suShape_ne_zero {D : D7} (u : D.what₂.Word) (s : ℂ) (h : SuShape D u s) : s ≠ 0 := by
  obtain ⟨e, z, c, hz, hc, rfl⟩ := h
  have hpos : ∀ p ∈ suPrimes D u, 0 < p := by
    intro p hp
    simp only [suPrimes, Finset.mem_insert, Finset.mem_union] at hp
    rcases hp with h | h | h | h | h | h
    · rw [h]; exact (D.mem u).A.T_prime.pos
    · rw [h]; exact (D.host.g_prime 0).pos
    · rw [h]; exact (D.host.g_prime 1).pos
    · exact (Nat.prime_of_mem_primeFactors h).pos
    · rw [h]; exact lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.1
    · exact (Nat.prime_of_mem_primeFactors h).pos
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · rw [Complex.ofReal_ne_zero, Finset.prod_ne_zero_iff]
    intro p hp
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hpos p hp) _).ne'
  · intro h0
    rw [h0, norm_zero] at hz
    exact zero_ne_one hz
  · exact inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hc j)

variable {T : ThetaX D}

def MatrixIdentityOffBase (X : Loc D T) (u : D.what₂.Word) (h : FFStable D u) (s : ℂ) : Prop :=
  ∀ (da : X.ArchDat u) (μ : D.what₂.Tup) (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ,
    X.zeX u μ * X.ellT u da * X.B0 u (FFm u h φ) (D.what₂.iota μ F) =
      s⁻¹ * X.Au u da * D.what₂.perCol u μ φ F

def MI (X : Loc D T) (u : D.what₂.Word) (h : FFStable D u) (s : ℂ) : Prop :=
  ∀ c : ℂ, c ≠ 0 → (∀ da, X.Au u da = c * X.ellT u da) → (∃ da, X.ellT u da ≠ 0) →
    ∀ (μ : D.what₂.Tup) (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ,
      D.what₂.perCol u μ φ F =
        X.zeX u μ * ((c * s⁻¹)⁻¹ * X.B0 u (FFm u h φ) (D.what₂.iota μ F))

def UnfoldingScalarUnitary (X : Loc D T) : Prop :=
  ∀ u : D.what₂.Word, ∃ h : FFStable D u, FFScalarUnitary u h ∧ ∃ s : ℂ, SuShape D u s ∧ MatrixIdentityOffBase X u h s

def RealConstantNonvanishing (X : Loc D T) : Prop :=
  ∀ u, ∃ c : ℂ, c ≠ 0 ∧ (∀ da, X.Au u da = c * X.ellT u da) ∧ ∃ da, X.ellT u da ≠ 0

def MultiplicityOneExplicit (X : Loc D T) : Prop :=
  ∀ u : D.what₂.Word, ∃ h : FFStable D u, FFScalarUnitary u h ∧
    ∃ s c : ℂ, SuShape D u s ∧ c ≠ 0 ∧ (∀ da, X.Au u da = c * X.ellT u da) ∧
      ∀ (μ : D.what₂.Tup) (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ,
        D.what₂.perCol u μ φ F =
          X.zeX u μ * ((c * s⁻¹)⁻¹ * X.B0 u (FFm u h φ) (D.what₂.iota μ F))

def MultiplicityOneConditional (X : Loc D T) : Prop :=
  ∀ u : D.what₂.Word, ∃ h : FFStable D u, FFScalarUnitary u h ∧
    ∃ s : ℂ, SuShape D u s ∧ MatrixIdentityOffBase X u h s ∧ MI X u h s

def ZeDef (X : Loc D T) : Prop := ∀ u μ, D.what₂.zeC u μ = X.zeX u μ

def MultiplicityOneWithZeta (X : Loc D T) : Prop :=
  Rows.BuDefQ D.what₂ → ZeDef X → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ →
  ∀ u : D.what₂.Word, ∃ h : FFStable D u, FFScalarUnitary u h ∧
    (∀ μ : D.what₂.Tup, ∃ n : ℕ, 0 < n ∧ D.what₂.zeC u μ ^ n = 1) ∧
    ∃ s : ℂ, SuShape D u s ∧
    ∀ c : ℂ, c ≠ 0 → (∀ da, X.Au u da = c * X.ellT u da) → (∃ da, X.ellT u da ≠ 0) →
      (∀ (φ : D.what₂.Mu u) (F : D.what₂.EE),
        D.what₂.Bu u φ F = (c * s⁻¹)⁻¹ * X.B0 u (FFm u h φ) F) ∧
      ∀ (μ : D.what₂.Tup) (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ,
        D.what₂.perCol u μ φ F = D.what₂.zeC u μ * D.what₂.Bu u φ (D.what₂.iota μ F)

def bPer (T : ThetaX D) (u : D.what₂.Word) (p : T.Pos (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0))
    (g : T.Gf (D.sp.Y 0)) (φ : D.what₂.Mu u) (F : D.what₂.EE) : ℂ :=
  T.Bper (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) p 0
    (T.conjAF _ ((T.colAF u D.what₂.mu0 0 φ : T.cusp (D.sp.X 0)) : T.AF (D.sp.X 0)))
    ⟨T.actF _ g ((T.rowAF D.what₂.mu0 0 ((D.what₂.multZero D.what₂.mu0).symm F) : T.cusp (D.sp.Y 0)) :
        T.AF (D.sp.Y 0)),
      T.actF_cusp _ g _ (T.rowAF D.what₂.mu0 0 ((D.what₂.multZero D.what₂.mu0).symm F)).2⟩

def RealTr (T : ThetaX D) (V : TH.HSp D) : Submonoid (Module.End ℂ (T.AF V)) :=
  Submonoid.closure {R | ∃ τ, ∃ h ∈ Formalism.QuantumDeterminants.UH (TH.gramAt D V τ), R = T.actR V τ h}

def KernelFromExponentialTwist (X : Loc D T) : Prop :=
  ∀ u, ∃ bes : Module.End ℂ (T.AF (D.sp.X 0)) → Module.End ℂ (T.AF (D.sp.Y 0)) → ℂ,
    (∃ R' ∈ RealTr T (D.sp.X 0), ∃ R ∈ RealTr T (D.sp.Y 0), bes R' R ≠ 0) ∧
    ∀ R' ∈ RealTr T (D.sp.X 0), ∀ R ∈ RealTr T (D.sp.Y 0),
      ∀ (φ : D.what₂.Mu u) (F : D.what₂.EE) (G : T.cusp (D.sp.Y 0)),
      (G : T.AF (D.sp.Y 0)) = R (T.actF _ (X.gl1 u)
        ((T.rowAF D.what₂.mu0 0 ((D.what₂.multZero D.what₂.mu0).symm F) : T.cusp (D.sp.Y 0)) : T.AF (D.sp.Y 0))) →
      T.Bper (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (T.pos1 u) 0
          (T.conjAF _ (R' ((T.colAF u D.what₂.mu0 0 φ : T.cusp (D.sp.X 0)) : T.AF (D.sp.X 0)))) G =
        bes R' R * X.B0 u φ F

def DataChain (T : ThetaX D) (μ : D.what₂.Tup) (Ph : ∀ j, T.Sch (D.sp.Y (j + 1)) (D.sp.Y j))
    (G : ∀ j, T.cusp (D.sp.Y j)) : Prop :=
  ∀ j, j < D.R.m → ((G j : T.cusp (D.sp.Y j)) : T.AF (D.sp.Y j)) =
    (T.mY μ (j + 1) : ℂ) • T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) (Ph j) (G (j + 1))

def bPos1 (X : Loc D T) (u : D.what₂.Word) (R' : Module.End ℂ (T.AF (D.sp.X 0))) (φ : D.what₂.Mu u)
    (G₀ : T.cusp (D.sp.Y 0)) : ℂ :=
  T.Bper (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (T.pos1 u) 0
    (T.conjAF _ (R' ((T.colAF u D.what₂.mu0 0 φ : T.cusp (D.sp.X 0)) : T.AF (D.sp.X 0))))
    ⟨T.actF _ (X.gl1 u) (G₀ : T.AF (D.sp.Y 0)), T.actF_cusp _ (X.gl1 u) _ G₀.2⟩

def TieArch (X : Loc D T) : Prop :=
  ∀ u, ∃ (cv : X.ArchDat u → Module.End ℂ (T.AF (D.sp.X 0)))
      (Ph : X.ArchDat u → ∀ (_ : D.what₂.Tup) (j : ℕ), T.Sch (D.sp.Y (j + 1)) (D.sp.Y j))
      (rv : X.ArchDat u → Module.End ℂ (T.AF (D.sp.Y D.R.m)))
      (Yf : ∀ μ : D.what₂.Tup, D.what₂.Mu u → D.what₂.Amb μ → ℂ),
    (∀ da, cv da ∈ Submodule.span ℂ (RealTr T (D.sp.X 0) : Set (Module.End ℂ (T.AF (D.sp.X 0))))) ∧
    (∀ da, rv da ∈ Submodule.span ℂ (RealTr T (D.sp.Y D.R.m) : Set (Module.End ℂ (T.AF (D.sp.Y D.R.m))))) ∧
    (∀ da μ j, Ph da μ j ∈ T.kfin _ _) ∧
    (∀ (da : X.ArchDat u) (μ : D.what₂.Tup) (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ, ∀ G : ∀ j, T.cusp (D.sp.Y j),
      ((G D.R.m : T.cusp (D.sp.Y D.R.m)) : T.AF (D.sp.Y D.R.m)) =
        rv da ((T.rowAF μ D.R.m ((D.what₂.multTop μ).symm F) : T.cusp (D.sp.Y D.R.m)) : T.AF (D.sp.Y D.R.m)) →
      DataChain T μ (Ph da μ) G →
      bPos1 X u (cv da) φ (G 0) = X.ellT u da * X.B0 u φ (D.what₂.iota μ F) ∧
      bPos1 X u (cv da) φ (G 0) = X.Au u da * Yf μ φ F) ∧
    ((∀ da, X.ellT u da = 0) → ∀ da, X.Au u da = 0)

def Tied (X : Loc D T) : Prop := (KernelFromExponentialTwist X ∧ TieArch X) ∧ ZeDef X

def ExchangeOfPositions (X : Loc D T) : Prop :=
  (∀ u : D.what₂.Word, ∃ (Dp : Module.End ℂ (D.what₂.Mu u)) (κ' κ : ℂ),
    κ' ≠ 0 ∧ κ ≠ 0 ∧
    (∀ x y : D.what₂.Mu u, inner ℂ (Dp x) (Dp y) = ((‖κ'‖ ^ 2 : ℝ) : ℂ) * inner ℂ x y) ∧
    ∀ (φ : D.what₂.Mu u) (F : D.what₂.EE),
      bPer T u (T.posSym u) (X.glSym u) φ F =
        κ * bPer T u (T.pos1 u) (X.gl1 u) ((Dp ^ D.R.rS) φ) F) ∧
  ∃ U₀ : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u : D.what₂.Word,
    ∃ (Uu : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u) (κ : ℂ), κ ≠ 0 ∧
      ∀ (φ : D.what₂.Mu u) (F : D.what₂.EE), D.besS u φ F = κ * X.B0 u (Uu φ) (U₀ F)

def IntPlace (Z : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) : Prop :=
  D.what₂.places.resChar w ≠ (D.mem u).A.T ∧ D.what₂.places.resChar w ≠ D.host.g 0 ∧
  D.what₂.places.resChar w ≠ D.host.g 1 ∧ D.what₂.places.resChar w ≠ D.host.d ∧
  D.what₂.places.resChar w ∉ Z.Qp μ

def PeriodIntegrality (Z : DivX D) : Prop :=
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl), DV.Used D μ → IntPlace Z u μ w →
    ∀ y ∈ (D.fm u).ramL, ∀ φ : D.what₂.Mu u,
      ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) = (D.fm u).emb 0 y →
    ∀ F ∈ (D.what₂.Mtilde μ).carrier,
      ∃ x : D.what₂.LL,
        D.what₂.embLL x = ((D.mem u).C.DGam : ℂ) ^ (D.R.m + 1) * D.what₂.perCol u μ φ F ∧
        0 ≤ D.what₂.places.val w x

def parD (T : ThetaX D) : TH.TPar D := T.parOf D.u₀

def IsTypeDv (T : ThetaX D) (j : ℕ) (F : T.AF (D.sp.Y j)) : Prop :=
  T.conjAF _ F ∈ T.typ _ ((parD T).Dpar j)

def WtHyp (T : ThetaX D) : Prop :=
  (parD T).Interlace ∧ (parD T).Centred ∧
  ∀ j, j ≤ D.R.m → ∀ τ, ∀ a ∈ (parD T).Dpar j τ, ∀ b ∈ (parD T).Dpar j τ, a.2 ≠ b.2 →
    ((D.R.rankY D.R.m : ℝ)) ^ 3 < |((a.1 - b.1 : ℚ) : ℝ)| ∧
    120 * (D.R.rankY j : ℝ) * ((min (sigYD D.R j).1 (sigYD D.R j).2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      |((a.1 - b.1 : ℚ) : ℝ)|

def vth (T : ThetaX D) (μ : D.what₂.Tup) (j : ℕ) :
    T.cusp (D.sp.Y (j + 1)) →ₗ[ℂ] T.AF (D.sp.Y j) :=
  T.dnY μ j

def LiftChain (T : ThetaX D) (μ : D.what₂.Tup) (F : D.what₂.Amb μ) (G : ∀ j, T.cusp (D.sp.Y j)) : Prop :=
  G D.R.m = T.rowAF μ D.R.m ((D.what₂.multTop μ).symm F) ∧
  ∀ j, j < D.R.m → ((G j : T.cusp (D.sp.Y j)) : T.AF (D.sp.Y j)) = vth T μ j (G (j + 1))

inductive InChain (T : ThetaX D) (μ : D.what₂.Tup) : (j : ℕ) → T.AF (D.sp.Y j) → Prop
  | top (x : D.what₂.Mult μ D.R.m) :
      IsTypeDv T D.R.m ((T.rowAF μ D.R.m x : T.cusp (D.sp.Y D.R.m)) : T.AF (D.sp.Y D.R.m)) →
      InChain T μ D.R.m ((T.rowAF μ D.R.m x : T.cusp (D.sp.Y D.R.m)) : T.AF (D.sp.Y D.R.m))
  | step (j : ℕ) (hj : j < D.R.m) (Φ : T.Sch (D.sp.Y (j + 1)) (D.sp.Y j)) (F : T.cusp (D.sp.Y (j + 1))) :
      InChain T μ (j + 1) (F : T.AF (D.sp.Y (j + 1))) →
      InChain T μ j (T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F)

def TieRowTyp (T : ThetaX D) : Prop :=
  ∀ μ x, IsTypeDv T D.R.m ((T.rowAF μ D.R.m x : T.cusp (D.sp.Y D.R.m)) : T.AF (D.sp.Y D.R.m))

def TypStable (T : ThetaX D) : Prop :=
  ∀ j, j ≤ D.R.m →
    (∀ g F, IsTypeDv T j F → IsTypeDv T j (T.actF _ g F)) ∧
    ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (TH.gramAt D (D.sp.Y j) τ), ∀ F, IsTypeDv T j F → IsTypeDv T j (T.actR _ τ h F)

def ChainInRows (T : ThetaX D) : Prop :=
  ∀ (μ : D.what₂.Tup), ∀ F ∈ D.what₂.V0 μ, ∀ G : ∀ j, T.cusp (D.sp.Y j), LiftChain T μ F G →
    ∀ j, j < D.R.m → ∃ x : D.what₂.Mult μ j, G j = T.rowAF μ j x

def ThetaLiftChainTyped (T : ThetaX D) : Prop :=
  WtHyp T → TieRowTyp T → TypStable T →
  (∀ (μ : D.what₂.Tup) (F : D.what₂.Amb μ), ∃ G : ∀ j, T.cusp (D.sp.Y j), LiftChain T μ F G ∧
    ∀ j, j ≤ D.R.m → IsTypeDv T j ((G j : T.cusp (D.sp.Y j)) : T.AF (D.sp.Y j))) ∧
  (T.TieIo → T.TieRowIsom → ChainInRows T →
    ∀ (μ : D.what₂.Tup), ∀ F ∈ D.what₂.V0 μ, ∀ G : ∀ j, T.cusp (D.sp.Y j), LiftChain T μ F G →
      G 0 = T.rowAF μ 0 ((D.what₂.multZero μ).symm (D.what₂.iota μ F)))

def ThetaLevelsInE (T : ThetaX D) : Prop := WtHyp T → TieRowTyp T → TypStable T → ChainInRows T

section Local

open MeasureTheory Matrix ComplexConjugate Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def idxPar (q : ℝ) (r s : ℕ) : ℝ := TH.parIdx q r s

def Lpair (q : ℝ) (t : ℕ) (x : ℂ) : ℂ :=
  (∏ s ∈ Icc 1 t, ((1 - x * ((q : ℂ) ^ (-(s : ℤ)))) * (1 - x⁻¹ * ((q : ℂ) ^ (-(s : ℤ))))))⁻¹

def blockCond {F : Type} [Field F] (O : Subring F) (ϖ : F) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (A : GL (Fin (a + t)) F) : Prop :=
  let M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A : Matrix (Fin (a + t)) (Fin (a + t)) F)
  (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = M.toBlocks₁₁) ∧
  (∀ i j, M.toBlocks₁₂ i j ∈ O) ∧
  M.toBlocks₂₁ ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ∧
  (∃ D ∈ Formalism.DoubleCosetMeasures.GLint O t, (D : Matrix (Fin t) (Fin t) F) = M.toBlocks₂₂)

def L1rallis : Prop := Formalism.DoubleCosetMeasures.LemmaUSplit

def L1index : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (O : Subring F),
    IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a → IsCompact (J' : Set (GL (Fin a) F)) →
    ∀ (ρ : J' →* ℂˣ), (∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) →
    ∀ (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (lam : J' →* ℂˣ),
    (∀ k : J', ((χ (Matrix.GeneralLinearGroup.det (k : GL (Fin a) F)) : ℂˣ) : ℂ) *
        (((nrm ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) F) : Fˣ) : F)) ^
          (((a + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((ρ k : ℂˣ) : ℂ) * conj ((lam k : ℂˣ) : ℂ) = 1) →
    ∀ (c : GL (Fin a) F → ℂ), (∀ g : GL (Fin a) F, ∀ k : J', c (g * k) = ((lam k : ℂˣ) : ℂ) * c g) →
    c 1 = 1 →
    ∀ (μ : Measure (GL (Fin a) F)) [μ.IsMulLeftInvariant], μ (J' : Set (GL (Fin a) F)) = 1 →
    ∀ (ν₁ : Measure (Matrix (Fin a) (Fin a) F)) [ν₁.IsAddLeftInvariant] [SFinite ν₁],
    ν₁ (Formalism.DoubleCosetMeasures.intMat O a a) = 1 →
    ∀ (ν₂ : Measure (Matrix (Fin t) (Fin a) F)) [ν₂.IsAddLeftInvariant] [SFinite ν₂],
    ν₂ (Formalism.DoubleCosetMeasures.intMat O t a) = 1 →
    ∀ (J : Subgroup (GL (Fin (a + t)) F)), (∀ A, A ∈ J ↔ blockCond O ϖ J' A) →
    let q : ℝ := Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)
    ((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index : ℂ) * ((zetaProd q (a + t) : ℝ) : ℂ) *
        Formalism.DoubleCosetMeasures.localZ μ ((ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2)) χ nrm
          (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) c =
      ((zetaProd q t : ℝ) : ℂ)

def L1type : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a →
    ∀ (ρ : J' →* ℂˣ), (∀ k : J', (k : GL (Fin a) F) ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a → ρ k = 1) →
    ∀ h : GL (Fin (a + t)) F, blockCond O ϖ J' h →
      let Mi : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
        Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
          ((h⁻¹ : GL (Fin (a + t)) F) : Matrix (Fin (a + t)) (Fin (a + t)) F)
      ∃ k' : J', ((k' : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = Mi.toBlocks₁₁ ∧
        ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
          Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ (Mi * x) = ((ρ k' : ℂˣ) : ℂ) * Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x

def L1comm : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (a t : ℕ) (k : GL (Fin a) F),
    k ∈ Formalism.DoubleCosetMeasures.GLint O a → ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
      Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1
                (Matrix.fromBlocks ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) 0 0
                  (1 : Matrix (Fin t) (Fin t) F) * x * (k : Matrix (Fin a) (Fin a) F)) =
        Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1 x

def L1 : Prop := L1rallis ∧ L1index ∧ L1type ∧ L1comm

def Witt : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x y, h y x = star (h x y)) →
    (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ (U W : Submodule K V) (f : U ≃ₗ[K] W), (∀ x y : U, h (f x : V) (f y : V) = h x y) →
    ∃ g : V ≃ₗ[K] V, (∀ x y, h (g x) (g y) = h x y) ∧ ∀ x : U, g x = f x

open NumberField IsDedekindDomain in

def Hasse : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsGalois F E → IsCyclic (E ≃ₐ[F] E) → ∀ x : F, x ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ y : TensorProduct F (v.adicCompletion F) E,
        Algebra.norm (v.adicCompletion F) y = algebraMap F (v.adicCompletion F) x) →
    (∀ σ : F →+* ℝ, (¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = σ) → 0 < σ x) →
    ∃ y : E, Algebra.norm F y = x

def adm1 : Prop := Witt ∧ Hasse

def MultOne : Prop :=
  ∀ (n N M : ℕ) (ι : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin (n + 1)) ℂ),
    (∀ g, ((ι g : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))) →
    ∀ (ρ : Matrix.unitaryGroup (Fin (n + 1)) ℂ →* GL (Fin N) ℂ)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* GL (Fin M) ℂ),
    Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) →
    Continuous (fun g => ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
    0 < N → 0 < M →
    (∀ S : Submodule ℂ (Fin N → ℂ),
      (∀ g, ∀ v ∈ S, ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) →
      S = ⊥ ∨ S = ⊤) →
    (∀ S : Submodule ℂ (Fin M → ℂ),
      (∀ g, ∀ v ∈ S, ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ).mulVec v ∈ S) →
      S = ⊥ ∨ S = ⊤) →
    ∀ Hm : Submodule ℂ (Matrix (Fin N) (Fin M) ℂ),
      (∀ T, T ∈ Hm ↔ ∀ g, ((ρ (ι g) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T =
        T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)) →
      Module.finrank ℂ Hm ≤ 1

def adm3 : Prop := MultOne

def minkM (n : ℕ) : ℕ :=
  ∏ p ∈ (range (n + 2)).filter Nat.Prime, p ^ (∑ k ∈ range (n + 1), n / (p ^ k * (p - 1)))

def adm7 : Prop :=
  ∀ (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)), Finite G → Nat.card G ∣ minkM n

end Local

def ellQ (Z : DivX D) (μ : D.what₂.Tup) (v : Z.QPl μ) (j : ℕ) : ℂ :=
  ((idxPar (Z.qv μ v) D.R.r (j * D.R.t) * zetaProd (Z.qv μ v) (D.R.r + j * D.R.t) : ℝ) : ℂ) *
    Z.ZQ μ v j

def singleBlockLocalFactor (Z : DivX D) (μ : D.what₂.Tup) (v : Z.QPl μ) : ℂ :=
  ((idxPar (Z.qv μ v) D.R.r D.R.t * zetaProd (Z.qv μ v) (D.R.r + D.R.t) : ℝ) : ℂ) * Z.quotientLocalValueFirst μ v

def L2 (Z : DivX D) : Prop :=
  ∀ μ (v : Z.QPl μ),
    (∀ j, j ≤ D.R.m → Z.typeDim μ v j = 1) ∧
    (∀ j, 1 ≤ j → j ≤ D.R.m →
      ellQ Z μ v j = ((zetaProd (Z.qv μ v) D.R.t : ℝ) : ℂ) *
        ∏ i ∈ Finset.Ico 1 j, Lpair (Z.qv μ v) D.R.t (Z.nu μ v i / Z.nu μ v j)) ∧
    singleBlockLocalFactor Z μ v = ((zetaProd (Z.qv μ v) D.R.t : ℝ) : ℂ)

def adm2 (T : ThetaX D) : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), j < D.R.m → ∀ π : Submodule ℂ (T.AF (D.sp.Y (j + 1))),
    T.IsStable _ π → π ≤ T.cusp _ →
    (∀ i, 1 ≤ i → i ≤ (sigYD D.R j).2 → ∀ (Φ : T.Sch (D.sp.Y (j + 1)) (T.YsLow D.R.t j i))
      (F : T.cusp (D.sp.Y (j + 1))), (F : T.AF (D.sp.Y (j + 1))) ∈ π →
      T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F = 0) →
    ∀ (Φ : T.Sch (D.sp.Y (j + 1)) (D.sp.Y j)) (F : T.cusp (D.sp.Y (j + 1))),
      (F : T.AF (D.sp.Y (j + 1))) ∈ π →
      T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F ∈ T.cusp (D.sp.Y j)

def adm5 (D : D7) : Prop :=
  ∀ u : D.what₂.Word,
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
    (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v φ) ψ = (D.fm u).ipC i φ (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v ψ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
    Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i ∧
    Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i ∧
    (∀ a, Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) ∧ Formalism.MainNotions.product_first_zeroth_parts.trp D u i v φ = 0 ∧
    Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ ∧
    Formalism.MainNotions.product_first_zeroth_parts.Uop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ)

def HeckeKernelCommutation (D : D7) : Prop :=
  ∀ u : D.what₂.Word, ∀ i, i + 1 < D.R.m → ∀ v, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
    Formalism.MainNotions.product_first_zeroth_parts.FFop D u (i + 1) v (Formalism.MainNotions.product_first_zeroth_parts.KT D u i φ) =
      c • Formalism.MainNotions.product_first_zeroth_parts.KT D u i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ)

def adm6 (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) : Prop := Formalism.MainNotions.TaylorLogMetric.int22 D G.Tr G.e

def adm8 (A : TH.ProvA) : Prop :=
  Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth A ∧
    Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth A

def ThetaCuspidalChain (T : ThetaX D) : Prop :=
  WtHyp T →
  (∀ μ j, j < D.R.m → ∀ (Φ : T.Sch (D.sp.Y (j + 1)) (D.sp.Y j)) (F : T.cusp (D.sp.Y (j + 1))),
    InChain T μ (j + 1) (F : T.AF (D.sp.Y (j + 1))) →
    T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F ∈ T.cusp (D.sp.Y j) →
    IsTypeDv T j (T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F)) ∧
  (∀ μ j, j < D.R.m → ∀ i, 1 ≤ i → i ≤ (sigYD D.R j).2 →
    ∀ (Φ : T.Sch (D.sp.Y (j + 1)) (T.YsLow D.R.t j i)) (F : T.cusp (D.sp.Y (j + 1))),
    IsTypeDv T (j + 1) (F : T.AF (D.sp.Y (j + 1))) →
    T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F = 0)

def CuspTypeGeneralForm (T : ThetaX D) : Prop :=
  WtHyp T →
  (∀ μ j, j < D.R.m → ∀ (Φ : T.Sch (D.sp.Y (j + 1)) (D.sp.Y j)) (F : T.cusp (D.sp.Y (j + 1))),
    IsTypeDv T (j + 1) (F : T.AF (D.sp.Y (j + 1))) →
    T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F ∈ T.cusp (D.sp.Y j) →
    IsTypeDv T j (T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F)) ∧
  (∀ μ j, j < D.R.m → ∀ i, 1 ≤ i → i ≤ (sigYD D.R j).2 →
    ∀ (Φ : T.Sch (D.sp.Y (j + 1)) (T.YsLow D.R.t j i)) (F : T.cusp (D.sp.Y (j + 1))),
    IsTypeDv T (j + 1) (F : T.AF (D.sp.Y (j + 1))) →
    T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F = 0)

theorem InChain.isTypeDv {T : ThetaX D}
    (h1 : ∀ μ j, j < D.R.m → ∀ (Φ : T.Sch (D.sp.Y (j + 1)) (D.sp.Y j)) (F : T.cusp (D.sp.Y (j + 1))),
      IsTypeDv T (j + 1) (F : T.AF (D.sp.Y (j + 1))) →
      T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F ∈ T.cusp (D.sp.Y j) →
      IsTypeDv T j (T.th _ _ (T.carY μ (j + 1) (j + 1)) (T.carY μ (j + 1) j) Φ F))
    {μ : D.what₂.Tup} {j : ℕ} {G : T.AF (D.sp.Y j)} (hG : InChain T μ j G) :
    G ∈ T.cusp (D.sp.Y j) → IsTypeDv T j G := by
  induction hG with
  | top x hx => exact fun _ => hx
  | step j hj Φ F _ ih => exact fun hc => h1 μ j hj Φ F (ih F.2) hc

theorem cusp_type_of_general_form (T : ThetaX D) (h : CuspTypeGeneralForm T) : ThetaCuspidalChain T := by
  intro hW
  obtain ⟨h1, h2⟩ := h hW
  exact ⟨fun μ j hj Φ F hF hc => h1 μ j hj Φ F (InChain.isTypeDv h1 hF F.2) hc, h2⟩

def admitted (T : ThetaX D) (A : TH.ProvA) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) : Prop :=
  adm1 ∧ adm2 T ∧ adm3 ∧ adm5 D ∧ adm6 G ∧ adm7 ∧ adm8 A ∧ ThetaCuspidalChain T

def aux₃ (Z : DivX D) (X : Loc D T) : Prop :=
  MultiplicityOneConditional X ∧ MultiplicityOneWithZeta X ∧ ExchangeOfPositions X ∧ PeriodIntegrality Z ∧ L1 ∧ L2 Z ∧ ThetaLiftChainTyped T

def Stmt (Z : DivX D) (A : TH.ProvA) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) (X : Loc D T) : Prop :=
  Tied X → admitted T A G → aux₃ Z X

def HeckeScalarStatement (D : D7) : Prop := adm5 D → HeckeOperatorScalarUnitary D

def LocalComputationOne : Prop := L1

def DoublingComputation (Z : DivX D) : Prop := L2 Z

def UnfoldingStatement (X : Loc D T) : Prop :=
  Tied X → adm1 → adm2 T → adm3 → adm5 D → HeckeKernelCommutation D → ThetaCuspidalChain T → UnfoldingScalarUnitary X

def ExchangeStatement (X : Loc D T) : Prop := Tied X → adm5 D → ExchangeOfPositions X

def MultiplicityOneConditionalStatement (X : Loc D T) : Prop := UnfoldingScalarUnitary X → MultiplicityOneConditional X

def MultiplicityOneBlocks (X : Loc D T) : Prop := MultiplicityOneConditional X → MultiplicityOneWithZeta X

def MultiplicityOneStatement (X : Loc D T) : Prop := UnfoldingScalarUnitary X → RealConstantNonvanishing X → MultiplicityOneExplicit X

def ThetaChainStatement (T : ThetaX D) : Prop := adm2 T → ThetaCuspidalChain T → ThetaLiftChainTyped T

def ThetaLevelsStatement (Z : DivX D) (T : ThetaX D) : Prop := L1 → L2 Z → adm2 T → ThetaCuspidalChain T → ThetaLevelsInE T

def IntegralityStatement (Z : DivX D) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) : Prop := adm6 G → adm7 → PeriodIntegrality Z

def ConstantFreeStatements (Z : DivX D) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) (X : Loc D T) : Prop :=
  HeckeScalarStatement D ∧ LocalComputationOne ∧ DoublingComputation Z ∧ ThetaChainStatement T ∧ UnfoldingStatement X ∧ ExchangeStatement X ∧ IntegralityStatement Z G ∧ MultiplicityOneConditionalStatement X ∧ MultiplicityOneBlocks X

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA)
  (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th)

def AdmF : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.ex x hx i).th A (GF x i)

def OrbitValuationBound : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), aux₃ (Fm.X x i) (XF x hx i)

def KudlaFamilyStatement : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Stmt (Fm.X x i) A (GF x i) (XF x hx i)

def ConstantFreeFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConstantFreeStatements (Fm.X x i) (GF x i) (XF x hx i)

def UnfoldingFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), UnfoldingStatement (XF x hx i)

def MultiplicityOneFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), MultiplicityOneStatement (XF x hx i)

def ThetaLevelsFamily : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaLevelsStatement (Fm.X x i) (Fm.ex x hx i).th

end Family

abbrev LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type 1 :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th

abbrev LocClass : Type 1 := ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), LocF Fm → Prop

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ A GF, ∀ XF : LocF Fm, 𝒴 Fm XF → KudlaFamilyStatement Fm A GF XF)

def ClosedConstantFreeStatements (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ GF, ∀ XF : LocF Fm, 𝒴 Fm XF → ConstantFreeFamily Fm GF XF)

def ClosedUnfolding (𝒞 : Formalism.MainNotions.FamClass) (𝒴 : LocClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ XF : LocF Fm, 𝒴 Fm XF → UnfoldingFamily Fm XF)

def ClosedThetaLevels (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ThetaLevelsFamily Fm)

def ClosedMultiplicityOne (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ XF : LocF Fm, MultiplicityOneFamily Fm XF)

end Formalism.MainNotions.ZetaProductPairs

end
