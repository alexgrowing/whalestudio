import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import BuildAid.D3

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.RecTie
open scoped InnerProductSpace

namespace GlobalTheory.RowTieRead

open GlobalTheory.HilbertLevels

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)

theorem mem_cc (b : Bool) (μ : D.what₂.Tup) {k : ℕ} (hk : k < D.R.m) (x : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) :
    x ∈ (toChainReal R F tupT hm hTop).CC b μ k ↔ x ∈ R.CC (tupT μ) k := by
  show x ∈ MultT R.θ (R.MY k) (if k < D.R.m then _ else Set.univ) (if k < D.R.m then _ else 0) ↔ _
  rw [if_pos hk, if_pos hk]

theorem ioC_coe (b : Bool) (μ : D.what₂.Tup) (k : ℕ) (hk : k + 1 < D.R.m)
    (z : (toChainReal R F tupT hm hTop).CC b μ (k + 1)) :
    (((toChainReal R F tupT hm hTop).ioC b μ k z).1 :
        SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) =
      (((R.ioY (tupT μ) k ⟨(z.1 : SmT (R.MY (k + 1)) →ₗ[ℂ] GA D (Yc D (k + 1)) → ℂ),
        (mem_cc R F tupT hm hTop b μ hk _).1 z.2⟩).1 : _)) := by
  simp only [toChainReal, dif_pos hk]
  rfl

theorem ioOK (hC : R.IsChain) (b : Bool) (μ : D.what₂.Tup) : (toChainReal R F tupT hm hTop).IoOK b μ := by
  refine ⟨fun k hk => ⟨fun Fz φ v g => ?_, fun Fz φ v g => ?_⟩, fun _ => ⟨fun Fz φ v g => ?_, fun Fz φ v g => ?_⟩⟩
  · exact (hC.ioY (tupT μ) k hk).integ ⟨Fz.1, (mem_cc R F tupT hm hTop b μ (by omega) _).1 Fz.2⟩ φ v g
  · rw [ioC_coe R F tupT hm hTop b μ k (by omega)]
    exact (hC.ioY (tupT μ) k hk).eq ⟨Fz.1, (mem_cc R F tupT hm hTop b μ (by omega) _).1 Fz.2⟩ φ v g
  · exact (hC.ioX (tupT μ)).integ ⟨Fz.1, (hTop (tupT μ)).symm ▸ Fz.2⟩ φ v g
  · exact (hC.ioX (tupT μ)).eq ⟨Fz.1, (hTop (tupT μ)).symm ▸ Fz.2⟩ φ v g

def nuW (t : T) : ∀ j, Measure (GA D (Yc D j))
  | 0 => ENNReal.ofReal (RealDat.nP F true)⁻¹ • R.ν0
  | j + 1 => R.νY t (j + 1)

def fdW (t : T) : ∀ j, Set (GA D (Yc D j))
  | 0 => R.fd0
  | j + 1 => R.fdY t (j + 1)

def cW : ℕ → ℝ
  | 0 => 1
  | _ + 1 => (RealDat.nP F true)⁻¹

def cXW : ℝ := (RealDat.nP F true)⁻¹ * ∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)

variable (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true)

def eW (μ : D.what₂.Tup) (hμ : Used0 D μ) : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j
  | 0 => LinearMap.codRestrict (R.CC (tupT μ) 0)
      (((toChainReal R F tupT hm hTop).EEc true).subtype ∘ₗ I.jE.toLinearMap ∘ₗ
        (D.what₂.multZero μ).toLinearEquiv.toLinearMap)
      (fun x => (mem_cc R F tupT hm hTop true μ hm _).1 (eec_le_cc R F tupT hm hTop true μ (I.jE _).2))
  | j + 1 => if h : j + 1 ≤ D.R.m - 1 then
      LinearMap.codRestrict (R.CC (tupT μ) (j + 1))
        (((toChainReal R F tupT hm hTop).CCP true μ (j + 1)).subtype ∘ₗ
          (I.jM μ hμ (j + 1) (by omega) h).toLinearMap)
        (fun x => (mem_cc R F tupT hm hTop true μ (by omega) _).1
          (ccp_le R F tupT hm hTop true μ (by omega) (I.jM μ hμ (j + 1) (by omega) h x).2))
    else 0

def eXW (μ : D.what₂.Tup) (hμ : Used0 D μ) :
    D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) :=
  LinearMap.codRestrict (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e))
    (((toChainReal R F tupT hm hTop).CCXP true μ).subtype ∘ₗ (I.jX μ hμ).toLinearMap)
    (fun x => (hTop (tupT μ)).symm ▸ ccxp_le R F tupT hm hTop true μ (I.jX μ hμ x).2)

theorem eW_pos (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (x : D.what₂.Mult μ j) :
    ((eW R F tupT hm hTop I μ hμ j x).1 : SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ) = (I.jM μ hμ j h1 h2 x).1 := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [eW, dif_pos h2]
  rfl

theorem nuW_pos (t : T) (j : ℕ) (h1 : 1 ≤ j) : nuW R F t j = R.νY t j := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem fdW_pos (t : T) (j : ℕ) (h1 : 1 ≤ j) : fdW R t j = R.fdY t j := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem cW_pos (j : ℕ) (h1 : 1 ≤ j) : cW F j = (RealDat.nP F true)⁻¹ := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

theorem eW_succ_eq (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (x : D.what₂.Mult μ j) :
    eW R F tupT hm hTop I μ hμ j x = ⟨(I.jM μ hμ j h1 h2 x).1, (mem_cc R F tupT hm hTop true μ (by omega) _).1
      (ccp_le R F tupT hm hTop true μ (by omega) (I.jM μ hμ j h1 h2 x).2)⟩ :=
  Subtype.ext (eW_pos R F tupT hm hTop I μ hμ j h1 h2 x)

theorem inner_io_cast (μ : D.what₂.Tup) {k k' : ℕ} (h : k = k') (x : D.what₂.Mult μ k) (y : D.what₂.Mult μ (k + 1)) :
    ⟪x, D.what₂.io μ k y⟫_ℂ = ⟪cast (congrArg (D.what₂.Mult μ) h) x,
      D.what₂.io μ k' (cast (congrArg (fun i => D.what₂.Mult μ (i + 1)) h) y)⟫_ℂ := by
  subst h; rfl

theorem rhs_cast (μ : D.what₂.Tup) (hμ : Used0 D μ) {k k' : ℕ} (h : k = k')
    (a : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) (x : D.what₂.Mult μ k) :
    (cW F k : ℂ) * ipT (R.MY k) (nuW R F (tupT μ) k) (fdW R (tupT μ) k) a (eW R F tupT hm hTop I μ hμ k x).1 =
      (cW F k' : ℂ) * ipT (R.MY k') (nuW R F (tupT μ) k') (fdW R (tupT μ) k')
        (cast (congrArg (fun i => SmT (R.MY i) →ₗ[ℂ] GA D (Yc D i) → ℂ) h) a)
        (eW R F tupT hm hTop I μ hμ k' (cast (congrArg (D.what₂.Mult μ) h) x)).1 := by
  subst h; rfl

variable {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE} {ty : Fin n → D.what₂.FT}

theorem levels (hM : R.IsModels) (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j < D.R.m) :
    IsQuot (Yc D j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j) ∧ 0 < cW F j ∧ ∀ x y : D.what₂.Mult μ j,
      ⟪x, y⟫_ℂ = (cW F j : ℂ) * ipT (R.MY j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j)
        (eW R F tupT hm hTop I μ hμ j y).1 (eW R F tupT hm hTop I μ hμ j x).1 := by
  cases j with
  | zero =>
    refine ⟨scaled (inv_pos.2 (nP_pos F true)) hM.ν0.1.1 hM.ν0.2, one_pos, fun x y => ?_⟩
    rw [← LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ)]
    refine (hRS.ee _ _).trans ?_
    show _ = ((1 : ℝ) : ℂ) * _
    rw [Complex.ofReal_one, one_mul]
    rfl
  | succ j =>
    have h2 : j + 1 ≤ D.R.m - 1 := by omega
    refine ⟨measY R hM (tupT μ) h2 hm, inv_pos.2 (nP_pos F true), fun x y => ?_⟩
    refine (hRS.mult μ hμ (j + 1) (by omega) h2 x y).trans ?_
    rw [eW_pos R F tupT hm hTop I μ hμ (j + 1) (by omega) h2 x, eW_pos R F tupT hm hTop I μ hμ (j + 1) (by omega) h2 y]
    rfl

theorem ipT_eq {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (ν : Measure (GA D V)) (𝓕 : Set (GA D V))
    (a b : SmT M →ₗ[ℂ] GA D V → ℂ) : ipT M ν 𝓕 a b = ipMT M ν 𝓕 b a := rfl

theorem eW_zero_coe (μ : D.what₂.Tup) (hμ : Used0 D μ) (x : D.what₂.Mult μ 0) :
    ((eW R F tupT hm hTop I μ hμ 0 x).1 : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) = (I.jE (D.what₂.multZero μ x)).1 := rfl

theorem ipE_eq (t : T) (a a' : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) :
    (toChainReal R F tupT hm hTop).ipE true a a' = ipMT (R.MY 0) (nuW R F t 0) (fdW R t 0) a a' := rfl

theorem weightedInner_eq (μ : D.what₂.Tup) (j : ℕ) (a a' : SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ) :
    (toChainReal R F tupT hm hTop).ipP true μ j a a' =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ipMT (R.MY j) (R.νY (tupT μ) j) (R.fdY (tupT μ) j) a a' := rfl

theorem ipXP_eq (μ : D.what₂.Tup) (a a' : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ) :
    (toChainReal R F tupT hm hTop).ipXP true μ a a' =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / 1 : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) a a') := rfl

theorem top_pos : 0 < cXW R F := by
  have hdef : D.sp.X'.IsDefinite := (factXmDef D.R D.host.F D.sp).1
  exact mul_pos (inv_pos.2 (nP_pos F true))
    (Finset.prod_pos fun τ _ => by exact_mod_cast finrank_model_pos D.sp.X'_sig hdef R.MX τ)

theorem top_inner (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (x y : D.what₂.Mult μ D.R.m) :
    ⟪x, y⟫_ℂ = (cXW R F : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
      (eXW R F tupT hm hTop I μ hμ y).1 (eXW R F tupT hm hTop I μ hμ x).1 := by
  rw [ipT_eq]
  refine (hRS.multX (by omega) μ hμ x y).trans ?_
  have key : ∀ (a b : ℝ) (c : ℂ), (a : ℂ) * (((b / 1 : ℝ)) * c) = ((a * b : ℝ) : ℂ) * c := by
    intro a b c; push_cast; ring
  exact (ipXP_eq R F tupT hm hTop μ _ _).trans ((key _ _ _).trans rfl)

theorem eW_incl (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1) (y : D.what₂.Mult μ j) :
    eW R F tupT hm hTop I μ hμ j y =
      ⟨((Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y)).1 :
        SmT (R.MY j) →ₗ[ℂ] GA D (Yc D j) → ℂ), (mem_cc R F tupT hm hTop true μ (by omega) _).1
          (Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y)).2⟩ := by
  have e1 : (((Submodule.inclusion (ccp_le R F tupT hm hTop true μ (by omega)) (I.jM μ hμ j h1 h2 y) :
      (toChainReal R F tupT hm hTop).CC true μ j)) : (toChainReal R F tupT hm hTop).Amb j) =
      ((I.jM μ hμ j h1 h2 y : (toChainReal R F tupT hm hTop).CCP true μ j) : (toChainReal R F tupT hm hTop).Amb j) :=
    Submodule.coe_inclusion _ _
  exact Subtype.ext ((eW_pos R F tupT hm hTop I μ hμ j h1 h2 y).trans e1.symm)

theorem eXW_val (μ : D.what₂.Tup) (hμ : Used0 D μ) (y : D.what₂.Mult μ D.R.m) :
    ((eXW R F tupT hm hTop I μ hμ y).1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ) = (I.jX μ hμ y).1 := by
  simp only [eXW, LinearMap.codRestrict_apply]
  rfl

theorem eXW_incl (μ : D.what₂.Tup) (hμ : Used0 D μ) (y : D.what₂.Mult μ D.R.m) :
    eXW R F tupT hm hTop I μ hμ y =
      ⟨((Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y)).1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ),
        (hTop (tupT μ)).symm ▸ (Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y)).2⟩ := by
  have e1 : (((Submodule.inclusion (ccxp_le R F tupT hm hTop true μ) (I.jX μ hμ y) :
      (toChainReal R F tupT hm hTop).CCX true μ)) : (toChainReal R F tupT hm hTop).AmbX) =
      ((I.jX μ hμ y : (toChainReal R F tupT hm hTop).CCXP true μ) : (toChainReal R F tupT hm hTop).AmbX) :=
    Submodule.coe_inclusion _ _
  exact Subtype.ext ((eXW_val R F tupT hm hTop I μ hμ y).trans e1.symm)

theorem ioX_coe (b : Bool) (μ : D.what₂.Tup) (z : (toChainReal R F tupT hm hTop).CCX b μ) :
    (((toChainReal R F tupT hm hTop).ioX b μ z).1 : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] GA D (Yc D (D.R.m - 1)) → ℂ) =
      ((R.ioX (tupT μ) ⟨(z.1 : SmT R.MX →ₗ[ℂ] GA D D.sp.X' → ℂ), (hTop (tupT μ)).symm ▸ z.2⟩).1 : _) := by
  simp only [toChainReal]
  rfl

theorem L0 (μ : D.what₂.Tup) (hj : 0 + 1 < D.R.m) (a : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ)
    (z : (toChainReal R F tupT hm hTop).CC true μ 1) :
    (toChainReal R F tupT hm hTop).ipE true a ((toChainReal R F tupT hm hTop).ioC true μ 0 z).1 =
      ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0) a
        (R.ioY (tupT μ) 0 ⟨(z.1 : SmT (R.MY 1) →ₗ[ℂ] GA D (Yc D 1) → ℂ), (mem_cc R F tupT hm hTop true μ hj _).1 z.2⟩).1 :=
  (congrArg ((toChainReal R F tupT hm hTop).ipE true a) (ioC_coe R F tupT hm hTop true μ 0 hj z)).trans
    (ipE_eq R F tupT hm hTop (tupT μ) _ _)

theorem inner_io_zero (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (hj : 0 + 1 < D.R.m) (x : D.what₂.Mult μ 0) (y : D.what₂.Mult μ 1) :
    ⟪x, D.what₂.io μ 0 y⟫_ℂ = (cW F 0 : ℂ) * ipT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0)
      (R.ioY (tupT μ) 0 (eW R F tupT hm hTop I μ hμ 1 y)).1 (eW R F tupT hm hTop I μ hμ 0 x).1 := by
  have h1 : ((cW F 0 : ℝ) : ℂ) = 1 := by simp [cW]
  rw [eW_incl R F tupT hm hTop I μ hμ 1 le_rfl (by omega) y, ipT_eq, h1, one_mul,
    ← LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ)]
  exact (hRS.io0 (by omega) μ hμ (ioOK R F tupT hm hTop hC true μ) (D.what₂.multZero μ x) y).trans
    ((L0 R F tupT hm hTop μ hj _ _).trans (congrArg (fun a => ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0) a _)
      (eW_zero_coe R F tupT hm hTop I μ hμ x).symm))

theorem inner_io_succ (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j + 1 + 1 < D.R.m) (x : D.what₂.Mult μ (j + 1))
    (y : D.what₂.Mult μ (j + 1 + 1)) :
    ⟪x, D.what₂.io μ (j + 1) y⟫_ℂ = (cW F (j + 1) : ℂ) * ipT (R.MY (j + 1)) (nuW R F (tupT μ) (j + 1)) (fdW R (tupT μ) (j + 1))
      (R.ioY (tupT μ) (j + 1) (eW R F tupT hm hTop I μ hμ (j + 1 + 1) y)).1 (eW R F tupT hm hTop I μ hμ (j + 1) x).1 := by
  rw [nuW_pos R F (tupT μ) (j + 1) (by omega), fdW_pos R (tupT μ) (j + 1) (by omega), cW_pos F (j + 1) (by omega),
    ipT_eq, eW_incl R F tupT hm hTop I μ hμ (j + 1 + 1) (by omega) (by omega) y,
    eW_succ_eq R F tupT hm hTop I μ hμ (j + 1) (by omega) (by omega) x]
  exact (hRS.io μ hμ (ioOK R F tupT hm hTop hC true μ) (j + 1) (by omega) (by omega) x y).trans
    ((congrArg ((toChainReal R F tupT hm hTop).ipP true μ (j + 1) (I.jM μ hμ (j + 1) (by omega) (by omega) x).1)
      (ioC_coe R F tupT hm hTop true μ (j + 1) hj _)).trans (weightedInner_eq R F tupT hm hTop μ (j + 1) _ _))

theorem io_step (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (j : ℕ) (hj : j + 1 < D.R.m) (x : D.what₂.Mult μ j) (y : D.what₂.Mult μ (j + 1)) :
    ⟪x, D.what₂.io μ j y⟫_ℂ = (cW F j : ℂ) * ipT (R.MY j) (nuW R F (tupT μ) j) (fdW R (tupT μ) j)
      (R.ioY (tupT μ) j (eW R F tupT hm hTop I μ hμ (j + 1) y)).1 (eW R F tupT hm hTop I μ hμ j x).1 := by
  cases j with
  | zero => exact inner_io_zero R F tupT hm hTop I hC hRS μ hμ hj x y
  | succ j => exact inner_io_succ R F tupT hm hTop I hC hRS μ hμ j hj x y

theorem rhs_gen (t : T) (k : ℕ) (hk : 1 ≤ k) (a b : SmT (R.MY k) →ₗ[ℂ] GA D (Yc D k) → ℂ) :
    (cW F k : ℂ) * ipT (R.MY k) (nuW R F t k) (fdW R t k) a b =
      (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ipMT (R.MY k) (R.νY t k) (R.fdY t k) b a := by
  obtain ⟨j, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  rfl

theorem rhs_zero (t : T) (a b : SmT (R.MY 0) →ₗ[ℂ] GA D (Yc D 0) → ℂ) :
    (cW F 0 : ℂ) * ipT (R.MY 0) (nuW R F t 0) (fdW R t 0) a b = ipMT (R.MY 0) (nuW R F t 0) (fdW R t 0) b a := by
  have h : ((cW F 0 : ℝ) : ℂ) = 1 := by simp [cW]
  rw [h, one_mul]
  rfl

theorem rowChain_intertwiner_top_second (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (h2 : 1 < D.R.m) (x : D.what₂.Mult μ (D.R.m - 1))
    (y' : D.what₂.Mult μ D.R.m) :
    ⟪x, D.what₂.io μ (D.R.m - 1) (cast (congrArg (D.what₂.Mult μ) (by omega : D.R.m = D.R.m - 1 + 1)) y')⟫_ℂ =
      (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  have h1m : 1 ≤ D.R.m - 1 := by omega
  refine (hRS.ioTop (by omega) μ hμ (ioOK R F tupT hm hTop hC true μ) x y').trans
    ((congrArg ((toChainReal R F tupT hm hTop).ipP true μ (D.R.m - 1) (I.jM μ hμ (D.R.m - 1) h1m le_rfl x).1)
      (ioX_coe R F tupT hm hTop true μ _)).trans ((weightedInner_eq R F tupT hm hTop μ (D.R.m - 1) _ _).trans
        (Eq.trans ?_ (rhs_gen R F (tupT μ) (D.R.m - 1) h1m _ _).symm)))
  exact congrArg₂ (fun a b => (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) *
      ipMT (R.MY (D.R.m - 1)) (R.νY (tupT μ) (D.R.m - 1)) (R.fdY (tupT μ) (D.R.m - 1)) a b)
    (congrArg Subtype.val (eW_succ_eq R F tupT hm hTop I μ hμ (D.R.m - 1) h1m le_rfl x)).symm
    (congrArg (fun z => (R.ioX (tupT μ) z).1) (eXW_incl R F tupT hm hTop I μ hμ y')).symm

theorem rowChain_intertwiner_top_first (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (h1' : D.R.m = 1) (x : D.what₂.Mult μ (D.R.m - 1))
    (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m) (hy : HEq y y') :
    ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  have hk : D.R.m - 1 = 0 := by omega
  have hIo := ioOK R F tupT hm hTop hC true μ
  have key : ∀ (a : D.what₂.Mult μ 1) (z : D.what₂.Mult μ D.R.m), HEq a z → ∀ w : D.what₂.Mult μ 0,
      ⟪D.what₂.multZero μ w, D.what₂.multZero μ (D.what₂.io μ 0 a)⟫_ℂ =
        (toChainReal R F tupT hm hTop).ipE true (I.jE (D.what₂.multZero μ w)).1
          (cast (congrArg (toChainReal R F tupT hm hTop).Amb (show D.R.m - 1 = 0 by omega))
            ((toChainReal R F tupT hm hTop).ioX true μ
              (Submodule.inclusion (hRS.lvlX μ hμ) (I.jX μ hμ z))).1) := by
    intro a z haz w
    obtain rfl : z = cast (congrArg ((RowSide.sharp D).Mult μ) h1'.symm) a := (cast_eq_iff_heq.2 haz).symm
    exact hRS.io0X h1' μ hμ hIo _ a
  refine (inner_io_cast μ hk x y).trans ((LinearIsometryEquiv.inner_map_map (D.what₂.multZero μ) _ _).symm.trans
    ((key _ y' ((cast_heq _ _).trans hy) _).trans ((ipE_eq R F tupT hm hTop (tupT μ) _ _).trans
      ((Eq.trans ?_ (rhs_zero R F (tupT μ) _ _).symm).trans (rhs_cast R F tupT hm hTop I μ hμ hk _ x).symm))))
  exact congrArg₂ (ipMT (R.MY 0) (nuW R F (tupT μ) 0) (fdW R (tupT μ) 0))
    (eW_zero_coe R F tupT hm hTop I μ hμ _).symm
    (congrArg (fun w => cast (congrArg (fun i => SmT (R.MY i) →ₗ[ℂ] GA D (Yc D i) → ℂ) hk) w)
      ((ioX_coe R F tupT hm hTop true μ _).trans
        (congrArg (fun z => (R.ioX (tupT μ) z).1) (eXW_incl R F tupT hm hTop I μ hμ y')).symm))

theorem io_top (hC : R.IsChain)
    (hRS : RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (x : D.what₂.Mult μ (D.R.m - 1)) (y : D.what₂.Mult μ (D.R.m - 1 + 1))
    (y' : D.what₂.Mult μ D.R.m) (hy : HEq y y') :
    ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (cW F (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1))
      (nuW R F (tupT μ) (D.R.m - 1)) (fdW R (tupT μ) (D.R.m - 1))
      (R.ioX (tupT μ) (eXW R F tupT hm hTop I μ hμ y')).1 (eW R F tupT hm hTop I μ hμ (D.R.m - 1) x).1 := by
  by_cases h2 : 1 < D.R.m
  · have hyy : cast (congrArg (D.what₂.Mult μ) (by omega : D.R.m = D.R.m - 1 + 1)) y' = y :=
      cast_eq_iff_heq.2 hy.symm
    exact (congrArg (fun z => ⟪x, D.what₂.io μ (D.R.m - 1) z⟫_ℂ) hyy.symm).trans
      (rowChain_intertwiner_top_second R F tupT hm hTop I hC hRS μ hμ h2 x y')
  · exact rowChain_intertwiner_top_first R F tupT hm hTop I hC hRS μ hμ (by omega) x y y' hy

theorem weak_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE) (ty : Fin n → D.what₂.FT), R.IsModels → R.IsChain → RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty → ∀ μ, Used0 D μ → (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop I n bs ty hM hC hRS μ hμ
  exact ⟨eW R F tupT hm hTop I μ hμ, eXW R F tupT hm hTop I μ hμ, nuW R F (tupT μ), fdW R (tupT μ), cW F, cXW R F,
    fun j hj => levels R F tupT hm hTop I hM hRS μ hμ j hj, ⟨_, _, (hTop (tupT μ)).le⟩, top_pos R F,
    top_inner R F tupT hm hTop I hRS μ hμ, fun j hj x y => io_step R F tupT hm hTop I hC hRS μ hμ j hj x y,
    fun x y y' hy => io_top R F tupT hm hTop I hC hRS μ hμ x y y' hy⟩

end GlobalTheory.RowTieRead

end
