import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.DstarEq
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace TensorProduct
open Matrix

namespace Formalism.L2.SG.RowDict

section Conj

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

def conjL : Lp ℂ 2 μ ≃ₗᵢ⋆[ℂ] Lp ℂ 2 μ where
  toFun := star
  invFun := star
  map_add' f g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g, Lp.coeFn_add (star f) (star g), Lp.coeFn_star f,
      Lp.coeFn_star g] with x h1 h2 h3 h4 h5
    rw [h1, h3, Pi.star_apply, h2, Pi.add_apply, Pi.add_apply, h4, h5, Pi.star_apply, Pi.star_apply, star_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f, Lp.coeFn_smul ((starRingEnd ℂ) c) (star f),
      Lp.coeFn_star f] with x h1 h2 h3 h4
    rw [h1, h3, Pi.star_apply, h2, Pi.smul_apply, Pi.smul_apply, h4, Pi.star_apply, smul_eq_mul, smul_eq_mul,
      star_mul', starRingEnd_apply]
  left_inv f := star_star f
  right_inv f := star_star f
  norm_map' f := by
    show ‖star f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

theorem conjL_apply (f : Lp ℂ 2 μ) : conjL μ f = star f := rfl

end Conj

section Good

variable {D : D7} (X : HidaSetting D)

def wLat (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E) :=
  Submodule.span (𝓞 X.B.I.E) {z | ∃ a : 𝓞 X.B.I.E, (∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) ∧
    ∃ y ∈ X.B.I.L, z = (a : X.B.I.E) • y}

abbrev wLf (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (IntAf X.B.I.F X.B.I.E) (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
  lamAf (F := X.B.I.F) (wLat X w)

def IsRedBasis (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (b : Fin D.R.r → (Fin X.B.I.n → X.B.I.E)) :
    Prop :=
  (∀ i, b i ∈ X.B.I.L) ∧ ∀ y ∈ X.B.I.L, ∃ c : Fin D.R.r → ℤ, y - ∑ i, (c i : X.B.I.E) • b i ∈ wLat X w

def RedMat (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ) (x : X.B.I.Gf)
    (M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) : Prop :=
  ∃ b, IsRedBasis X w b ∧ ∀ i, X.B.I.fmat x *ᵥ incl X.B.I (b i) -
    ∑ j, (((M j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (b j) ∈ wLf X w

def GoodAt (x : X.B.I.Gf) (γ : G0g D.nd) : Prop :=
  ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
    RedMat X (D.naut.plGw kv.1 kv.2) (D.host.g kv.1) x ((γ kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))

open Classical in

def eg (x : X.B.I.Gf) : ℂ :=
  if h : x ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ then
    D.ntypes.e0.coeff (Classical.choose h.2) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ)
  else 0

def RedExists : Prop := ∀ x ∈ X.B.I.Kset, ∃ γ : G0g D.nd, GoodAt X x γ

def EgWellDef : Prop :=
  ∀ x (γ γ' : G0g D.nd), GoodAt X x γ → GoodAt X x γ' → D.ntypes.e0.coeff γ = D.ntypes.e0.coeff γ'

def IdempotentRealFixed (D : D7) : Prop := ∀ γ : G0g D.nd, star (D.ntypes.e0.coeff γ) = D.ntypes.e0.coeff γ

structure GoodOp where
  Rg : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund
  Rg_spec : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R (eg X) Rg

end Good

section Rows

open Formalism.L2.SG.ProjRows

variable {D : D7} (X : HidaSetting D)

abbrev L2X : Type := X.B.I.L2 X.B.μf X.B.fund

abbrev muX : Measure X.B.I.GA := (X.B.I.muA X.B.μf).restrict X.B.fund

def goodSub (G : GoodOp X) : Submodule ℂ (L2X X) :=
  HHX X ⊓ LinearMap.ker ((G.Rg : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def EEC (G : GoodOp X) : Submodule ℂ (L2X X) :=
  (goodSub X G).comap (conjL (muX X)).toLinearEquiv.toLinearMap

theorem mem_EEC (G : GoodOp X) (F : L2X X) : F ∈ EEC X G ↔ star F ∈ goodSub X G := Iff.rfl

def conjHH (G : GoodOp X) : EEC X G →ₗᵢ⋆[ℂ] HHX X where
  toFun F := ⟨star (F : L2X X), ((mem_EEC X G F).1 F.2).1⟩
  map_add' F F' := Subtype.ext (by
    show star ((F : L2X X) + F') = star (F : L2X X) + star (F' : L2X X)
    exact (conjL (muX X)).map_add _ _)
  map_smul' c F := Subtype.ext (by
    show star (c • (F : L2X X)) = (starRingEnd ℂ c) • star (F : L2X X)
    exact (conjL (muX X)).map_smulₛₗ c _)
  norm_map' F := by
    show ‖star (F : L2X X)‖ = ‖(F : L2X X)‖
    exact (conjL (muX X)).norm_map _

theorem conjHH_apply (G : GoodOp X) (F : EEC X G) : ((conjHH X G F : HHX X) : L2X X) = star (F : L2X X) := rfl

end Rows

def IsConjOnto {E W H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : E → H) (c : W →ₗᵢ⋆[ℂ] H) : Prop :=
  ∃ j : E ≃ₗᵢ[ℂ] W, ∀ F, s F = c (j F)

section Comparison₂

open Formalism.L2.SG.ProjRows

variable {D : D7} (X : HidaSetting D)

def RowDictTie (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) : Prop :=
  IsConjOnto (fun F : D.what₂.EE => ι (D.sEE F)) (conjHH X G)

theorem finiteDimensional_HHX (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) : FiniteDimensional ℂ (HHX X) := LinearEquiv.finiteDimensional ι.toLinearEquiv

theorem dall_eq (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) : D.what₂.Dall = Module.finrank ℂ (HHX X) := by
  rw [← D.s_HH]
  exact ι.toLinearEquiv.finrank_eq

theorem drows_eq {G : GoodOp X} {ι : D.s.HH ≃ₗᵢ[ℂ] HHX X} (h : RowDictTie X G ι) :
    D.what₂.Drows = Module.finrank ℂ (EEC X G) := by
  obtain ⟨j, -⟩ := h
  rw [← j.toLinearEquiv.finrank_eq, Module.finrank_eq_card_basis D.what₂.onb.toBasis, Fintype.card_fin]

theorem range_sEE {G : GoodOp X} {ι : D.s.HH ≃ₗᵢ[ℂ] HHX X} (h : RowDictTie X G ι) (y : HHX X) :
    (y : L2X X) ∈ goodSub X G ↔ ∃ F : D.what₂.EE, ι (D.sEE F) = y := by
  obtain ⟨j, hj⟩ := h
  have hj' : ∀ F, ι (D.sEE F) = conjHH X G (j F) := hj
  constructor
  · intro hy
    have hmem : star (y : L2X X) ∈ EEC X G := by
      rw [mem_EEC, star_star]; exact hy
    refine ⟨j.symm ⟨star (y : L2X X), hmem⟩, ?_⟩
    rw [hj', LinearIsometryEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [conjHH_apply]
    exact star_star _
  · rintro ⟨F, rfl⟩
    rw [hj', conjHH_apply]
    exact (mem_EEC X G _).1 (j F).2

def EEB (G : GoodOp X) : Submodule ℂ (L2X X) :=
  (HHX X).comap (conjL (muX X)).toLinearEquiv.toLinearMap ⊓ LinearMap.ker ((G.Rg : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def RgReal (G : GoodOp X) : Prop := ∀ φ : L2X X, star (G.Rg φ) = G.Rg (star φ)

theorem eec_eq_eeb (G : GoodOp X) (h : RgReal X G) : EEC X G = EEB X G := by
  ext F
  rw [mem_EEC]
  simp only [EEB, goodSub, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker]
  refine and_congr Iff.rfl ?_
  simp only [LinearMap.sub_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe, sub_eq_zero]
  rw [← h]
  exact star_inj

theorem D_eq_of (hB : Formalism.L2.SG.RowsDef.RowsBij) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X)
    (hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v)) (hIrr : ∀ v, IsIrredOn (UJset (X.B.I.ε v)) (X.B.σ v))
    (hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)))
    (hw : ∀ v, ‖X.B.w v‖ = 1)
    (hint : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v))) :
    X.B.D = D.what₂.Dall := by
  rw [dall_eq X ι]
  exact (Formalism.L2.SG.RowsDef.RowsAut.D_eq_finrank_HH hB X.B _ hU hIrr hF hw hint X.Rph X.Rph_spec).1

theorem D_eq_holds (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X)
    (hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v)) (hIrr : ∀ v, IsIrredOn (UJset (X.B.I.ε v)) (X.B.σ v))
    (hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)))
    (hw : ∀ v, ‖X.B.w v‖ = 1)
    (hint : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v))) (Formalism.REAL.muG (X.B.I.ε v))) :
    X.B.D = D.what₂.Dall :=
  D_eq_of X Formalism.L2.SG.Closed.RowsBij_holds ι hU hIrr hF hw hint

def DstarAgree : Prop :=
  Formalism.MainNotions.StandardLattice.DstarD D =
    X.B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.μf X.B.fund X.B.e

theorem dstar_iff (hT : AutTie D X.B X.pl) : D.what₂.Dstar = Formalism.MainNotions.StandardLattice.DstarD D ↔ DstarAgree X := by
  rw [hT.Dstar_eq, DstarAgree, eq_comm]

end Comparison₂

end Formalism.L2.SG.RowDict
