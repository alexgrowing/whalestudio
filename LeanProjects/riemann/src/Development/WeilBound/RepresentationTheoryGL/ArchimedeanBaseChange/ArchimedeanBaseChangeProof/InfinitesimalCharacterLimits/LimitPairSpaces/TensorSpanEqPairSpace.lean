import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def TypF {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (f : GA E N → ℂ) : Prop :=
  (∀ u ∈ K, ∀ g, f (g * finGL E N u) = f g) ∧ ∀ g, (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ W

def TypSp {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (U : Submodule ℂ (Sm E N)) :
    Submodule ℂ (Sm E N) :=
  Submodule.span ℂ {φ | φ ∈ U ∧ TypeB K W φ}

def _root_.PositivityTheory.Rg.BcB.SpectralAccumulation.Tr.addTw : {N : ℕ} → Tr E N → (ℕ → ℂ) → Tr E N
  | _, .leaf V z, α => .leaf V (z + α 0)
  | _, .node t₁ t₂, α => .node (t₁.addTw α) (t₂.addTw fun i => α (i + t₁.twists.length))

abbrev Cint (E : Type) [Field E] [NumberField E] (n : ℕ) : Subgroup (GL (Fin n) (Af E)) :=
  GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n

theorem exists_decI {r s : ℕ} (x : GA E (r + s)) :
    ∃ q : (BlockIx (r + s) r → Ad E) × (GA E r × GA E s) × Kinf E (r + s) × GL (Fin (r + s)) (Af E),
      q.2.2.2 ∈ Cint E (r + s) ∧ x = unip q.1 * lev (Ad E) r s q.2.1 * InducedTensorMap.cf (r + s) q.2.2.1 q.2.2.2 := by
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (Matrix.GeneralLinearGroup.map (pInf E) x)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (Matrix.GeneralLinearGroup.map (pFin E) x)
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add, show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add, show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨(fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), k, c), hc, ga_ext ?_ ?_⟩
  · simp only [InducedTensorMap.cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [InducedTensorMap.cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf]

def mult : {N : ℕ} → Tr E N → (ℕ → ℂ) → GA E N → ℂ
  | _, .leaf _ _, γ => GlobalTheory.CompanionTheory.LimV.absFn _ (γ 0)
  | _, @Tr.node _ _ _ _ _ _ t₁ t₂, γ => GlobalTheory.CompanionTheory.LimV.nodeFn (mult t₁ γ) (mult t₂ fun i => γ (i + t₁.twists.length))

theorem typeB_iff {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (φ : Sm E N) :
    TypeB K W φ ↔ TypF K W φ.1 := Iff.rfl

theorem tensor_span_eq_pair_space {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ = tens2 U₁ U₂ := rfl

theorem mult_leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℂ) (γ : ℕ → ℂ) (x : GA E N) :
    mult (Tr.leaf V z) γ x = ((chiDet _ (Model.absC E (γ 0)) x : ℂˣ) : ℂ) := rfl

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
