import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearMapVaryPureTensorFactorSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorPureTensorCoefficientSplitsTrivialPlacStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalTwistDatumRenumberRowsColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistLinModel
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl)
variable {D : D7}

theorem triv_eq_ofLocal (Pg : Finset (Pl D.host.E)) (r : ℕ) :
    LevelP.triv Pg r ℂ = LevelP.ofLocal (fun _ => ⊥) (fun _ => 1) := by
  have hH : Subgroup.pi Set.univ (fun PP : ↥Pg => (⊥ : Subgroup (GL (Fin r) (kP PP.1)))) = ⊥ := by
    ext x
    simp only [Subgroup.mem_pi, Set.mem_univ, true_implies, Subgroup.mem_bot]
    exact ⟨fun h => funext h, fun h PP => congrFun h PP⟩
  have key : ∀ (H H' : Subgroup (G0 Pg r)) (h : H = H'), HEq (1 : H →* ℂˣ) (1 : H' →* ℂˣ) := by
    intro H H' h; subst h; rfl
  unfold LevelP.triv LevelP.ofLocal
  simp only [MonoidHom.one_comp, Finset.prod_const_one]
  congr 1
  · exact hH.symm
  · exact key _ _ hH.symm

end GlobalTheory.TwistLinModel

namespace GlobalTheory.TwistLinModel
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl)
variable {D : D7}

set_option maxHeartbeats 2000000 in
theorem detAt_exists {v : FinPl D} (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) (V : HSp D)
    (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    ∃ a : (AE D)ˣ, IsDetAt e V g a ∧ (1 - e) * (a : AE D) = 1 - e ∧
      rdA φ (a : AE D) = ((Matrix.GeneralLinearGroup.det (grpCo φ V B g) : (Fv D.host.F v)ˣ) : Fv D.host.F v) := by
  have hee : e * e = e := he.1.1
  obtain ⟨u, hu⟩ : ∃ u : (AE D)ˣ, (u : AE D) = (Formalism.L2.Theta.mt V g).det :=
    ⟨Matrix.GeneralLinearGroup.det (matHom V g), rfl⟩
  refine ⟨⟨e * u + (1 - e), e * (u⁻¹ : (AE D)ˣ) + (1 - e), ?_, ?_⟩, ?_, ?_, ?_⟩
  · have h1 : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv u
    linear_combination ((u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) - u - ((u⁻¹ : (AE D)ˣ) : AE D) + 1) * hee + e * h1
  · have h1 : ((u⁻¹ : (AE D)ˣ) : AE D) * (u : AE D) = 1 := Units.inv_mul u
    linear_combination (((u⁻¹ : (AE D)ˣ) : AE D) * (u : AE D) - u - ((u⁻¹ : (AE D)ˣ) : AE D) + 1) * hee + e * h1
  · show e * (u : AE D) + (1 - e) = e * (Formalism.L2.Theta.mt V g).det + (1 - e)
    rw [hu]
  · show (1 - e) * (e * (u : AE D) + (1 - e)) = 1 - e
    linear_combination (1 - (u : AE D)) * hee
  · show rdA φ (e * (u : AE D) + (1 - e)) = _
    rw [map_add, map_mul, map_sub, map_one, he.2.2, one_mul, sub_self, add_zero, hu]
    simp only [grpCo, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.det_mul, Matrix.GeneralLinearGroup.map]
    have h : ((B⁻¹ : GL (Fin V.rank) (Fv D.host.F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v)).det *
        ((B : GL (Fin V.rank) (Fv D.host.F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v)).det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.det_one]
    show (rdA φ) (Formalism.L2.Theta.mt V g).det = _ * ((rdA φ).mapMatrix (Formalism.L2.Theta.mt V g)).det * _
    generalize Formalism.L2.Theta.mt V g = M
    rw [RingHom.map_det]
    linear_combination (-((rdA φ).mapMatrix M).det) * h

end GlobalTheory.TwistLinModel

namespace GlobalTheory.TwistLinModel
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl)
variable {D : D7}

theorem mem_GfC_of_gAt {v : FinPl D} (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) (V : HSp D)
    (g : GA D V) (hg : gAt V (.inl v) g = g) : g ∈ GfC V := by
  refine GlobalTheory.WeilProduct.mem_GfC_of_suppAt he.1 fun i j => ?_
  have hm := ((GlobalTheory.PlaceComponent.gAt_laws D).1 V (.inl v) g).1
  rw [hg] at hm
  have hij := congrFun (congrFun hm i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hij
  rw [he.2.1]
  change GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) * (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
    Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j
  linear_combination (-1 : AE D) * hij
end GlobalTheory.TwistLinModel

namespace GlobalTheory.TwistLinModel
variable {D : D7}

theorem splitFac_coe (χS χT : (AE D)ˣ →* Circle) (a b : (AE D)ˣ) :
    ((splitFacO χS χT a b : Circle) : ℂ) = (((Circle.toUnits (χT a))⁻¹ * Circle.toUnits (χS b) : ℂˣ) : ℂ) := by
  simp [splitFacO]

end GlobalTheory.TwistLinModel

namespace GlobalTheory.TwistLinModel
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (IsBase IsPure IsBaseOff StepVecLocal onHalf mapCo ipO wAt idem FinPl Place)
open GlobalTheory.PlaceTensor (pull IsCoord)

theorem placeModel_isometry_borel (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀)
    (hc : IsCovolOne (ratL T S) μ 𝓕) (v : FinPl D) (a : AE D) (ha : IsSplitIdem D a) (m n : ℕ)
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) (hκ : IsCoord a (latO S T ΛS ΛT fun _ => True) κ)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    [inst : MeasurableSpace (Fv D.host.F v)] [hbor : BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v))
    (hν : ν.IsAddHaarMeasure) :
    GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t}) ≠ 0 ∧
    GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t}) ≠ ⊤ ∧
    ∀ Φ₁ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), ∀ Φ₂ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)),
      ((GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n) (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) *
        ipO μ 𝓕 (Tm (pull a κ Φ₁)) (Tm (pull a κ Φ₂)) = GlobalTheory.SplitWeil.ip ν Φ₁ Φ₂ := by
  obtain rfl : inst = borel _ := hbor.measurable_eq
  exact GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hc v a ha m n κ hκ Tm hT ν hν

end GlobalTheory.TwistLinModel

set_option maxHeartbeats 1000000 in
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (IsBase IsPure IsBaseOff StepVecLocal onHalf mapCo ipO wAt idem FinPl Place) in

theorem GlobalTheory.TwistLinModel.linearModel_at_twist : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P m X, IsCovolOne (ratL s'.V s.V) m X → ∃ (hW : ∀ g h, ∀ u ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)), GlobalTheory.ParHecke.omTwo μS μT g h u ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v))) (hΦ : datum ξl⁻¹ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v))) (T : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ (∀ g h (u : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v))), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩) ∧ ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ x : GA D s.V, gAt s.V (.inl v) x = 1 → ∃ C : ℂ, ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)), ∫ z in X, p.ω (x, 1) (T u) z * conj (T u' z) ∂m = C * GlobalTheory.SplitWeil.ip ν u.1 u'.1 := by
  classical
  intro D hgap c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hμS hμT hξl P m X hX
  have hs0 := hs
  obtain ⟨hr, hsL, hsf⟩ := hs
  obtain ⟨hr', hsL', hsf'⟩ := hs'
  have hψ : IsStdChar D c.ψ (-1) := hw.com.std
  have hθ : IsInfFam c.θ := hw.com.inf
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hbase : IsBase c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ f₀ :=
    ⟨fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ, fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ,
      hsf.selfDual, hsf'.selfDual, hvec.1⟩
  have hLP : s.L.P = LevelP.ofLocal (fun _ => ⊥) (fun _ => 1) := by
    rw [hsL]; exact GlobalTheory.TwistLinModel.triv_eq_ofLocal _ _
  have hPg : s.L.Pg = w.Pg := by rw [hsL]; rfl
  have hLr : s.L.r = D.R.r := by rw [hsL]; rfl
  have hdisj : Disjoint s.L.Pg w.Q := hPg ▸ hw.disj
  have ht : s.V.rank + D.R.t = s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hsf.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hsf'.rank
    rw [h1, h2]; show D.R.r + k * D.R.t + D.R.t = D.R.r + (k + 1) * D.R.t; ring
  obtain ⟨⟨x, hxoff, hxloc⟩, hxall⟩ := GlobalTheory.StepVec.stepVecLocal D c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β
    s.L (w.chi (k + 1)) w.Q w.ξ f₀ p.f m X D.R.t ht _ _ hLP hbase hX hsf.frame hsf'.frame hdisj hvec
  have hxpure := hxall x ⟨hxoff, hxloc⟩

  obtain ⟨e, he⟩ := ((GlobalTheory.T.exists_charts_at_twist_places_chain D c w hw k hk.le s hs0 PP hPP).2 v φ hφ).1

  obtain ⟨ε, hε, hιy⟩ := hι
  obtain ⟨ε', hε', hιy'⟩ := hι'
  have hre := GlobalTheory.T.local_twist_datum_renumber_rows_columns D v D.R.r s.V.rank s'.V.rank (Blocks k D.R.t) (Blocks (k + 1) D.R.t) ε ε' hε hε'

  have htame : GlobalTheory.SplitWeil.IsTame ξl⁻¹ := by
    have h := (GlobalTheory.tameLift_isTame_not_isUnram D v φ PP (w.ξ PP) hφ (hw.ne PP hPP) ξl hξl).1
    intro y hy; rw [MonoidHom.inv_apply, h y hy, inv_one]
  have hlift : LiftsChar φ PP ξl⁻¹ (w.ξ PP)⁻¹ := by
    intro u k' hu; rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hξl u k' hu]
  have hΦ : datum ξl⁻¹ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) :=
    (hre.1 ξl⁻¹).2 htame

  obtain ⟨R, hR⟩ : ∃ R : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) →ₗ[ℂ]
      GlobalTheory.SplitWeil.SB (Matrix (Fin s'.V.rank) (Fin s.V.rank) (Fv D.host.F v)),
      ∀ u z, (R u).1 z = u.1 (z.submatrix ε' ε) :=
    ⟨{ toFun := fun u => ⟨fun z => u.1 (z.submatrix ε' ε), (hre.2.1 u.1).1 u.2⟩
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl }, fun _ _ => rfl⟩

  have hth := (hxloc v φ e he ξl⁻¹).2 PP hPP hφ hlift
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hxv : x (.inl v) = Tm (onHalf φ s.V s'.V (frCo φ s.β) (frCo φ s'.β) e (R ⟨_, hΦ⟩).1) := by
    rw [hall Tm hTm, hLr, (hre.1 ξl⁻¹).1]; congr 2; funext z; rw [hR]
  obtain ⟨T₀, hT₀Φ, hT₀pure, hT₀act⟩ := GlobalTheory.T.exists_linearMap_vary_pureTensor_factor_split_place D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω (cart s.M) (cart s'.M)
    s.Λ s'.Λ f₀ m X hp.weil hθ hbase hX x p.f hxpure v φ e he (frCo φ s.β) (frCo φ s'.β) (R ⟨_, hΦ⟩) Tm hTm hxv
  have hT₀θ : ∀ u, IsThetaFunO c.ψ s.V s'.V (T₀ u) := fun u => by
    obtain ⟨x', -, -, hx'⟩ := hT₀pure u; exact hx'.2.1
  have hW : ∀ g h, ∀ u ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)),
      GlobalTheory.ParHecke.omTwo μS μT g h u ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) :=
    fun g h u hu => (hre.2.2.1 μS μT g h u).1 hu
  refine ⟨hW, hΦ,
    { toFun := fun u => pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) (T₀ (R u)) P
      map_add' := fun u u' => ?_
      map_smul' := fun a u => ?_ }, ?_, fun u => ?_, fun g h u => ?_, ?_⟩
  · simp only [map_add]
    have := GlobalTheory.FockFiniteHeis.pureTensorO_lin c.ψ c.θ s.V s'.V hψ hθ (cart s.M) (onb s.M) (cart s'.M) (onb s'.M) 1
      (hT₀θ (R u)) (hT₀θ (R u')) P
    simpa using this
  · simp only [map_smul, RingHom.id_apply]
    have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin c.ψ c.θ s.V s'.V hψ hθ (cart s.M) (onb s.M) (cart s'.M) (onb s'.M) a
      (hT₀θ (R u)) GlobalTheory.OrientedHeis.theta_zero P
    rwa [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero c.ψ c.θ s.V s'.V hψ hθ, add_zero] at h
  · show pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) (T₀ (R ⟨_, hΦ⟩)) P = p.pt P
    rw [hT₀Φ]; rfl
  · exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ (cart s.M) (onb s.M) (cart s'.M) (onb s'.M) (hT₀θ _) P
  · show p.ω (ι g, ι' h) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) (T₀ (R u)) P) =
      pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) (T₀ (R ⟨_, hW g h u u.2⟩)) P
    have hg := (hιy g).1
    have hh := (hιy' h).1
    rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω hp.weil c.θ hθ (ι g)
      (GlobalTheory.TwistLinModel.mem_GfC_of_gAt φ he s.V (ι g) hg) (ι' h) (GlobalTheory.TwistLinModel.mem_GfC_of_gAt φ he s'.V (ι' h) hh)
      (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) (T₀ (R u)) P (hT₀θ _)]
    obtain ⟨a, hda, ha1, ha2⟩ := GlobalTheory.TwistLinModel.detAt_exists φ he s.V (frCo φ s.β) (ι g)
    obtain ⟨b, hdb, hb1, hb2⟩ := GlobalTheory.TwistLinModel.detAt_exists φ he s'.V (frCo φ s'.β) (ι' h)
    have hra := (hre.2.2.1 μS μT g h u.1).2 (grpCo φ s.V (frCo φ s.β) (ι g)) (grpCo φ s'.V (frCo φ s'.β) (ι' h))
      (hιy g).2 (hιy' h).2
    have hmuT := hμT a _ ⟨e, he, ha1, ha2⟩
    have hmuS := hμS b _ ⟨e, he, hb1, hb2⟩
    obtain ⟨cc, hcc⟩ : ∃ cc : ℂ, cc = (((μT (Matrix.GeneralLinearGroup.det (grpCo φ s.V (frCo φ s.β) (ι g))))⁻¹ *
      μS (Matrix.GeneralLinearGroup.det (grpCo φ s'.V (frCo φ s'.β) (ι' h))) : ℂˣ) : ℂ) := ⟨_, rfl⟩
    have hcc0 : cc ≠ 0 := by rw [hcc]; exact Units.ne_zero _
    rw [← hcc] at hra
    have hlin : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.linOm v (grpCo φ s.V (frCo φ s.β) (ι g)) (grpCo φ s'.V (frCo φ s'.β) (ι' h)) (R u).1 ∈
        GlobalTheory.SplitWeil.SB (Matrix (Fin s'.V.rank) (Fin s.V.rank) (Fv D.host.F v)) := by
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.linOm v (grpCo φ s.V (frCo φ s.β) (ι g)) (grpCo φ s'.V (frCo φ s'.β) (ι' h)) (R u).1 =
          cc⁻¹ • (R ⟨_, hW g h u u.2⟩).1 := by
        funext z
        have := congrFun hra z
        simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [hR]; dsimp only; rw [this, ← mul_assoc, inv_mul_cancel₀ hcc0, one_mul]
        congr 1; funext z'; rw [hR]
      rw [e1]; exact Submodule.smul_mem _ _ (R _).2
    have hact := hT₀act (ι g) (ι' h) hg hh a b hda hdb (R u) ⟨_, hlin⟩ rfl
    rw [hact]
    have hRu : R ⟨_, hW g h u u.2⟩ = cc • (⟨_, hlin⟩ : GlobalTheory.SplitWeil.SB (Matrix (Fin s'.V.rank) (Fin s.V.rank) (Fv D.host.F v))) := by
      apply Subtype.ext; funext z
      have := congrFun hra z
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [hR]; dsimp only; rw [this]
      congr 1; congr 1; funext z'; rw [hR]
    have hsf : ((splitFacO (c.chS (k + 1)) (c.chT (k + 1)) a b : Circle) : ℂ) = cc := by
      rw [hcc, hmuT, hmuS]; exact GlobalTheory.TwistLinModel.splitFac_coe _ _ _ _
    have hfin : T₀ (R ⟨_, hW g h u u.2⟩) = cc • T₀ ⟨_, hlin⟩ := (congrArg T₀ hRu).trans (T₀.map_smul cc _)
    have hfin2 := (congrArg (fun z : ℂ => z • T₀ ⟨_, hlin⟩) hsf).trans hfin.symm
    exact congrArg (fun f => pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f P) hfin2
  · intro inst1 inst2 ν hν g hg1
    have hri := hre.2.2.2 ν hν.1
    obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.fockVector_pureTensor_coefficient_splits_trivial_place D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω (cart s.M) (cart s'.M) s.Λ s'.Λ f₀
      m X hp.weil hθ hbase hX (onb s.M) (onb s'.M) x hxoff.1 v P g hg1
    have hco := (GlobalTheory.PlaceCoord.isCoord_mapCo D s.V s'.V s.Λ s'.Λ hsf.selfDual hsf'.selfDual v φ e he (frCo φ s.β) (frCo φ s'.β)).1
    have hI := GlobalTheory.TwistLinModel.placeModel_isometry_borel D c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ f₀ m X
      hbase hX v e he.1 s'.V.rank s.V.rank (mapCo φ s.V s'.V (frCo φ s.β) (frCo φ s'.β)) hco Tm hTm (inst := inst1) (hbor := inst2) ν hν.1
    have hv0 := hI.1
    have hvtop := hI.2.1
    have hiso := hI.2.2
    have hvol : (ENNReal.toReal (GlobalTheory.SplitWeil.volM ν (Fin s'.V.rank) (Fin s.V.rank)
        (mapCo φ s.V s'.V (frCo φ s.β) (frCo φ s'.β) '' {t | t ∈ latO s.V s'.V s.Λ s'.Λ (fun _ => True) ∧ IsHalf e t})) : ℂ) ≠ 0 := by
      exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hv0, hvtop⟩)
    refine ⟨C₁ / (ENNReal.toReal (GlobalTheory.SplitWeil.volM ν (Fin s'.V.rank) (Fin s.V.rank)
        (mapCo φ s.V s'.V (frCo φ s.β) (frCo φ s'.β) '' {t | t ∈ latO s.V s'.V s.Λ s'.Λ (fun _ => True) ∧ IsHalf e t})) : ℂ),
      fun u u' => ?_⟩
    have hx₁ := (hT₀pure (R u)).choose_spec
    have hx₂ := (hT₀pure (R u')).choose_spec
    have key := hC₁ _ _ (T₀ (R u)) (T₀ (R u')) hx₁.1 hx₂.1 hx₁.2.2 hx₂.2.2
    have hx₁v := hx₁.2.1
    have hx₂v := hx₂.2.1
    have h3 := hiso (R u).1 (R u).2 (R u').1 (R u').2
    have h4 := hri u.1 u'.1
    have e1 : (fun z : Matrix (Fin s'.V.rank) (Fin s.V.rank) (Fv D.host.F v) => u.1 (z.submatrix ε' ε)) = (R u).1 := by
      funext z; rw [hR]
    have e2 : (fun z : Matrix (Fin s'.V.rank) (Fin s.V.rank) (Fv D.host.F v) => u'.1 (z.submatrix ε' ε)) = (R u').1 := by
      funext z; rw [hR]
    rw [e1, e2] at h4
    change ipO m X (p.ω (g, 1) (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) (T₀ (R u)) P))
      (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) (T₀ (R u')) P) = _
    rw [key, hx₁v, hx₂v]
    rw [← h4, ← h3, ← mul_assoc, div_mul_cancel₀ C₁ hvol]
    rfl
