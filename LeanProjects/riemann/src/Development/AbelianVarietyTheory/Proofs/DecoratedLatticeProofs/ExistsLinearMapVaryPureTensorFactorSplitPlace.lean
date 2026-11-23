import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniquePureTensorRestrictedFamily
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepActsOnPureTensorsPlacewise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelCoordinatesBijOnAndWeilLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryComponentAtPlaceLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.VarySplitFactor.exists_linearMap_pure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (Φ₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))), ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → x (.inl v) = Tm (onHalf φ S T BS BT e Φ₀.1) → ∃ T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ] (WO S T → ℂ), T₀ Φ₀ = f ∧ (∀ u, ∃ x' : Place D → WO S T → ℂ, (∀ p, p ≠ .inl v → x' p = x p) ∧ x' (.inl v) = Tm (onHalf φ S T BS BT e u.1) ∧ IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (T₀ u)) ∧ ∀ g h, gAt S (.inl v) g = g → gAt T (.inl v) h = h → ∀ a b, IsDetAt e S g a → IsDetAt e T h b → ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)), u'.1 = linOm v (grpCo φ S BS g) (grpCo φ T BT h) u.1 → om (g, h) (T₀ u) = ((splitFacO χS χT a b : Circle) : ℂ) • T₀ u' := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW _hθ hB hC x f hx v φ e he BS BT Φ₀ Tm hT hxv
  classical
  have hcoord := GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hsplit := GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕
    hW hB hC v e e he.1 he.2.1 (Or.inl rfl) T.rank S.rank (mapCo φ S T BS BT) hcoord.1 Tm hT
  have honHalf : ∀ Φ, onHalf φ S T BS BT e Φ = pull e (mapCo φ S T BS BT) Φ := fun Φ => rfl
  let xf : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →
      Place D → WO S T → ℂ :=
    fun u => Function.update x (.inl v) (Tm (onHalf φ S T BS BT e u.1))
  have hres : ∀ u, IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (xf u) := by
    intro u
    refine ⟨fun p => ?_, ?_⟩
    · by_cases hp : p = .inl v
      · subst hp
        simp only [xf, Function.update_self]
        rw [honHalf]
        exact hsplit.1.mapsTo u.2
      · simp only [xf, Function.update_of_ne hp]
        exact hx.1.1 p
    · apply (hx.1.2.union (Set.finite_singleton (Sum.inl v : Place D))).subset
      intro p hp
      by_cases h : p = .inl v
      · exact Or.inr h
      · left
        simpa [xf, Function.update_of_ne h] using hp
  have hEU := fun u => GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕
    hB hC (xf u) (hres u)
  let F := fun u => (hEU u).exists.choose
  have hF : ∀ u, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (xf u) (F u) :=
    fun u => (hEU u).exists.choose_spec
  have huniq : ∀ y f1 f2, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f1 →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f2 → f1 = f2 := fun y f1 f2 h1 h2 =>
    (GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC y h1.1).unique
      h1 h2
  have hlin := (GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1
  have hscale : ∀ (y z : Place D → WO S T → ℂ) (g : WO S T → ℂ) (q : Place D) (c : ℂ),
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → z p = y p) → z q = c • y q →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • g) := by
    intro y z g q c hy hz hzq
    have := hlin y y z g g q (c - 1) hy hy (fun _ _ => rfl) hz
      (by rw [hzq, sub_smul, one_smul, sub_add_cancel])
    rwa [sub_smul, one_smul, sub_add_cancel] at this
  have hOnAdd : ∀ (Φ Ψ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (Φ + Ψ) = onHalf φ S T BS BT e Φ + onHalf φ S T BS BT e Ψ := by
    intro Φ Ψ
    funext t
    simp only [onHalf, Pi.add_apply]
    split_ifs <;> simp
  have hOnSmul : ∀ (c : ℂ) (Φ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (c • Φ) = c • onHalf φ S T BS BT e Φ := by
    intro c Φ
    funext t
    simp only [onHalf, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  let T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ]
      (WO S T → ℂ) :=
    { toFun := F
      map_add' := by
        intro u u'
        have hz := hlin (xf u) (xf u') (xf (u + u')) (F u) (F u') (.inl v) 1 (hF u) (hF u')
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_add]
            rw [hOnAdd, map_add, one_smul])
        rw [one_smul] at hz
        exact huniq _ _ _ (hF (u + u')) hz
      map_smul' := by
        intro c u
        have hz := hscale (xf u) (xf (c • u)) (F u) (.inl v) c (hF u)
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_smul]
            rw [hOnSmul, map_smul])
        exact huniq _ _ _ (hF (c • u)) hz }
  have hT₀ : ∀ u, T₀ u = F u := fun u => rfl
  refine ⟨T₀, ?_, fun u => ⟨xf u, fun p hp => by simp only [xf, Function.update_of_ne hp],
    by simp only [xf, Function.update_self], hF u⟩, ?_⟩
  · rw [hT₀]
    have hxx : xf Φ₀ = x := by
      simp only [xf]
      rw [← hxv]
      exact Function.update_eq_self _ _
    exact huniq _ _ _ (hF Φ₀) (hxx ▸ hx)
  · intro g h hg hh a b ha hb u u' hu'
    have laws := GlobalTheory.PlaceComponent.gAt_laws D
    have hgp : ∀ p, p ≠ Sum.inl v → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact ((laws.1 S (.inl v) g).2.2 p hp)
    have hhp : ∀ p, p ≠ Sum.inl v → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact ((laws.1 T (.inl v) h).2.2 p hp)
    have hsupp : ∀ (V : HSp D) (k : GA D V), gAt V (.inl v) k = k → SuppAt e V k := by
      intro V k hk i j
      have hm := (laws.1 V (.inl v) k).1
      rw [hk] at hm
      have key : Formalism.L2.Theta.mt V k - 1 =
          idem D (Sum.inl v) • (Formalism.L2.Theta.mt V k - 1) := by
        conv_lhs => rw [hm]
        rw [smul_sub, sub_smul, one_smul]
        abel
      rw [he.2.1]
      have := congrFun (congrFun key i) j
      rw [Matrix.smul_apply, smul_eq_mul] at this
      exact this.symm
    have hom := GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hC
      (xf u) (F u) (hF u) g h
    have hact := hsplit.2 g h (hsupp S g hg) (hsupp T h hh) a b ha hb
      (grpCo φ S BS g) (grpCo φ T BT h) (hcoord.2 g h) u.1 u.2
    have hz := hscale (xf u') (fun p => om (gAt S p g, gAt T p h) (xf u p)) (F u') (.inl v)
      ((splitFacO χS χT a b : Circle) : ℂ) (hF u')
      (fun p hp => by
        simp only [xf, Function.update_of_ne hp, hgp p hp, hhp p hp]
        have h11 : ((1 : GA D S), (1 : GA D T)) = 1 := rfl
        rw [h11, map_one]; rfl)
      (by
        simp only [xf, Function.update_self, hg, hh]
        rw [honHalf, hact, honHalf, hu'])
    exact huniq _ _ _ hom hz
