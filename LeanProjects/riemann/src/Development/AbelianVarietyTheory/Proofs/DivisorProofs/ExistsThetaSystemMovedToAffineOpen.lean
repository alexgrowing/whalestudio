import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartLiftToModuliSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8ThetaPowerOverModuliDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpOverOfPolarizedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonGenericFibreDiagonalEndEighthPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineCStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescalingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.exists_rechart_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ w : X₁.M.Z, X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (fg : (X₁.M.ringOn U).FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ X₁.M.ringOn U) (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ X₁.M.ringOn U) (ρ' : (X₁.S.rechart c₀ hc (X₁.M.ringOn U) fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ IsDiagEnd F W ρ'.P u' ε' ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u' = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ _hg1 _hn3 _hodd _himm he8 _hti _hproj ε₁ hε₁ w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hU₀i, hu₀⟩ := GlobalTheory.T.exists_affineChart_lift_to_moduli_scheme g n F W Z i X₁ w hw
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_e8ThetaPower_over_moduli_domain g n F W he8 (X₁.M.ringOn U₀) u₀
  have hN : 1 ≤ X₁.S.N := by have := X₁.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₀, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.T.exists_universal_section_bases_shrunk_affineChart X₁.o₁ X₁.Ω₁ X₁.M U₀ w hU₀a hwU₀ P₁ X₁.S.N hN
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hsh : SharpOver F W P' (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) :=
    GlobalTheory.T.sharpOver_of_polarized_pullback g n F W _ _ P₁ P' u₀ _ φ hP₁ hφ hφL
  have hsp : spMap (X₁.M.ringOn U).val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom =
      spMap (X₁.M.ringOn U₀).val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have hcomp : spMap X₁.S.R.val.toRingHom ≫ X₁.u =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) := by
    rw [← Category.assoc, hsp, hu₀]
  obtain ⟨ε', hε', P₀, a, a', ε₀, ha, ha', hL, hL', hε₀⟩ :=
    GlobalTheory.T.exists_common_genericFibre_diagonalEnd_eighthPower g n F W X₁.S.R (X₁.M.ringOn U) X₁.Ω₁ X₁.S.R.val.toRingHom (X₁.M.ringOn U).val.toRingHom X₁.ρ.P X₁.u ε₁ P' _
      hε₁ hsh hcomp
  have hg' : P'.g = X₁.S.g :=
    (GlobalTheory.T.polAV_dim_eq_of_grpPullback_field X₁.Ω₁ _ P' P₀ _ a' ha').symm.trans ((GlobalTheory.T.polAV_dim_eq_of_grpPullback_field X₁.Ω₁ _ X₁.ρ.P P₀ _ a ha).trans X₁.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.T.lineBundleSymmetryHypothesis_extends_normal_affineChart X₁.o₁ X₁.Ω₁ X₁.M U hUa hne X₁.normal X₁.S.R X₁.ρ.P P' P₀ _ a a' ha ha' hL hL' X₁.ρ.hypS
  obtain ⟨pt', hadd, hbij, hweil, hmatch⟩ := GlobalTheory.T.polarized_abelian_variety_pullback_affine_open g n F W Z i X₁ U P' P₀ a a' hUa hne ha ha' hL hL'
  have fg : (X₁.M.ringOn U).FG := GlobalTheory.T.ringOn_affineOpen_finitelyGenerated X₁.o₁ X₁.Ω₁ X₁.M U hUa hne
  have frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ε'', hSame, hi₀, hD⟩ :=
    GlobalTheory.T.thetaSetup_extends_normal_affineChart_after_rescaling g n F W Z i X₁ U ε₁ fg frac _ P' ε' P₀ a a' ε₀ pt' th b hUa hne hε₁ hε' ha ha' hL hL' hε₀ hg' hyp hadd hbij
      hweil hmatch hth hb
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', ε'', _, hUa, hwU, fun w' hw' => hU₀i w' (hUU₀ hw'), hSame, hi₀, hD,
    hcomp.symm⟩
