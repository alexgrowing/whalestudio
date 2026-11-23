import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactorStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOnto

theorem exists_finite_quotient_ne_zero {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (M : AddSubgroup X)
    (hM : M ≠ ⊤) : ∃ (F : Type) (_ : AddCommGroup F) (_ : Finite F) (l : X →+ F), l ≠ 0 ∧ ∀ x ∈ M, l x = 0 := by
  have hM' : M.toIntSubmodule ≠ ⊤ := fun h => hM (eq_top_iff.2 fun x _ => by
    have : x ∈ M.toIntSubmodule := h ▸ Submodule.mem_top
    exact this)
  obtain ⟨N, hN, hMN⟩ := (IsCoatomic.eq_top_or_exists_le_coatom M.toIntSubmodule).resolve_left hM'
  haveI : IsSimpleModule ℤ (X ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 this
  haveI : Finite (ℤ ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField)
  haveI : Finite (X ⧸ N) := Finite.of_equiv _ e.toEquiv.symm
  refine ⟨X ⧸ N, inferInstance, inferInstance, N.mkQ.toAddMonoidHom, fun h => hN.1 ?_, fun x hx => ?_⟩
  · refine eq_top_iff.2 fun x _ => (Submodule.Quotient.mk_eq_zero N).1 ?_
    exact DFunLike.congr_fun h x
  · exact (Submodule.Quotient.mk_eq_zero N).2 (hMN hx)

instance isFinite_splitTorus (S : Scheme.{0}) (F : Type) [AddCommGroup F] [Finite F] :
    IsFinite (splitTorus S F).hom := by
  have : IsFinite (splitTorusAff ZU.{0} F).hom := by
    show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} (torusRing ZU.{0} F))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  exact inferInstanceAs (IsFinite (pullback.snd _ _))

end GlobalTheory.TorusOnto

namespace GlobalTheory.TorusOnto

theorem restrict_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    Function.Surjective ρ := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ _ hΩ hφ₀ h₀j
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V) 0 ≫ j := by
    haveI : IsSeparated tV.G.hom := tV.semi.separated
    have hjac : maximalIdeal V ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V (maximalIdeal V) hjac (splitTorus (Sp V) F) tV.G _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V ⧸ maximalIdeal V ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V →+* V ⧸ maximalIdeal V ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback tV.G (thick V (maximalIdeal V) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V (maximalIdeal V) e tV.G) t.G (spMap (q.comp ψ))
        (pullback.fst tV.G.hom (thick V (maximalIdeal V) e) ≫ mV.φ) :=
      (he.comp mV.cart).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P _ (q.comp ψ) e ha _ _ hR
    obtain ⟨ρe, hρe⟩ := hfac P'.D.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance

    have hres : ∀ x ∈ maximalIdeal V ^ (e + 1), residue V x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres m₀.cart
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V).comp ψ) x = 0 := fun x hx =>
      h₀ x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus m₀.cart j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he m₀.cart (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres m₀.cart).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha' m₀'.cart :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V) hres) (P.U.gt e) ha ha' hR m₀'.cart ke
        (RingHom.ext fun x => rfl)
        (hφ₀.trans (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst]))
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P _ ((residue V).comp ψ) e ha' t₀.G m₀'.φ m₀'.cart
    obtain ⟨u, hu⟩ := hfac' P.D.toPre.X (GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : P'.D.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : P'.D.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V) F).hom (thick V (maximalIdeal V) e) ≫ _ =
      pullback.fst (splitTorus (Sp V) F).hom (thick V (maximalIdeal V) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.PELUnif.torus P' hβ n') :=
    (GlobalTheory.T.uniformisationTorus_mono_and_factor E H W (maximalIdeal W) t' P' Ω β 0 (GlobalTheory.TorusPart.map_pow_one_eq_zero hβ) tΩ.G n'.φ n'.cart).1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus n.cart) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOnto
