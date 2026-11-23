import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Adelic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionsFieldChange

open GlobalTheory.AbLaw
open scoped TensorProduct

variable {X Y : Scheme.{0}}

theorem ofSec_secPull {L : LB X} (s : L.Sec) (π : Y ⟶ X) (V : X.Opens) :
    GlobalTheory.LB.ofSec (secPull s π) (π ⁻¹ᵁ V) =
      SecOn.pullLE L π V (π ⁻¹ᵁ V) le_rfl (GlobalTheory.LB.ofSec s V) := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_ofSec, SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  exact GlobalTheory.LB.resG_appLE π _ _ (s.f (j PUnit.unit))

theorem ofSec_smul {L : LB X} (a : Γ(X, ⊤)) (s : L.Sec) (V : X.Opens) :
    GlobalTheory.LB.ofSec (a • s) V = rs X (le_top : V ≤ ⊤) a • GlobalTheory.LB.ofSec s V := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.smul_f, map_mul, GlobalTheory.resG_resG]
  exact congrArg (· * _) (GlobalTheory.resG_resG _ _ _).symm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev secModule {k : Type} [Field k] (S : LinSys k) : Module k S.L.Sec :=
  Module.compHom _ (algebraMap k Γ(S.Y, ⊤))

attribute [local instance] secModule

theorem secTower {k : Type} [Field k] (S : LinSys k) : IsScalarTower k Γ(S.Y, ⊤) S.L.Sec :=
  ⟨fun a g s => by
    show (algebraMap k Γ(S.Y, ⊤) a * g) • s = algebraMap k Γ(S.Y, ⊤) a • (g • s)
    rw [mul_smul]⟩

attribute [local instance] secTower

theorem isProper_str {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : IsProper S.str := by
  obtain ⟨N, i, hi, e⟩ := hS.proj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
  rw [← e]
  infer_instance

theorem finite_sec {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : Module.Finite k S.L.Sec := by
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) S.L) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj S.isLB
  exact Module.Finite.equiv ((cohZeroTwistEquiv S.L).restrictScalars k)

theorem finrank_baseChange (S : LinSys F) (hS : S.IsVariety) :
    Module.finrank E (S.baseChange E).L.Sec = Module.finrank F S.L.Sec := by
  have := isProper_str hS
  rw [← lineBundleGlobalSectionsDim_eq_finrank, ← lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_def, lineBundleGlobalSectionsDim_def]
  exact FieldChangeInter.hdim_pull (S.isPullback_baseChange E) S.isLB 0

def resTo {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens) :
    L.Sec →+ SecOnR f L V where
  toFun s := SecOnR.of f L V (GlobalTheory.LB.ofSec s V)
  map_zero' := SecOnR.ext fun i => by
    rw [SecOnR.coord_of, GlobalTheory.LB.coord_ofSec, LB.zero_f, map_zero, SecOnR.coord_zero]
  map_add' s t := SecOnR.ext fun i => by
    rw [SecOnR.coord_add, SecOnR.coord_of, SecOnR.coord_of, SecOnR.coord_of, GlobalTheory.LB.coord_ofSec,
      GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.add_f, map_add]

theorem resTo_smul {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens)
    (a : R) (s : L.Sec) :
    letI := algebraΓOfHom f
    resTo f L V (algebraMap R Γ(X, ⊤) a • s) = a • resTo f L V s :=
  ofSec_smul _ s V

theorem resTo_secPull (S : LinSys F) (E : Type) [Field E] [Algebra F E] (V : S.Y.Opens) (s : S.L.Sec) :
    resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ V) (secPull s (S.bcFst E)) =
      SecOnR.pull S.L (S.isPullback_baseChange E).w V _ le_rfl (resTo S.str S.L V s) :=
  congrArg (SecOnR.of _ _ _) (ofSec_secPull s (S.bcFst E) V)

def pullSecs (S : LinSys F) (E : Type) [Field E] [Algebra F E] {n : ℕ} (b : Fin n → S.L.Sec) :
    Fin n → (S.baseChange E).L.Sec := fun j => secPull (b j) (S.bcFst E)

theorem linearIndependent_secPull (S : LinSys F) (hS : S.IsVariety) {n : ℕ} (b : Fin n → S.L.Sec)
    (hb : LinearIndependent F b) :
    LinearIndependent E (pullSecs S E b) := by
  classical
  have := isProper_str hS
  haveI : CompactSpace S.Y := QuasiCompact.compactSpace_of_compactSpace S.str
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := S.Y) (V := ⊤) isCompact_univ
  have H := S.isPullback_baseChange E
  let R : (Fin n → F) →ₗ[F] (∀ i, SecOnR S.str S.L (D i)) :=
    LinearMap.pi fun i => ∑ j, (LinearMap.proj j).smulRight (resTo S.str S.L (D i) (b j))
  have hRi : ∀ u i, R u i = resTo S.str S.L (D i) (∑ j, u j • b j) := fun u i => by
    rw [map_sum]
    simp only [R, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    exact Finset.sum_congr rfl fun j _ => (resTo_smul S.str S.L (D i) (u j) (b j)).symm
  have hR : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun u hu => ?_
    have h2 : ∑ j, u j • b j = 0 := by
      refine (SecOn.ofSec_bijective (M := S.L) (V := ⊤) rfl).injective ?_
      refine SecOn.ext_of_cover D (fun _ => le_top) hc.ge fun a => ?_
      rw [SecOn.restrict_ofSec, SecOn.restrict_ofSec]
      have := (hRi u a).symm.trans (congrFun hu a)
      exact this.trans (map_zero (resTo S.str S.L (D a))).symm
    funext j
    exact Fintype.linearIndependent_iff.1 hb u h2 j
  let Bc : ∀ i, E ⊗[F] SecOnR S.str S.L (D i) →ₗ[E]
      SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) := fun i =>
    SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
  have hBc : ∀ i, Function.Bijective (Bc i) := fun i =>
    SecOnR.baseChangeHom_bijective S.isLB H (hD i) rfl
  let Φ : (Fin n → E) →ₗ[E] ∀ i, SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) :=
    LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) ∘ₗ
      (TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).toLinearMap ∘ₗ
      R.baseChange E ∘ₗ (TensorProduct.piScalarRight F E E (Fin n)).symm.toLinearMap
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (R.baseChange E) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap R hR
    have h2 : Function.Injective (LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) :
        (∀ i, E ⊗[F] SecOnR S.str S.L (D i)) →ₗ[E] _) :=
      fun x y h => funext fun i => (hBc i).1 (congrFun h i)
    exact h2.comp ((TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).injective.comp
      (h1.comp (TensorProduct.piScalarRight F E E (Fin n)).symm.injective))
  have hΦc : ∀ c : Fin n → E, Φ c = fun i =>
      resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) (∑ j, c j • pullSecs S E b j) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    funext i
    rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piScalarRight_symm_single,
      LinearMap.baseChange_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      LinearMap.pi_apply, LinearMap.proj_apply, Bc, SecOnR.baseChangeHom_tmul]
    change SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
      (c j ⊗ₜ[F] R (Pi.single j 1) i) = _
    rw [SecOnR.baseChangeHom_tmul, hRi]
    have hs : ∑ k, (Pi.single j (1 : F) : Fin n → F) k • b k = b j := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    rw [hs, ← resTo_secPull]
    exact (resTo_smul _ _ _ (c j) _).symm
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h0 : Φ c = Φ 0 := by
    rw [hΦc, hc, map_zero]
    funext i
    exact map_zero _
  exact congrFun (hΦ h0)

theorem exists_pullSecs_spanning : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (S : LinSys F),
    S.IsVariety → ∃ (n : ℕ) (b : Fin n → S.L.Sec), ∀ t : (S.baseChange E).L.Sec, ∃ u : Fin n → E,
      (({ S with N := n, b := b } : LinSys F).baseChange E).comb u = t := by
  intro F E _ _ _ S hS
  haveI := finite_sec hS
  haveI : Module.Finite E (S.baseChange E).L.Sec := finite_sec (hS.baseChange E)
  let B := Module.finBasis F S.L.Sec
  refine ⟨_, B, fun t => ?_⟩
  have hli := linearIndependent_secPull (E := E) S hS B B.linearIndependent
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_baseChange S hS])
  have ht : t ∈ Submodule.span E (Set.range (pullSecs S E B)) := hsp ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ht
  exact ⟨u, hu⟩

end GlobalTheory.SectionsFieldChange
