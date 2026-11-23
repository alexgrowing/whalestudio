import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.PreSec
open GlobalTheory.Points GlobalTheory.ExpansionLinear

theorem eq_zero_of_valR {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (p : X ⟶ Sp K) [LocallyOfFiniteType p]
    [IsReduced X] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp K ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → valR x U f = 0) : f = 0 := by
  refine eq_zero_of_basicOpen_eq_bot f (le_bot_iff.1 (ComplexPoints.opens_le_of_geomPoints p (𝟙 _) _ _ ?_))
  intro x hx hxf
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := fun a ha => X.basicOpen_le f (hxf ha)
  exact absurd (h x hx hxU) ((le_preimage_basicOpen_iff x hxU f).1 hxf).ne_zero

theorem exists_matrix {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {J : Type} [Fintype J]
    [DecidableEq J] (W : M.Z.Opens) (b : Matrix J J Ω)
    (hb : ∀ z ∈ W, (RatModel.Lat.const M J).E z = Submodule.span (M.O z) (Set.range b)) :
    ∃ B C : Matrix J J Γ(M.Z, W), C * B = 1 ∧ ((W : Set M.Z).Nonempty → ∀ i l, valF M.pt W (B i l) = b i l) := by
  by_cases hW : (W : Set M.Z).Nonempty
  swap
  · exact ⟨1, 1, _root_.mul_one _, fun h => absurd h hW⟩
  have h1 : ∀ z ∈ W, ∃ c : Matrix J J Ω, (∀ i l, c i l ∈ M.O z) ∧ c * b = 1 := fun z hz => by
    have : ∀ i, ∃ c : J → M.O z, ∑ l, c l • b l = Pi.single i 1 := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (hb z hz ▸ Submodule.subset_span ⟨i, rfl⟩)
    choose c hc using this
    refine ⟨Matrix.of fun i l => (c i l : Ω), fun i l => (c i l).2, Matrix.ext fun i j => ?_⟩
    have := congrFun (hc i) j
    rw [Finset.sum_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact this.trans (by rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl)
  obtain ⟨c, -, hc⟩ := h1 _ hW.some_mem
  have h2 : ∀ i l, c i l ∈ M.ringOn W := fun i l => RatModel.mem_ringOn.2 fun z hz => by
    obtain ⟨c', h, h'⟩ := h1 z hz
    rw [Matrix.left_inv_eq_left_inv hc h']
    exact h i l
  have h3 : ∀ i l, b i l ∈ M.ringOn W := fun i l => RatModel.mem_ringOn.2 fun z hz =>
    (RatModel.Lat.mem_const_iff M).1 (hb z hz ▸ Submodule.subset_span ⟨i, rfl⟩) l
  choose B hB using fun i l => (RatModel.mem_ringOn_iff_exists hW).1 (h3 i l)
  choose C hC using fun i l => (RatModel.mem_ringOn_iff_exists hW).1 (h2 i l)
  refine ⟨Matrix.of B, Matrix.of C, Matrix.ext fun i j => M.res_injective W hW ?_, fun _ => hB⟩
  have := congrFun (congrFun hc i) j
  rw [Matrix.mul_apply] at this ⊢
  rw [map_sum, Matrix.one_apply, apply_ite (M.res W hW), map_one, map_zero, ← Matrix.one_apply, ← this]
  exact Finset.sum_congr rfl fun l _ => by
    rw [map_mul, M.res_apply, M.res_apply, Matrix.of_apply, Matrix.of_apply, hB, hC]

open GlobalTheory.SecAff in

theorem indep_fibre (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) {n : ℕ}
    (hn : 1 ≤ n) {J : Type} [Fintype J] (hJ : Fintype.card J = n ^ P.g)
    (s : J → LB.Sec (LPow P.A P.L n (baseOver S)))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L n (baseOver S)), ∃ c : J → Γ((baseOver S).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j)
    {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (c : J → K)
    (hc : ∀ (r : Sp K ⟶ (baseOver S ⊗ P.A).left) (j), r ≫ (fst (baseOver S) P.A).left = x →
      ⊤ ≤ r ⁻¹ᵁ (LPow P.A P.L n (baseOver S)).U j → ∑ l, c l * valR r _ ((s l).f j) = 0) : c = 0 := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn (x (IsLocalRing.closedPoint K))
  obtain ⟨t₀, ht₀⟩ := exists_lift (T := baseOver S) (T' := Over.mk x) (Over.homMk x (Category.comp_id _)) V
    (fun y => by rw [Subsingleton.elim (α := PrimeSpectrum K) y (IsLocalRing.closedPoint K)]; exact hV)
  let t : Spec (CommRingCat.of K) ⟶ (overRes (T := baseOver S) V).left := t₀.left
  have ht : (baseAt t).hom = x := Over.w t₀
  have hA : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨h₁, h₂⟩ := hb K t (fun i => SecM.toSec P.A (pull P.A P.L n (homAt t) (SecM.ofSec P.A (b i))))
    (fun i => (isPullSec_iff P.A P.L n _ _ _).2 rfl)
  have hrk := (Module.finrank_eq_card_basis (Module.Basis.mk h₁ h₂.ge)).trans (Fintype.card_fin _)
  let k : baseAt t ⟶ baseOver S := Over.homMk (baseAt t).hom (Category.comp_id _)
  obtain ⟨m, b₀, hb₀⟩ := GlobalTheory.exists_sections_span_affine hS S P n hn ⊤ (isAffineOpen_top S)
  obtain ⟨e, -⟩ := exists_lift (T := baseOver S) (𝟙 _) ⊤ (fun _ => trivial)
  have h₃ := hb₀ (baseAt t) (k ≫ e) (fun i => SecM.toSec P.A (pull P.A P.L n (k ≫ e) (SecM.ofSec P.A (b₀ i))))
    (fun i => (isPullSec_iff P.A P.L n _ _ _).2 rfl)
  have hcomb : ∀ (T : Over S) (d : J → Γ(T.left, ⊤)) (v : J → SecM P.A P.L n T) (j),
      (∑ l, d l • v l).1 j = ∑ l, liftFun P.A _ (d l) * (v l).1 j := fun T d v j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have h₄ : ⊤ ≤ Submodule.span Γ((baseAt t).left, ⊤)
      (Set.range fun l => pull P.A P.L n k (SecM.ofSec P.A (s l))) := by
    refine h₃.ge.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    obtain ⟨d, hd⟩ := hs (SecM.toSec P.A (pull P.A P.L n e (SecM.ofSec P.A (b₀ i))))
    have := map_mem_span (pull P.A P.L n k) (fun l => SecM.ofSec P.A (s l)) (pull P.A P.L n e (SecM.ofSec P.A (b₀ i)))
      ((Submodule.mem_span_range_iff_exists_fun _).2
        ⟨d, Subtype.ext (funext fun j => (hcomb _ d _ j).trans (hd j).symm)⟩)
    rw [pull_pull] at this
    exact this
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank h₄ (hJ.trans hrk.symm)
  have := P.isAb.smooth
  have hsm : Smooth (fst (baseAt t) P.A).left := inferInstanceAs (Smooth (pullback.fst (baseAt t).hom P.A.hom))
  have : IsReduced (baseAt t ⊗ P.A).left := isReduced_scheme_of_smooth_of_isIntegrallyClosed K (fst (baseAt t) P.A).left
  have h0 := Fintype.linearIndependent_iff.1 hli (fun l => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c l))
    (Subtype.ext (funext fun j => (hcomb _ _ _ j).trans (eq_zero_of_valR (K := K) (fst (baseAt t) P.A).left _ _
      fun p hp hU => ?_)))
  · funext l
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
      ((h0 l).trans (map_zero _).symm)
  refine Eq.trans ?_ (hc (p ≫ (k ▷ P.A).left) j ?_ (le_preimage_comp p _ (chart_le P.A P.L n k j) hU))
  · refine (valR_eq p _ hU _).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun l _ => (map_mul _ _ _).trans ?_))
    refine congrArg₂ (· * ·) ((valR_eq p _ hU _).symm.trans ?_) ((valR_eq p _ hU _).symm.trans
      (valR_appLE p _ (chart_le P.A P.L n k j) hU _))
    exact valR_constFn_of_section (fst (baseAt t) P.A).left p hp _ hU (c l)
  · rw [Category.assoc, whisker_fst_left, ← Category.assoc, hp, Category.id_comp]
    exact ht

def chartPullOne {X Y Y' : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (k : Y' ⟶ Y) (a' : Y' ⟶ X) (e : a' = k ≫ a) :
    ChartPull (L.pull a') (LB.LinComb L (fun _ : Fin 1 => a) (fun _ => 1)) k :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => a') j ≤
      k ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => a) (fun _ => j PUnit.unit) := fun j y hy => Set.mem_iInter.2 fun _ => by
    have : a' y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
    rw [e] at this; exact this
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y') y j j' hj hj').trans (Eq.trans ?_
        (gm_linComb L (fun _ : Fin 1 => a) (fun _ => 1) k y _ _ (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, Category.id_comp, e] }

theorem exists_theta (hS : SecBaseChangeSt) {S X : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (p : X ⟶ S)
    (ψ : X ⟶ P.A.left) [IsIso ψ] (hψ : ψ ≫ P.A.hom = p) (L : LB X) (hL : L.IsLB) (H : LBIso L (P.L.pull ψ)) (z : S) :
    ∃ (N : S.Opens) (σ : LB.Sec (L.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z' := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  obtain ⟨V, hV, θ, hθ⟩ := SepPoints.exists_sec_meetsFibres hS P z
  subst hψ
  let i := ((ψ ≫ P.A.hom) ⁻¹ᵁ V).ι
  have sq : IsPullback (i ≫ ψ) ((ψ ≫ P.A.hom) ∣_ V) P.A.hom (V.ι ≫ 𝟙 S) :=
    (isPullback_morphismRestrict (ψ ≫ P.A.hom) V).flip.paste_horiz (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩ :
      IsPullback ψ (ψ ≫ P.A.hom) P.A.hom (𝟙 S))
  let k : _ ⟶ (overRes (T := baseOver S) V ⊗ P.A).left := sq.flip.isoPullback.hom
  have k₁ : k ≫ (fst (overRes (T := baseOver S) V) P.A).left = (ψ ≫ P.A.hom) ∣_ V := sq.flip.isoPullback_hom_fst
  have k₂ : k ≫ (snd (overRes (T := baseOver S) V) P.A).left = i ≫ ψ := sq.flip.isoPullback_hom_snd
  have hk : Function.Surjective k := sq.flip.isoPullback.hom.homeomorph.surjective
  obtain ⟨σ, hσ⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hL i) (LB.isLB_pull P.isLB (i ≫ ψ))
    (LBIso.chartPull (chartPullPull L i) (chartPullSame P.L _ _ _ i fun _ => rfl) H)
    (chartSec (chartPullOne P.L _ k _ k₂.symm) θ)
  rw [nonzeroLocus_chartSec _ _ fun y _ _ => exists_chart (LB.isLB_pull P.isLB (i ≫ ψ)) y] at hσ
  refine ⟨V, σ, hV, fun z' hz' => ?_⟩
  obtain ⟨x, hx, e⟩ := hθ ⟨z', hz'⟩
  obtain ⟨y, rfl⟩ := hk x
  refine ⟨y, hσ.ge hx, ?_⟩
  have e₁ : ((ψ ≫ P.A.hom) ∣_ V) y = ⟨z', hz'⟩ := (congrArg (fun q => q y) k₁).symm.trans e
  exact (congrArg (fun q => q y) (morphismRestrict_ι (ψ ≫ P.A.hom) V)).symm.trans (congrArg V.ι e₁)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  [Algebra.FiniteType o S.R] [IsFractionRing S.R Ω]

theorem u₀_eq (Q : ZHPre ρ (RatModel.ofAffine o Ω S.R) ⊤) : Q.u₀ = (⊤ : (Sp S.R).Opens).ι := by
  let M := RatModel.ofAffine o Ω S.R
  have h : (M.pt ≫ M.Z.topIso.inv) ≫ (⊤ : M.Z.Opens).ι = M.pt :=
    (Category.assoc _ _ _).trans ((congrArg (M.pt ≫ ·) M.Z.topIso.inv_hom_id).trans (Category.comp_id _))
  have e : M.Z.topIso.inv ≫ Q.u₀ = 𝟙 M.Z :=
    ext_of_isDominant M.pt ((Category.assoc _ _ _).symm.trans ((Q.u₀_gen _ h).trans (Category.comp_id _).symm))
  exact (M.Z.topIso.hom_inv_id_assoc Q.u₀).symm.trans ((congrArg (M.Z.topIso.hom ≫ ·) e).trans (Category.comp_id _))

theorem exists_iso (Q : ZHPre ρ (RatModel.ofAffine o Ω S.R) ⊤) : ∃ ψ : Q.G.left ⟶ ρ.P.A.left, IsIso ψ ∧
    ψ ≫ ρ.P.A.hom = Q.G.hom ∧ Q.φ ≫ ψ = pullback.fst _ _ ∧ LBIso Q.L.L (ρ.P.L.pull ψ) := by
  have h₀ : IsIso (⊤ : (Sp S.R).Opens).ι := inferInstanceAs (IsIso (Sp S.R).topIso.hom)
  have h₁ : IsIso Q.φ := MorphismProperty.of_isPullback (P := .isomorphisms _) Q.cart.1.flip h₀
  have h₂ : IsIso Q.u₀ := by rw [u₀_eq]; exact h₀
  refine ⟨inv Q.φ ≫ pullback.fst _ _, inferInstance, ?_, IsIso.hom_inv_id_assoc _ _, ?_⟩
  · refine (Category.assoc _ _ _).trans ((IsIso.inv_comp_eq _).2 (pullback.condition.trans ?_))
    exact (congrArg (pullback.snd ρ.P.A.hom Q.u₀ ≫ ·) (u₀_eq Q)).trans Q.cart.1.w.symm
  · refine LBIso.trans Q.L.isLB (LB.isLB_pull Q.L.isLB (𝟙 _)) (LB.isLB_pull ρ.P.isLB _)
      (lbIso_of_chartPull (chartPullUnpull Q.L.L _ rfl) (LB.isLB_pull Q.L.isLB (𝟙 _))) ?_
    exact LBIso.chartPull (chartPullSame Q.L.L _ _ _ (inv Q.φ) fun _ => (IsIso.inv_hom_id _).symm)
      (chartPullSame ρ.P.L _ _ _ (inv Q.φ) fun _ => rfl) ⟨Q.w, Q.w_gen⟩

end GlobalTheory.ZH.PreSec
end
