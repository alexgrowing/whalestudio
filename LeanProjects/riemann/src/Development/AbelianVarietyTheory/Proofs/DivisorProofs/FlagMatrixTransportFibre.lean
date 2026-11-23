import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

open GlobalTheory.TangentOrigin

variable {K : Type} [Field K]

theorem matIso_top_le (U : (Sp K).Opens) (p : Sp K) (hp : p ∈ U) : ⊤ ≤ U := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  intro q _
  rwa [Subsingleton.elim q p]

theorem matIso_range_eq {P Q : (Sp K).Modules} (u : P ⟶ Q) [Mono u] {k : ℕ} (hP : IsVB P k) {ι : Type} [Fintype ι]
    (hι : Fintype.card ι = k) (v : ι → Γ(Q, ⊤))
    (h : ∀ t, u.app ⊤ t ∈ Submodule.span Γ(Sp K, ⊤) (Set.range v)) :
    LinearMap.range (QCoh.appLinear u ⊤) = Submodule.span Γ(Sp K, ⊤) (Set.range v) := by
  have hF : IsField Γ(Sp K, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  letI := hF.toField
  obtain ⟨U, e, hU, he⟩ := hP (IsLocalRing.closedPoint K)
  have hb := he.basis (matIso_top_le U _ hU)
  haveI : FiniteDimensional Γ(Sp K, ⊤) (Submodule.span Γ(Sp K, ⊤) (Set.range v)) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range v)
  refine Submodule.eq_of_le_of_finrank_le (K := Γ(Sp K, ⊤)) ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact h t
  · rw [LinearMap.finrank_range_of_inj (f := QCoh.appLinear u ⊤) (QCoh.injective_app_of_mono u ⊤), Module.finrank_eq_card_basis hb,
      Fintype.card_fin, ← hι]
    exact finrank_range_le_card v

theorem matIso_same {P P' Q : (Sp K).Modules} (u : P ⟶ Q) [Mono u] (u' : P' ⟶ Q) [Mono u'] {k : ℕ} (hP : IsVB P k)
    (hP' : IsVB P' k) {ι : Type} [Fintype ι] (hι : Fintype.card ι = k) (v : ι → Γ(Q, ⊤))
    (h : ∀ t, u.app ⊤ t ∈ Submodule.span Γ(Sp K, ⊤) (Set.range v))
    (h' : ∀ t, u'.app ⊤ t ∈ Submodule.span Γ(Sp K, ⊤) (Set.range v)) : FlagLocal.Same u u' := by
  refine FlagLocal.same_of_range fun V => ?_
  by_cases hV : V = ⊥
  · subst hV
    haveI : Subsingleton Γ(Q, ⊥) := Module.subsingleton Γ(Sp K, ⊥) _
    ext s
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨p, hp⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hV
    obtain rfl : V = ⊤ := top_le_iff.1 (matIso_top_le V p hp)
    exact congrArg (fun S : Submodule Γ(Sp K, ⊤) Γ(Q, ⊤) => (S : Set Γ(Q, ⊤)))
      ((matIso_range_eq u hP hι v h).trans (matIso_range_eq u' hP' hι v h').symm)

theorem matIso_mem_span {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (φ : R ≃+* K) {r : ℕ} (e : Fin r → N)
    (A : Matrix (Fin r) (Fin r) K) (k : ℕ) (c : Fin r → R) (cf : Fin r → K) (h0 : ∀ l : Fin r, k ≤ l → cf l = 0)
    (hc : (fun b => φ (c b)) = Matrix.vecMul cf A) :
    ∑ b, c b • e b ∈ Submodule.span R (Set.range fun l : {l : Fin r // (l : ℕ) < k} => ∑ b, φ.symm (A l b) • e b) := by
  have e1 (b : Fin r) : c b = ∑ l, φ.symm (cf l) * φ.symm (A l b) := by
    apply φ.injective
    simpa [Matrix.vecMul, dotProduct] using congrFun hc b
  simp only [e1, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← Finset.smul_sum]
  rcases lt_or_ge (l : ℕ) k with hl | hl
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
  · rw [h0 l hl, map_zero, zero_smul]
    exact zero_mem _

theorem stepIso_of_flagMat : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [Field K] (x : Sp K ⟶ B), ⊤ ≤ x ⁻¹ᵁ V → ∀ (fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r) (A : Matrix (Fin r) (Fin r) K), FlagMat hM x fl' hf (𝟙 (Sp K)) A → ∀ (y : Sp K ⟶ Y) (w : y ≫ π = x), FlagMat hM π fl hf y A → StepIso π fl fl' y w := by
  intro B Y M r hM π fl V f hf K _ x hx fl' A hA' y w hA i
  subst w
  haveI := hM.isQuasicoherent
  haveI := (fl.isVB i).isQuasicoherent
  haveI := (hM.pullback π).isQuasicoherent
  haveI : Mono ((Scheme.Modules.pullback y).map (fl.ι i)) :=
    FlagPull.mono_pullback_map_f y (.mk (fl.ι i) (Limits.cokernel.π _) (Limits.cokernel.condition _))
      { exact := ShortComplex.exact_cokernel _ } (fl.isVB_cokernel i)
  let φ : Γ(Sp K, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  let e : Fin r → Γ((Scheme.Modules.pullback (y ≫ π)).obj M, ⊤) := fun b => QCoh.pullbackSections (y ≫ π) M hx (f b)
  let c := (Scheme.Modules.pullbackComp y π).hom.app M ≫ (Scheme.Modules.pullbackCongr (rfl : y ≫ π = y ≫ π)).hom.app M
  refine matIso_same ((Scheme.Modules.pullback y).map (fl.ι i) ≫ c) (fl'.ι i) ((fl.isVB i).pullback y) (fl'.isVB i)
    (Fintype.card_fin_lt_of_le (Nat.lt_succ_iff.1 i.2))
    (fun l : {l : Fin r // (l : ℕ) < i} => ∑ b, φ.symm (A l b) • e b) (fun t => ?_) fun t => ?_
  · let p : Sp K := IsLocalRing.closedPoint K
    obtain ⟨W, s, -, hpW, hWV, hs⟩ := (fl.isVB i).exists_affine (V := π ⁻¹ᵁ V) (x := y p) (hx (Set.mem_univ p))
    have hy : ⊤ ≤ y ⁻¹ᵁ W := matIso_top_le _ p hpW
    have hc (b : Fin r) : c.app ⊤ (QCoh.pullbackSections y _ hy (((hf.pullback π).basis hWV) b)) = e b := by
      rw [IsFrame.basis_apply]
      erw [QCoh.res_pullbackSections]
      rw [← Vert.DivPull.pullbackComp_inv_app y π M hWV hy hx, QCoh.app_app, Iso.inv_hom_id_app_assoc]
      rfl
    rw [← ((hs.pullback y).basis hy).sum_repr t, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Scheme.Modules.Hom.app_smul]
    refine Submodule.smul_mem _ _ ?_
    rw [IsFrame.basis_apply]
    erw [QCoh.res_pullbackSections]
    rw [← QCoh.app_app, QCoh.pullback_map_app_pullbackSections,
      ← ((hf.pullback π).basis hWV).sum_repr ((fl.ι i).app W (s j))]
    simp only [map_sum, QCoh.pullbackSections_smul, Scheme.Modules.Hom.app_smul, hc]
    obtain ⟨cf, h0, h1⟩ := hA.2 i W hWV (s j) hy
    exact matIso_mem_span φ e A i _ cf h0 h1
  · obtain ⟨cf, h0, h1⟩ := hA'.2 i ⊤ hx t le_rfl
    rw [← ((hf.pullback (y ≫ π)).basis hx).sum_repr ((fl'.ι i).app ⊤ t)]
    have hc (b : Fin r) : ((hf.pullback (y ≫ π)).basis hx) b = e b := by
      rw [IsFrame.basis_apply]
      exact QCoh.res_pullbackSections _ _ _ _ _
    simp only [hc]
    refine matIso_mem_span φ e A i _ cf h0 (Eq.trans (funext fun b => ?_) h1)
    simp [coordAt, evalPt, φ, Scheme.Hom.appLE]
    rfl

end GlobalTheory.FlagCls

end
