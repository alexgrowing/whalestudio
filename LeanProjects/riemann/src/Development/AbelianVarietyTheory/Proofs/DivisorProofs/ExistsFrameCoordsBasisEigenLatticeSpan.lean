import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DimEqOfFiniteSurjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueHomOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieCombAddPowMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReFrameIffReframeIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open scoped MonObj

namespace GlobalTheory.PtDeg.FrameExact
open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

section
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

lemma comb_add' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c c' : Fin n → R) :
    comb v (c + c') = comb v c * comb v c' :=
  ((isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_add hv
    ((isLieComb_iff_comb _ _ _).2 rfl) ((isLieComb_iff_comb _ _ _).2 rfl))).symm

lemma comb_zero' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) :
    comb v 0 = 1 :=
  ((isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_zero hv)).symm

lemma comb_sum' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) {κ : Type}
    (s : Finset κ) (f : κ → Fin n → R) : comb v (∑ j ∈ s, f j) = ∏ j ∈ s, comb v (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using comb_zero' hv
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, comb_add' hv, ih]

lemma comb_comb' {n m : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (w : Fin m → (epsR R ⟶ G)) (B : Fin m → Fin n → R) (hw : ∀ j, w j = comb v (B j)) (g : Fin m → R) :
    comb w g = comb v (∑ j, g j • B j) := by
  rw [comb_sum' hv]
  unfold comb
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hw j]
  exact epsScale_comb v (B j) (g j)

lemma comb_comp_hom' {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f]
    {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) :
    comb v c ≫ f = comb (fun i => v i ≫ f) c :=
  (isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_comp f ((isLieComb_iff_comb _ _ _).2 rfl))

end
end GlobalTheory.PtDeg.FrameExact

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent GlobalTheory.PtDeg.FrameExact in

theorem GlobalTheory.PtDeg.FrameExact.comb_comp_eq_of_isDiffOf : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib P) (f : P.A ⟶ P.A) (M : F.P₀.A ⟶ F.P₀.A) [IsMonHom M] (L : Module.End K (Fin F.P₀.g → K)), F.IsDiffOf F f L → Over.Hom.left M ≫ F.φ = F.φ ≫ Over.Hom.left f → ∀ c : Fin F.P₀.g → K, GlobalTheory.Reg.VecEig.comb F.v c ≫ M = GlobalTheory.Reg.VecEig.comb F.v (L c) := by
  intro K _ _ P F f M _ L hL hM
  have hv := F.basis
  let Sg : Submodule K (Fin F.P₀.g → K) :=
    { carrier := {c | comb F.v c ≫ M = comb F.v (L c)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rw [comb_add' hv.1, map_add, comb_add' hv.1, ← ha, ← hb, MonObj.mul_comp]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, comb_zero' hv.1, MonObj.one_comp]
      smul_mem' := by
        intro s a ha
        simp only [Set.mem_ofPred_eq] at *
        rw [map_smul, ← epsScale_comb, ← epsScale_comb, ← ha, Category.assoc] }
  have hspan : Submodule.span K {c | ∃ u, F.IsCoord u c} = ⊤ := by
    have := (GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K P F).2
    rw [GlobalTheory.CM.GenFib.lieLat, Submodule.span_span_of_tower] at this
    exact this
  have hpb : IsPullback F.φ F.P₀.A.hom P.A.hom (spMap (algebraMap (𝓞 K) K)) := F.fib.2.1.1
  have hsub : {c | ∃ u, F.IsCoord u c} ⊆ (Sg : Set _) := by
    rintro c ⟨u, hut, w, hwv, hwc⟩
    obtain ⟨hut', w', hw'v, hw'c⟩ := hL u c ⟨hut, w, hwv, hwc⟩
    obtain ⟨z, -, hz⟩ := GlobalTheory.existsUnique_isVecOver hpb (u ≫ f)
    have hwM : GlobalTheory.IsVecOver (algebraMap (𝓞 K) K) F.φ (u ≫ f) (w ≫ M) := by
      unfold GlobalTheory.IsVecOver at hwv ⊢
      simp only [Over.comp_left, Category.assoc]
      rw [hM, ← Category.assoc, hwv, Category.assoc]
    have e := (hz _ hwM).trans (hz _ hw'v).symm
    show comb F.v c ≫ M = comb F.v (L c)
    rw [(isLieComb_iff_comb _ _ _).1 hwc] at e
    rw [← (isLieComb_iff_comb _ _ _).1 hw'c, e]
  intro c
  have h := Submodule.span_le.2 hsub
  rw [hspan] at h
  exact h (Submodule.mem_top : c ∈ ⊤)

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent GlobalTheory.PtDeg.FrameExact in

theorem GlobalTheory.PtDeg.exists_frameCoord_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ' : E →+* ℂ) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ' a)) → ∃ v : Fin (Dw.mult ρ') → Fin F.P₀.g → K, GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ' v ∧ LinearIndependent K v ∧ Submodule.span K (Set.range v) = Submodule.span K (F.eigLat B.t.act t : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ' t ht
  have h1 : IsGrpPullback t₀.G Xo.univ.t.G y.x m1.φ := m1.cart
  have h2 : IsGrpPullback t₀.G B.t.G (spMap (algebraMap (𝓞 K) K)) m2.φ := m2.cart
  have h3 : IsGrpPullback F.P₀.A B.pol.A (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  obtain ⟨⟨ψ, hψ, -⟩, hψm⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h2 h3 (𝟙 _)
  obtain ⟨⟨ψ', hψ', -⟩, hψm'⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h3 h2 (𝟙 _)
  haveI : IsMonHom ψ := hψm ψ hψ inferInstance
  haveI : IsMonHom ψ' := hψm' ψ' hψ' inferInstance
  simp only [Over.id_left, Category.comp_id] at hψ hψ'
  have hψψ' : ψ ≫ ψ' = 𝟙 _ := by
    apply GlobalTheory.Reg.VecEig.pt_ext m2
    simp only [Over.comp_left, Category.assoc, Over.id_left, Category.id_comp]
    rw [hψ', hψ]
  have hψ'ψ : ψ' ≫ ψ = 𝟙 _ := by
    obtain ⟨⟨k, hk, hk1⟩, -⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h3 h3 (𝟙 _)
    have a1 := hk1 (ψ' ≫ ψ) (by simp only [Over.comp_left, Category.assoc, Over.id_left, Category.comp_id]; rw [hψ, hψ'])
    have a2 := hk1 (𝟙 _) (by simp)
    rw [a1, a2]
  obtain ⟨r, hrD, hr⟩ := GlobalTheory.CM.GenFib.exists_lieRep_eigLat K B.pol F (𝓞 E) B.t.act
  have hv := F.basis

  have key : ∀ (u : epsR K ⟶ t₀.G) (d : Fin F.P₀.g → K), u ≫ ψ = comb F.v d → ∀ a : 𝓞 E,
      (u ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ u ↔ r a d = t a • d) := by
    intro u d hud a
    haveI := t₀.act.hom a
    have hM : Over.Hom.left (ψ' ≫ t₀.act.act a ≫ ψ) ≫ F.φ = F.φ ≫ Over.Hom.left (B.t.act.act a) := by
      simp only [Over.comp_left, Category.assoc, hψ]
      have := m2.act a
      simp only [SABMap.φ] at hψ' ⊢
      rw [this, ← Category.assoc, hψ']
    have hE := GlobalTheory.PtDeg.FrameExact.comb_comp_eq_of_isDiffOf K B.pol F (B.t.act.act a) (ψ' ≫ t₀.act.act a ≫ ψ) (r a) (hrD a) hM d
    rw [← hud] at hE
    have hE' : u ≫ t₀.act.act a ≫ ψ = comb F.v (r a d) := by
      rw [← hE]; simp only [Category.assoc, reassoc_of% hψψ']
    have hs : comb F.v (((t a : 𝓞 K) : K) • d) = epsScale ((t a : 𝓞 K) : K) ≫ u ≫ ψ := by
      rw [hud, epsScale_comb]
    have hsm : ((t a : 𝓞 K) : K) • d = t a • d := algebraMap_smul K (t a) d
    constructor
    · intro h
      apply comb_injective hv
      rw [← hE', ← hsm, hs, ← Category.assoc, h, Category.assoc]
    · intro h
      have h' : (u ≫ t₀.act.act a) ≫ ψ = (epsScale ((t a : 𝓞 K) : K) ≫ u) ≫ ψ := by
        rw [Category.assoc, hE', h, ← hsm, hs, Category.assoc]
      have := congrArg (· ≫ ψ') h'
      simpa only [Category.assoc, hψψ', reassoc_of% hψψ', Category.comp_id] using this

  have hlift : ∀ i, ∃ u : epsR K ⟶ t₀.G, Over.Hom.left u ≫ m1.φ = y.u ρ' i :=
    fun i => GlobalTheory.KSExist.FrameLift.exists_lift h1 (T := epsR K) (y.u ρ' i) (y.tan ρ' i).1
  choose U hU using hlift
  have hUt : ∀ i, IsTangent (U i) := fun i =>
    (GlobalTheory.KSExist.FrameLift.tan_iff h1 (U i)).1 (by rw [hU]; exact y.tan ρ' i)
  have hUe : ∀ i a, U i ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ U i := fun i a =>
    (GlobalTheory.KSExist.FrameLift.eig_iff h1 (m1.act a) (U i) _).1 (by
      have := y.eig ρ' i a
      rw [hU, ht]; simpa only [Category.assoc] using this)
  have hWt : ∀ i, IsTangent (U i ≫ ψ) := fun i => GlobalTheory.CM.DiffCoord.isTangent_comp_hom ψ (hUt i)
  have hco : ∀ i, ∃ d, U i ≫ ψ = comb F.v d := fun i => by
    obtain ⟨d, hd, -⟩ := hv.2 _ (hWt i)
    exact ⟨d, (isLieComb_iff_comb _ _ _).1 hd⟩
  choose V hV using hco
  have hUy : (fun i => Over.Hom.left (U i) ≫ m1.φ) = y.u ρ' := funext hU
  refine ⟨V, ?_, ?_, ?_⟩
  · intro i
    refine ⟨Over.Hom.left (U i), U i ≫ ψ, hU i, ?_, ?_⟩
    · simp only [Over.comp_left, Category.assoc, hψ]
    · rw [isLieComb_iff_comb]; exact hV i
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have e1 : comb U g ≫ ψ = comb F.v 0 := by
      rw [comb_comp_hom', comb_comb' hv.1 _ V hV, hg]
    have e0 : comb U 0 ≫ ψ = comb F.v 0 := by
      rw [comb_comp_hom', comb_comb' hv.1 _ V hV]; simp
    have hW : comb U g = comb U 0 := by
      have := congrArg (· ≫ ψ') (e1.trans e0.symm)
      simpa only [Category.assoc, hψψ', Category.comp_id] using this
    have c1 := GlobalTheory.LieBasisRing.isCombAt_of_isLieComb h1 U g (comb U g) ((isLieComb_iff_comb _ _ _).2 rfl)
    have c0 := GlobalTheory.LieBasisRing.isCombAt_of_isLieComb h1 U 0 (comb U g) ((isLieComb_iff_comb _ _ _).2 hW)
    rw [hUy] at c1 c0
    have htan := GlobalTheory.ReframeClauses.isTanAt_of_isCombAt (y.tan ρ') c1
    have heig := GlobalTheory.ReframeClauses.isEigAt_of_isCombAt (y.tan ρ') (y.eig ρ') c1
    obtain ⟨a0, -, huniq⟩ := y.basis ρ' _ htan heig
    have := (huniq g c1).trans (huniq 0 c0).symm
    intro i
    simpa using congrFun this i
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ((hr t (V i)).2).2 fun a => (key (U i) (V i) (hV i) a).1 (hUe i a)
    · intro d hd
      have hd' := ((hr t d).2).1 hd
      have hwt : IsTangent (comb F.v d) := isTangent_comb hv.1 d
      have hu : (comb F.v d ≫ ψ') ≫ ψ = comb F.v d := by
        simp only [Category.assoc, hψ'ψ, Category.comp_id]
      have hut : IsTangent (comb F.v d ≫ ψ') := GlobalTheory.CM.DiffCoord.isTangent_comp_hom ψ' hwt
      have hue : ∀ a, (comb F.v d ≫ ψ') ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ (comb F.v d ≫ ψ') :=
        fun a => (key _ d hu a).2 (hd' a)
      have htan : IsTanAt y.x (Over.Hom.left (comb F.v d ≫ ψ') ≫ m1.φ) :=
        (GlobalTheory.KSExist.FrameLift.tan_iff h1 _).2 hut
      have heig : IsEigAt c ρ' (Over.Hom.left (comb F.v d ≫ ψ') ≫ m1.φ) := fun a => by
        have := (GlobalTheory.KSExist.FrameLift.eig_iff h1 (m1.act a) (comb F.v d ≫ ψ') _).2 (hue a)
        rw [← ht]; simpa only [Category.assoc] using this
      obtain ⟨g, hg, -⟩ := y.basis ρ' _ htan heig
      rw [← hUy] at hg
      have hl := GlobalTheory.KSExist.FrameLift.isLieComb_of_isCombAt h1 U g _ hg
      rw [isLieComb_iff_comb] at hl
      have hdd : comb F.v d = comb F.v (∑ j, g j • V j) := by
        rw [← hu, hl, comb_comp_hom', comb_comb' hv.1 _ V hV]
      rw [comb_injective hv hdd]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
