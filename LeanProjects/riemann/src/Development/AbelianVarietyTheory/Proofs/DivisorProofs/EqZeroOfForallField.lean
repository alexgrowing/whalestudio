import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteAffineCharts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixIntertwinesAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.InvFieldBasis GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange GlobalTheory.KS GlobalTheory.CechKS

noncomputable section

namespace GlobalTheory.LogKSBal

section Values

variable {B : Type} [CommRing B] {Y Z : Scheme.{0}}

theorem valR_eq (x : Sp B ⟶ Y) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) (f : Γ(Y, O)) : valR x O f = evalPt x O h f := by
  rw [valR, dif_pos h]; rfl

theorem valR_pbT (x : Sp B ⟶ Z) (f : Z ⟶ Y) {O : Y.Opens} {O' : Z.Opens} (h : O' ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ x ⁻¹ᵁ O')
    (s : Γ(Y, O)) : valR x O' (pbT f s O') = valR (x ≫ f) O s := by
  have h'' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ O := fun p hp => h (h' hp)
  rw [valR_eq x h', valR_eq _ h'', evalPt_pbT x f h h' _ rfl h'']

theorem valR_rsT (x : Sp B ⟶ Y) {O O' : Y.Opens} (h : O' ≤ O) (h' : ⊤ ≤ x ⁻¹ᵁ O') (s : Γ(Y, O)) :
    valR x O' (rsT s O') = valR x O s := by
  rw [rsT_of_le h, valR_resG x h h']

theorem valR_constFn {R : Type} [CommRing R] (p : Y ⟶ Sp R) (x : Sp B ⟶ Y) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O)
    {β : R →+* B} (hβ : x ≫ p = spMap β) (a : R) : valR x O (constFn p O a) = β a := by
  rw [valR_eq x h, evalPt_constFn, ← evalPt_spMap β a]
  congr 2

theorem valR_chart {X : Scheme.{0}} (U : X.affineOpens) (β : Γ(X, U.1) →+* B) (r : Γ(X, U.1)) :
    valR (spMap β ≫ chart U) U.1 r = β r := by
  have hU : ⊤ ≤ (spMap β ≫ GlobalTheory.FlagMod.tau U.2) ⁻¹ᵁ U.1 :=
    GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le U.2 le_rfl)
  exact (valR_eq_ev _ _ hU r).trans (congrArg (fun k : Γ(X, U.1) →+* B => k r) (GlobalTheory.FlagMod.ev_spMap_tau U.2 β hU))

theorem ext_valR {O : Y.Opens} (s s' : Γ(Y, O))
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ Y), ⊤ ≤ x ⁻¹ᵁ O → valR x O s = valR x O s') : s = s' := by
  refine eq_of_rsT_eq (fun V : {V : Y.affineOpens // V.1 ≤ O} => V.1.1) (fun V => V.2) (fun y hy => ?_) _ _ fun V => ?_
  · obtain ⟨_, ⟨V, hV, rfl⟩, hy', hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy O.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hy'⟩
  · obtain ⟨x, hx, e⟩ := exists_evalPt_eq V.1.2 (RingHom.id _)
    have := h _ x fun p hp => V.2 (hx hp)
    rw [← valR_rsT x V.2 hx, ← valR_rsT x V.2 hx, valR_eq x hx, valR_eq x hx, e] at this
    exact this

theorem exists_section (io : Z ⟶ Y) [IsOpenImmersion io] :
    ∃ σ : ∀ O : Z.Opens, Γ(Z, O) →+* Γ(Y, io ''ᵁ O), (∀ O f, pbT io (σ O f) O = f) ∧
      ∀ O (s : Γ(Y, io ''ᵁ O)), σ O (pbT io s O) = s := by
  have e : ∀ O (s : Γ(Y, io ''ᵁ O)), pbT io s O = (io.appIso O).hom.hom s := fun O s => by
    rw [pbT_of_le io (io.preimage_image_eq O).ge, Scheme.Hom.appIso_hom']
  refine ⟨fun O => (io.appIso O).inv.hom, fun O f => ?_, fun O s => ?_⟩
  · rw [e]; exact (io.appIso O).inv_hom_id_apply f
  · rw [e]; exact (io.appIso O).hom_inv_id_apply s

end Values

theorem snd_valR_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {u : epsR K ⟶ A}
    (hu : IsTangent u) {dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hd : IsInvDer u dd) {B : Type}
    [CommRing B] {β : K →+* B} {x : Sp B ⟶ A.left} {w : Sp (DualNumber B) ⟶ A.left} (hw : IsTransl β x u w)
    {O : A.left.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) (f : Γ(A.left, O)) : (valR w O f).snd = valR x O (dd O f) := by
  obtain ⟨x', v', h₁, h₂, rfl⟩ := hw
  letI : Algebra K (DualNumber B) := ((algebraMap B (DualNumber B)).comp β).toAlgebra
  have hz : ⊤ ≤ x'.left ⁻¹ᵁ O := by
    rw [h₁]; exact fun p _ => h (Set.mem_univ _)
  obtain ⟨h', e⟩ := evalPt_translate (B := DualNumber B) hu hd DualNumber.eps DualNumber.eps_mul_eps x' O hz
  have ev' : v' = (Chart.spMap (epsTo K (DualNumber.eps : DualNumber B) DualNumber.eps_mul_eps) ≫ u : Chart.sp (R₀ := K) (DualNumber B) ⟶ A) := by
    refine Over.OverMorphism.ext (h₂.trans ?_)
    change _ = spMap _ ≫ u.left
    congr 2
    refine RingHom.ext fun c => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, epsTo, dualTo_apply, Algebra.ofId_apply, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
  have k : ∀ s, evalPt x'.left O hz s = algebraMap B (DualNumber B) (valR x O s) := fun s => by
    rw [valR_eq x h, ← evalPt_spMap_comp _ x O h (h₁ ▸ hz)]
    congr 2
  rw [_root_.mul_comm x' v', ev', valR_eq _ h', e, k, k]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_lieBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    {K : Type} [CommRing K] {x : Sp K ⟶ X} {A : Over (Sp K)} [GrpObj A] {M : A.left ⟶ t.G.left}
    (h : IsGrpPullback A t.G x M) {n : ℕ} (v : Fin n → (Sp (DualNumber K) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → K, IsCombAtG t x v cf w) :
    ∃ u : Fin n → (epsR K ⟶ A), (∀ i, (u i).left ≫ M = v i) ∧ IsLieBasis u ∧
      ∀ c (w : epsR K ⟶ A), IsCombAtG t x v c (w.left ≫ M) → IsLieComb c u w := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h (spMap (algebraMap K (DualNumber K)))
    (spMap (algebraMap K (DualNumber K)) ≫ x) rfl
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h (𝟙 _) x (Category.id_comp _)
  have one : η[A].left ≫ M = (1 : Over.mk x ⟶ t.G).left := by
    rw [← map_one B₀, hB₀, Hom.one_def, Over.comp_left]
    congr 1
  have inj : ∀ w w' : epsR K ⟶ A, w.left ≫ M = w'.left ≫ M → w = w' := fun w w' e =>
    Over.OverMorphism.ext (h.1.hom_ext e ((Over.w w).trans (Over.w w').symm))
  have tan : ∀ w : epsR K ⟶ A, IsTangent w ↔ IsTanAtG t x (w.left ≫ M) := fun w => by
    refine ⟨fun hw => ⟨by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w w]; rfl, ?_⟩, fun hw => ?_⟩
    · rw [← Category.assoc, hw, one]
    · refine h.1.hom_ext (by rw [Category.assoc, hw.2, one]) ?_
      rw [Category.assoc, Over.w w, Over.w η[A]]
      change spMap _ ≫ spMap _ = 𝟙 _
      rw [← Spec.map_comp, ← Spec.map_id]
      rfl
  let u : Fin n → (epsR K ⟶ A) := fun i => B.symm (Over.homMk (v i) (hv i).1)
  have hu : ∀ i, (u i).left ≫ M = v i := fun i => by
    rw [← hB, B.apply_symm_apply]; rfl
  have comb : ∀ c (w : epsR K ⟶ A), IsCombAtG t x v c (w.left ≫ M) ↔ IsLieComb c u w := fun c w => by
    constructor
    · rintro ⟨y, hy, e⟩
      refine ⟨fun i => B.symm (y i), fun i => h.1.hom_ext ?_ ?_, inj _ _ ?_⟩
      · rw [← hB, B.apply_symm_apply, hy, Category.assoc, hu]; rfl
      · rw [Over.w (B.symm (y i)), Category.assoc, Over.w (u i)]
        exact (GlobalTheory.Exist.FlagBaseChange.epsMul_over (c i)).symm
      · rw [← e, ← hB, map_list_prod, List.map_ofFn]
        congr 3
        funext i
        exact (B.apply_symm_apply _).symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun i => B (y i), fun i => ?_, ?_⟩
      · rw [hB, hy, Category.assoc, hu]; rfl
      · rw [← hB, map_list_prod, List.map_ofFn]; rfl
  refine ⟨u, hu, ⟨fun i => (tan _).2 (hu i ▸ hv i), fun w hw => ?_⟩, fun c w => (comb c w).1⟩
  simpa only [comb] using hb _ ((tan w).1 hw)

theorem pull_g {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (i k : L.ι) :
    (L.pull f).g (fun _ => i) (fun _ => k) = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => f)
      (fun _ => i) PUnit.unit)) (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => f) (fun _ => k) PUnit.unit)))
        (pullU f _ (L.g i k)) := by
  unfold LB.pull LB.LinComb
  dsimp only
  rw [Fintype.prod_unique, zpow_one]

theorem pbT_base {G X Z : Scheme.{0}} (p : G ⟶ X) (U : X.affineOpens) {R : Type} [CommRing R] (q : Z ⟶ Sp R) (z : Z ⟶ G)
    (β : Γ(X, U.1) →+* R) (hz : z ≫ p = q ≫ spMap β ≫ chart U) (O : Z.Opens) (O₀ : G.Opens) (h₀ : O₀ ≤ p ⁻¹ᵁ U.1)
    (hO : O ≤ z ⁻¹ᵁ O₀) (r : Γ(X, U.1)) : pbT z ((p.appLE U.1 O₀ h₀).hom r) O = constFn q O (β r) := by
  refine ext_valR _ _ fun B _ y hy => ?_
  have e : y ≫ q = spMap (Spec.preimage (y ≫ q)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ q)).hom = β' at e
  have hy' : ⊤ ≤ (y ≫ z) ⁻¹ᵁ O₀ := fun p hp => hO (hy hp)
  rw [valR_constFn q y hy e, ← pbT_of_le, valR_pbT y z hO hy, valR_pbT _ _ h₀ hy',
    Category.assoc, hz, ← Category.assoc, e, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', valR_chart]
  rfl

theorem exists_ksCoc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    {V : X.Opens} {U : X.affineOpens} (hUV : U.1 ≤ V) {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)}
    {D : Γ(X, U.1) → Γ(X, U.1)} {Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)} (hKS : IsKS t V U v D Θ)
    {G : Over (Sp Γ(X, U.1))} {io : G.left ⟶ t.G.left} (hio : IsPullback io G.hom t.G.hom (chart U))
    [CompactSpace G.left] {K : Type} [Field K] (x₀ : Γ(X, U.1) →+* K) {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    {m : A.left ⟶ G.left} (hM : IsGrpPullback A t.G (spMap x₀ ≫ chart U) (m ≫ io)) {u : Fin n → (epsR K ⟶ A)}
    (hut : ∀ a, IsTangent (u a)) (hu : ∀ a, (u a).left ≫ m ≫ io = spMap (Formalism.L2.Pj.dualMap x₀) ≫ v a)
    {dd : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hdd : ∀ a, IsInvDer (u a) (dd a)) :
    ∃ L : LB G.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso (t.PP.L.pull io) L ∧
      ∃ d, ∀ φ, IsDlog m L dd φ →
        KSCoc A.hom G.hom m (fun r => x₀ (D r)) L.U dd d fun a => lc A.hom (fun b => -x₀ (Θ a b)) φ := by
  obtain ⟨J, W, j, d, hcov, hWj, hfld, hlift, hdiff⟩ := hKS
  have : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion io := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hio.flip inferInstance
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup W i).trans (hcov.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hloc : ∀ x : G.left, ∃ (Ω : G.left.Opens) (k : J), IsAffineOpen Ω ∧ x ∈ Ω ∧ Ω ≤ io ⁻¹ᵁ W k := by
    intro x
    have h1 : (io ≫ t.G.hom) x ∈ U.1 := by
      rw [hio.w, Scheme.Hom.comp_apply]
      exact U.2.range_fromSpec.subset ⟨_, rfl⟩
    have h2 : io x ∈ ⨆ k, W k := by
      rw [hcov]; exact ⟨h1, hUV h1⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨_, ⟨Ω, hΩ, rfl⟩, hx, hle⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ io ⁻¹ᵁ W k from hk) (io ⁻¹ᵁ W k).isOpen
    exact ⟨Ω, k, hΩ, hx, hle⟩
  obtain ⟨s, hfin, Ω, κ, hΩ, hΩW, hs⟩ : ∃ (s : Type) (_ : Finite s) (Ω : s → G.left.Opens) (κ : s → J),
      (∀ a, IsAffineOpen (Ω a)) ∧ (∀ a, Ω a ≤ io ⁻¹ᵁ W (κ a)) ∧ ⨆ a, Ω a = ⊤ := by
    choose Ω κ hΩ hxΩ hΩW using hloc
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (Ω x : Set G.left))
      (fun x => (Ω x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxΩ x⟩)
    refine ⟨s, inferInstance, fun a => Ω a, fun a => κ a, fun a => hΩ a, fun a => hΩW a, top_le_iff.1 fun x _ => ?_⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  have hle : ∀ a : s, Ω a ≤ (t.PP.L.pull io).U fun _ => j (κ a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hWj _ (hΩW a hy)
  have hP := pull_isLB t.PP.isLB io
  let L := GlobalTheory.FinAffineCharts.refineLB (t.PP.L.pull io) (fun a : s => Ω a) (fun a _ => j (κ a)) hle
  obtain ⟨σ, σ₁, σ₂⟩ := exists_section io
  have him : ∀ (a : s) (O : G.left.Opens), O ≤ Ω a → io ''ᵁ O ≤ W (κ a) := fun a O h =>
    (io.image_mono (h.trans (hΩW a))).trans (io.image_preimage_le _)
  have hpre : ∀ O : G.left.Opens, m ⁻¹ᵁ O ≤ (m ≫ io) ⁻¹ᵁ (io ''ᵁ O) := fun O => by
    rw [Scheme.Hom.comp_preimage, io.preimage_image_eq]
  have hσ : ∀ (O : G.left.Opens) (O₀ : t.G.left.Opens) (h : io ''ᵁ O ≤ O₀) (f : Γ(t.G.left, O₀)),
      σ O (pbT io f O) = resG _ h f := fun O O₀ h f => by
    rw [← pbT_rsT io h (io.preimage_image_eq O).ge, σ₂, rsT_of_le h]
  have happ : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), (m.app O).hom f = pbT (m ≫ io) (σ O f) (m ⁻¹ᵁ O) := fun O f => by
    rw [← GlobalTheory.KS.Sym.pbT_pbT m io (io.preimage_image_eq O).ge le_rfl, σ₁, pbT_of_le m le_rfl, Scheme.Hom.appLE_eq_app]
  have hg : ∀ a b : s, (L.g a b).val = pbT io (t.PP.L.g (j (κ a)) (j (κ b))).val (Ω a ⊓ Ω b) := fun a b => by
    have e : Ω a ⊓ Ω b ≤ io ⁻¹ᵁ (t.PP.L.U (j (κ a)) ⊓ t.PP.L.U (j (κ b))) :=
      fun p hp => ⟨hWj _ (hΩW a hp.1), hWj _ (hΩW b hp.2)⟩
    rw [← rsT_pbT io le_rfl e, pbT_of_le io le_rfl, Scheme.Hom.appLE_eq_app, rsT_of_le e]
    have : L.g a b = res e (pullU io _ (t.PP.L.g (j (κ a)) (j (κ b)))) := by
      refine Eq.trans ?_ (GlobalTheory.FinAffineCharts.res_res (le_inf (inf_le_left.trans (LB.wchart_le t.PP.L (fun _ : PUnit => io)
        (fun _ => j (κ a)) PUnit.unit)) (inf_le_right.trans (LB.wchart_le t.PP.L (fun _ : PUnit => io)
        (fun _ => j (κ b)) PUnit.unit))) (inf_le_inf (hle a) (hle b)) _)
      refine congrArg (res (inf_le_inf (hle a) (hle b))) ?_
      exact pull_g _ _ _ _
    rw [this]
    rfl
  refine ⟨L, hfin, GlobalTheory.FinAffineCharts.refineLB_isLB hP _ _ hle hs,
    fun a => hΩ a, GlobalTheory.FinAffineCharts.iso_refineLB hP _ _ hle,
    fun a O f => pbT (m ≫ io) (d (κ a) _ (σ O f)) _, fun φ hφ => ⟨fun a => ⟨fun O hO f f' => ?_, fun O hO f f' => ?_,
      fun O O' h hO f => ?_, fun O hO r => ?_⟩, fun a b O hO f => ?_⟩⟩
  · rw [map_add, (hfld _).1 _ (him a O hO), pbT_add]
  · rw [map_mul, (hfld _).2.1 _ (him a O hO), pbT_add, pbT_mul, pbT_mul, happ, happ]
  · have h' := io.image_mono h
    have e : σ O' (resG _ h f) = resG _ h' (σ O f) := by
      rw [← hσ O' _ h', ← rsT_pbT io (io.preimage_image_eq O).ge h, σ₁, rsT_of_le h]
    rw [e, (hfld _).2.2 _ _ h' (him a O hO), ← rsT_of_le h', pbT_rsT _ h' (hpre O'),
      rsT_pbT _ (hpre O) (m.preimage_mono h)]
  · have h' := him a O hO
    have e := pbT_base t.G.hom U G.hom io (RingHom.id _) (by
      rw [hio.w, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]) O _ (hWU (κ a)) (hO.trans (hΩW a)) r
    rw [RingHom.id_apply] at e
    rw [← e, hσ O _ h', (hfld _).2.2 _ _ h' le_rfl, hlift, ← rsT_of_le h', pbT_rsT _ h' (hpre O)]
    exact pbT_base t.G.hom U A.hom _ x₀ hM.1.w _ _ _ ((hpre O).trans ((m ≫ io).preimage_mono h')) _
  · refine ext_valR _ _ fun B _ y hy => ?_
    have e : y ≫ A.hom = spMap (Spec.preimage (y ≫ A.hom)).hom := (Spec.map_preimage _).symm
    generalize (Spec.preimage (y ≫ A.hom)).hom = β at e
    choose w hw using fun c => exists_isTransl β y e (u c)
    have hab : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b := m.preimage_mono hO
    have hy₁ : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) := fun p hp => hab (hy hp)
    have hy₂ : ⊤ ≤ (y ≫ m ≫ io) ⁻¹ᵁ (io ''ᵁ O) := fun p hp => hpre O (hy hp)
    have hgm : m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b ≤ (m ≫ io) ⁻¹ᵁ (t.PP.L.U (j (κ a)) ⊓ t.PP.L.U (j (κ b))) :=
      fun p hp => ⟨hWj _ (hΩW a hp.1), hWj _ (hΩW b hp.2)⟩
    have hy₃ : ⊤ ≤ (y ≫ m ≫ io) ⁻¹ᵁ (t.PP.L.U (j (κ a)) ⊓ t.PP.L.U (j (κ b))) := fun p hp => hgm (hy₁ hp)
    have hwO : ∀ c (O₁ : A.left.Opens), ⊤ ≤ y ⁻¹ᵁ O₁ → ⊤ ≤ w c ⁻¹ᵁ O₁ := fun c O₁ h =>
      le_preimage_of_red ((hw c).red (hut c)) h
    have key := hdiff (κ a) (κ b) _ (le_inf (him a O (hO.trans inf_le_left)) (him b O (hO.trans inf_le_right))) (σ O f) B
      (β.comp x₀) (y ≫ m ≫ io) (fun c => w c ≫ m ≫ io)
      (by rw [Category.assoc, hM.1.w, ← Category.assoc, e, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']) hy₂
      fun c => IsTransl.isTranslate_comp t _ A _ hM x₀ (v c) (u c) (hu c) β y e (w c) (hw c)
    have k₁ : ∀ c, (valR (w c ≫ m ≫ io) _ (σ O f)).snd = valR y _ (dd c _ ((m.app O).hom f)) := fun c => by
      rw [← snd_valR_transl (hut c) (hdd c) (hw c) hy, happ, valR_pbT _ _ (hpre O) (hwO c _ hy)]
    have gm : pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) =
        pbT (m ≫ io) (t.PP.L.g (j (κ a)) (j (κ b))).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) := by
      refine (congrArg (pbT m · _) (hg a b)).trans ?_
      exact GlobalTheory.KS.Sym.pbT_pbT m io (O₁ := Ω a ⊓ Ω b) (fun p hp => by exact ⟨hWj _ (hΩW a hp.1), hWj _ (hΩW b hp.2)⟩)
        (fun p hp => hp) _
    have k₂ : ∀ c, (valR (w c ≫ m ≫ io) _ (t.PP.L.g (j (κ a)) (j (κ b))).val).snd *
        valR (y ≫ m ≫ io) _ (t.PP.L.g (j (κ a)) (j (κ b)))⁻¹.val = valR y _ (φ c a b) := fun c => by
      rw [← valR_pbT _ _ hgm (hwO c _ hy₁), snd_valR_transl (hut c) (hdd c) (hw c) hy₁, ← gm, ← hφ c a b, gm,
        valR_eq y hy₁, map_mul, ← valR_eq y hy₁, valR_pbT _ _ hgm hy₁, valR_eq _ hy₃, valR_eq _ hy₃, mul_right_comm,
        ← map_mul, Units.mul_inv, map_one, _root_.one_mul, valR_eq y hy₁]
    simp only [k₁, k₂] at key
    rw [valR_eq _ hy₂, map_sub, ← valR_eq, ← valR_eq, ← valR_pbT _ _ (hpre O) hy, ← valR_pbT _ _ (hpre O) hy] at key
    rw [valR_eq y hy, valR_eq y hy, map_sub, map_sum, ← valR_eq, ← valR_eq, ← neg_sub, key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, ← valR_eq, ← valR_eq, valR_rsT y hab hy, lc, valR_eq y hy₁, map_sum, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [map_mul, ← valR_eq, ← valR_eq, valR_constFn A.hom y hy₁ e, map_neg, RingHom.comp_apply]
    ring

theorem lc_sub {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ}
    (F F' : Matrix (Fin g) (Fin g) K) (φ : Fin g → C1 U) (b : Fin g) :
    lc q ((F - F') b) φ = lc q (F b) φ - lc q (F' b) φ := by
  funext i k
  simp [lc, constFn, sub_mul, Finset.sum_sub_distrib]

theorem map_mem_balanced {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {U : Y.X.affineOpens}
    (hU : U.1 ≤ interior Y) {n : ℕ} {v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)}
    {A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)} (hv : ∀ i, IsTanAtG Y.t (chart U) (v i))
    (hb : ∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w)
    (hA : ∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left))
    {D : Γ(Y.X, U.1) → Γ(Y.X, U.1)} {Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)} (hKS : IsKS Y.t (interior Y) U v D Θ)
    {K : Type} [Field K] (x₀ : Γ(Y.X, U.1) →+* K) : Θ.map x₀ ∈ balanced H.bar fun a => (A a).map x₀ := by
  have hr : Set.range (chart U) ⊆ Set.range Y.j := fun y hy => hU (U.2.range_fromSpec.subset hy)
  let f := IsOpenImmersion.lift Y.j (chart U) hr
  have hf : f ≫ Y.j = chart U := IsOpenImmersion.lift_fac _ _ _
  have id' : ∀ {S : Scheme.{0}} (s : S ⟶ Sp (KA l)), s = s ≫ spMap (RingHom.id _) := fun s => by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  obtain ⟨o, ⟨mo⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ _ f rfl rfl (id' _) Y.oF
  obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ _ (spMap x₀) rfl rfl (id' _) o
  obtain ⟨n₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m mo.toSABMap
  have hio : IsGrpPullback o.t.G Y.t.G (chart U) n₁.φ := n₁.cart.congr hf rfl
  have hm := m₀.cart
  have hM := hm.comp hio
  obtain ⟨b₁, b₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t x₀ _ n v hv hb
  obtain ⟨u, hu, hbas, hcomb⟩ := exists_lieBasis Y.t hM _ b₁ b₂
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K o₀.t.G (u a) (hbas.1 a)).1
  have := o.proper
  have : CompactSpace o.t.G.left := QuasiCompact.compactSpace_of_compactSpace o.t.G.hom
  obtain ⟨L, hfin, hL, haff, hiso, d, hd⟩ := exists_ksCoc Y.t hU hKS hio.1 x₀ hM hbas.1 hu hdd
  have i₁ : LBIso o.t.PP.L (Y.t.PP.L.pull n₁.φ) := by
    obtain ⟨w, hw, -⟩ := n₁.lin
    exact ⟨w, hw⟩
  have i₀ : LBIso o₀.t.PP.L (o.t.PP.L.pull m₀.cm.F) := by
    obtain ⟨w, hw, -⟩ := m₀.lin
    exact ⟨w, hw⟩
  have i₂ := LBIso.trans o.t.PP.isLB (pull_isLB Y.t.PP.isLB _) hL i₁ hiso
  have hI : LBIso o₀.t.PP.L (L.pull m₀.cm.F) := LBIso.trans o₀.t.PP.isLB (pull_isLB o.t.PP.isLB _) (pull_isLB hL _) i₀
    (i₂.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K (GlobalTheory.Obj.toPolAV o₀) n u dd hbas hdd _ _ L hL hI
  obtain ⟨Θ', hs, hΘ'⟩ := GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.T.theorem_of_cube_polAbelianScheme K (GlobalTheory.Obj.toPolAV o₀) n u dd hbas hdd _ x₀ (GlobalTheory.Obj.toPolAV o) _ L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e : Θ' = -Θ.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [lc_sub]
    exact hΘ' b
  have hact : ∀ a k, IsLieComb (fun i => ((A a).map x₀)ᵀ i k) u (u k ≫ o₀.t.act.act a) := fun a k => by
    refine hcomb _ _ ?_
    have h := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H _ Y.t _ _ x₀ _ _ rfl).2 n v _ _ (hA a k)
    rw [← Category.assoc, ← hu k] at h
    rw [Over.comp_left, Category.assoc, reassoc_of% (m₀.act a), n₁.act a]
    simp only [Category.assoc] at h ⊢
    exact h
  refine ⟨?_, fun a => ?_⟩
  · have h : Θ'ᵀ = Θ' := hs
    rwa [e, Matrix.transpose_neg, neg_inj] at h
  · have h := GlobalTheory.KS.matrix_intertwines_adjoint K (GlobalTheory.Obj.toPolAV o₀) n u dd hbas hdd _ x₀ (GlobalTheory.Obj.toPolAV o) _ L _ d _ φ
      hm hL haff hI (hd φ hφ) hφ Θ' (o.t.act.act a) (o₀.t.act.act a) (o₀.t.act.act (H.bar a)) _ _ hΘ' (o₀.t.act.hom _)
      (o₀.t.act.hom _) (m₀.act a) (o₀.t.adj a) (hact a) (hact (H.bar a))
    rwa [e, Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h

theorem eq_zero_of_forall_field {R : Type} [CommRing R] [_root_.IsReduced R] (r : R)
    (h : ∀ (K : Type) [Field K] (f : R →+* K), f r = 0) : r = 0 := by
  have hn : r ∈ nilradical R := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro p hp
    haveI : Ideal.IsPrime p := hp
    have h0 := h (FractionRing (R ⧸ p)) ((algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p))
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact (mem_nilradical.1 hn).eq_zero

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {V : X.Opens} (hV : Dense (V : Set X)) (U : X.affineOpens)
    (r : Γ(X, U.1)) (h : ∀ g : Γ(X, U.1), X.basicOpen g ≤ V → ∀ (K : Type) [Field K] (x : Γ(X, X.basicOpen g) →+* K),
      x (resG X (X.basicOpen_le g) r) = 0) : r = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro p hp
  obtain ⟨y, hy, hyV⟩ := hV.inter_open_nonempty _ (X.basicOpen r).isOpen ⟨p, hp⟩
  obtain ⟨g, hg, hyg⟩ := U.2.exists_basicOpen_le (V := V) ⟨y, hyV⟩ (X.basicOpen_le r hy)
  have h0 := eq_zero_of_forall_field _ (h g hg)
  have h1 : y ∈ X.basicOpen (resG X (X.basicOpen_le g) r) := by
    rw [resG, Scheme.basicOpen_res]
    exact ⟨hyg, hy⟩
  rw [h0, Scheme.basicOpen_zero] at h1
  exact h1.elim

theorem ksClass_mem_balanced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), IsKS Y.t (interior Y) U v D.1 Θ → Θ ∈ balanced H.bar A := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ _ U n v A hv hb hA D Θ hKS
  have : IsReduced Y.X := by
    have := fun x => (Y.normal x).1
    exact isReduced_of_isReduced_stalk _
  have key : ∀ g : Γ(Y.X, U.1), Y.X.basicOpen g ≤ interior Y → ∀ (K : Type) [Field K]
      (x : Γ(Y.X, Y.X.basicOpen g) →+* K), Θ.map (x.comp (resG Y.X (Y.X.basicOpen_le g))) ∈
        balanced H.bar fun a => (A a).map (x.comp (resG Y.X (Y.X.basicOpen_le g))) := by
    intro g hg K _ x
    let W := Y.X.affineBasicOpen g
    have hW : W.1 ≤ U.1 := Y.X.basicOpen_le g
    obtain ⟨DW, -, hDW⟩ := GlobalTheory.LogDerLoc.exists_logDer_basicOpen _ _ Y.s _ U W hW g rfl D.1 D.2
    have h₁ := GlobalTheory.LogKSLoc.isKS_basicOpen E H _ Y.t _ U W hW g rfl n v D.1 DW Θ hDW hKS
    have hc := GlobalTheory.LogKSLoc.spMap_res_chart U W hW
    obtain ⟨b₁, b₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (resG Y.X hW) _ n v hv hb
    rw [hc] at b₁ b₂
    exact map_mem_balanced Y (U := W) hg (A := fun a => (A a).map (resG Y.X hW)) b₁ b₂ (fun a i => by
      rw [Category.assoc]
      exact (GlobalTheory.TanBaseChange.tan_comb_baseChange E H _ Y.t _ _ _ _ _ hc).2 n v _ _ (hA a i)) h₁ x
  refine ⟨?_, fun z => ?_⟩
  · ext a b
    rw [← sub_eq_zero]
    refine eq_zero_of_dense (dense_interior Y) U _ fun g hg K _ x => ?_
    have e := congrFun₂ (key g hg K x).1 a b
    rw [map_sub, map_sub, sub_eq_zero]
    exact e
  · ext a b
    rw [← sub_eq_zero]
    refine eq_zero_of_dense (dense_interior Y) U _ fun g hg K _ x => ?_
    have e := congrFun₂ ((key g hg K x).2 z) a b
    rw [← RingHom.comp_apply, map_sub, RingHom.map_matrix_mul, RingHom.map_matrix_mul, Matrix.transpose_map, e, sub_self]

end GlobalTheory.LogKSBal
