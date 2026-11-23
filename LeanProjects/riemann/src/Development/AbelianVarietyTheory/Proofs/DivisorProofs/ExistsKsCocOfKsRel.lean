import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSCechData

open GlobalTheory.KS GlobalTheory.LogKSBal

theorem constFn_spMap {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {Y : Scheme.{0}} (q : Y ⟶ Sp K)
    (O : Y.Opens) (r : R) : constFn (q ≫ spMap x₀) O r = constFn q O (x₀ r) := by
  refine ext_valR _ _ fun B _ y hy => ?_
  have e : y ≫ q = spMap (Spec.preimage (y ≫ q)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ q)).hom = β at e
  rw [valR_constFn q y hy e, valR_constFn (q ≫ spMap x₀) y hy (β := β.comp x₀)
    (by rw [← Category.assoc, e, GlobalTheory.LogKSLoc.spMap_comp'])]
  rfl

theorem constFn_neg {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (r : K) :
    constFn q O (-r) = -constFn q O r := by
  simp [constFn]

theorem exists_ksCoc_of_ksRel : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ P.A.left), m ≫ P.A.hom = A.hom ≫ spMap x₀ → ∀ {g : ℕ} (e : Fin g → Fld P.A.left) (dd : Fin g → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), (∀ a, IsField ⊤ (e a)) → (∀ a (O : P.A.left.Opens) (f : Γ(P.A.left, O)), dd a (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e a O f) (m ⁻¹ᵁ O)) → ∀ (D : Derivation ℤ R R) (M : Matrix (Fin g) (Fin g) R), KSRel P.A (𝟙 P.A.left) P.L e ⇑D M → ∃ L : LB P.A.left, Finite L.ι ∧ L.IsLB ∧ (∀ i, IsAffineOpen (L.U i)) ∧ LBIso P.L L ∧ ∃ d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(A.left, m ⁻¹ᵁ O), ∀ φ, GlobalTheory.KS.IsDlog m L dd φ → GlobalTheory.KS.KSCoc A.hom P.A.hom m (fun r => x₀ (D r)) L.U dd d (fun a => GlobalTheory.KS.lc A.hom (fun b => -x₀ (M a b)) φ) := by
  intro R _ K _ x₀ P A _ m hm g e dd he hdd D M hKS
  obtain ⟨J, W, j, d, hcov, hWj, hlift, hdiff⟩ := hKS
  have := P.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hloc : ∀ x : P.A.left, ∃ (Ω : P.A.left.Opens) (k : J), IsAffineOpen Ω ∧ x ∈ Ω ∧ Ω ≤ W k := by
    intro x
    have h2 : x ∈ ⨆ k, W k := by
      rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨_, ⟨Ω, hΩ, rfl⟩, hx, hle⟩ := P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (W k).isOpen
    exact ⟨Ω, k, hΩ, hx, hle⟩
  obtain ⟨s, hfin, Ω, κ, hΩ, hΩW, hs⟩ : ∃ (s : Type) (_ : Finite s) (Ω : s → P.A.left.Opens) (κ : s → J),
      (∀ a, IsAffineOpen (Ω a)) ∧ (∀ a, Ω a ≤ W (κ a)) ∧ ⨆ a, Ω a = ⊤ := by
    choose Ω κ hΩ hxΩ hΩW using hloc
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (Ω x : Set P.A.left))
      (fun x => (Ω x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxΩ x⟩)
    refine ⟨s, inferInstance, fun a => Ω a, fun a => κ a, fun a => hΩ a, fun a => hΩW a, top_le_iff.1 fun x _ => ?_⟩
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  have hle : ∀ a : s, Ω a ≤ P.L.U (j (κ a)) := fun a => (hΩW a).trans (hWj (κ a))
  let L := GlobalTheory.FinAffineCharts.refineLB P.L Ω (fun a => j (κ a)) hle
  have happ : ∀ (O : P.A.left.Opens) (f : Γ(P.A.left, O)), (m.app O).hom f = pbT m f (m ⁻¹ᵁ O) :=
    fun O f => GlobalTheory.KS.AdjDlog.app_eq_pbT m O f
  have hconst : ∀ (O : P.A.left.Opens) (r : R), pbT m (constFn P.A.hom O r) (m ⁻¹ᵁ O) =
      constFn A.hom (m ⁻¹ᵁ O) (x₀ r) := fun O r => by
    rw [pbT_constFn _ _ le_rfl, hm, constFn_spMap]
  refine ⟨L, hfin, GlobalTheory.FinAffineCharts.refineLB_isLB P.isLB _ _ hle hs,
    fun a => hΩ a, GlobalTheory.FinAffineCharts.iso_refineLB P.isLB _ _ hle,
    fun a O f => pbT m (d (κ a) O f) _, fun φ hφ => ⟨fun a => ⟨fun O hO f f' => ?_, fun O hO f f' => ?_,
      fun O O' h hO f => ?_, fun O hO r => ?_⟩, fun a b O hO f => ?_⟩⟩
  · rw [(hlift _).1.1 _ (hO.trans (hΩW a)), pbT_add]
  · rw [(hlift _).1.2.1 _ (hO.trans (hΩW a)), pbT_add, pbT_mul, pbT_mul, happ, happ]
  · rw [(hlift _).1.2.2 _ _ h (hO.trans (hΩW a)), ← rsT_of_le h, pbT_rsT _ h le_rfl,
      rsT_pbT _ le_rfl (m.preimage_mono h)]
  · rw [(hlift _).2 _ (hO.trans (hΩW a)), hconst]
  · have hO' : O ≤ Ω a ⊓ Ω b := hO
    have hU : Ω a ⊓ Ω b ≤ P.L.U (j (κ a)) ⊓ P.L.U (j (κ b)) := inf_le_inf (hle a) (hle b)
    have hab : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b := m.preimage_mono hO
    have hab' : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ (Ω a ⊓ Ω b) := m.preimage_mono hO
    have hg : (L.g a b).val = rsT (P.L.g (j (κ a)) (j (κ b))).val (Ω a ⊓ Ω b) :=
      GlobalTheory.KS.AdjDlog.val_res hU _
    have hφ' : ∀ c, rsT (φ c a b) (m ⁻¹ᵁ O) =
        pbT m (dlg P.A (𝟙 P.A.left) P.L (e c) (j (κ a)) (j (κ b)) O) (m ⁻¹ᵁ O) := fun c => by
      have h₁ : pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b =
          pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b)) :=
        (hφ c a b).trans ((congrArg (dd c (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (happ (Ω a ⊓ Ω b) (L.g a b).val).symm).trans
          (hdd c (Ω a ⊓ Ω b) (L.g a b).val))
      have h₂ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b) * φ c a b) (m ⁻¹ᵁ O) =
          rsT (pbT m (e c (Ω a ⊓ Ω b) (L.g a b).val) (m ⁻¹ᵁ (Ω a ⊓ Ω b))) (m ⁻¹ᵁ O) :=
        congrArg (rsT · (m ⁻¹ᵁ O)) h₁
      have h₃ : rsT (pbT m (L.g a b).val (m ⁻¹ᵁ L.U a ⊓ m ⁻¹ᵁ L.U b)) (m ⁻¹ᵁ O) =
          pbT m (P.L.g (j (κ a)) (j (κ b))).val (m ⁻¹ᵁ O) :=
        (rsT_pbT m (O₀ := Ω a ⊓ Ω b) (fun p hp => hp) hab _).trans
          ((congrArg (pbT m · (m ⁻¹ᵁ O)) hg).trans (pbT_rsT m hU hab' _))
      have h₄ : rsT (e c (Ω a ⊓ Ω b) (L.g a b).val) O = e c O (rsT (P.L.g (j (κ a)) (j (κ b))).val O) := by
        refine (rsT_of_le hO' _).trans (((he c).2.2 _ _ hO' le_top _).symm.trans (congrArg (e c O) ?_))
        refine (rsT_of_le (O₀ := Ω a ⊓ Ω b) hO' _).symm.trans ?_
        rw [← rsT_rsT hU hO']
        exact congrArg (fun z => rsT z O) hg
      rw [rsT_mul, h₃, rsT_pbT m le_rfl hab', ← pbT_rsT m hO' le_rfl, h₄] at h₂
      rw [dlg, GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), GlobalTheory.KS.AdjDlog.pbT_id _ _ (hO'.trans hU), pbT_mul, ← h₂,
        pbT_rsT m (hO'.trans hU) le_rfl, mul_right_comm, ← pbT_mul, Units.mul_inv,
        pbT_one m (m.preimage_mono (hO'.trans hU)), _root_.one_mul]
    have key := hdiff (κ a) (κ b) O (hO'.trans (inf_le_inf (hΩW a) (hΩW b))) f
    rw [← pbT_sub, ← neg_sub, key, pbT_neg, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hdd, lc, rsT_sum, Finset.sum_mul, pbT_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [rsT_mul, rsT_constFn _ hab, hφ', pbT_mul, pbT_mul, hconst, constFn_neg]
    ring

end GlobalTheory.KSCechData
