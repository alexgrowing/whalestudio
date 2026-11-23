import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSmulCocycleEqCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitOfEventually
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorQuotientTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationallyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentDevissageCommRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

noncomputable section

namespace GlobalTheory.TorsLL

section Maps

variable {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
  {AA : Subalgebra O WC} {act : G →* (WC ≃ₐ[O] WC)} {ξ : WCˣ}

def iQ {a e : ℤ} (b : ℤ) (hae : Mxi AA ξ e ≤ Mxi AA ξ a) : Qab AA ξ e b →ₗ[O] Qab AA ξ a b :=
  Submodule.mapQ _ _ (Submodule.inclusion hae) (fun _ hx => hx)

def pQ (a : ℤ) {e b : ℤ} (heb : Mxi AA ξ b ≤ Mxi AA ξ e) : Qab AA ξ a b →ₗ[O] Qab AA ξ a e :=
  Submodule.mapQ _ _ LinearMap.id (fun _ hx => heb hx)

theorem iQ_injective {a e : ℤ} (b : ℤ) (hae : Mxi AA ξ e ≤ Mxi AA ξ a) :
    Function.Injective (iQ b hae) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : (Submodule.Quotient.mk (Submodule.inclusion hae y) : Qab AA ξ a b) = 0 := hx
  rw [Submodule.Quotient.mk_eq_zero] at hx' ⊢
  exact hx'

theorem pQ_surjective (a : ℤ) {e b : ℤ} (heb : Mxi AA ξ b ≤ Mxi AA ξ e) :
    Function.Surjective (pQ a heb) := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem exact_iQ_pQ {a e b : ℤ} (hae : Mxi AA ξ e ≤ Mxi AA ξ a) (heb : Mxi AA ξ b ≤ Mxi AA ξ e) :
    Function.Exact (iQ b hae) (pQ a heb) := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro hx
    rw [pQ, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact ⟨Submodule.Quotient.mk ⟨y.1, hx⟩, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← hz]
    change (Submodule.Quotient.mk (Submodule.inclusion hae w) : Qab AA ξ a e) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact w.2

variable {T : Type} [AddCommGroup T] [Module O T] (ρT : G →* (T →ₗ[O] T)) (h : XiOK AA act ξ)

theorem iQ_equiv {a e : ℤ} (b : ℤ) (hae : Mxi AA ξ e ≤ Mxi AA ξ a) (g : G)
    (x : TensorProduct O T (Qab AA ξ e b)) :
    LinearMap.lTensor T (iQ b hae) (repX ρT h e b g x) =
      repX ρT h a b g (LinearMap.lTensor T (iQ b hae) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t q =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pQ_equiv (a : ℤ) {e b : ℤ} (heb : Mxi AA ξ b ≤ Mxi AA ξ e) (g : G)
    (x : TensorProduct O T (Qab AA ξ a b)) :
    LinearMap.lTensor T (pQ a heb) (repX ρT h a b g x) =
      repX ρT h a e g (LinearMap.lTensor T (pQ a heb) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t q =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem repX_res {G' : Type} [Group G'] (φ : G' →* G) (act' : G' →* (WC ≃ₐ[O] WC))
    (hact : ∀ g, act' g = act (φ g)) (ρ' : G' →* (T →ₗ[O] T)) (hρ : ∀ g, ρ' g = ρT (φ g))
    (h' : XiOK AA act' ξ) (a b : ℤ) (g : G') : repX ρ' h' a b g = repX ρT h a b (φ g) := by
  obtain rfl : act' = act.comp φ := MonoidHom.ext hact
  obtain rfl : ρ' = ρT.comp φ := MonoidHom.ext hρ
  rfl

end Maps

theorem tors_of_subgroup {R Γ X : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup X]
    [Module R X] [TopologicalSpace X] (G H : Subgroup Γ) (hHG : H ≤ G) (ρ : Representation R G X)
    (ρ' : Representation R H X) (hρ : ∀ g : H, ρ' g = ρ (Subgroup.inclusion hHG g)) (l v c : ℕ)
    (hl : l ≠ 0) (hidx : H.relIndex G = l ^ v) (hT : TorsKilledBy ρ' (l : R) ((l : R) ^ c)) :
    TorsKilledBy ρ (l : R) ((l : R) ^ (v + c)) := by
  rintro f ⟨hfc, hf⟩ ⟨k, x, hx⟩
  have hcont : Continuous (Subgroup.inclusion hHG) :=
    Continuous.subtype_mk continuous_subtype_val _
  obtain ⟨y, hy⟩ := hT (fun g => f (Subgroup.inclusion hHG g))
    ⟨hfc.comp hcont, fun g g' => by simp only [map_mul, hf, hρ]⟩
    ⟨k, x, fun g => by rw [hρ, ← hx]; rfl⟩
  have : (H.subgroupOf G).FiniteIndex := ⟨by
    change H.relIndex G ≠ 0
    rw [hidx]; exact pow_ne_zero _ hl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.index_smul_cocycle_eq_coboundary R G X ρ (H.subgroupOf G) ((l : R) ^ c • f)
    (fun g g' => by simp only [Pi.smul_apply, hf, smul_add, map_smul])
    ⟨y, fun g hg => by
      have := hy ⟨g.1, hg⟩
      rw [hρ] at this
      exact this⟩
  refine ⟨z, fun g => ?_⟩
  rw [← hz g]
  change _ = H.relIndex G • _
  rw [hidx, ← Nat.cast_smul_eq_nsmul R, Pi.smul_apply, Pi.smul_apply, smul_smul, pow_add, Nat.cast_pow]

theorem tors_repX {O Γ WC : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing WC]
    [Algebra O WC] {AA : Subalgebra O WC} {act : Γ →* (WC ≃ₐ[O] WC)} {ξ : WCˣ} (G H : Subgroup Γ)
    (hHG : H ≤ G) {T : Type} [AddCommGroup T] [Module O T] (ρ : ↥G →* (T →ₗ[O] T))
    (ρ' : ↥H →* (T →ₗ[O] T)) (hρ : ∀ g, ρ' g = ρ (Subgroup.inclusion hHG g))
    (hG : XiOK AA (act.comp G.subtype) ξ) (hH : XiOK AA (act.comp H.subtype) ξ) (a b : ℤ)
    [TopologicalSpace (TensorProduct O T (Qab AA ξ a b))] (l v c : ℕ)
    (hl : l ≠ 0) (hidx : H.relIndex G = l ^ v)
    (hT : TorsKilledBy (repX ρ' hH a b) (l : O) ((l : O) ^ c)) :
    TorsKilledBy (repX ρ hG a b) (l : O) ((l : O) ^ (v + c)) :=
  tors_of_subgroup G H hHG _ _
    (fun g => repX_res ρ hG (Subgroup.inclusion hHG) _ (fun _ => rfl) ρ' hρ hH a b g) l v c hl hidx hT

theorem comp_inclusion {Γ M : Type} [Group Γ] [Monoid M] {L G H : Subgroup Γ} (hHG : H ≤ G)
    (hG : G ≤ L) (hH : H ≤ L) (ρ : ↥L →* M) (g : ↥H) :
    (ρ.comp (Subgroup.inclusion hH)) g = (ρ.comp (Subgroup.inclusion hG)) (Subgroup.inclusion hHG g) :=
  rfl

variable {l : ℕ} [Fact l.Prime]

theorem tors_repQ {P : LocPrime l} (AI : LocAinf l P) (G H : Subgroup (GQ l))
    (hHG : H ≤ G) {T : Type} [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥G →* (T →ₗ[ℤ_[l]] T))
    (ρ' : ↥H →* (T →ₗ[ℤ_[l]] T)) (hρ : ∀ g, ρ' g = ρ (Subgroup.inclusion hHG g)) (a b : ℤ)
    [TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))] (v c : ℕ)
    (hidx : H.relIndex G = l ^ v)
    (hT : TorsKilledBy (repQ AI H ρ' a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ c)) :
    TorsKilledBy (repQ AI G ρ a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (v + c)) := by
  unfold repQ at hT ⊢
  exact tors_repX G H hHG ρ ρ' hρ _ _ a b l v c (Fact.out : l.Prime).ne_zero hidx hT

theorem Gj_anti (K : FinExt l) {i j : ℕ} (hij : i ≤ j) : Gj K j ≤ Gj K i := by
  refine IntermediateField.fixingSubgroup_le (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  change x ^ l ^ i = 1 at hx
  change x ^ l ^ (i + k) = 1
  rw [pow_add, pow_mul, hx, one_pow]

theorem compact_Gj (K : FinExt l) (j : ℕ) : CompactSpace ↥(Gj K j) :=
  isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed (Ks K j)).isCompact

theorem finrank_cyclotomicTowerBase_ne_zero (K : FinExt l) : Module.finrank ℚ_[l] ↥(K0 K) ≠ 0 := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  exact Module.finrank_pos.ne'

theorem deg_Ks (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) = l ^ (j - i) * Module.finrank ℚ_[l] ↥(Ks K i) ∧
      Module.finrank ℚ_[l] ↥(Ks K i) ≠ 0 := by
  have hl : l.Prime := Fact.out
  have h1 := (finrank_Ks_and_chi_surjective l K).1
  rw [h1 j (hi.trans hij), h1 i hi]
  refine ⟨?_, mul_ne_zero (finrank_cyclotomicTowerBase_ne_zero K) (mul_ne_zero ?_ (pow_ne_zero _ hl.ne_zero))⟩
  · have : j - 1 = (j - i) + (i - 1) := by omega
    rw [this, pow_add]; ring
  · have := hl.two_le; omega

theorem relIndex_Gj (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    (Gj K j).relIndex (Gj K i) = l ^ (j - i) := by
  have h := Subgroup.relIndex_mul_index (Gj_anti K hij)
  obtain ⟨h1, h2⟩ := deg_Ks K hi hij
  rw [Gj, Gj, ← IntermediateField.finrank_eq_fixingSubgroup_index,
    ← IntermediateField.finrank_eq_fixingSubgroup_index, h1] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h2) h

theorem val_deg (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    padicValNat l (Module.finrank ℚ_[l] ↥(Ks K j)) - padicValNat l (Module.finrank ℚ_[l] ↥(Ks K i))
      = j - i := by
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2⟩ := deg_Ks K hi hij
  rw [h1, padicValNat.mul (pow_ne_zero _ hl.ne_zero) h2, padicValNat.prime_pow]
  omega

theorem free_finite (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlMod LL T
    Module.Free ℤ_[l] ↥T.L.T ∧ Module.Finite ℤ_[l] ↥T.L.T := by
  obtain ⟨d, M, A, hM⟩ := (GlobalTheory.Cyc.isMat_exists_and_props l K LL T).1
  unfold IsMat at hM
  obtain ⟨bT, _⟩ := hM
  letI := zlMod LL T
  exact ⟨Module.Free.of_basis bT, Module.Finite.of_basis bT⟩

theorem tors_induction {P : LocPrime l} (AI : LocAinf l P) (G : Subgroup (GQ l)) [CompactSpace ↥G]
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (c : ℤ → ℕ)
    (hcont : ∀ a b : ℤ, a ≤ b →
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      ∀ x, Continuous fun g => repQ AI G ρ a b g x)
    (hinv : ∀ a e b : ℤ, a ≤ e → e ≤ b →
      ∀ p : Qab (AinfSub l) (xiU AI) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e,
      (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) →
      ∀ z : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a e)), (∀ g, repQ AI G ρ a e g z = z) →
        ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))), (∀ g, repQ AI G ρ a b g x = x) ∧
          LinearMap.lTensor T p x = (l : ℤ_[l]) ^ k • z)
    (hC : ∀ i : ℤ,
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) i (i + 1))) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      TorsKilledBy (repQ AI G ρ i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ c i))
    (a : ℤ) (n : ℕ) :
    letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a (a + n + 1))) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
    TorsKilledBy (repQ AI G ρ a (a + n + 1)) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ ∑ i ∈ Finset.Ico a (a + n + 1), c i) := by
  induction n with
  | zero =>
    have e : a + ((0 : ℕ) : ℤ) + 1 = a + 1 := by simp
    rw [e]
    have e2 : Finset.Ico a (a + 1) = {a} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [e2, Finset.sum_singleton]
    exact hC a
  | succ n ih =>
    have e : a + ((n + 1 : ℕ) : ℤ) + 1 = (a + n + 1) + 1 := by push_cast; ring
    rw [e]
    generalize hb : a + n + 1 = b at ih ⊢
    have hab : a ≤ b := by omega
    have hb1 : b ≤ b + 1 := by omega
    have e2 : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [e2, Finset.sum_insert (by simp)]
    have hae := Mxi_anti (xiOK AI) hab
    have heb := Mxi_anti (xiOK AI) hb1
    obtain ⟨_, _⟩ := GlobalTheory.XiQuotient.tensor_quotient_torsionFree_complete l P AI a (b + 1) (hab.trans hb1) T
    obtain ⟨_, _⟩ := GlobalTheory.XiQuotient.tensor_quotient_torsionFree_complete l P AI b (b + 1) hb1 T
    obtain ⟨_, _⟩ := GlobalTheory.XiQuotient.tensor_quotient_torsionFree_complete l P AI a b hab T
    exact GlobalTheory.torsKilledBy_devissage l ↥G _ _ _ (repQ AI G ρ a (b + 1)) (repQ AI G ρ b (b + 1)) (repQ AI G ρ a b)
      (LinearMap.lTensor T (iQ (b + 1) hae))
      (LinearMap.lTensor T (pQ a heb)) _ _
      (Module.Flat.lTensor_preserves_injective_linearMap _ (iQ_injective _ hae))
      (LinearMap.lTensor_surjective _ (pQ_surjective a heb))
      (lTensor_exact _ (exact_iQ_pQ hae heb) (pQ_surjective a heb))
      (fun g x => iQ_equiv ρ _ _ hae g x) (fun g x => pQ_equiv ρ _ _ heb g x)
      (hcont a (b + 1) (hab.trans hb1))
      (hinv a b (b + 1) hab hb1 (pQ a heb) (fun _ => rfl))
      (hC b) ih

theorem tors_descend {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (G : Subgroup (GQ l)) (hle : Gj K i ≤ G) (hle' : Gj K j ≤ G)
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (a b : ℤ) (c : ℕ)
    [TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))]
    (h : TorsKilledBy (repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a b) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ c)) :
    TorsKilledBy (repQ AI (Gj K i) (ρ.comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ (j - i + c)) :=
  tors_repQ AI (Gj K i) (Gj K j) (Gj_anti K hij) _ _ (comp_inclusion (Gj_anti K hij) hle hle' ρ) a b _ _
    (relIndex_Gj K hi hij) h

set_option maxHeartbeats 1000000 in

theorem tors_combine {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (G : Subgroup (GQ l)) (hle : Gj K i ≤ G) (hle' : Gj K j ≤ G)
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (c : ℤ → ℕ)
    (hcont : ∀ a b : ℤ, a ≤ b →
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      ∀ x, Continuous fun g => repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a b g x)
    (hinv : ∀ a e b : ℤ, a ≤ e → e ≤ b →
      ∀ p : Qab (AinfSub l) (xiU AI) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e,
      (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) →
      ∀ z : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a e)),
        (∀ g, repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a e g z = z) →
        ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))),
          (∀ g, repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a b g x = x) ∧
          LinearMap.lTensor T p x = (l : ℤ_[l]) ^ k • z)
    (hC : ∀ e : ℤ,
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) e (e + 1))) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      TorsKilledBy (repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) e (e + 1)) (l : ℤ_[l])
        ((l : ℤ_[l]) ^ c e))
    (a b : ℤ) (hab : a < b) (N : ℕ) (hN : N = j - i + ∑ e ∈ Finset.Ico a b, c e) :
    letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
    TorsKilledBy (repQ AI (Gj K i) (ρ.comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ N) := by
  subst hN
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n + 1 := ⟨(b - a - 1).toNat, by omega⟩
  have := compact_Gj K j
  have key := tors_induction AI (Gj K j) T (ρ.comp (Subgroup.inclusion hle')) c hcont hinv hC a n
  exact @tors_descend l _ P AI K i j hi hij G hle hle' T _ _ ρ a _ _ (_) key

theorem vdeg_eq (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (m : ℕ) (hsm : s ≤ m) :
    vdegMs (sit D.loc HW l (D.locA l) K s LL h) m = m - s := by
  have h1 : ell (sit D.loc HW l (D.locA l) K s LL h) = l := (D.loc l).PD_p K
  have h2 : (sit D.loc HW l (D.locA l) K s LL h).W.s = s := (HW l).W_s K s LL h
  rw [vdegMs, h1, h2]
  exact val_deg K h.1 hsm

set_option maxHeartbeats 1000000 in

theorem torsion_bound_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (a b : ℤ) (hle : Gj K s ≤ GK K), a < b → HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ cLL l (mN l s (M0 + h0)) (vdegMs S (mN l s (M0 + h0))) (Jset S T) a b) := by
  intro D HW F h5 h7 l _ K s LL h S E T M0 h0 a b hle hab hW
  have hsm : s ≤ mN l s (M0 + h0) := by unfold mN; omega
  have hc : cLL l (mN l s (M0 + h0)) (vdegMs S (mN l s (M0 + h0))) (Jset S T) a b =
      mN l s (M0 + h0) - s + ∑ e ∈ Finset.Ico a b, (2 + max 1 (rI l (mN l s (M0 + h0)) (Jset S T) e)) := by
    rw [cLL, vdeg_eq D HW K s LL h _ hsm]
  have hle' := (Gj_anti K hsm).trans hle
  obtain ⟨hfree, hfin⟩ := free_finite K LL T
  have hC := fun i : ℤ => GlobalTheory.Cyc.GradedTorsion.torsion_killed D HW F h7 l K s LL h T M0 h0 i hle' hW
  have hcont := fun a b : ℤ => GlobalTheory.AinfCont.continuous_orbit_tensor_Qab D HW F l K s LL h T a b _ hle'
  have hinv := fun (a e b : ℤ) (hae : a ≤ e) (heb : e ≤ b) =>
    GlobalTheory.T.xiQuotient_invariants_lift_rationally D HW F h5 h7 l K s LL h T a e b _ hle' hsm hae heb hW.1
  exact @tors_combine l _ _ (D.locA l) K _ _ h.1 hsm (GK K) hle hle' _ _ (zlMod LL T) hfree hfin
    (actTZ LL T) _ hcont hinv hC a b hab _ hc

end GlobalTheory.TorsLL
