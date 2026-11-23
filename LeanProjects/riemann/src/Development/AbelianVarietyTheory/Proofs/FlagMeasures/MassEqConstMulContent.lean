import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonnegStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThickOrbitSelfDualUnramifiedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedContentThickenedSetIndependentOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContentThickenedTupleOrbitNormalSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupOrthogonalComplementUnimodularStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.QuotMass

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem unif_pow_mem (L : LocE F E) (ϖ : 𝒪[F]) (e : ℕ) : algebraMap F E ((ϖ : F) ^ e) ∈ L.O :=
  (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem ϖ.2 e)

theorem exists_pow_mul (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (c : E) :
    ∃ e : ℕ, algebraMap F E ((ϖ : F) ^ e) * c ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] c :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨e, (L.O_def _).2 ?_⟩
  have h1 := hd.smul (↑u⁻¹ : 𝒪[F])
  rw [smul_smul, hu, Units.inv_mul_cancel_left, Algebra.smul_def] at h1
  exact h1

theorem pow_smul_mono (L : LocE F E) (ϖ : 𝒪[F]) {n : ℕ} (Λ : Submodule L.O (Fin n → E))
    {v : Fin n → E} {e e' : ℕ} (h : e ≤ e') (hv : algebraMap F E ((ϖ : F) ^ e) • v ∈ Λ) :
    algebraMap F E ((ϖ : F) ^ e') • v ∈ Λ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, map_mul, mul_smul]
  exact Λ.smul_mem (⟨_, unif_pow_mem L ϖ k⟩ : L.O) hv

theorem exists_pow_smul (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {m : ℕ} (x : Fin m → Fin n → E) :
    ∃ e : ℕ, ∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ := by
  have h1 : ∀ v : Fin n → E, ∃ e : ℕ, algebraMap F E ((ϖ : F) ^ e) • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv => exact ⟨0, by simpa using hv⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨e, he⟩ := ha
      obtain ⟨f, hf⟩ := hb
      refine ⟨max e f, ?_⟩
      rw [smul_add]
      exact Λ.add_mem (pow_smul_mono L ϖ Λ (le_max_left _ _) he)
        (pow_smul_mono L ϖ Λ (le_max_right _ _) hf)
    | smul c a _ ha =>
      obtain ⟨e, he⟩ := ha
      obtain ⟨f, hf⟩ := exists_pow_mul L ϖ hϖ c
      refine ⟨f + e, ?_⟩
      have : algebraMap F E ((ϖ : F) ^ (f + e)) • c • a =
          (algebraMap F E ((ϖ : F) ^ f) * c) • algebraMap F E ((ϖ : F) ^ e) • a := by
        rw [smul_smul, smul_smul, pow_add, map_mul]; congr 1; ring
      rw [this]
      exact Λ.smul_mem (⟨_, hf⟩ : L.O) he
  choose e he using h1
  exact ⟨Finset.univ.sup fun a => e (x a), fun a =>
    pow_smul_mono L ϖ Λ (Finset.le_sup (f := fun a => e (x a)) (Finset.mem_univ a)) (he _)⟩

variable [CharZero F]

theorem cont_inf (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm) {Λs : Submodule L.O (Fin n → E)}
    (hs : IsSD L Hm Λs) {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det)
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) (hΛ' : IsLat L Λ') :
    ∃ i0 : ℕ, ∀ i ≥ i0, cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λ) x) i) *
      ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ (stabL L Λ ⊓ stabL L Λ')).relIndex
        (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) : ℝ) =
      ((isomG L Hm ⊓ stabL L Λ').relIndex (isomG L Hm ⊓ stabL L Λ) : ℝ) *
        cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ (stabL L Λ ⊓ stabL L Λ')) x) i) := by
  obtain ⟨N, hN⟩ := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ hΛ.1 1).2.2 Λ' hΛ'
  have hN' := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ' hΛ' 1).2.1 le_rfl
  obtain ⟨C, hC, hCi, hCn⟩ := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ hΛ.1 (max N 1)).1
  have hC1 := (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λ hΛ.1 (max N 1)).2.1 (le_max_right _ _)
  obtain ⟨e, he⟩ := exists_pow_smul L ϖ hϖ hΛ.1 x
  obtain ⟨i0, hi0, hth⟩ := GlobalTheory.T.thick_orbit_selfDual_unramified_lattice L ϖ hϖ Hm hH Λs hs Λ hΛ m _ hx (max N 1) e
  refine ⟨i0, fun i hi => ?_⟩
  set U := isomG L Hm with hU
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have hHU : H ≤ U := inf_le_left
  have hCS : C ≤ stabL L Λ := fun g hg => ((hC g).1 hg).1
  have hCS' : C ≤ stabL L Λ' := by
    intro g hg
    refine hN' g (hN g fun v hv => ?_)
    obtain ⟨w, hw, hgw⟩ := ((hC g).1 hg).2 v hv
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left N 1)
    refine ⟨algebraMap F E ((ϖ : F) ^ k) • w, Λ.smul_mem (⟨_, unif_pow_mem L ϖ k⟩ : L.O) hw, ?_⟩
    rw [hgw, hk, pow_add, map_mul, mul_smul]
  have h12 : U ⊓ C ≤ U ⊓ (stabL L Λ ⊓ stabL L Λ') := inf_le_inf_left _ (le_inf hCS hCS')
  have h1 : U ⊓ (stabL L Λ ⊓ stabL L Λ') ≤ U ⊓ stabL L Λ := inf_le_inf_left _ inf_le_left
  have hnorm : ∀ a ∈ U ⊓ stabL L Λ, MulAut.conj a • (U ⊓ C) = U ⊓ C := by
    intro a ha
    rw [Subgroup.smul_inf, hCn a ha.2, Subgroup.conj_smul_eq_self_of_mem ha.1]
  have hfin : ∀ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), ∀ T, T ≤ stabL L Λ →
      (K ⊓ C).relIndex (K ⊓ T) ≠ 0 := by
    intro K T hT
    have h := Subgroup.relIndex_ne_zero_trans (H := C) (K := stabL L Λ) (L := K ⊓ T)
    have h2 : C.relIndex (K ⊓ T) ≠ 0 := fun h0 =>
      hCi (Subgroup.relIndex_eq_zero_of_le_right (inf_le_right.trans hT) h0)
    rwa [← Subgroup.inf_relIndex_right (K ⊓ C), show K ⊓ C ⊓ (K ⊓ T) = C ⊓ (K ⊓ T) by
      ext g; simp only [Subgroup.mem_inf]; tauto, Subgroup.inf_relIndex_right]
  obtain ⟨hco, hst⟩ := hth i hi (U ⊓ C) (h12.trans h1)
    (fun g hg hg' => ⟨hg, (hC g).2 ⟨hC1 g hg', hg'⟩⟩) x he rfl
  have e1 := GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup L ϖ hϖ Hm hH Λs hs m x hx (U ⊓ stabL L Λ) (U ⊓ C) inf_le_left
    (h12.trans h1) hnorm (hfin U _ le_rfl) i (hi0.trans hi) hst hco
  have e2 := GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup L ϖ hϖ Hm hH Λs hs m x hx (U ⊓ (stabL L Λ ⊓ stabL L Λ')) (U ⊓ C)
    inf_le_left h12 (fun a ha => hnorm a (h1 ha)) (hfin U _ inf_le_left) i (hi0.trans hi) hst hco
  have hHi : ∀ T, H ⊓ (U ⊓ T) = H ⊓ T := fun T => by rw [← inf_assoc, inf_eq_left.2 hHU]
  rw [← hHdef] at e1 e2
  simp only [hHi] at e1 e2
  have m1 := Subgroup.relIndex_mul_relIndex _ _ _ h12 h1
  have m2 := Subgroup.relIndex_mul_relIndex (H ⊓ C) (H ⊓ (stabL L Λ ⊓ stabL L Λ')) (H ⊓ stabL L Λ)
    (inf_le_inf_left _ (le_inf hCS hCS')) (inf_le_inf_left _ inf_le_left)
  have m3 : (U ⊓ (stabL L Λ ⊓ stabL L Λ')).relIndex (U ⊓ stabL L Λ) =
      (U ⊓ stabL L Λ').relIndex (U ⊓ stabL L Λ) := by
    rw [← Subgroup.inf_relIndex_right (U ⊓ stabL L Λ')]
    congr 1
    ext g; simp only [Subgroup.mem_inf]; tauto
  rw [← m1, ← m2, m3] at e1
  push_cast at e1
  have hne : ((H ⊓ C).relIndex (H ⊓ (stabL L Λ ⊓ stabL L Λ')) : ℝ) ≠ 0 := by
    exact_mod_cast hfin H _ inf_le_left
  apply mul_left_cancel₀ hne
  linear_combination e1 - ((U ⊓ stabL L Λ').relIndex (U ⊓ stabL L Λ) : ℝ) * e2

theorem relIndex_symm (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm)
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) (hΛ' : IsSD L Hm Λ') :
    ((isomG L Hm ⊓ stabL L Λ').relIndex (isomG L Hm ⊓ stabL L Λ) : ℝ) =
      (isomG L Hm ⊓ stabL L Λ).relIndex (isomG L Hm ⊓ stabL L Λ') := by
  obtain ⟨g, hg, hgΛ⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).2 Λ Λ' hΛ hΛ'
  have hfix : fixG L Hm (Submodule.span E (Set.range (Fin.elim0 : Fin 0 → Fin n → E))) =
      isomG L Hm := by
    rw [Set.range_eq_empty, Submodule.span_empty]
    refine inf_eq_left.2 fun a _ => ⟨fun v => by simp, fun v hv => ?_⟩
    rw [(Submodule.mem_bot E).1 hv]; simp
  have h := GlobalTheory.T.unitaryGroup_orthogonalComplement_unimodular L Hm hH 0 Fin.elim0 (by simp) Λ Λ hΛ.1 hΛ.1 g (by rwa [hfix])
  rw [hfix, hgΛ] at h
  have hne : ((isomG L Hm ⊓ stabL L Λ).relIndex (isomG L Hm ⊓ stabL L Λ') : ℝ) ≠ 0 := by
    exact_mod_cast (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ' Λ hΛ'.1 hΛ.1 (isomG L Hm)).1
  simp only [invVol, Subgroup.relIndex_self, Nat.cast_one, div_one] at h
  exact (div_eq_one_iff_eq hne).1 h

end

theorem mass_eq_const_mul_content : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ Λ0, IsLat L Λ0 → ∃ κ : ℝ, 0 < κ ∧ ∀ Λ, IsSD L Hm Λ → ∃ i0 : ℕ, ∀ i ≥ i0, invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) = κ * cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λ) x) i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hs m x hx Λ0 h0
  have hΓ : IsHerm L (gramT L Hm x) := by
    funext a b
    exact DualInter.cj_hf hH _ _
  obtain ⟨e, he⟩ := exists_pow_smul L ϖ hϖ hs.1 x
  obtain ⟨j, hj, hth⟩ := GlobalTheory.T.thick_orbit_selfDual_unramified_lattice L ϖ hϖ Hm hH Λs hs Λs hs m _ hx 1 e
  have hth' := fun i hi => hth i hi (isomG L Hm ⊓ stabL L Λs) le_rfl
    (fun g hg hg' => ⟨hg, (GlobalTheory.T.congruence_subgroup_lattice_stabilizer L ϖ hϖ Λs hs.1 1).2.1 le_rfl g hg'⟩) x he rfl
  have h1K := fun i hi => GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  have hcpos : 0 < cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) x) j) :=
    (GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg _ _).2.2.2 (hth' j le_rfl).1
      ⟨_, _, ⟨1, Subgroup.one_mem _, rfl⟩, 1, (h1K j hj).1, rfl⟩
  have hhpos := ((h1K j hj).2.2 _ hΓ hx).2
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have hcomm : ∀ A B, IsLat L A → IsLat L B → (H ⊓ stabL L B).relIndex (H ⊓ stabL L A) ≠ 0 :=
    fun A B hA hB => (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L A B hA hB H).1
  have hvpos : 0 < invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) :=
    (GlobalTheory.HL.invVol_mul_pos_le_conj _ (H ⊓ stabL L Λs) _ (hcomm _ _ hs.1 h0) (hcomm _ _ h0 hs.1)
      (hcomm _ _ hs.1 h0) (hcomm _ _ h0 hs.1)).2.1
  refine ⟨invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) j) /
    cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) x) j), by positivity, ?_⟩
  intro Λ hΛ
  obtain ⟨i1, k1⟩ := cont_inf L ϖ hϖ hH hs x hx hΛ hs.1
  obtain ⟨i2, k2⟩ := cont_inf L ϖ hϖ hH hs x hx hs hΛ.1
  refine ⟨max j (max i1 i2), fun i hi => ?_⟩
  have hij : j ≤ i := (le_max_left _ _).trans hi
  have k1 := k1 i ((le_max_left _ _).trans ((le_max_right _ _).trans hi))
  have k2 := k2 i ((le_max_right _ _).trans ((le_max_right _ _).trans hi))
  rw [← hHdef] at k1 k2
  rw [inf_comm (stabL L Λs) (stabL L Λ), ← relIndex_symm L hH hΛ hs] at k2
  have lev := GlobalTheory.T.normalisedContent_thickenedSet_independent_of_level L ϖ hϖ Hm hH Λs hs m _ hΓ hx (torb (isomG L Hm ⊓ stabL L Λs) x)
    (by
      rintro _ ⟨g, hg, rfl⟩
      ext a b
      exact hg.1 _ _) j i hj hij (hth' j le_rfl).2 (hth' i hij).1
  have hsplit : H ⊓ (stabL L Λ ⊓ stabL L Λs) = (H ⊓ stabL L Λ) ⊓ (H ⊓ stabL L Λs) := inf_inf_distrib_left _ _ _
  have a1 : (H ⊓ (stabL L Λ ⊓ stabL L Λs)).relIndex (H ⊓ stabL L Λ0) ≠ 0 := by
    rw [hsplit]
    exact Subgroup.relIndex_inf_ne_zero (hcomm _ _ h0 hΛ.1) (hcomm _ _ h0 hs.1)
  have a2 : (H ⊓ stabL L Λ0).relIndex (H ⊓ (stabL L Λ ⊓ stabL L Λs)) ≠ 0 := fun h =>
    hcomm _ _ hΛ.1 h0 (Subgroup.relIndex_eq_zero_of_le_right (inf_le_inf_left _ inf_le_left) h)
  have v1 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ (H ⊓ stabL L Λ) _ (hcomm _ _ hΛ.1 h0) (hcomm _ _ h0 hΛ.1)
      a2 a1).2.2.1 (inf_le_inf_left _ inf_le_left)
  have v2 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ (H ⊓ stabL L Λs) _ (hcomm _ _ hs.1 h0) (hcomm _ _ h0 hs.1)
      a2 a1).2.2.1 (inf_le_inf_left _ inf_le_right)
  have hne : ((H ⊓ (stabL L Λ ⊓ stabL L Λs)).relIndex (H ⊓ stabL L Λ) : ℝ) ≠ 0 := by
    rw [hsplit, inf_comm, Subgroup.inf_relIndex_right]
    exact_mod_cast hcomm _ _ hΛ.1 hs.1
  rw [div_mul_eq_mul_div, eq_div_iff hcpos.ne']
  apply mul_left_cancel₀ hne
  rw [v1] at v2
  rw [← k1] at k2
  linear_combination
    (cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) *
      cont (tupLat L Λs m) (thick L ϖ (torb (isomG L Hm ⊓ stabL L Λs) x) j)) * v2 +
    (invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) *
      ((H ⊓ (stabL L Λ ⊓ stabL L Λs)).relIndex (H ⊓ stabL L Λs) : ℝ)) * lev +
    (invVol (H ⊓ stabL L Λ0) (H ⊓ stabL L Λs) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) j)) * k2

end GlobalTheory.HL.QuotMass
