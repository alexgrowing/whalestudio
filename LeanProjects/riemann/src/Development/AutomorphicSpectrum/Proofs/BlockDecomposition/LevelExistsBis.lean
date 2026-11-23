import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpenNhdOneOfIntegralEqOneOnFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.LevelU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_conj_ext (w : Pl E) (hw : ¬ IsSplitAt w) :
    ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  have hc : GlobalTheory.CuspRep.conjSrc (GlobalTheory.SplitPts.conjE E) w = w := (GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).2 hw
  obtain ⟨h1, h2⟩ := GlobalTheory.SplitPts.psi_spec w
  have key : ∀ (u : Pl E) (f : w.adicCompletion E →+* u.adicCompletion E), u = w → Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (GlobalTheory.SplitPts.conjE E k)) →
      ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
    rintro u f rfl hf hk
    exact ⟨f, hf, fun x => hk x⟩
  exact key _ (GlobalTheory.SplitPts.psi w) hc h1 h2

private theorem exists_continuousMulEquiv_subgroup_of_forall_mem {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (B : Subgroup H) (hB : ∀ h, h ∈ B) (e0 : G ≃ₜ* H) : ∃ e : G ≃ₜ* B, ∀ x, (e x : H) = e0 x :=
  ⟨{ toFun := fun x => ⟨e0 x, hB _⟩
     invFun := fun y => e0.symm y.1
     left_inv := fun x => by simp
     right_inv := fun y => by ext; simp
     map_mul' := fun x y => by ext; simp
     continuous_toFun := e0.continuous.subtype_mk _
     continuous_invFun := e0.symm.continuous.comp continuous_subtype_val }, fun _ => rfl⟩

private theorem exists_continuousMulEquiv_of_subgroup_eq {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (A B : Subgroup H) (hAB : ∀ h, h ∈ A → h ∈ B) (hBA : ∀ h, h ∈ B → h ∈ A) (e0 : G ≃ₜ* A) :
    ∃ e : G ≃ₜ* B, ∀ x, (e x : H) = (e0 x : H) :=
  ⟨{ toFun := fun x => ⟨(e0 x : H), hAB _ (e0 x).2⟩
     invFun := fun y => e0.symm ⟨y.1, hBA _ y.2⟩
     left_inv := fun x => by simp
     right_inv := fun y => by ext; simp
     map_mul' := fun x y => by ext; simp
     continuous_toFun := (continuous_subtype_val.comp e0.continuous).subtype_mk _
     continuous_invFun := e0.symm.continuous.comp (continuous_subtype_val.subtype_mk _) }, fun _ => rfl⟩

theorem exists_equiv (n : ℕ) (w : Pl E) :
    ∃ e : locU n w ≃ₜ* UL n w, ∀ x : locU n w, ((e x : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  by_cases hw : IsSplitAt w
  · obtain ⟨e0, he0⟩ := GlobalTheory.locU_equiv_GL E n w hw
    have hmem : ∀ g : GLw n w, g ∈ UL n w := by intro g; simp [GlobalTheory.BCT.UL, hw]
    obtain ⟨e, he⟩ := exists_continuousMulEquiv_subgroup_of_forall_mem (UL n w) hmem e0
    exact ⟨e, fun x => by rw [he, he0]⟩
  · have hspec := GlobalTheory.ConjAtPlace.cj_spec w (exists_conj_ext w hw)
    obtain ⟨e0, he0⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) hspec.2 (GlobalTheory.PrincCong.v_cj w)
    have hiff : ∀ g : GLw n w, g ∈ UL n w ↔ g ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      intro g; simp [GlobalTheory.BCT.UL, hw]
    obtain ⟨e, he⟩ := exists_continuousMulEquiv_of_subgroup_eq _ (UL n w) (fun g hg => (hiff g).2 hg) (fun g hg => (hiff g).1 hg) e0
    exact ⟨e, fun x => by rw [he, he0]⟩

theorem isClosed_UL (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  by_cases hw : IsSplitAt w
  · have : (UL n w : Set (GLw n w)) = Set.univ := by ext g; simp [GlobalTheory.BCT.UL, hw]
    rw [this]; exact isClosed_univ
  · have hc : Continuous (cj w) := (GlobalTheory.ConjAtPlace.cj_spec w (exists_conj_ext w hw)).1
    have : (UL n w : Set (GLw n w)) = {g : GL (Fin n) (w.adicCompletion E) |
        Formalism.UG.cT (cj w) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
          (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1} := by
      ext g; simp [GlobalTheory.BCT.UL, hw, Formalism.UG.UJ]
    rw [this]
    have hv : Continuous (fun g : GL (Fin n) (w.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :=
      Units.continuous_val
    apply isClosed_eq _ continuous_const
    unfold Formalism.UG.cT
    exact ((hv.matrix_map hc).matrix_transpose.matrix_mul continuous_const).matrix_mul hv

private theorem isCompact_adicCompletionIntegers' (w : Pl E) :
    IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (0 : w.adicCompletion E)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hC
  have hB := (Valued.mem_nhds_zero (R := w.adicCompletion E)).2 ⟨γ, subset_refl _⟩
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer (K := E) w
  have hv0 : Valued.v (π : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [← hπ]
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
  have hlt : Valued.v (π : w.adicCompletion E) < 1 := by
    rw [hv0]
    have h : WithZero.exp (-1 : ℤ) < WithZero.exp 0 := WithZero.exp_lt_exp.2 (by norm_num)
    simpa using h
  have hne : (π : w.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv0
    exact WithZero.exp_ne_zero hv0.symm
  obtain ⟨N, hN⟩ := ((GlobalTheory.ConjAtPlace.tendsto_pow_of_lt_one _ hlt).eventually hB).exists
  have hcne : (π : w.adicCompletion E) ^ N ≠ 0 := pow_ne_zero _ hne
  have hsub : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) ⊆
      (fun y => ((π : w.adicCompletion E) ^ N)⁻¹ * y) '' C := by
    intro x hx
    have hx1 : Valued.v x ≤ 1 := hx
    refine ⟨(π : w.adicCompletion E) ^ N * x, hγ ?_, ?_⟩
    · rw [Set.mem_ofPred_eq, map_mul]
      refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) hN
      exact (Valuation.restrict_le_one_iff _).2 hx1
    · simp only
      rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  have hcl : IsClosed (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    Valued.isClosed_integer (w.adicCompletion E)
  exact (hCc.image (continuous_const.mul continuous_id)).of_isClosed_subset hcl hsub

private theorem isCompact_KGL' (w : Pl E) : IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
  have hO := isCompact_adicCompletionIntegers' w
  let A : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    {M | ∀ i j, M i j ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E))}
  have hA : IsCompact A := by
    have h : A = Set.univ.pi (fun _ : Fin n => Set.univ.pi
        (fun _ : Fin n => (w.adicCompletionIntegers E : Set (w.adicCompletion E)))) := by
      ext M
      constructor
      · intro h i _ j _
        exact h i j
      · intro h i j
        exact h i (Set.mem_univ _) j (Set.mem_univ _)
    rw [h]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => hO))
  let f := Units.embedProduct (Matrix (Fin n) (Fin n) (w.adicCompletion E))
  have hind : Topology.IsInducing f := Units.isEmbedding_embedProduct.isInducing
  let P : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E) × (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ) :=
    (A ×ˢ (MulOpposite.unop ⁻¹' A)) ∩ {q | q.1 * q.2.unop = 1 ∧ q.2.unop * q.1 = 1}
  have hP : IsCompact P := by
    apply IsCompact.inter_right
    · exact hA.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hA)
    · exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
        continuous_const).inter
        (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  have hclosed : IsClosed (GlobalTheory.LFun.KGL w n : Set (GLw n w)) :=
    Subgroup.isClosed_of_isOpen _
      (Subgroup.isOpen_mono (fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w n 0 g).1 hg).1)
        (GlobalTheory.PrincCong.isOpen_congSub w n 0))
  have hfP : IsCompact (f ⁻¹' P) := by
    rw [hind.isCompact_iff]
    have h : f '' (f ⁻¹' P) = P := by
      apply Set.image_preimage_eq_of_subset
      rintro ⟨a, b⟩ ⟨-, h1, h2⟩
      exact ⟨⟨a, b.unop, h1, h2⟩, rfl⟩
    rw [h]
    exact hP
  refine hfP.of_isClosed_subset hclosed ?_
  intro g hg
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j
    exact GlobalTheory.UnramDict.entry_mem hg i j
  · intro i j
    exact GlobalTheory.UnramDict.entry_mem (inv_mem hg) i j
  · exact g.mul_inv
  · exact g.inv_mul

theorem isCompact_locK (w : Pl E) :
    IsCompact (((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) : Set (locU n w)) := by
  obtain ⟨e, he⟩ := exists_equiv n w
  have hK : IsCompact ((Subtype.val : UL n w → GLw n w) ⁻¹' (GlobalTheory.LFun.KGL w n : Set (GLw n w))) :=
    (isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_KGL' w)
  have heq : (((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) :
      Set (locU n w)) = e ⁻¹' ((Subtype.val : UL n w → GLw n w) ⁻¹' (GlobalTheory.LFun.KGL w n : Set (GLw n w))) := by
    ext x
    show cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w n ↔ ((e x : UL n w) : GLw n w) ∈ GlobalTheory.LFun.KGL w n
    rw [he]
  rw [heq]
  exact (e.toHomeomorph.isCompact_preimage).2 hK

theorem exists_cong_le (w : Pl E) (U : Subgroup (UL n w)) (hU : IsOpen (U : Set (UL n w))) :
    ∃ k₀ : ℕ, ∀ m ≥ k₀, ∀ γ : UL n w, γ.1 ∈ GlobalTheory.PrincCong.congSub w n m → γ ∈ U := by
  have hU1 : (U : Set (UL n w)) ∈ 𝓝 (1 : UL n w) := hU.mem_nhds U.one_mem
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap] at hU1
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU1
  have hV' : V ∈ 𝓝 (1 : GL (Fin n) (w.adicCompletion E)) := by simpa using hV
  rw [(Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))).isInducing.nhds_eq_comap]
    at hV'
  obtain ⟨t, ht, htV⟩ := Filter.mem_comap.1 hV'
  simp only [Units.embedProduct_apply, Units.val_one, inv_one, MulOpposite.op_one] at ht
  rw [nhds_prod_eq] at ht
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_prod_iff.1 ht
  have hC2 : MulOpposite.op ⁻¹' t2 ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using ht2)
  obtain ⟨N1, hN1⟩ := GlobalTheory.PrincCong.exists_mat_subset w n ht1
  obtain ⟨N2, hN2⟩ := GlobalTheory.PrincCong.exists_mat_subset w n hC2
  refine ⟨max N1 N2, fun m hm γ hγ => ?_⟩
  have hγ1 := (GlobalTheory.PrincCong.mem_congSub_iff w n m γ.1).1 hγ
  have hγ2 := (GlobalTheory.PrincCong.mem_congSub_iff w n m γ.1⁻¹).1 (inv_mem hγ)
  apply hVU
  apply htV
  apply hsub
  exact ⟨hN1 m (le_of_max_le_left hm) _ hγ1.2, hN2 m (le_of_max_le_right hm) _ hγ2.2⟩

theorem congSub_le_KGL (w : Pl E) (m : ℕ) : GlobalTheory.PrincCong.congSub w n m ≤ GlobalTheory.LFun.KGL w n := by
  intro g hg
  exact ((GlobalTheory.PrincCong.mem_congSub_iff w n m g).1 hg).1

def cong (n : ℕ) (w : Pl E) (m : ℕ) : Subgroup (UL n w) := (GlobalTheory.PrincCong.congSub w n m).subgroupOf (UL n w)

theorem isCong_cong (w : Pl E) (m : ℕ) : IsCong m (cong n w m) := by
  unfold PositivityTheory.Rg.BcB.F.Eig.IsCong
  intro k
  rw [cong, Subgroup.mem_subgroupOf, GlobalTheory.PrincCong.mem_congSub_iff, GlobalTheory.BCT.KL, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j => by simpa [Matrix.sub_apply] using h2 i j⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j => by simpa [Matrix.sub_apply] using h2 i j⟩

theorem isLevel_cong (w : Pl E) (m : ℕ) : IsLevel (MonoidHom.id (UL n w)) (KL n w) (cong n w m) := by
  unfold GlobalTheory.BCT.IsLevel
  refine ⟨?_, ?_, fun k hk => hk⟩
  · rw [cong, Subgroup.coe_subgroupOf]
    exact (GlobalTheory.PrincCong.isOpen_congSub w n m).preimage continuous_subtype_val
  · intro k hk
    rw [cong, Subgroup.mem_subgroupOf] at hk
    rw [GlobalTheory.BCT.KL, Subgroup.mem_subgroupOf]
    exact congSub_le_KGL w m hk

theorem isLevel_KL (w : Pl E) : IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w) := by
  unfold GlobalTheory.BCT.IsLevel
  refine ⟨?_, le_rfl, fun k hk => hk⟩
  have hK : IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) :=
    Subgroup.isOpen_mono (congSub_le_KGL w 0) (GlobalTheory.PrincCong.isOpen_congSub w n 0)
  rw [GlobalTheory.BCT.KL, Subgroup.coe_subgroupOf]
  exact hK.preimage continuous_subtype_val

def fixG (φ : UA E n → ℂ) : Subgroup (UA E n) where
  carrier := {x | RU E n x φ = φ}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change RU E n (a * b) φ = φ
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    change RU E n a⁻¹ φ = φ
    conv_lhs => rw [← show RU E n a φ = φ from ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_level_at {φ : UA E n → ℂ} (hφ : IsAutFormU φ) (w : Pl E) :
    ∃ k₀ : ℕ, ∀ m ≥ k₀, ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.PrincCong.congSub w n m → RU E n x φ = φ := by
  obtain ⟨e, he⟩ := exists_equiv n w
  let U : Subgroup (UL n w) := (fixG φ).comap ((locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom)
  have hUo : IsOpen (U : Set (UL n w)) :=
    hφ.level.preimage ((GlobalTheory.DefU.LocAdm.continuous_inclusion_locU (n := n) w).comp e.symm.continuous)
  obtain ⟨k₀, hk₀⟩ := exists_cong_le w U hUo
  refine ⟨k₀, fun m hm x hx hc => ?_⟩
  have hγ : (e ⟨x, hx⟩ : UL n w).1 ∈ GlobalTheory.PrincCong.congSub w n m := by rw [he]; exact hc
  have h2 : RU E n ((e.symm (e ⟨x, hx⟩) : locU n w) : UA E n) φ = φ := hk₀ m hm _ hγ
  simpa using h2

theorem exists_fix_off {φ : UA E n → ℂ} (hφ : IsAutFormU φ) :
    ∃ T : Finset (Pl E), ∀ w : Pl E,
      (∀ t ∈ T, t.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) →
      ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ := by
  obtain ⟨T, hT⟩ := GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset E n
    {k : finU E n | RU E n (k : UA E n) φ = φ} hφ.level (by simp)
  refine ⟨T, fun w hw x hx hc => ?_⟩
  have hxf : x ∈ finU E n := GlobalTheory.DefU.LocAdm.locU_le_finU w hx
  have h := hT ⟨x, hxf⟩ (fun v hv => GlobalTheory.DefU.LocRet.mem_locU_ne hx (hw v hv))
    (fun v i j => GlobalTheory.UnramDict.cLoc_entry_mem hx hc v i j)
    (fun v i j => by
      have h1 := GlobalTheory.UnramDict.cLoc_entry_mem (inv_mem hx) (by rw [map_inv]; exact inv_mem hc) v i j
      rwa [map_inv] at h1)
  exact h

theorem commute_locU {u w : Pl E}
    (h : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) {x y : UA E n}
    (hx : x ∈ locU n u) (hy : y ∈ locU n w) : x * y = y * x := by
  apply Subtype.ext
  apply GlobalTheory.DefU.LocRet.ga_ext'
  · have h1 := GlobalTheory.DefU.LocRet.mem_locU_inf hx
    have h2 := GlobalTheory.DefU.LocRet.mem_locU_inf hy
    simp only [Subgroup.coe_mul, map_mul, h1, h2]
  · intro v
    by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))
    · have hvw : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
        rw [hv]; exact h
      have h2 := GlobalTheory.DefU.LocRet.mem_locU_ne hy hvw
      simp only [Subgroup.coe_mul, map_mul, h2, mul_one, one_mul]
    · have h1 := GlobalTheory.DefU.LocRet.mem_locU_ne hx hv
      simp only [Subgroup.coe_mul, map_mul, h1, mul_one, one_mul]

theorem step {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : Pl E} (hu : IsUnramU π w) (Q : Set (UA E n))
    (hQ : ∀ q ∈ Q, ∀ x ∈ locU n w, q * x = x * q) {φ : UA E n → ℂ} (hφ : φ ∈ π) (h0 : φ ≠ 0)
    (hfix : ∀ q ∈ Q, RU E n q φ = φ) :
    ∃ ψ ∈ π, ψ ≠ 0 ∧ (∀ q ∈ Q, RU E n q ψ = ψ) ∧
      ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x ψ = ψ := by
  obtain ⟨φ1, hφ1, hne1, hfix1⟩ := hu
  have hst : ∀ (x : UA E n), ∀ f ∈ π, (GlobalTheory.PRep.rightReg ℂ (UA E n) ℂ x) f ∈ π := hπ.stable
  let j : locU n w →* UA E n := (locU n w).subtype
  let p : UA E n →* locU n w := GlobalTheory.DefU.LocRet.ret w n
  let Z : Subgroup (UA E n) := Subgroup.centralizer (locU n w : Set (UA E n))
  have hZ1 : ∀ x : UA E n, (j (p x))⁻¹ * x ∈ Z := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((GlobalTheory.DefU.LocRet.commute_ret x ⟨h, hh⟩).eq).symm
  have hZ2 : ∀ x ∈ Z, ∀ h : locU n w, x * j h = j h * x := by
    intro x hx h
    rw [Subgroup.mem_centralizer_iff] at hx
    exact (hx (j h) h.2).symm
  have key : ∀ (g : locU n w) (v : π),
      ((GlobalTheory.UnitaryBC.SatEx.pull π hst j g v : π) : UA E n → ℂ) = RU E n (g : UA E n) (v : UA E n → ℂ) :=
    fun _ _ => rfl
  have hsm : GlobalTheory.PRep.IsSmooth (GlobalTheory.UnitaryBC.SatEx.pull π hst j) := by
    intro v
    have h2 := (hπ.aut (v : UA E n → ℂ) v.2).level.preimage
      (GlobalTheory.DefU.LocAdm.continuous_inclusion_locU (n := n) w)
    have hset : {g : locU n w | (GlobalTheory.UnitaryBC.SatEx.pull π hst j g) v = v} =
        {g : locU n w | RU E n (g : UA E n) (v : UA E n → ℂ) = v} := by
      ext g
      simp only [Set.mem_ofPred_eq, Subtype.ext_iff, key]
    rw [hset]
    exact h2
  have hφ1ne : (⟨φ1, hφ1⟩ : π) ≠ 0 := fun h => hne1 (congrArg Subtype.val h)
  have hφ1K : (⟨φ1, hφ1⟩ : π) ∈ GlobalTheory.PRep.fixed (GlobalTheory.UnitaryBC.SatEx.pull π hst j)
      ((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype)) := by
    intro h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    apply Subtype.ext
    rw [key]
    exact hfix1 _ (h : locU n w).2 h.2
  let W : Submodule ℂ π :=
    { carrier := {v | ∀ q ∈ Q, RU E n q (v : UA E n → ℂ) = v}
      add_mem' := by
        intro a b ha hb q hq
        simp only [Submodule.coe_add, map_add, ha q hq, hb q hq]
      zero_mem' := by
        intro q hq
        simp
      smul_mem' := by
        intro c v hv q hq
        simp only [Submodule.coe_smul, map_smul, hv q hq] }
  have hWst : ∀ (g : locU n w), ∀ v ∈ W, (GlobalTheory.UnitaryBC.SatEx.pull π hst j g) v ∈ W := by
    intro g v hv q hq
    change RU E n q (((GlobalTheory.UnitaryBC.SatEx.pull π hst j g) v : π) : UA E n → ℂ) =
      (((GlobalTheory.UnitaryBC.SatEx.pull π hst j g) v : π) : UA E n → ℂ)
    rw [key, ← Module.End.mul_apply, ← map_mul, hQ q hq g g.2, map_mul, Module.End.mul_apply, hv q hq]
  have hne : W ⊓ GlobalTheory.PRep.fixed (GlobalTheory.UnitaryBC.SatEx.pull π hst j)
      ((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype)) ≠ ⊥ := by
    intro hbot
    have hWb := GlobalTheory.UnitaryBC.SatEx.pull_eq_bot (Z := Z) (p := p) hπ.irred hZ1 hZ2 hsm
      (isCompact_locK w) hφ1ne hφ1K W hWst hbot
    have hφW : (⟨φ, hφ⟩ : π) ∈ W := hfix
    rw [hWb] at hφW
    exact h0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hφW))
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hv1 := (Submodule.mem_inf.1 hv).1
  have hv2 := (Submodule.mem_inf.1 hv).2
  refine ⟨v, v.2, fun h => hv0 (Subtype.ext h), hv1, ?_⟩
  intro x hx hc
  have h := hv2 ⟨⟨x, hx⟩, hc⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h
  have h' := congrArg Subtype.val h
  rw [key] at h'
  exact h'

private theorem sum_le_mul_sum_of_fiber_weight_bound (t u : Pl E)
    (hu : u.under (𝓞 (maximalRealSubfield E)) = t.under (𝓞 (maximalRealSubfield E))) :
    u = t ∨ u = GlobalTheory.CuspRep.conjSrc (GlobalTheory.SplitPts.conjE E) t := by
  by_cases ht : IsSplitAt t
  · exact (GlobalTheory.SplitPts.over_split ht).2.2 u hu
  · left
    by_contra h
    exact ht ⟨u, h, hu⟩

theorem levelEx : LevelEx := by
  unfold PositivityTheory.Rg.BcB.F.Eig.LevelEx
  intro E _ _ _ n π hπ S hS R M
  obtain ⟨φ0, hφ0, hne0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ.ne_bot
  have ha0 := hπ.aut φ0 hφ0
  obtain ⟨T, hT⟩ := exists_fix_off ha0
  choose k hk using fun w : Pl E => exists_level_at ha0 w
  let Tb : Finset (Pl E) := T ∪ T.image (GlobalTheory.CuspRep.conjSrc (GlobalTheory.SplitPts.conjE E)) ∪ R
  let m : ℕ := max (max M 1) (Tb.sup k)
  have hoff : ∀ w : Pl E, w ∉ Tb →
      ∀ t ∈ T, t.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
    intro w hw t ht heq
    apply hw
    rcases sum_le_mul_sum_of_fiber_weight_bound t w heq.symm with h | h
    · subst h
      simp [Tb, ht]
    · simp only [Tb, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨t, ht, h.symm⟩)
  have hunr : ∀ w : Pl E, w ∉ Tb → IsUnramU π w := fun w hw => ⟨φ0, hφ0, hne0, hT w (hoff w hw)⟩
  let K₀ : (w : Pl E) → Subgroup (UL n w) := fun w =>
    if IsUnramU π w ∧ w ∉ R then KL n w else cong n w m
  have hlev : ∀ w : Pl E, IsLevel (MonoidHom.id (UL n w)) (KL n w) (K₀ w) := by
    intro w
    by_cases h : IsUnramU π w ∧ w ∉ R
    · simp only [K₀, if_pos h]
      exact isLevel_KL w
    · simp only [K₀, if_neg h]
      exact isLevel_cong w m
  have hcof : ∀ᶠ w in Filter.cofinite, K₀ w = KL n w := by
    rw [Filter.eventually_cofinite]
    refine (Tb.finite_toSet).subset ?_
    intro w hw
    by_contra hwT
    apply hw
    have h : IsUnramU π w ∧ w ∉ R := ⟨hunr w hwT, fun hR => hwT (by simp [Tb, hR])⟩
    simp only [K₀, if_pos h]
  have hfam : IsLevelFam (fun w => MonoidHom.id (UL n w)) (KL n) K₀ := by
    unfold GlobalTheory.BCT.IsLevelFam
    exact ⟨hlev, hcof⟩
  have hK1 : ∀ w : Pl E, IsUnramU π w → w ∉ R → K₀ w = KL n w := by
    intro w h1 h2
    simp only [K₀, if_pos (And.intro h1 h2)]
  have hK2 : ∀ w : Pl E, ¬ IsUnramU π w ∨ w ∈ R → IsCong m (K₀ w) := by
    intro w h
    have h' : ¬ (IsUnramU π w ∧ w ∉ R) := by
      rintro ⟨h1, h2⟩
      rcases h with h | h
      · exact h h1
      · exact h2 h
    simp only [K₀, if_neg h']
    exact isCong_cong w m
  let F : Finset (Pl E) := Tb.filter (fun w => w ∈ S ∧ IsUnramU π w ∧ w ∉ R)
  have hbase : ∀ w ∈ S, w ∉ F → ∀ x ∈ locU n w,
      (∃ κ ∈ K₀ w, (κ : GLw n w) = cLoc w x) → RU E n x φ0 = φ0 := by
    rintro w hwS hwF x hx ⟨κ, hκ, hκx⟩
    by_cases hT' : w ∈ Tb
    · have h' : ¬ (IsUnramU π w ∧ w ∉ R) := fun h => hwF (Finset.mem_filter.2 ⟨hT', hwS, h⟩)
      simp only [K₀, if_neg h'] at hκ
      rw [cong, Subgroup.mem_subgroupOf] at hκ
      have hc : cLoc w x ∈ GlobalTheory.PrincCong.congSub w n m := by
        rw [← hκx]
        exact hκ
      exact hk w m (le_trans (Finset.le_sup hT') (le_max_right _ _)) x hx hc
    · have hKL : cLoc w x ∈ GlobalTheory.LFun.KGL w n := by
        by_cases h : IsUnramU π w ∧ w ∉ R
        · simp only [K₀, if_pos h] at hκ
          rw [GlobalTheory.BCT.KL, Subgroup.mem_subgroupOf] at hκ
          rw [← hκx]
          exact hκ
        · simp only [K₀, if_neg h] at hκ
          rw [cong, Subgroup.mem_subgroupOf] at hκ
          rw [← hκx]
          exact congSub_le_KGL w m hκ
      exact hT w (hoff w hT') x hx hKL
  have hind : ∀ F' : Finset (Pl E), F' ⊆ F → ∃ φ ∈ π, φ ≠ 0 ∧ ∀ w ∈ S, (w ∉ F ∨ w ∈ F') →
      ∀ x ∈ locU n w, (∃ κ ∈ K₀ w, (κ : GLw n w) = cLoc w x) → RU E n x φ = φ := by
    intro F'
    induction F' using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨φ0, hφ0, hne0, fun w hw h => ?_⟩
      rcases h with h | h
      · exact hbase w hw h
      · simp at h
    | insert a F' haF ih =>
      intro hsub
      obtain ⟨φ, hφ, hne, hfx⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      have haF' : a ∈ F := hsub (Finset.mem_insert_self a F')
      obtain ⟨_, haS, haU, haR⟩ := Finset.mem_filter.1 haF'
      let Q : Set (UA E n) := {x | ∃ w ∈ S, w ≠ a ∧ (w ∉ F ∨ w ∈ F') ∧ x ∈ locU n w ∧
        ∃ κ ∈ K₀ w, (κ : GLw n w) = cLoc w x}
      have hQ : ∀ q ∈ Q, ∀ x ∈ locU n a, q * x = x * q := by
        rintro q ⟨w, hwS, hwa, -, hqw, -⟩ x hx
        refine commute_locU ?_ hqw hx
        intro heq
        apply hwa
        obtain ⟨u, -, huniq⟩ := hS a
        exact (huniq w ⟨hwS, heq⟩).trans (huniq a ⟨haS, rfl⟩).symm
      obtain ⟨ψ, hψ, hψ0, hψQ, hψa⟩ := step hπ haU Q hQ hφ hne (by
        rintro q ⟨w, hwS, -, hw, hqw, hκ⟩
        exact hfx w hwS hw q hqw hκ)
      refine ⟨ψ, hψ, hψ0, fun w hwS hw => ?_⟩
      by_cases hwa : w = a
      · subst hwa
        rintro x hx ⟨κ, hκ, hκx⟩
        simp only [K₀, if_pos (And.intro haU haR)] at hκ
        rw [GlobalTheory.BCT.KL, Subgroup.mem_subgroupOf] at hκ
        apply hψa x hx
        rw [← hκx]
        exact hκ
      · have hw' : w ∉ F ∨ w ∈ F' := by
          rcases hw with h | h
          · exact Or.inl h
          · exact Or.inr ((Finset.mem_insert.1 h).resolve_left hwa)
        intro x hx hκ
        exact hψQ x ⟨w, hwS, hwa, hw', hx, hκ⟩
  refine ⟨K₀, m, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), hfam, hK1, hK2, ?_⟩
  intro K' hK'
  obtain ⟨φ, hφ, hne, hfx⟩ := hind F (subset_refl F)
  unfold GlobalTheory.BCT.HasLevel
  refine ⟨φ, hφ, hne, ?_⟩
  rintro w hwS x hx ⟨κ, hκ, hκx⟩
  have hw : w ∉ F ∨ w ∈ F := by
    by_cases h : w ∈ F
    · exact Or.inr h
    · exact Or.inl h
  exact hfx w hwS hw x hx ⟨κ, hK' w hκ, hκx⟩

end GlobalTheory.CompanionTheory.LevelU

end
