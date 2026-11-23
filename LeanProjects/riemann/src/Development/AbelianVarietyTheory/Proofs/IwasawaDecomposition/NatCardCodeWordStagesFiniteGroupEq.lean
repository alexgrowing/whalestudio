import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPiecesStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.Mem.CyclotomicFieldContainment

theorem natCard_codeWordStages_finiteGroup_eq (X : Stages) : Nat.card (G0g X.toD7.nd) = X.B.restRowsFiniteGroupCard := by
  have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
  rw [Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
  rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
  rfl

theorem rootsField_le_iff (X : Stages) {N : IntermediateField ℚ ℂ} :
    rootsField X.B.toPre ≤ N ↔ ∀ n ∈ rootOrders X.toD7, cycField n ≤ N := by
  simp only [rootsField, rootOrders, natCard_codeWordStages_finiteGroup_eq, sup_le_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_assoc]
  rfl

theorem rootOrders_ne_zero (X : Stages) : ∀ n ∈ rootOrders X.toD7, n ≠ 0 := by
  have hg : ∀ k, X.toD7.host.g k * (X.toD7.host.g k - 1) ≠ 0 := fun k => by
    have hp := X.toD7.host.g_prime k
    exact mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  simp only [rootOrders, natCard_codeWordStages_finiteGroup_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨X.B.restRowsFiniteGroupCard_pos.ne', hg 0, hg 1, by norm_num, by norm_num⟩

variable (ι : Qb →+* ℂ)

theorem le_map_of_qb_le {A : IntermediateField ℚ ℂ} {Y : Fld} (hA : ∀ z ∈ A, ∃ x, ι x = z) (h : qb ι A ≤ Y) :
    A ≤ Y.map ι.toRatAlgHom := fun z hz => by
  obtain ⟨x, rfl⟩ := hA z hz
  exact ⟨x, h (mem_qb.2 hz), rfl⟩

theorem muFld_le_qb {n : ℕ} (hn : n ≠ 0) {N : IntermediateField ℚ ℂ} (h : cycField n ≤ N) : muFld n ≤ qb ι N := by
  rw [muFld, IntermediateField.adjoin_le_iff]
  intro x hx
  refine mem_qb.2 (h (mem_cycField hn ?_))
  rw [← map_pow, show x ^ n = 1 from hx, map_one]

theorem cycField_le_map {n : ℕ} (hn : n ≠ 0) {Y : Fld} (hY : muFld n ≤ Y) (hz : ∃ x, ι x = rootOne n) :
    cycField n ≤ Y.map ι.toRatAlgHom := by
  obtain ⟨x, hx⟩ := hz
  refine cycField_le_iff.2 ⟨x, hY (IntermediateField.subset_adjoin ℚ _ ?_), hx⟩
  apply ι.injective
  rw [map_pow, hx, map_one]
  exact (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

variable {E : Type} [Field E] [NumberField E]

theorem valsOf_subset_qb {χ : HChar E} {s : ℝ} {N : IntermediateField ℚ ℂ} (h : valueField χ s ≤ N) :
    valsOf ι s χ ⊆ qb ι N := fun _ ⟨v, hv, e⟩ =>
  mem_qb.2 (h (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, e⟩))

theorem valueField_le_map {χ : HChar E} {s : ℝ} {Y : Fld} (hY : valsOf ι s χ ⊆ Y)
    (hz : ∀ z ∈ valueField χ s, ∃ x, ι x = z) : valueField χ s ≤ Y.map ι.toRatAlgHom := by
  rw [valueField, IntermediateField.adjoin_le_iff]
  rintro z ⟨v, hv, rfl⟩
  obtain ⟨x, hx⟩ := hz _ (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, rfl⟩)
  exact ⟨x, hY ⟨v, hv, hx⟩, hx⟩

theorem ksQ_eq (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (hx : X.B.KsExact δ f) (T : HostTied X.toD7)
    (P : KsPieces X.toD7 T) (hR : P.rcf = qb T.fr.ι δ.ray) (hM : P.M = qb T.fr.ι δ.M) (hD : P.MDel = qb T.fr.ι δ.M')
    (hK : P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j)) :
    KsQ X.toD7 T (Fr.at X f) P = qb T.fr.ι (listField δ f) := by
  have hran : ∀ z ∈ listField δ f, ∃ x, T.fr.ι x = z := by
    intro z hz
    have hz' : z ∈ X.B.KsC := by rw [show X.B.KsC = listField δ f from hx]; exact hz
    obtain ⟨x, -, rfl⟩ := hz'
    exact ⟨T.jLL x, T.embLL x⟩
  have hle : ∀ {A : IntermediateField ℚ ℂ}, A ≤ listField δ f → ∀ z ∈ A, ∃ x, T.fr.ι x = z :=
    fun h z hz => hran z (h hz)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (listField_le_iff δ f).1 le_rfl
  have hKP : (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) ≤ listField δ f :=
    iSup₂_le fun j hj => h6 j hj.1 hj.2
  have hroots := (rootsField_le_iff X).1 h4
  have hne := rootOrders_ne_zero X
  simp only [charField, sup_le_iff, iSup_le_iff] at h5
  obtain ⟨⟨⟨⟨hmu, heta⟩, hdel⟩, hdel'⟩, hom⟩ := h5
  apply le_antisymm
  · have hM' : P.M ≤ qb T.fr.ι (listField δ f) := by
      rw [hM]
      exact fun x hx => mem_qb.2 (h2 (δ.M_le_M' hx))
    simp only [KsQ, sup_le_iff, iSup_le_iff]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hM'⟩, ?_⟩, ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact mem_qb.2 (h1 ⟨a, (T.fr.phi0 a).symm⟩)
    · exact fun n hn => muFld_le_qb _ (hne n hn) (hroots n hn)
    · rw [valsFld, IntermediateField.adjoin_le_iff]
      rintro x (((hx | hx) | hx) | hx)
      · obtain ⟨j, hx⟩ := Set.mem_iUnion.1 hx
        exact valsOf_subset_qb _ (hmu j) hx
      · exact valsOf_subset_qb _ heta hx
      · exact valsOf_subset_qb _ hdel hx
      · exact valsOf_subset_qb _ hdel' hx
    · rw [hR]; exact fun x hx => mem_qb.2 (h3 hx)
    · rw [hD]; exact fun x hx => mem_qb.2 (h2 hx)
    · rw [hK]; exact fun x hx => mem_qb.2 (hKP hx)
  · obtain ⟨Y, hYe⟩ : ∃ Y, Y = KsQ X.toD7 T (Fr.at X f) P := ⟨_, rfl⟩
    have hY : KsQ X.toD7 T (Fr.at X f) P ≤ Y := hYe.ge
    rw [← hYe]
    simp only [KsQ, sup_le_iff, iSup_le_iff] at hY
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, a6⟩, a7⟩ := hY
    have ha3 : ∀ {A : Set Qb}, A ⊆ valsFld X.toD7 T (Fr.at X f) → A ⊆ Y := fun h _ hx => a3 (h hx)
    have hv : (⋃ j, valsOf T.fr.ι 0 ((Fr.at X f).mu0 j)) ∪ valsOf T.fr.ι (1 / 2) (Fr.at X f).eta ∪
        valsOf T.fr.ι 0 (Fr.at X f).del ∪ valsOf T.fr.ι 0 (Fr.at X f).del' ⊆ Y :=
      ha3 (IntermediateField.subset_adjoin ℚ _)
    have hr : rootsField X.B.toPre ≤ Y.map T.fr.ι.toRatAlgHom := (rootsField_le_iff X).2 fun n hn =>
      cycField_le_map _ (hne n hn) (a2 n hn) (hran _ (hroots n hn (IntermediateField.mem_adjoin_simple_self ℚ _)))
    have hmap : listField δ f ≤ Y.map T.fr.ι.toRatAlgHom := by
      refine (listField_le_iff δ f).2 ⟨?_, ?_, ?_, hr, ?_, fun j hj hj' => ?_⟩
      · rintro _ ⟨a, rfl⟩
        exact ⟨T.fr.j a, a1 ⟨a, rfl⟩, T.fr.phi0 a⟩
      · exact le_map_of_qb_le _ (hle h2) (hD ▸ a6)
      · exact le_map_of_qb_le _ (hle h3) (hR ▸ a4)
      · simp only [charField, sup_le_iff, iSup_le_iff]
        refine ⟨⟨⟨⟨fun j => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, hx⟩))))) (hle (hmu j))
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inr hx)))) (hle heta)
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inr hx))) (hle hdel)
        · exact valueField_le_map _ (fun x hx => hv (Or.inr hx)) (hle hdel')
        · rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨k, a, rfl⟩
          exact hr (om_mem_rootsField f k a)
      · refine le_map_of_qb_le _ (hle (h6 j hj hj')) fun x hx => a7 ?_
        rw [hK]
        exact mem_qb.2 ((le_iSup₂_of_le j ⟨hj, hj'⟩ le_rfl : δ.KPsi j ≤ ⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) hx)
    intro x hx
    obtain ⟨y, hy, e⟩ := hmap hx
    have hyx : y = x := T.fr.ι.injective e
    exact hyx ▸ hy

theorem oTied_of_ksExact : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre)
    (δ : FieldDat X.B.toPre), X.B.KsExact δ f → ∀ T : HostTied X.toD7, ∃ O : OTied X.toD7 T (Fr.at X f),
      O.pieces.rcf = qb T.fr.ι δ.ray ∧ O.pieces.MDel = qb T.fr.ι δ.M' := by
  intro hA hW X f δ hx T
  obtain ⟨P, -, hR, hM, hD, hK⟩ := GlobalTheory.T.exists_smallField_classFieldPieces hA hW X f δ T
  have hq := ksQ_eq X f δ hx T P hR hM hD hK
  refine ⟨⟨P, X.B.OtoLL_injective, fun x => ?_⟩, hR, hD⟩
  rw [hq]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨mem_qb.2 ?_, (X.toD7.O_int y).map T.jLL.toIntAlgHom⟩
    rw [T.embLL, ← show X.B.KsC = listField δ f from hx]
    exact ⟨_, (algebraMap (𝓞 X.B.Ks) X.B.Ks y).2, rfl⟩
  · rintro ⟨hxq, hi⟩
    have hz : T.fr.ι x ∈ X.B.KsC := by
      rw [show X.B.KsC = listField δ f from hx]
      exact hxq
    obtain ⟨w, hw, e⟩ := hz
    have hwx : T.jLL w = x := T.fr.ι.injective ((T.embLL w).trans e)
    subst hwx
    have hwi : IsIntegral ℤ w := (isIntegral_algHom_iff T.jLL.toIntAlgHom T.jLL.injective).1 hi
    obtain ⟨y, hy⟩ := X.B.O_full w hw hwi
    exact ⟨y, congrArg T.jLL hy⟩

end GlobalTheory.Mem.CyclotomicFieldContainment

end
