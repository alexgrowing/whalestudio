import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.EmbeddingSecondCoefficient

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

abbrev RelG (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) : Submodule M.L.O (Ix r → M.L.O) :=
  relG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')

abbrev DG (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) : Type :=
  DDg M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')

def cOf (m m' : Fin (r + 1) → M.R) : Ix r → M.L.O
  | Sum.inl a => ⟨g.e.symm ((trO hs (m a) : F), (trO hs (m' a) : F)),
      mem_O_of_comp g _ (by simpa using (trO hs (m a)).2) (by simpa using (trO hs (m' a)).2)⟩
  | Sum.inr a => ⟨g.e.symm ((g.e (m a : E)).1, (g.e (m' a : E)).1),
      mem_O_of_comp g _ (by simpa using (comp_of_mem_R hs (m a).2).1)
        (by simpa using (comp_of_mem_R hs (m' a).2).1)⟩

theorem mOf1_cOf (m m' : Fin (r + 1) → M.R) : mOf1 hs (cOf hs m m') = m := by
  funext a; apply Subtype.ext; apply g.e.injective
  rw [embedding_firstCoefficient]
  simp only [cOf, AlgEquiv.apply_symm_apply]
  refine Prod.ext rfl ?_
  simp only [trO_coe]
  field_simp [q_ne g]
  ring

theorem mOf2_cOf (m m' : Fin (r + 1) → M.R) : mOf2 hs (cOf hs m m') = m' := by
  funext a; apply Subtype.ext; apply g.e.injective
  rw [embedding_secondCoefficient]
  simp only [cOf, AlgEquiv.apply_symm_apply]
  refine Prod.ext rfl ?_
  simp only [trO_coe]
  field_simp [q_ne g]
  ring

variable {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {T T' : F} {TT : M.R} {Z Zσ : M.Mat (r + 1)}
variable (hTT : g.e (TT : E) = (T, T')) (hZ : Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
  (hZσ : Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T')

include hTT hZ hZσ in
theorem rel_iff (Y : Ix r → M.L.O) :
    Y ∈ RelG g Zh T T' ↔ cmp1 hs Y ∈ LL hs Z TT ∧ cmp2 hs Y ∈ LL hs Zσ TT := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨AddMonoidHom.mem_range.2 ⟨_, (firstComponent_gram_rows hs hTT hZ c Y hc).symm⟩,
      AddMonoidHom.mem_range.2 ⟨_, (secondComponent_gram_rows hs hTT hZσ c Y hc).symm⟩⟩
  · rintro ⟨hm, hm'⟩
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 hm
    obtain ⟨m', hm'⟩ := AddMonoidHom.mem_range.1 hm'
    have hq := q_ne g
    have hmc : llMap hs Z TT (mOf1 hs (cOf hs m m')) = cmp1 hs Y := by rw [mOf1_cOf]; exact hm
    have hmc' : llMap hs Zσ TT (mOf2 hs (cOf hs m m')) = cmp2 hs Y := by rw [mOf2_cOf]; exact hm'
    refine ⟨cOf hs m m', fun j => ?_⟩
    have h1 : ∀ b, g.e ((cmp1 hs Y b : M.R) : E) = ((g.e (∑ i, (cOf hs m m' i : E) * GG (g := g) Zh T T' i (Sum.inl b))).1, (g.e (∑ i, (cOf hs m m' i : E) * GG (g := g) Zh T T' i (Sum.inl b))).1 + (g.q : F) * (g.e (∑ i, (cOf hs m m' i : E) * GG (g := g) Zh T T' i (Sum.inr b))).1) :=
      fun b => by rw [← hmc]; exact (gram_rows_firstEmbedding hs hTT hZ (cOf hs m m') b).symm
    have h2 : ∀ b, g.e ((cmp2 hs Y b : M.R) : E) = ((g.e (∑ i, (cOf hs m m' i : E) * GG (g := g) Zh T T' i (Sum.inl b))).2, (g.e (∑ i, (cOf hs m m' i : E) * GG (g := g) Zh T T' i (Sum.inl b))).2 + (g.q : F) * (g.e (∑ i, (cOf hs m m' i : E) * GG (g := g) Zh T T' i (Sum.inr b))).2) :=
      fun b => by rw [← hmc']; exact (gram_rows_secondEmbedding hs hTT hZσ (cOf hs m m') b).symm
    apply g.e.injective
    rcases j with b | b
    · have a1 := congrArg Prod.fst (h1 b)
      have a2 := congrArg Prod.fst (h2 b)
      rw [embedding_firstComponent] at a1; rw [embedding_secondComponent] at a2
      exact Prod.ext a1 a2
    · have a1 := congrArg Prod.fst (h1 b)
      have a2 := congrArg Prod.fst (h2 b)
      have b1 := congrArg Prod.snd (h1 b)
      have b2 := congrArg Prod.snd (h2 b)
      rw [embedding_firstComponent] at a1 b1; rw [embedding_secondComponent] at a2 b2
      simp only at a1 a2 b1 b2
      refine Prod.ext ?_ ?_
      · apply mul_left_cancel₀ hq; linear_combination b1 - a1
      · apply mul_left_cancel₀ hq; linear_combination b2 - a2

theorem iotaOne_zero : iota1 hs (0 : Fin (r + 1) → M.R) = 0 := by
  have h := iotaOne_add hs (0 : Fin (r + 1) → M.R) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem iotaTwo_zero : iota2 hs (0 : Fin (r + 1) → M.R) = 0 := by
  have h := iotaTwo_add hs (0 : Fin (r + 1) → M.R) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

def iota1H : (Fin (r + 1) → M.R) →+ (Ix r → M.L.O) where
  toFun := iota1 hs
  map_zero' := iotaOne_zero hs
  map_add' := iotaOne_add hs

def iota2H : (Fin (r + 1) → M.R) →+ (Ix r → M.L.O) where
  toFun := iota2 hs
  map_zero' := iotaTwo_zero hs
  map_add' := iotaTwo_add hs

include hTT hZ hZσ in

def toP : DG g Zh T T' →+ DD1 hs Z TT × DD1 hs Zσ TT :=
  QuotientAddGroup.lift (RelG g Zh T T').toAddSubgroup
    (((QuotientAddGroup.mk' (LL hs Z TT)).comp (cmp1 hs)).prod ((QuotientAddGroup.mk' (LL hs Zσ TT)).comp (cmp2 hs)))
    (fun Y hY => by
      obtain ⟨h1, h2⟩ := (rel_iff hs hTT hZ hZσ Y).1 hY
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.prod_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        QuotientAddGroup.mk'_apply]
      exact Prod.ext ((QuotientAddGroup.eq_zero_iff _).2 h1) ((QuotientAddGroup.eq_zero_iff _).2 h2))

include hTT hZ hZσ in

def ofP : DD1 hs Z TT × DD1 hs Zσ TT →+ DG g Zh T T' :=
  AddMonoidHom.coprod
    (QuotientAddGroup.lift (LL hs Z TT) ((RelG g Zh T T').mkQ.toAddMonoidHom.comp (iota1H hs))
      (fun l hl => by
        show Submodule.Quotient.mk (iota1 hs l) = (0 : DG g Zh T T')
        refine (Submodule.Quotient.mk_eq_zero _).2 ((rel_iff hs hTT hZ hZσ _).2 ⟨?_, ?_⟩)
        · rw [firstComponent_iotaOne]; exact hl
        · rw [secondComponent_iotaOne]; exact zero_mem _))
    (QuotientAddGroup.lift (LL hs Zσ TT) ((RelG g Zh T T').mkQ.toAddMonoidHom.comp (iota2H hs))
      (fun l hl => by
        show Submodule.Quotient.mk (iota2 hs l) = (0 : DG g Zh T T')
        refine (Submodule.Quotient.mk_eq_zero _).2 ((rel_iff hs hTT hZ hZσ _).2 ⟨?_, ?_⟩)
        · rw [firstComponent_iotaTwo]; exact zero_mem _
        · rw [secondComponent_iotaTwo]; exact hl))

theorem toP_mk (Y : Ix r → M.L.O) :
    toP hs hTT hZ hZσ (Submodule.Quotient.mk Y : DG g Zh T T') =
      ((QuotientAddGroup.mk (cmp1 hs Y) : DD1 hs Z TT), (QuotientAddGroup.mk (cmp2 hs Y) : DD1 hs Zσ TT)) :=
  rfl

theorem ofP_mk (l w : Fin (r + 1) → M.R) :
    ofP hs hTT hZ hZσ ((QuotientAddGroup.mk l : DD1 hs Z TT), (QuotientAddGroup.mk w : DD1 hs Zσ TT)) =
      (Submodule.Quotient.mk (iota1 hs l + iota2 hs w) : DG g Zh T T') :=
  rfl

def splitQ : DG g Zh T T' ≃+ DD1 hs Z TT × DD1 hs Zσ TT where
  toFun := toP hs hTT hZ hZσ
  invFun := ofP hs hTT hZ hZσ
  left_inv x := by
    obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [toP_mk, ofP_mk, iota_cmp]
  right_inv p := by
    obtain ⟨x, y⟩ := p
    obtain ⟨l, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [ofP_mk, toP_mk, map_add, map_add, firstComponent_iotaOne, secondComponent_iotaOne, firstComponent_iotaTwo, secondComponent_iotaTwo, add_zero, zero_add]
  map_add' := (toP hs hTT hZ hZσ).map_add

theorem splitQ_mk (Y : Ix r → M.L.O) :
    splitQ hs hTT hZ hZσ (Submodule.Quotient.mk Y : DG g Zh T T') =
      ((QuotientAddGroup.mk (cmp1 hs Y) : DD1 hs Z TT), (QuotientAddGroup.mk (cmp2 hs Y) : DD1 hs Zσ TT)) :=
  rfl

end Formalism.L2.SG.LocalCountModules.AlgGSplit
