import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.GammaOneNonempty

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

theorem firstProj_firstComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) : p1 g (cmp1 hs Y b : E) = p1 g (Y (Sum.inl b)) := by
  simp [p1, cmp1, e_rOf, c1]
theorem secondProj_firstComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) :
    p2 g (cmp1 hs Y b : E) = p1 g (Y (Sum.inl b)) + (g.q : F) * p1 g (Y (Sum.inr b)) := by
  simp [p1, p2, cmp1, e_rOf, c1]
theorem firstProj_secondComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) : p1 g (cmp2 hs Y b : E) = p2 g (Y (Sum.inl b)) := by
  simp [p1, p2, cmp2, e_rOf, c2]
theorem secondProj_secondComponent (Y : Ix r → M.L.O) (b : Fin (r + 1)) :
    p2 g (cmp2 hs Y b : E) = p2 g (Y (Sum.inl b)) + (g.q : F) * p2 g (Y (Sum.inr b)) := by
  simp [p1, p2, cmp2, e_rOf, c2]
theorem firstProj_uniformizer_mul (x : M.R) : p1 g ((q2 hs * x : M.R) : E) = 0 := by
  simp [p1, q2]
theorem secondProj_uniformizer_mul (x : M.R) : p2 g ((q2 hs * x : M.R) : E) = (g.q : F) * p2 g (x : E) := by
  simp [p2, q2]

theorem dl_cast (a : Fin r) : dl (F := F) r a.castSucc = 0 := by
  unfold dl
  rw [if_neg (Fin.castSucc_lt_last a).ne]

theorem gamSup_holds : GamSupP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ h
  rintro _ ⟨⟨a, b⟩, ⟨⟨l, η, rfl⟩, ⟨l', η', rfl⟩⟩, rfl⟩
  have hZh : IsUnit Zh.det := h.2.2.2.2.2.1
  set u : Fin (r + 1) → M.R := η • (eV r : Fin (r + 1) → M.R) + q2 hs • l
  set u' : Fin (r + 1) → M.R := η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l'
  set Y : Ix r → M.L.O := iota1 hs u + iota2 hs u'
  set Y'' : Ix r → M.L.O := iota1 hs l + iota2 hs l'
  set Y' : Ix r → M.L.O := Y - dgO g g.q • Y''
  have h1 : cmp1 hs Y = u := by simp only [Y, map_add, firstComponent_iotaOne, firstComponent_iotaTwo, add_zero]
  have h2 : cmp2 hs Y = u' := by simp only [Y, map_add, secondComponent_iotaOne, secondComponent_iotaTwo, zero_add]
  have h3 : cmp1 hs Y'' = l := by simp only [Y'', map_add, firstComponent_iotaOne, firstComponent_iotaTwo, add_zero]
  have h4 : cmp2 hs Y'' = l' := by simp only [Y'', map_add, secondComponent_iotaOne, secondComponent_iotaTwo, zero_add]
  have hY : ∀ i, (Y i : E) - Y' i = algebraMap F E (g.q : F) * Y'' i := fun i => by
    simp only [Y', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dgO, AddSubgroupClass.coe_sub,
      MulMemClass.coe_mul]
    ring
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (hY i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (hY i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  have fY := components_of_firstComponent_eq hs h1
  have gY := components_of_secondComponent_eq hs h2
  have fZ := components_of_firstComponent_eq hs h3
  have gZ := components_of_secondComponent_eq hs h4
  simp only [u, u', firstProj_unit_vector_eq hs, secondProj_unit_vector_eq hs] at fY gY
  refine ⟨Y, Y', Y'', fun a => ?_, fun a => ?_, hY, ?_⟩
  · apply Subtype.ext
    apply E_ext (g := g)
    · rw [(fY _).1, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
    · rw [(gY _).1, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
  · apply E_ext (g := g)
    · rw [map_add, map_mul, firstProj_algebraMap_split, hW1, hW1, map_zero]
      linear_combination (fY a.castSucc).2 - (g.q : F) * (fZ a.castSucc).2 + p2 g η * dl_cast (F := F) a
    · rw [map_add, map_mul, secondProj_algebraMap_split, hW2, hW2, map_zero]
      linear_combination (gY a.castSucc).2 - (g.q : F) * (gZ a.castSucc).2 + p2 g η' * dl_cast (F := F) a
  · exact Prod.ext rfl (Prod.ext rfl (vals hs hZh T T' h1 h2 h3 h4 hY).symm)

theorem gamSub_holds : GamSubP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ h
  rintro _ ⟨Y, Y', Y'', c1, c2, c3, rfl⟩
  have hZh : IsUnit Zh.det := h.2.2.2.2.2.1
  set l := cmp1 hs Y''
  set l' := cmp2 hs Y''
  set η : M.R := cmp1 hs Y (Fin.last r) - q2 hs * l (Fin.last r)
  set η' : M.R := cmp2 hs Y (Fin.last r) - q2 hs * l' (Fin.last r)
  have hW1 : ∀ i, p1 g (Y' i) = p1 g (Y i) - (g.q : F) * p1 g (Y'' i) := fun i => by
    have := congrArg (p1 g) (c3 i); rw [map_sub, map_mul, firstProj_algebraMap_split] at this; linear_combination -this
  have hW2 : ∀ i, p2 g (Y' i) = p2 g (Y i) - (g.q : F) * p2 g (Y'' i) := fun i => by
    have := congrArg (p2 g) (c3 i); rw [map_sub, map_mul, secondProj_algebraMap_split] at this; linear_combination -this
  have h1 : cmp1 hs Y = η • (eV r : Fin (r + 1) → M.R) + q2 hs • l := by
    funext b
    apply R_ext (g := g)
    · rw [firstProj_unit_vector_eq hs, firstProj_firstComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η, AddSubgroupClass.coe_sub, map_sub, firstProj_uniformizer_mul, firstProj_firstComponent, dl_last, mul_one, sub_zero]
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        rw [c1 a, dl_cast, mul_zero, ZeroMemClass.coe_zero, map_zero]
    · rw [secondProj_unit_vector_eq hs, secondProj_firstComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η, l, AddSubgroupClass.coe_sub, map_sub, secondProj_uniformizer_mul, secondProj_firstComponent, dl_last, mul_one]
        ring
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg (p1 g) (c2 a)
        rw [map_add, map_mul, firstProj_algebraMap_split, hW1, hW1, map_zero] at e
        simp only [l, secondProj_firstComponent, dl_cast, mul_zero, zero_add]
        linear_combination e
  have h2 : cmp2 hs Y = η' • (eV r : Fin (r + 1) → M.R) + q2 hs • l' := by
    funext b
    apply R_ext (g := g)
    · rw [firstProj_unit_vector_eq hs, firstProj_secondComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η', AddSubgroupClass.coe_sub, map_sub, firstProj_uniformizer_mul, firstProj_secondComponent, dl_last, mul_one, sub_zero]
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg Prod.snd (congrArg g.e (congrArg Subtype.val (c1 a)))
        rw [dl_cast, mul_zero]
        simpa [adele_ext_components] using e
    · rw [secondProj_unit_vector_eq hs, secondProj_secondComponent]
      by_cases hb : b = Fin.last r
      · subst hb
        simp only [η', l', AddSubgroupClass.coe_sub, map_sub, secondProj_uniformizer_mul, secondProj_secondComponent, dl_last, mul_one]
        ring
      · obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hb
        have e := congrArg (p2 g) (c2 a)
        rw [map_add, map_mul, secondProj_algebraMap_split, hW2, hW2, map_zero] at e
        simp only [l', secondProj_secondComponent, dl_cast, mul_zero, zero_add]
        linear_combination e
  refine ⟨(((QuotientAddGroup.mk (cmp1 hs Y) : DD1 hs Z TT), (QuotientAddGroup.mk l : DD1 hs Z TT), η,
      laG (ZZm g Zh T T') l), ((QuotientAddGroup.mk (cmp2 hs Y) : DD1 hs Zσ TT),
      (QuotientAddGroup.mk l' : DD1 hs Zσ TT), η', laG (ZZm g (Zh.map M.L.cj) T T') l')),
    ⟨⟨l, η, by rw [h1]⟩, ⟨l', η', by rw [h2]⟩⟩, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact (splitH hs h).symm_apply_apply (Submodule.Quotient.mk Y)
  · exact (splitH hs h).symm_apply_apply (Submodule.Quotient.mk Y'')
  · exact (vals hs hZh T T' h1 h2 rfl rfl c3).symm

end Formalism.L2.SG.LocalCountModules.AlgGSplit
