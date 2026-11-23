import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.SecondProjConjEqFirstProj

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section DuU2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem firstProj_conj_apply (x : E) : ph1 g (M.L.cj x) = ph2 g x := firstProj_conj_eq_secondProj x

theorem duU_core (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (hG : GHyp M g T T' TT Zh Z Zσ)
    (hdet : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (w w' : Fin (r + 1) → M.R)
    (h : ∀ l : Fin (r + 1) → M.R,
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs l) (iota2 hs w) -
        formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
          (iota1 hs l) (iota2 hs w') ∈ M.L.O) :
    w - w' ∈ LL hs Zσ TT := by
  obtain ⟨G, hGd⟩ : ∃ G, gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') = G := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Ix r → E, (fun j => (M.L.cj : E →+* E) ((iota2 hs w j : M.L.O) : E) -
      (M.L.cj : E →+* E) ((iota2 hs w' j : M.L.O) : E)) = v := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Ix r → E, Matrix.mulVec G⁻¹ v = c := ⟨_, rfl⟩
  have hsum : ∀ l, ∑ i, ((iota1 hs l i : M.L.O) : E) * c i ∈ M.L.O := by
    intro l
    have := h l
    rw [duU_formG_sub, hGd, hv, hc] at this
    exact this
  have hint := duU_c_int hs c hsum
  have hGc : Matrix.mulVec G c = v := by
    rw [← hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hGd ▸ hdet), Matrix.one_mulVec]
  have hrow : ∀ i, ∑ j, ph1 g (G i j) * ph1 g (c j) = ph1 g (v i) := by
    intro i
    have := congrArg (ph1 g) (congrFun hGc i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at this
    exact this
  have hG11 : ∀ a b, ph1 g (G (Sum.inl a) (Sum.inl b)) = cor r a b (-T) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap]
  have hG12 : ∀ a b, ph1 g (G (Sum.inl a) (Sum.inr b)) = (g.q : F)⁻¹ * (ph2 g (Zh a b) + cor r a b T) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap, firstProj_conj_apply]
  have hG21 : ∀ a b, ph1 g (G (Sum.inr a) (Sum.inl b)) = (g.q : F)⁻¹ * (ph1 g (Zh b a) + cor r a b T) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap]
  have hG22 : ∀ a b, ph1 g (G (Sum.inr a) (Sum.inr b)) =
      (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(ph1 g (Zh b a)) - ph2 g (Zh a b) - cor r a b (T + T')) := by
    intro a b; rw [← hGd]; simp [gramG, firstProj_corner, firstProj_algebraMap, firstProj_conj_apply]
  have hv1 : ∀ a, ph1 g (v (Sum.inl a)) = ph1 g (((w - w') a : M.R) : E) := by
    intro a; rw [← hv]; simp only [map_sub, firstProj_conj_iotaTwo, firstProj_iotaOne_inl, Pi.sub_apply]; push_cast
    rw [map_sub]
  have hv2 : ∀ a, ph1 g (v (Sum.inr a)) =
      (ph2 g (((w - w') a : M.R) : E) - ph1 g (((w - w') a : M.R) : E)) / (g.q : F) := by
    intro a; rw [← hv]; simp only [map_sub, firstProj_conj_iotaTwo, firstProj_iotaOne_inr, Pi.sub_apply]; push_cast
    simp only [map_sub]; ring
  have E1 : ∀ a, ∑ b, cor r a b (-T) * ph1 g (c (Sum.inl b)) +
      ∑ b, (g.q : F)⁻¹ * (ph2 g (Zh a b) + cor r a b T) * ph1 g (c (Sum.inr b)) =
        ph1 g (((w - w') a : M.R) : E) := by
    intro a; rw [← hv1, ← hrow, Fintype.sum_sum_type]; simp only [hG11, hG12]
  have E2 : ∀ a, ∑ b, (g.q : F)⁻¹ * (ph1 g (Zh b a) + cor r a b T) * ph1 g (c (Sum.inl b)) +
      ∑ b, (g.q : F)⁻¹ * (g.q : F)⁻¹ * (-(ph1 g (Zh b a)) - ph2 g (Zh a b) - cor r a b (T + T')) *
        ph1 g (c (Sum.inr b)) =
        (ph2 g (((w - w') a : M.R) : E) - ph1 g (((w - w') a : M.R) : E)) / (g.q : F) := by
    intro a; rw [← hv2, ← hrow, Fintype.sum_sum_type]; simp only [hG21, hG22]
  have hc1 : ∀ b, ph1 g (c (Sum.inl b)) ∈ 𝒪[F] := fun b => hint (Sum.inl b)
  have hc2 : ∀ b, ph1 g (c (Sum.inr b)) ∈ 𝒪[F] := fun b => hint (Sum.inr b)
  let m : Fin (r + 1) → M.R := fun b =>
    ⟨g.e.symm (ph1 g (c (Sum.inr b)), ph1 g (c (Sum.inr b)) - (g.q : F) * ph1 g (c (Sum.inl b))),
      mem_R_of hs _ ⟨_, hc2 b⟩ ⟨_, sub_mem (hc2 b) (mul_mem g.q.2 (hc1 b))⟩ ⟨_, hc1 b⟩ (by simp)
        (by show ph1 g (c (Sum.inr b)) - (ph1 g (c (Sum.inr b)) - (g.q : F) * ph1 g (c (Sum.inl b))) =
              (g.q : F) * ph1 g (c (Sum.inl b)); ring)⟩
  have hm1 : ∀ b, ph1 g ((m b : M.R) : E) = ph1 g (c (Sum.inr b)) := by intro b; simp [m, firstProj_apply]
  have hm2 : ∀ b, ph2 g ((m b : M.R) : E) = ph1 g (c (Sum.inr b)) - (g.q : F) * ph1 g (c (Sum.inl b)) := by
    intro b; simp [m, secondProj_apply]
  have htr : ((trO hs (m (Fin.last r)) : 𝒪[F]) : F) = ph1 g (c (Sum.inl (Fin.last r))) := by
    rw [trO_coe, ← firstProj_apply, ← secondProj_apply, hm1, hm2, div_eq_iff (q_ne g)]; ring
  have hZσ : ∀ a b, ((Zσ.Z a b : M.R) : E) = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' a b := by
    intro a b; have := congrFun (congrFun hG.2.2.2.2.1 a) b; simpa using this
  have hTT1 : ph1 g (TT : E) = T := by rw [firstProj_apply, hG.2.2.1]
  have hTT2 : ph2 g (TT : E) = T' := by rw [secondProj_apply, hG.2.2.1]
  have hcoe : ∀ a, ((llMap hs Zσ TT m a : M.R) : E) =
      ∑ b, ((Zσ.Z a b : M.R) : E) * ((m b : M.R) : E) -
        (TT : E) * algebraMap F E (ph1 g (c (Sum.inl (Fin.last r)))) * (((eV (M := M) r) a : M.R) : E) := by
    intro a
    simp only [llMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct]
    push_cast
    rw [dgR_coe, htr]
  have heV1 : ∀ a, ph1 g (((eV (M := M) r) a : M.R) : E) = if a = Fin.last r then 1 else 0 := by
    intro a; by_cases ha : a = Fin.last r
    · subst ha; simp [eV]
    · simp [eV, ha]
  have heV2 : ∀ a, ph2 g (((eV (M := M) r) a : M.R) : E) = if a = Fin.last r then 1 else 0 := by
    intro a; by_cases ha : a = Fin.last r
    · subst ha; simp [eV]
    · simp [eV, ha]
  refine AddMonoidHom.mem_range.2 ⟨m, ?_⟩
  funext a
  apply Subtype.ext
  apply (eq_iff_ph (g := g) _ _).2
  constructor
  · rw [hcoe a]
    simp only [map_sub, map_sum, map_mul, hZσ, firstProj_zzPlus_conj hs, hm1, hTT1, firstProj_algebraMap, heV1]
    rw [← E1 a]
    have hk : T * ph1 g (c (Sum.inl (Fin.last r))) * (if a = Fin.last r then (1 : F) else 0) =
        ∑ b, cor r a b T * ph1 g (c (Sum.inl b)) := by
      rw [duU_sum_cor]; split_ifs <;> simp
    rw [hk]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold cor; split_ifs <;> ring
  · rw [hcoe a]
    simp only [map_sub, map_sum, map_mul, hZσ, secondProj_zzPlus_conj hs, hm2, hTT2, ph2_algebraMap_eq, heV2]
    have hD2 : ph2 g (((w - w') a : M.R) : E) = ph1 g (((w - w') a : M.R) : E) +
        (g.q : F) * ((ph2 g (((w - w') a : M.R) : E) - ph1 g (((w - w') a : M.R) : E)) / (g.q : F)) := by
      rw [mul_div_cancel₀ _ (q_ne g)]; ring
    rw [hD2, ← E2 a, ← E1 a]
    have hk : T' * ph1 g (c (Sum.inl (Fin.last r))) * (if a = Fin.last r then (1 : F) else 0) =
        ∑ b, cor r a b T' * ph1 g (c (Sum.inl b)) := by
      rw [duU_sum_cor]; split_ifs <;> simp
    rw [hk]
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hq := q_ne g
    unfold cor; split_ifs <;> field_simp <;> ring

def UnitGramG : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g → ∀ (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh Z Zσ →
    IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).det

theorem stepDuU_of (hU : UnitGramG) : StepDuU := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh₁ Zh₂ Z₁ Z₂ Zσ₁ Zσ₂ h₁ h₂ _ θ₁ θ₂ θ₂' hB hB'
  have hdet := hU F E M g hs r T T' TT Zh₂ Z₂ Zσ₂ h₂
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H w =>
    obtain ⟨w₂, hw₂⟩ := QuotientAddGroup.mk_surjective (θ₂ (mk1 hs Zσ₁ TT w))
    obtain ⟨w₂', hw₂'⟩ := QuotientAddGroup.mk_surjective (θ₂' (mk1 hs Zσ₁ TT w))
    have key : w₂ - w₂' ∈ LL hs Zσ₂ TT := by
      refine duU_core hs h₂ hdet w₂ w₂' fun l₂ => ?_
      obtain ⟨l, hl⟩ := QuotientAddGroup.mk_surjective (θ₁.symm (mk1 hs Z₂ TT l₂))
      have hl' : θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ := by
        show θ₁ (QuotientAddGroup.mk l) = _
        rw [hl]; simp
      have e1 := hB l l₂ w w₂ hl' hw₂.symm
      have e2 := hB' l l₂ w w₂' hl' hw₂'.symm
      convert sub_mem e1 e2 using 1
      ring
    show θ₂ (QuotientAddGroup.mk w) = θ₂' (QuotientAddGroup.mk w)
    rw [← hw₂, ← hw₂']
    exact (QuotientAddGroup.eq_iff_sub_mem).2 key

end DuU2

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
