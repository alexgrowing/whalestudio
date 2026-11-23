import Formalism.AdmissibleDesigns.BlockTwistedCyclotomic
import ReciprocityTheory.GaloisValuations.ArithOfA

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN Pointwise

section Coc

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] (ρ : Representation R G M)

theorem coc_one (c : coZ1s ρ) : (c : G → M) 1 = 0 := by
  have h := c.2 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at h
  have h' : (c : G → M) 1 + (c : G → M) 1 = (c : G → M) 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

theorem coc_conj (c : coZ1s ρ) (σ n : G) (hn : ∀ m, ρ n m = m) :
    (c : G → M) (σ * n * σ⁻¹) = ρ σ ((c : G → M) n) := by
  have h1 := c.2 (σ * n) σ⁻¹
  have h2 := c.2 σ n
  have h3 := c.2 σ σ⁻¹
  rw [mul_inv_cancel, coc_one] at h3
  rw [h1, h2, map_mul, Module.End.mul_apply, hn]
  have : (c : G → M) σ + ρ σ ((c : G → M) σ⁻¹) = 0 := h3.symm
  rw [← sub_eq_zero]
  have e : (c : G → M) σ + ρ σ ((c : G → M) n) + ρ σ ((c : G → M) σ⁻¹) - ρ σ ((c : G → M) n) =
      (c : G → M) σ + ρ σ ((c : G → M) σ⁻¹) := by abel
  rw [e, this]

theorem coc_zero_of_unr (c : coZ1s ρ) (J : Subgroup G) (hJ : ∀ g ∈ J, ∀ m, ρ g m = m)
    (h : resH1 ρ J (Submodule.Quotient.mk c) = 0) : ∀ g ∈ J, (c : G → M) g = 0 := by
  intro g hg
  have h' : restrictCocycles1 ρ J c ∈ (coB1 (resRep ρ J)).comap (coZ1s (resRep ρ J)).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 h
  obtain ⟨m, hm⟩ := h'
  have h2 : ρ g m - m = (c : G → M) g := congrFun hm ⟨g, hg⟩
  rw [← h2, hJ g hg, sub_self]

end Coc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (e : ℕ)

abbrev SS : Set (HeightOneSpectrum (𝓞 D.host.E)) := ((D.nd.ldat (D.nd.l i)).S : Set (HeightOneSpectrum (𝓞 D.host.E)))

theorem qzE_eq (g : GE D.nd) (m : Formalism.GaloisCohomology.QZ (D.nd.l i)) :
    qzE i e g m = Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ) (toGS D.nd.Om (SS i) g) m := by
  have h := congrArg (fun f => f g) (D.nd.ldat (D.nd.l i)).hchi
  simp only [MonoidHom.comp_apply] at h
  simp only [qzE, Formalism.GaloisCohomology.qzTw, Formalism.GaloisCohomology.scalRep_apply, MonoidHom.zpow_apply, cycE, h]

theorem qzE_NS {n : GE D.nd} (hn : n ∈ NS D.nd.Om (SS i)) (m : Formalism.GaloisCohomology.QZ (D.nd.l i)) : qzE i e n m = m := by
  have h1 : toGS D.nd.Om (SS i) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
  rw [qzE_eq, h1, map_one, Module.End.one_apply]

theorem coc_NS (c : coZ1s (qzE i e)) (hc : IsLocallyConstant (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)))
    (h : ∀ v ∉ SS i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) g = 0) :
    ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0 := by
  have hNSn : (NS D.nd.Om (SS i)).Normal := inferInstance
  let K : Subgroup (GE D.nd) :=
    { carrier := {n | n ∈ NS D.nd.Om (SS i) ∧ (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0}
      one_mem' := ⟨(NS D.nd.Om (SS i)).one_mem, coc_one (qzE i e) c⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(NS D.nd.Om (SS i)).mul_mem ha hb, ?_⟩
        rw [c.2 a b, ha', hb', map_zero, add_zero]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(NS D.nd.Om (SS i)).inv_mem ha, ?_⟩
        have h3 := c.2 a a⁻¹
        rw [mul_inv_cancel, coc_one (qzE i e) c, ha', zero_add, qzE_NS i e ha] at h3
        exact h3.symm }
  have hK : K.Normal := ⟨fun n hn σ => ⟨hNSn.conj_mem n hn.1 σ, by
    rw [coc_conj (qzE i e) c σ n (qzE_NS i e hn.1), hn.2, map_zero]⟩⟩
  have hgen : (⋃ v ∈ (SS i)ᶜ, ⋃ A ∈ {A : ValuationSubring D.nd.Om | IsPlaceOver A v}, Inertia (F := D.host.E) A) ⊆
      (K : Set (GE D.nd)) := by
    intro σ hσ
    have hNS : σ ∈ NS D.nd.Om (SS i) := Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)
    refine ⟨hNS, ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 v) hA
    have h1 : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ Ine (F := D.host.E) (τ⁻¹ • A) := conj_mem_Ine_smul (γ := τ⁻¹) hσA
    rw [← hτ, inv_smul_smul, inv_inv] at h1
    have hn : τ⁻¹ * σ * τ ∈ NS D.nd.Om (SS i) := by
      have := hNSn.conj_mem σ hNS τ⁻¹
      simpa using this
    have e1 : σ = τ * (τ⁻¹ * σ * τ) * τ⁻¹ := by group
    rw [e1, coc_conj (qzE i e) c τ _ (qzE_NS i e hn), h v hv _ h1, map_zero]
  have hcl : IsClosed (K : Set (GE D.nd)) := by
    have e2 : (K : Set (GE D.nd)) = (NS D.nd.Om (SS i) : Set (GE D.nd)) ∩ (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) ⁻¹' {0} := rfl
    rw [e2]
    exact (Subgroup.isClosed_topologicalClosure _).inter (hc.isClosed_fiber 0)
  have hle : NS D.nd.Om (SS i) ≤ K :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hgen) hcl
  exact fun n hn => (hle hn).2

end Rec

section Coc2

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] (ρ : Representation R G M)

theorem coc_conj_cob (c : coZ1s ρ) (τ k : G) (m0 : M) (hk : (c : G → M) k = ρ k m0 - m0) :
    (c : G → M) (τ * k * τ⁻¹) =
      ρ (τ * k * τ⁻¹) (ρ τ m0 - (c : G → M) τ) - (ρ τ m0 - (c : G → M) τ) := by
  have h1 := c.2 (τ * k) τ⁻¹
  have h2 := c.2 τ k
  have h3 := c.2 τ⁻¹ τ
  rw [inv_mul_cancel, coc_one ρ c] at h3
  have h4 : (c : G → M) τ⁻¹ = -ρ τ⁻¹ ((c : G → M) τ) := by
    rw [eq_neg_iff_add_eq_zero]; exact h3.symm
  rw [h1, h2, hk, h4]
  have h5 : ρ τ⁻¹ (ρ τ m0) = m0 := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [map_mul, Module.End.mul_apply, map_sub, map_neg, h5]
  abel

end Coc2

section Desc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (e : ℕ)

theorem selZ_mem {x : H1z (qzE i e)} (hx : x ∈ selZ i dc e) :
    x ∈ lcH1 (qzE i e) ∧ (∀ v, x ∈ unrH1 (qzE i e) (Io i v)) ∧ (∀ v, x ∈ unrH1 (qzE i e) (IS i v)) ∧
      ∀ w ∈ Pall i dc, NG.resH1 (qzE i e) (decs D.host.E (Aw i dc) w) x ∈
        Fsha (qzE i e) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc) w := by
  simp only [selZ, selRep2, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hx
  exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2, hx.2⟩

theorem mem_SS_iff (v : HeightOneSpectrum (𝓞 D.host.E)) :
    v ∈ SS i ↔ v ∈ placesOver D.host.E (D.nd.l i) := by
  show v ∈ ((D.nd.ldat (D.nd.l i)).S : Set (HeightOneSpectrum (𝓞 D.host.E))) ↔ _
  rw [(D.nd.ldat (D.nd.l i)).hS]
  rfl

theorem ine_le_NS {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∉ SS i) :
    Ine (F := D.host.E) (D.nd.plOm.1 v) ≤ NS D.nd.Om (SS i) := fun g hg =>
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (by
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨v, hv, _, D.nd.plOm.2 v, hg⟩))

theorem coc_ine (c : coZ1s (qzE i e)) (hx : Submodule.Quotient.mk c ∈ selZ i dc e)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∉ SS i) :
    ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) g = 0 := by
  obtain ⟨-, hIo, hIS, hP⟩ := selZ_mem i dc e hx
  have htriv : ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ m, qzE i e g m = m :=
    fun g hg => qzE_NS i e (ine_le_NS i hv hg)
  by_cases hS : v ∈ D.nd.S i
  · exact coc_zero_of_unr _ c _ htriv (hIS ⟨v, hS⟩)
  by_cases hQ : v ∈ D.nd.Q i
  · have hvP : v ∈ plSet i dc := q_mem_plSet i dc hQ
    have hAw : Aw i dc (idx i dc v) = D.nd.plOm.1 v := by unfold Aw; rw [plOf_idx i dc hvP]
    have hwq : idx i dc v ∈ qsN i dc := Finset.mem_image_of_mem _ hQ
    have hwP : idx i dc v ∈ Pall i dc := Finset.mem_union_left _ (Finset.mem_union_right _ hwq)
    have h1 := hP _ hwP
    unfold Fsha at h1
    rw [if_pos hwq] at h1
    intro g hg
    have hgD : g ∈ decs D.host.E (Aw i dc) (idx i dc v) := by
      show g ∈ (Aw i dc (idx i dc v)).decompositionSubgroup D.host.E
      rw [hAw]; exact Ine_le_Dec _ hg
    have hgI : (⟨g, hgD⟩ : decs D.host.E (Aw i dc) (idx i dc v)) ∈ I i dc (idx i dc v) := by
      show (⟨g, hgD⟩ : decs D.host.E (Aw i dc) (idx i dc v)) ∈
        (Ine (F := D.host.E) (Aw i dc (idx i dc v))).subgroupOf (decs D.host.E (Aw i dc) (idx i dc v))
      rw [Subgroup.mem_subgroupOf]
      show g ∈ Ine (F := D.host.E) (Aw i dc (idx i dc v))
      rw [hAw]; exact hg
    refine coc_zero_of_unr (resRep (qzE i e) (decs D.host.E (Aw i dc) (idx i dc v)))
      (NG.restrictCocycles1 _ _ c) (I i dc (idx i dc v)) ?_ h1 ⟨g, hgD⟩ hgI
    intro g' hg' m
    have hg'' : (g' : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := by
      have := (Subgroup.mem_subgroupOf).1 hg'
      rw [hAw] at this
      exact this
    exact htriv _ hg'' m
  · have hl : v ∉ placesOver D.host.E (D.nd.l i) := fun h => hv ((mem_SS_iff i v).2 h)
    exact coc_zero_of_unr _ c _ htriv (hIo ⟨v, hl, hS, hQ⟩)

theorem coc_loc (c : coZ1s (qzE i e)) (hx : Submodule.Quotient.mk c ∈ selZ i dc e)
    (v : (D.nd.ldat (D.nd.l i)).S) :
    ∃ m, ∀ h ∈ Dec (F := D.host.E) ((D.nd.ldat (D.nd.l i)).A v),
      (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) h = qzE i e h m - m := by
  have hvA : v.1 ∈ placesOver D.host.E (D.nd.l i) := (mem_SS_iff i v.1).1 v.2
  have hrc := (dc.cover v.1).2 hvA
  have hvP : v.1 ∈ plSet i dc := by
    rcases hrc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have hnq : idx i dc v.1 ∉ qsN i dc := by
    intro h
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 h
    have hqv := idx_inj i dc (q_mem_plSet i dc hq) hvP hqe
    exact D.nd.SQ_l i q (Or.inr hq) (hqv ▸ hvA)
  have hwP : idx i dc v.1 ∈ Pall i dc := by
    rcases hrc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨v.1, h⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨-, -, -, hP⟩ := selZ_mem i dc e hx
  have h1 := hP _ hwP
  unfold Fsha at h1
  rw [if_neg hnq, Submodule.mem_bot] at h1
  obtain ⟨m0, hm0⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
  have hAw : Aw i dc (idx i dc v.1) = D.nd.plOm.1 v.1 := by unfold Aw; rw [plOf_idx i dc hvP]
  have hcob : ∀ k ∈ Dec (F := D.host.E) (D.nd.plOm.1 v.1),
      (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) k = qzE i e k m0 - m0 := by
    intro k hk
    have hkD : k ∈ decs D.host.E (Aw i dc) (idx i dc v.1) := by
      show k ∈ (Aw i dc (idx i dc v.1)).decompositionSubgroup D.host.E
      rw [hAw]; exact hk
    exact (congrFun hm0 ⟨k, hkD⟩).symm
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 v.1) ((D.nd.ldat (D.nd.l i)).hA v)
  refine ⟨qzE i e τ m0 - (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) τ, fun h hh => ?_⟩
  have hk : τ⁻¹ * h * τ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v.1) := by
    show (τ⁻¹ * h * τ) • D.nd.plOm.1 v.1 = D.nd.plOm.1 v.1
    have hh' : h • ((D.nd.ldat (D.nd.l i)).A v) = (D.nd.ldat (D.nd.l i)).A v := hh
    rw [mul_smul, mul_smul, hτ, hh', ← hτ, inv_smul_smul]
  have e1 : h = τ * (τ⁻¹ * h * τ) * τ⁻¹ := by group
  rw [e1, coc_conj_cob (qzE i e) c τ _ m0 (hcob _ hk)]

theorem coc_coset (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0) (a b : GE D.nd)
    (h : toGS D.nd.Om (SS i) a = toGS D.nd.Om (SS i) b) :
    (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) a = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) b := by
  have hab : a⁻¹ * b ∈ NS D.nd.Om (SS i) := QuotientGroup.eq.1 h
  calc (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) a
      = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) a + qzE i e a ((c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) (a⁻¹ * b)) := by
        rw [hN _ hab, map_zero, add_zero]
    _ = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) (a * (a⁻¹ * b)) := (c.2 _ _).symm
    _ = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) b := by rw [mul_inv_cancel_left]

theorem toGS_out (x : GS D.nd.Om (SS i)) : toGS D.nd.Om (SS i) x.out = x := QuotientGroup.out_eq' x

def descFun (c : coZ1s (qzE i e)) : GS D.nd.Om (SS i) → Formalism.GaloisCohomology.QZ (D.nd.l i) :=
  fun x => (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) x.out

theorem descFun_toGS (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0) (g : GE D.nd) :
    descFun i e c (toGS D.nd.Om (SS i) g) = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) g :=
  coc_coset i e c hN _ _ (toGS_out i _)

theorem descFun_lc (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0)
    (hc : IsLocallyConstant (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i))) : IsLocallyConstant (descFun i e c) := by
  intro U
  have hU : descFun i e c ⁻¹' U = (toGS D.nd.Om (SS i)) '' ((c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) ⁻¹' U) := by
    ext x
    constructor
    · intro hx
      exact ⟨x.out, hx, toGS_out i x⟩
    · rintro ⟨g, hg, rfl⟩
      show descFun i e c (toGS D.nd.Om (SS i) g) ∈ U
      rw [descFun_toGS i e c hN]
      exact hg
  rw [hU]
  exact QuotientGroup.isOpenMap_coe _ (hc U)

def descendLocallyConstantCocycle (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0)
    (hc : IsLocallyConstant (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i))) :
    Z1 (Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ)) :=
  ⟨descFun i e c, (descFun_lc i e c hN hc).continuous, fun x y => by
    have hxy : toGS D.nd.Om (SS i) (x.out * y.out) = x * y := by rw [map_mul, toGS_out, toGS_out]
    rw [← hxy, descFun_toGS i e c hN, c.2, qzE_eq, toGS_out]
    rfl⟩

def inflZ : Z1 (Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ)) →ₗ[ℤ_[D.nd.l i]] coZ1s (qzE i e) where
  toFun f := ⟨fun g => f.1 (toGS D.nd.Om (SS i) g), fun g h => by
    show f.1 (toGS D.nd.Om (SS i) (g * h)) = f.1 (toGS D.nd.Om (SS i) g) + qzE i e g (f.1 (toGS D.nd.Om (SS i) h))
    rw [map_mul, f.2.2, qzE_eq]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def infl : H1 (Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ)) →ₗ[ℤ_[D.nd.l i]] H1z (qzE i e) :=
  Submodule.mapQ _ _ (inflZ i e) (by
    intro f hf
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
    refine ⟨m, funext fun g => ?_⟩
    show qzE i e g m - m = f.1 (toGS D.nd.Om (SS i) g)
    rw [qzE_eq]
    exact (hm _).symm)

theorem selZ_le_map : selZ i dc e ≤ (Formalism.GaloisCohomology.Sha (D.nd.ldat (D.nd.l i)) (e : ℤ)).map (infl i e) := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (selZ_mem i dc e hx).1
  have hN := coc_NS i e c hc (fun v hv => coc_ine i dc e c hx v hv)
  refine ⟨Submodule.Quotient.mk (descendLocallyConstantCocycle i e c hN hc), ?_, ?_⟩
  · rw [Formalism.GaloisCohomology.Sha, Sha1, SetLike.mem_coe, Submodule.mem_iInf]
    intro v
    rw [LinearMap.mem_ker]
    obtain ⟨m, hm⟩ := coc_loc i dc e c hx v
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun h => ?_⟩)
    show descFun i e c (toGS D.nd.Om (SS i) h.1) =
      Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ) (toGS D.nd.Om (SS i) h.1) m - m
    rw [descFun_toGS i e c hN, ← qzE_eq]
    exact hm h.1 h.2
  · show Submodule.Quotient.mk (inflZ i e (descendLocallyConstantCocycle i e c hN hc)) = Submodule.Quotient.mk c
    congr 1
    exact Subtype.ext (funext fun g => descFun_toGS i e c hN g)

theorem zlSha : ZlSha i dc e := by
  unfold ZlSha Formalism.GaloisCohomology.shaLen
  calc Module.length ℤ_[D.nd.l i] ↥(selZ i dc e)
      ≤ Module.length ℤ_[D.nd.l i] ↥((Formalism.GaloisCohomology.Sha (D.nd.ldat (D.nd.l i)) (e : ℤ)).map (infl i e)) :=
        Module.length_le_of_injective (Submodule.inclusion (selZ_le_map i dc e))
          (Submodule.inclusion_injective _)
    _ ≤ Module.length ℤ_[D.nd.l i] ↥(Formalism.GaloisCohomology.Sha (D.nd.ldat (D.nd.l i)) (e : ℤ)) :=
        Module.length_le_of_surjective ((infl i e).submoduleMap _) (LinearMap.submoduleMap_surjective _ _)

end Desc

end Formalism.MainNotions.N.K.ShaT

end
