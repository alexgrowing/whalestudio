import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.TransgressionLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

section Class

theorem isCocycleOne_cocycleOneApply (z : cocycles (Rep.res N.subtype A) 1) :
    IsCocycleOne A N (cocycleOneApply A N z) :=
  cocycleOneApply_mul A N z

variable {A N}

noncomputable def tgClass (z : cocycles (Rep.res N.subtype A) 1) {y : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y) :
    cohomology (A.quotientToInvariants N) 2 :=
  (cohomologyπ _ 2).hom (cocycleOf 2 (tgCochain (isCocycleOne_cocycleOneApply A N z) hy hyc)
    (tgCochain_d _ hy hyc))

omit [IsTopologicalGroup G] in

theorem quotientToInvariants_ρ_apply_coe (c : G ⧸ N) (w : Representation.invariants (A.ρ.comp N.subtype)) :
    (((A.quotientToInvariants N).ρ c w : Representation.invariants (A.ρ.comp N.subtype)) : A) =
      A.ρ c.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rfl

theorem tgClass_eq (z z' : cocycles (Rep.res N.subtype A) 1)
    (hzz : (cohomologyπ _ 1).hom z = (cohomologyπ _ 1).hom z') {y y' : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y)
    (hy' : IsTgLift A N (cocycleOneApply A N z') y') (hyc' : IsLocallyConstant y') :
    tgClass z hy hyc = tgClass z' hy' hyc' := by

  have h0 : (cohomologyπ _ (0 + 1)).hom (z' - z) = 0 := by
    rw [map_sub, ← hzz, sub_self]
  obtain ⟨w, hw⟩ := (homologyπ_succ_eq_zero_iff _ 0 _).1 h0
  set a : A := w.1 Fin.elim0
  have ha : ∀ n : N, cocycleOneApply A N z' n - cocycleOneApply A N z n = A.ρ n a - a := by
    intro n
    have := congrArg (fun c : locallyConstantCochains (Rep.res N.subtype A) 1 => c.1 fun _ => n) hw
    simp only [map_sub] at this
    exact this.symm.trans (cochainsComplex_d_zero_apply (Rep.res N.subtype A) w fun _ => n)

  set V : G → A := fun g => y' g - y g - (A.ρ g a - a)
  have hVr : ∀ (g : G) (n : N), V (g * n) = V g := by
    intro g n
    simp only [V, hy.mul_right, hy'.mul_right, map_mul, Module.End.mul_apply]
    rw [show cocycleOneApply A N z' n = cocycleOneApply A N z n + (A.ρ n a - a) by
      rw [← ha]; abel, map_add, map_sub]
    abel
  have hVi : ∀ (h : G) (n : N), A.ρ n (V h) = V h := by
    intro h n
    have c1 := hy.conj h n
    have c2 := hy'.conj h n
    rw [show cocycleOneApply A N z' (GroundTheory.GroupCoh.conjHom N h n) =
      cocycleOneApply A N z (GroundTheory.GroupCoh.conjHom N h n) +
        (A.ρ (GroundTheory.GroupCoh.conjHom N h n) a - a) by rw [← ha]; abel,
      show cocycleOneApply A N z' n = cocycleOneApply A N z n + (A.ρ n a - a) by rw [← ha]; abel,
      map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
      GroundTheory.GroupCoh.coe_conjHom_apply] at c2
    simp only [V, map_sub, ← Module.End.mul_apply, ← map_mul]
    rw [show h * (h⁻¹ * (n : G) * h) = n * h by group] at c2
    rw [← sub_eq_zero]
    have e : A.ρ n (y' h) - y' h = A.ρ n (y h) - y h + (A.ρ (n * h) a - A.ρ h a - (A.ρ n a - a)) := by
      rw [← c1, ← c2]; abel
    rw [show A.ρ (n : G) (y' h) = y' h + (A.ρ n (y h) - y h + (A.ρ (n * h) a - A.ρ h a -
      (A.ρ n a - a))) by rw [← e]; abel]
    simp only [Module.End.mul_apply, map_mul]
    abel
  have hVc : IsLocallyConstant V :=
    (hyc'.sub hyc).sub ((isLocallyConstant_apply A a).sub (IsLocallyConstant.const a))
  have hVeq : ∀ g g' : G, (g : G ⧸ N) = g' → V g = V g' := by
    intro g g' h
    have hm : g⁻¹ * g' ∈ N := QuotientGroup.eq.mp h
    rw [show g' = g * ((⟨g⁻¹ * g', hm⟩ : N) : G) by simp, hVr]
  let W : locallyConstantCochains (A.quotientToInvariants N) 1 :=
    ⟨fun c => ⟨V (c 0).out, fun n => hVi _ n⟩, by
      let q : (Fin 1 → G) → (Fin 1 → G ⧸ N) := Pi.map fun _ => QuotientGroup.mk
      have hq : Topology.IsQuotientMap q :=
        (IsOpenQuotientMap.piMap fun _ => QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
      refine isLocallyConstant_of_comp_isQuotientMap hq ?_
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      have : (Subtype.val ∘ ((fun c : Fin 1 → G ⧸ N => (⟨V (c 0).out, fun n => hVi _ n⟩ :
          Representation.invariants (A.ρ.comp N.subtype))) ∘ q)) = fun g : Fin 1 → G => V (g 0) := by
        funext g
        exact hVeq _ _ (QuotientGroup.out_eq' _)
      rw [this]
      exact hVc.comp_continuous (continuous_apply 0)⟩
  have hW : ((cochainsComplex (A.quotientToInvariants N)).d 1 (1 + 1)).hom W =
      tgCochain (isCocycleOne_cocycleOneApply A N z') hy' hyc' -
        tgCochain (isCocycleOne_cocycleOneApply A N z) hy hyc := by
    apply Subtype.ext
    funext c
    apply Subtype.ext
    have hd := congrArg Subtype.val (cochainsComplex_d_one_apply (A.quotientToInvariants N) W c)
    refine hd.trans ?_
    have hq : ∀ (c : G ⧸ N) (w : Representation.invariants (A.ρ.comp N.subtype)),
        ((A.ρ.quotientToInvariants N c w : Representation.invariants (A.ρ.comp N.subtype)) : A) =
          A.ρ c.out w := fun c w => quotientToInvariants_ρ_apply_coe c w
    simp only [Submodule.coe_add, Submodule.coe_sub]
    rw [hq]
    change A.ρ (c 0).out (V (c 1).out) - V (c 0 * c 1).out + V (c 0).out =
      tgDiff A y' (c 0).out (c 1).out - tgDiff A y (c 0).out (c 1).out
    rw [hVeq (c 0 * c 1).out ((c 0).out * (c 1).out) (by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq', QuotientGroup.out_eq'])]
    simp only [V, tgDiff, map_sub, map_mul, Module.End.mul_apply]
    abel
  exact (cohomologyπ_cocycleOf_eq 1 _ _ _ _ W hW).symm

theorem cocycleOneApply_add (z z' : cocycles (Rep.res N.subtype A) 1) :
    cocycleOneApply A N (z + z') = cocycleOneApply A N z + cocycleOneApply A N z' := by
  funext n
  simp only [cocycleOneApply, map_add]
  rfl

theorem cocycleOneApply_smul (r : k) (z : cocycles (Rep.res N.subtype A) 1) :
    cocycleOneApply A N (r • z) = r • cocycleOneApply A N z := by
  funext n
  simp only [cocycleOneApply, map_smul]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A] in
theorem IsTgLift.add {x x' : N → A} {y y' : G → A} (hy : IsTgLift A N x y)
    (hy' : IsTgLift A N x' y') : IsTgLift A N (x + x') (y + y') where
  map_one := by simp [hy.map_one, hy'.map_one]
  mul_right g n := by
    simp only [Pi.add_apply, hy.mul_right, hy'.mul_right, map_add]
    abel
  conj h n := by
    simp only [Pi.add_apply, map_add]
    rw [show A.ρ h (x _) + A.ρ h (x' _) - (x n + x' n) =
      (A.ρ h (x (GroundTheory.GroupCoh.conjHom N h n)) - x n) +
        (A.ρ h (x' (GroundTheory.GroupCoh.conjHom N h n)) - x' n) by abel, hy.conj, hy'.conj]
    abel

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A] in
theorem IsTgLift.smul (r : k) {x : N → A} {y : G → A} (hy : IsTgLift A N x y) :
    IsTgLift A N (r • x) (r • y) where
  map_one := by simp [hy.map_one]
  mul_right g n := by
    simp only [Pi.smul_apply, hy.mul_right, map_smul, smul_add]
  conj h n := by
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, hy.conj, smul_sub]

theorem tgClass_add (z z' : cocycles (Rep.res N.subtype A) 1) {y y' : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y)
    (hy' : IsTgLift A N (cocycleOneApply A N z') y') (hyc' : IsLocallyConstant y')
    (hs : IsTgLift A N (cocycleOneApply A N (z + z')) (y + y')) :
    tgClass (z + z') hs (hyc.add hyc') = tgClass z hy hyc + tgClass z' hy' hyc' := by
  simp only [tgClass]
  rw [← map_add]
  congr 1
  rw [cocycleOf_eq_iff, map_add, iCycles_cocycleOf, iCycles_cocycleOf]
  apply Subtype.ext
  funext c
  apply Subtype.ext
  change tgDiff A y _ _ + tgDiff A y' _ _ = tgDiff A (y + y') _ _
  simp only [tgDiff, Pi.add_apply, map_add]
  abel

theorem tgClass_smul (r : k) (z : cocycles (Rep.res N.subtype A) 1) {y : G → A}
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y)
    (hs : IsTgLift A N (cocycleOneApply A N (r • z)) (r • y)) :
    tgClass (r • z) hs (hyc.comp (r • ·)) = r • tgClass z hy hyc := by
  simp only [tgClass]
  rw [← map_smul]
  congr 1
  rw [cocycleOf_eq_iff, map_smul, iCycles_cocycleOf]
  apply Subtype.ext
  funext c
  apply Subtype.ext
  change r • tgDiff A y _ _ = tgDiff A (r • y) _ _
  simp only [tgDiff, Pi.smul_apply, map_smul, smul_add, smul_sub]

variable (A N) in

def IsTransgression (h : cohomology (Rep.res N.subtype A) 1)
    (t : cohomology (A.quotientToInvariants N) 2) : Prop :=
  ∃ (z : cocycles (Rep.res N.subtype A) 1) (y : G → A)
    (hy : IsTgLift A N (cocycleOneApply A N z) y) (hyc : IsLocallyConstant y),
    (cohomologyπ _ 1).hom z = h ∧ tgClass z hy hyc = t

theorem IsTransgression.unique {h : cohomology (Rep.res N.subtype A) 1}
    {t t' : cohomology (A.quotientToInvariants N) 2} (ht : IsTransgression A N h t)
    (ht' : IsTransgression A N h t') : t = t' := by
  obtain ⟨z, y, hy, hyc, hz, rfl⟩ := ht
  obtain ⟨z', y', hy', hyc', hz', rfl⟩ := ht'
  exact tgClass_eq z z' (hz.trans hz'.symm) hy hyc hy' hyc'

theorem IsTransgression.add {h h' : cohomology (Rep.res N.subtype A) 1}
    {t t' : cohomology (A.quotientToInvariants N) 2} (ht : IsTransgression A N h t)
    (ht' : IsTransgression A N h' t') : IsTransgression A N (h + h') (t + t') := by
  obtain ⟨z, y, hy, hyc, hz, rfl⟩ := ht
  obtain ⟨z', y', hy', hyc', hz', rfl⟩ := ht'
  have hs : IsTgLift A N (cocycleOneApply A N (z + z')) (y + y') := by
    rw [cocycleOneApply_add]
    exact hy.add hy'
  exact ⟨z + z', y + y', hs, hyc.add hyc', by rw [map_add, hz, hz'],
    tgClass_add z z' hy hyc hy' hyc' hs⟩

theorem IsTransgression.smul (r : k) {h : cohomology (Rep.res N.subtype A) 1}
    {t : cohomology (A.quotientToInvariants N) 2} (ht : IsTransgression A N h t) :
    IsTransgression A N (r • h) (r • t) := by
  obtain ⟨z, y, hy, hyc, hz, rfl⟩ := ht
  have hs : IsTgLift A N (cocycleOneApply A N (r • z)) (r • y) := by
    rw [cocycleOneApply_smul]
    exact hy.smul r
  exact ⟨r • z, r • y, hs, hyc.comp (r • ·), by rw [map_smul, hz], tgClass_smul r z hy hyc hs⟩

end Class

section Existence

variable [CompactSpace G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem isLocallyConstant_cocycleOneApply (z : cocycles (Rep.res N.subtype A) 1) :
    IsLocallyConstant (cocycleOneApply A N z) :=
  (((cochainsComplex (Rep.res N.subtype A)).iCycles 1).hom z).2.comp_continuous
    (continuous_pi fun _ => continuous_id)

theorem exists_isTgLift (hN : IsClosed (N : Set G)) (z : cocycles (Rep.res N.subtype A) 1)
    (hz : (cohomologyπ _ 1).hom z ∈ cohomologyConjInvariants A N 1) :
    ∃ y : G → A, IsTgLift A N (cocycleOneApply A N z) y ∧ IsLocallyConstant y := by
  set X := cocycleOneApply A N z with hXdef
  have hXlc : IsLocallyConstant X := isLocallyConstant_cocycleOneApply A N z
  have hXc : IsCocycleOne A N X := isCocycleOne_cocycleOneApply A N z
  have hX1 : X 1 = 0 := by
    have := hXc 1 1
    simpa using this
  obtain ⟨s, hs, hsec, hs1⟩ := exists_continuous_section N hN
  have : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  let φ : G ⧸ N → N → A := fun c n =>
    A.ρ (s c) (X (GroundTheory.GroupCoh.conjHom N (s c) n)) - X n
  let S : G ⧸ N → Set A := fun c => {a | ∀ n, φ c n = A.ρ n a - a}
  have hne : ∀ c, ∃ a, a ∈ S c := fun c => (cohomologyConj_π_eq_iff A N z (s c)).1 (hz (s c))
  let b₀ : G ⧸ N → A := fun c => Classical.epsilon fun a => a ∈ S c
  have hb₀ : ∀ c, b₀ c ∈ S c := fun c => Classical.epsilon_spec (hne c)
  have hΦ : IsLocallyConstant fun p : (G ⧸ N) × N => φ p.1 p.2 := by
    have hconj : Continuous fun p : (G ⧸ N) × N => GroundTheory.GroupCoh.conjHom N (s p.1) p.2 :=
      Continuous.subtype_mk (((hs.comp continuous_fst).inv.mul
        (continuous_subtype_val.comp continuous_snd)).mul (hs.comp continuous_fst)) _
    exact (isLocallyConstant_ρ_apply A (hs.comp continuous_fst)
      (hXlc.comp_continuous hconj)).sub (hXlc.comp_continuous continuous_snd)
  have hφ : ∀ c₀, ∀ᶠ c in nhds c₀, φ c = φ c₀ := by
    intro c₀
    have key := (isCompact_univ : IsCompact (Set.univ : Set N)).eventually_forall_of_forall_eventually
      (x₀ := c₀) (P := fun c n => φ c n = φ c₀ n) fun n _ => by
        have h1 := hΦ.eventually_eq (c₀, n)
        have h2 : ∀ᶠ p in nhds (c₀, n), φ c₀ p.2 = φ c₀ n :=
          (continuous_snd.tendsto (c₀, n)).eventually
            ((hΦ.comp_continuous (continuous_const.prodMk continuous_id)).eventually_eq n)
        filter_upwards [h1, h2] with p hp1 hp2
        exact hp1.trans hp2.symm
    filter_upwards [key] with c hc
    funext n
    exact hc n (Set.mem_univ n)
  have hb₀lc : IsLocallyConstant b₀ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro c₀
    filter_upwards [hφ c₀] with c hc
    simp only [b₀, S, hc]
  let b : G ⧸ N → A := fun c => b₀ c - b₀ 1
  have hφ1 : ∀ n, φ 1 n = 0 := by
    intro n
    have e : GroundTheory.GroupCoh.conjHom N 1 n = n := Subtype.ext (by simp)
    simp only [φ, hs1, e, map_one, Module.End.one_apply, sub_self]
  have hb : ∀ c n, φ c n = A.ρ n (b c) - b c := by
    intro c n
    have h1 := hb₀ c n
    have h2 := hb₀ 1 n
    rw [hφ1] at h2
    simp only [b, map_sub]
    rw [h1, ← sub_eq_zero]
    rw [show A.ρ (n : G) (b₀ c) - b₀ c - (A.ρ n (b₀ c) - A.ρ n (b₀ 1) - (b₀ c - b₀ 1)) =
      A.ρ n (b₀ 1) - b₀ 1 by abel, ← h2]
  have hr1 : sectionRetraction N hsec 1 = 1 :=
    Subtype.ext (by rw [coe_sectionRetraction, QuotientGroup.mk_one, hs1]; simp)
  refine ⟨fun g => b g + A.ρ (s g) (X (sectionRetraction N hsec g)), ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [b, hs1, hr1, hX1]
  · intro g n
    beta_reduce
    rw [mk_mul_mem N g n, sectionRetraction_mul N hsec, hXc, map_add, ← Module.End.mul_apply,
      ← map_mul, section_mul_sectionRetraction N hsec]
    abel
  · intro h n
    set c : G ⧸ N := (h : G ⧸ N) with hcdef
    set m : N := sectionRetraction N hsec h with hmdef
    have hh : s c * (m : G) = h := section_mul_sectionRetraction N hsec h
    set n' : N := GroundTheory.GroupCoh.conjHom N (s c) n with hn'def
    have F1 : GroundTheory.GroupCoh.conjHom N h n = GroundTheory.GroupCoh.conjHom N m n' :=
      Subtype.ext (by simp only [GroundTheory.GroupCoh.coe_conjHom_apply, hn'def]; rw [← hh]; group)
    have e : m * GroundTheory.GroupCoh.conjHom N m n' = n' * m :=
      Subtype.ext (by simp only [Subgroup.coe_mul, GroundTheory.GroupCoh.coe_conjHom_apply]; group)
    have F2 := hXc m (GroundTheory.GroupCoh.conjHom N m n')
    rw [e, hXc n' m] at F2
    have F2' : A.ρ m (X (GroundTheory.GroupCoh.conjHom N m n')) = X n' + A.ρ n' (X m) - X m := by
      rw [F2]; abel
    have F3 := hb c n
    have F4 : s c * (n' : G) = n * s c := by
      simp only [hn'def, GroundTheory.GroupCoh.coe_conjHom_apply]; group
    show A.ρ h (X (GroundTheory.GroupCoh.conjHom N h n)) - X n =
      A.ρ n (b c + A.ρ (s c) (X m)) - (b c + A.ρ (s c) (X m))
    rw [F1, ← hh, map_mul, Module.End.mul_apply, F2', map_sub, map_add,
      ← Module.End.mul_apply (A.ρ (s c)) (A.ρ n'), ← map_mul, F4, map_mul, Module.End.mul_apply]
    have F3' : A.ρ (s c) (X n') = X n + (A.ρ n (b c) - b c) := by
      rw [← F3]; simp only [φ, hn'def]; abel
    rw [F3', map_add]
    abel
  · exact ((hb₀lc.sub (IsLocallyConstant.const _)).comp_continuous
      QuotientGroup.continuous_mk).add
      (isLocallyConstant_ρ_apply A (hs.comp QuotientGroup.continuous_mk)
        (hXlc.comp_continuous (continuous_sectionRetraction N hs hsec)))

theorem exists_isTransgression (hN : IsClosed (N : Set G)) (h : cohomology (Rep.res N.subtype A) 1)
    (hh : h ∈ cohomologyConjInvariants A N 1) : ∃ t, IsTransgression A N h t := by
  obtain ⟨z, rfl⟩ := homologyπ_surjective (cochainsComplex (Rep.res N.subtype A)) 1 h
  obtain ⟨y, hy, hyc⟩ := exists_isTgLift A N hN z hh
  exact ⟨tgClass z hy hyc, z, y, hy, hyc, rfl, rfl⟩

noncomputable def transgression (hN : IsClosed (N : Set G)) :
    cohomologyConjInvariants A N 1 →ₗ[k] cohomology (A.quotientToInvariants N) 2 where
  toFun h := Classical.choose (exists_isTransgression A N hN h.1 h.2)
  map_add' h h' :=
    (Classical.choose_spec (exists_isTransgression A N hN (h + h').1 (h + h').2)).unique
      ((Classical.choose_spec (exists_isTransgression A N hN h.1 h.2)).add
        (Classical.choose_spec (exists_isTransgression A N hN h'.1 h'.2)))
  map_smul' r h :=
    (Classical.choose_spec (exists_isTransgression A N hN (r • h).1 (r • h).2)).unique
      ((Classical.choose_spec (exists_isTransgression A N hN h.1 h.2)).smul r)

theorem isTransgression_transgression (hN : IsClosed (N : Set G))
    (h : cohomologyConjInvariants A N 1) : IsTransgression A N h (transgression A N hN h) :=
  Classical.choose_spec (exists_isTransgression A N hN h.1 h.2)

theorem transgression_eq_iff (hN : IsClosed (N : Set G)) (h : cohomologyConjInvariants A N 1)
    (t : cohomology (A.quotientToInvariants N) 2) :
    transgression A N hN h = t ↔ IsTransgression A N h t :=
  ⟨fun e => e ▸ isTransgression_transgression A N hN h,
    fun ht => (isTransgression_transgression A N hN h).unique ht⟩

end Existence

end GroundTheory.ProfCoh
