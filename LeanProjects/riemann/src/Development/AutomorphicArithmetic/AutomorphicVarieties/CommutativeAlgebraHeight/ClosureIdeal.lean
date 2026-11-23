import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsOpenNormalSubgroupKillsOfGroupDetLawIsCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem dual_zero (F M : Type) [Field F] [AddCommGroup M] [Module F M] (x : M)
    (h : ∀ f : Module.Dual F M, f x = 0) : x = 0 := (Module.forall_dual_apply_eq_zero_iff F x).1 h

private theorem frat (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (hP : PhiCond G l) (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∃ hu : u ∈ H, ∀ (M : Type) [AddCommGroup M], (∀ x : M, l • x = 0) →
      ∀ ψ : H →* Multiplicative M, IsOpen (ψ.ker : Set H) → ψ ⟨u, hu⟩ = 1 := by
  classical
  haveI := hP H hH
  let W : Set H := ⋂ φ : {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H)}, (φ.1.ker : Set H)
  have hW : IsOpen W := isOpen_iInter_of_finite fun φ => φ.2
  have hW' : IsOpen (Subtype.val '' W : Set G) := hH.isOpenMap_subtype_val W hW
  have h1 : (1 : G) ∈ (Subtype.val '' W : Set G) :=
    ⟨1, Set.mem_iInter.2 fun φ => φ.1.ker.one_mem, rfl⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW' h1
  refine ⟨U, fun u hu => ?_⟩
  obtain ⟨v, hvW, rfl⟩ := hU hu
  refine ⟨v.2, fun M _ hM ψ hψ => ?_⟩
  haveI : Module (ZMod l) M := AddCommGroup.zmodModule hM
  by_contra hne
  have hne' : Multiplicative.toAdd (ψ v) ≠ 0 := fun h0 => hne (by simpa using congrArg Multiplicative.ofAdd h0)
  have hf : ∃ f : M →ₗ[ZMod l] ZMod l, f (Multiplicative.toAdd (ψ v)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne' (dual_zero (ZMod l) M _ hc)
  obtain ⟨f, hf⟩ := hf
  let φ : H →* Multiplicative (ZMod l) := (AddMonoidHom.toMultiplicative f.toAddMonoidHom).comp ψ
  have hle : ψ.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    simp [φ, hx]
  have hφ : IsOpen (φ.ker : Set H) := Subgroup.isOpen_mono hle hψ
  have hv := Set.mem_iInter.1 hvW ⟨φ, hφ⟩
  apply hf
  simpa [φ] using hv

private noncomputable def lev {A : Type} (G : Type) [CommRing A] [Group G] (J : TwoSidedIdeal (MonoidAlgebra A G)) : Subgroup G :=
  (((J.ringCon.mk' : MonoidAlgebra A G →+* J.ringCon.Quotient).toMonoidHom).comp (MonoidAlgebra.of A G)).ker

private theorem mk_eq {R : Type} [Ring R] (J : TwoSidedIdeal R) (x : R) : J.ringCon.mk' x = 0 ↔ x ∈ J := by
  rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
  rfl

private theorem mem_lev {A G : Type} [CommRing A] [Group G] (J : TwoSidedIdeal (MonoidAlgebra A G)) (g : G) :
    g ∈ lev G J ↔ MonoidAlgebra.single g 1 - 1 ∈ J := by
  rw [lev, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidAlgebra.of_apply, ← mk_eq, map_sub, map_one, sub_eq_zero]
  exact Iff.rfl

private theorem lev_open {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Ideal k) (S : Set (MonoidAlgebra k G)) [Finite (closureIdeal I S).ringCon.Quotient] :
    IsOpen (lev G (closureIdeal I S) : Set G) := by
  classical
  have key : ∀ q : (closureIdeal I S).ringCon.Quotient, q ≠ 0 → ∃ p : ℕ × OpenNormalSubgroup G, ∀ x,
      (closureIdeal I S).ringCon.mk' x = q → x ∉ TwoSidedIdeal.span (S ∪ {z | ∃ a ∈ I ^ p.1, z = MonoidAlgebra.single 1 a} ∪
        {z | ∃ h ∈ p.2, z = MonoidAlgebra.single h 1 - 1}) := by
    intro q hq
    obtain ⟨x0, rfl⟩ := (closureIdeal I S).ringCon.mk'_surjective q
    have hx0 : x0 ∉ closureIdeal I S := fun h => hq ((mk_eq _ x0).2 h)
    have hx1 : ¬ ∀ N : ℕ, ∀ H : OpenNormalSubgroup G, x0 ∈ TwoSidedIdeal.span (S ∪ {z | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪
        {z | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1}) := by
      intro hall
      apply hx0
      rw [closureIdeal, TwoSidedIdeal.mem_iInf]
      intro N
      rw [TwoSidedIdeal.mem_iInf]
      exact hall N
    push_neg at hx1
    obtain ⟨N, H, hN⟩ := hx1
    refine ⟨(N, H), fun x hx hxmem => hN ?_⟩
    have hd : x - x0 ∈ closureIdeal I S := (mk_eq _ _).1 (by rw [map_sub, hx, sub_self])
    rw [closureIdeal, TwoSidedIdeal.mem_iInf] at hd
    have hd' := (TwoSidedIdeal.mem_iInf _).1 (hd N) H
    have := TwoSidedIdeal.sub_mem _ hxmem hd'
    simpa using this
  choose p hp using key
  have hsub : (⨅ q, ⨅ hq : q ≠ 0, (p q hq).2.toSubgroup) ≤ lev G (closureIdeal I S) := by
    intro h hh
    rw [mem_lev]
    by_contra hc
    have hq : (closureIdeal I S).ringCon.mk' (MonoidAlgebra.single h 1 - 1) ≠ 0 := fun h0 => hc ((mk_eq _ _).1 h0)
    apply hp _ hq _ rfl
    apply TwoSidedIdeal.subset_span
    right
    exact ⟨h, Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh _) hq, rfl⟩
  apply Subgroup.isOpen_mono hsub
  rw [Subgroup.coe_iInf]
  refine isOpen_iInter_of_finite fun q => ?_
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun hq => (p q hq).2.isOpen'

private theorem lift_span {R R' : Type} [Ring R] [Ring R'] (f : R →+* R') (hf : Function.Surjective f)
    (K : TwoSidedIdeal R) (S : Set R') (hS : ∀ z ∈ S, ∃ x ∈ K, f x = z) (z : R') (hz : z ∈ TwoSidedIdeal.span S) :
    ∃ x ∈ K, f x = z := by
  let T : TwoSidedIdeal R' := TwoSidedIdeal.mk' {z | ∃ x ∈ K, f x = z}
    ⟨0, K.zero_mem, map_zero f⟩
    (by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, K.add_mem ha hb, map_add f a b⟩)
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨-a, K.neg_mem ha, map_neg f a⟩)
    (by
      rintro r _ ⟨a, ha, rfl⟩
      obtain ⟨r', rfl⟩ := hf r
      exact ⟨r' * a, K.mul_mem_left r' a ha, map_mul f r' a⟩)
    (by
      rintro _ r ⟨a, ha, rfl⟩
      obtain ⟨r', rfl⟩ := hf r
      exact ⟨a * r', K.mul_mem_right a r' ha, map_mul f a r'⟩)
  have hle : TwoSidedIdeal.span S ≤ T := TwoSidedIdeal.span_le.2 (fun w hw => by simpa [T] using hS w hw)
  have h' := hle hz
  simpa [T] using h'

private theorem ker_sq {k G : Type} [Field k] [Group G] (x y : MonoidAlgebra (DualNumber k) G)
    (hx : MonoidAlgebra.mapRingHom G (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k) x = 0)
    (hy : MonoidAlgebra.mapRingHom G (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k) y = 0) : x * y = 0 := by
  have hx' : ∀ a, (x.coeff a).fst = 0 := fun a => by
    have := congrArg (fun z => z.coeff a) hx
    simpa [MonoidAlgebra.coeff_mapRingHom] using this
  have hy' : ∀ a, (y.coeff a).fst = 0 := fun a => by
    have := congrArg (fun z => z.coeff a) hy
    simpa [MonoidAlgebra.coeff_mapRingHom] using this
  have hz : ∀ a b, x.coeff a * y.coeff b = 0 := fun a b => by
    ext
    · simp [hx' a, hy' b]
    · simp [hx' a, hy' b]
  classical
  apply MonoidAlgebra.ext
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.mul_apply]
  simp [Finsupp.sum, hz]

private theorem fst_surj {k G : Type} [Field k] [Group G] :
    Function.Surjective (MonoidAlgebra.mapRingHom G (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k)) := by
  intro y
  refine ⟨MonoidAlgebra.mapRingHom G (TrivSqZeroExt.inlHom k k) y, ?_⟩
  rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]
  have hc : (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k).comp (TrivSqZeroExt.inlHom k k) = RingHom.id k := by
    ext r
    simp
  rw [hc, MonoidAlgebra.mapRingHom_id, RingHom.id_apply]

private theorem kills_of_bot {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (I : Ideal A)
    (hI : I = ⊥) (g : G) (h : (D.map (Ideal.Quotient.mk I)).Kills (MonoidAlgebra.single g 1 - 1)) :
    D.Kills (MonoidAlgebra.single g 1 - 1) := by
  subst hI
  intro B _ _ x
  let φ : A ⧸ (⊥ : Ideal A) →+* B :=
    Ideal.Quotient.lift ⊥ (algebraMap A B) (fun a ha => by rw [Ideal.mem_bot.1 ha, map_zero])
  letI : Algebra (A ⧸ (⊥ : Ideal A)) B := φ.toAlgebra
  have e : ((φ.comp (Ideal.Quotient.mk ⊥)).toAlgebra : Algebra A B) = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ (fun r => by simp [φ, RingHom.algebraMap_toAlgebra])
  have h1 := h B x
  rw [show (MonoidAlgebra.mapRingHom G (algebraMap (A ⧸ (⊥ : Ideal A)) B)) (MonoidAlgebra.single g 1 - 1) =
    MonoidAlgebra.single g 1 - 1 by simp] at h1
  rw [show (MonoidAlgebra.mapRingHom G (algebraMap A B)) (MonoidAlgebra.single g 1 - 1) =
    MonoidAlgebra.single g 1 - 1 by simp]
  change (@GDet.D n A G _ _ D B _ ((φ.comp (Ideal.Quotient.mk ⊥)).toAlgebra)) (1 + x * (MonoidAlgebra.single g 1 - 1)) = 1 at h1
  rw [e] at h1
  exact h1

theorem UpperTheory.V.CA.u_tan :
    ∀ (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (Dbar : GDet n k G), PhiCond G l → Dbar.IsCont (maximalIdeal k) → Module.Finite k (Dbar.CHQuot ∅) → ∃ U : OpenNormalSubgroup G, ∀ D : GDet n (DualNumber k) G, D.IsCont (maximalIdeal (DualNumber k)) → D.map (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k) = Dbar → ∀ u ∈ U, D.Kills (MonoidAlgebra.single u 1 - 1) := by
  intro l _ n k G _ _ _ _ _ _ _ _ Dbar hP _ hfin
  haveI hQ : Finite (closureIdeal (maximalIdeal k) (Dbar.CH ∪ ∅)).ringCon.Quotient :=
    Module.finite_of_finite k (M := Dbar.CHQuot ∅)
  have hHo : IsOpen (lev G (closureIdeal (maximalIdeal k) (Dbar.CH ∪ ∅)) : Set G) := lev_open _ _
  set J := closureIdeal (maximalIdeal k) (Dbar.CH ∪ ∅) with hJ
  obtain ⟨U, hU⟩ := frat l hP (lev G J) hHo
  refine ⟨U, fun D hDc hDmap u hu => ?_⟩
  obtain ⟨hu1, hu2⟩ := hU u hu
  obtain ⟨HD, hHD⟩ := exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D (maximalIdeal (DualNumber k)) hDc 2
  have hsq : (maximalIdeal (DualNumber k)) ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun r hr s hs => ?_
    rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not] at hr hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr, hs]
  have hkD : ∀ h ∈ HD, D.Kills (MonoidAlgebra.single h 1 - 1) := fun h hh => kills_of_bot D _ hsq h (hHD h hh)
  have hK : ∀ x, x ∈ D.toDet.ker ↔ D.Kills x := fun x => ((d_ker D.toDet x).1).trans (d_toDet D x).2.2.2
  let π := MonoidAlgebra.mapRingHom G (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k)
  have hlift : ∀ z ∈ J, ∃ x ∈ D.toDet.ker, π x = z := by
    intro z hz
    rw [hJ, closureIdeal, TwoSidedIdeal.mem_iInf] at hz
    have hz1 := (TwoSidedIdeal.mem_iInf _).1 (hz 1) HD
    refine lift_span π fst_surj D.toDet.ker _ ?_ z hz1
    rintro w (((hw | hw) | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩)
    · rw [← hDmap] at hw
      have hw' : w ∈ TwoSidedIdeal.span ((MonoidAlgebra.mapRingHom G (TrivSqZeroExt.fstHom k k k : DualNumber k →+* k)) '' D.CH) := by
        rw [← g_chmap]
        exact TwoSidedIdeal.subset_span hw
      refine lift_span π fst_surj D.toDet.ker _ ?_ w hw'
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨v, ?_, rfl⟩
      apply d_ch_ker
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span hv
    · exact hw.elim
    · refine ⟨0, D.toDet.ker.zero_mem, ?_⟩
      rw [pow_one, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at ha
      rw [ha]
      simp
    · exact ⟨MonoidAlgebra.single h 1 - 1, (hK _).2 (hkD h hh), by simp [π]⟩
  have hlev : ∀ h : lev G J, ∃ e : MonoidAlgebra (DualNumber k) G, π e = 0 ∧
      (MonoidAlgebra.single (h : G) (1 : DualNumber k) - 1) - e ∈ D.toDet.ker := by
    intro h
    obtain ⟨x, hxK, hx⟩ := hlift _ ((mem_lev J h).1 h.2)
    refine ⟨(MonoidAlgebra.single (h : G) 1 - 1) - x, ?_, by rw [sub_sub_cancel]; exact hxK⟩
    rw [map_sub, hx]
    simp [π]
  choose e he using hlev
  have hmk : ∀ h : lev G J, D.toDet.ker.ringCon.mk' (MonoidAlgebra.single (h : G) (1 : DualNumber k) - 1) =
      D.toDet.ker.ringCon.mk' (e h) := by
    intro h
    rw [← sub_eq_zero, ← map_sub, mk_eq]
    exact (he h).2
  let ψ : lev G J →* Multiplicative D.toDet.ker.ringCon.Quotient :=
    { toFun := fun h => Multiplicative.ofAdd (D.toDet.ker.ringCon.mk' (MonoidAlgebra.single (h : G) 1 - 1))
      map_one' := by
        rw [OneMemClass.coe_one, ← MonoidAlgebra.one_def, sub_self, map_zero]
        rfl
      map_mul' := by
        intro a b
        have hs := MonoidAlgebra.single_mul_single (a : G) (b : G) (1 : DualNumber k) 1
        rw [mul_one] at hs
        have hab : (MonoidAlgebra.single ((a * b : lev G J) : G) (1 : DualNumber k) - 1) =
            (MonoidAlgebra.single (a : G) 1 - 1) + (MonoidAlgebra.single (b : G) 1 - 1) +
              (MonoidAlgebra.single (a : G) 1 - 1) * (MonoidAlgebra.single (b : G) 1 - 1) := by
          rw [Subgroup.coe_mul, ← hs]
          noncomm_ring
        have hee : D.toDet.ker.ringCon.mk' (e a * e b) = 0 := by
          rw [ker_sq _ _ (he a).1 (he b).1, map_zero]
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
        rw [← ofAdd_add]
        congr 1
        rw [hab, map_add, map_add, map_mul, hmk a, hmk b, ← map_mul, hee, add_zero] }
  have hψker : IsOpen (ψ.ker : Set (lev G J)) := by
    have hle : HD.toSubgroup.comap (lev G J).subtype ≤ ψ.ker := by
      intro h hh
      rw [MonoidHom.mem_ker]
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
      rw [(mk_eq _ _).2 ((hK _).2 (hkD h hh))]
    exact Subgroup.isOpen_mono hle (HD.isOpen'.preimage continuous_subtype_val)
  have hl : ∀ x : D.toDet.ker.ringCon.Quotient, l • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := D.toDet.ker.ringCon.mk'_surjective x
    rw [← map_nsmul, nsmul_eq_mul]
    have hl0 : (l : MonoidAlgebra (DualNumber k) G) = 0 := by
      rw [← map_natCast (algebraMap k (MonoidAlgebra (DualNumber k) G)) l, CharP.cast_eq_zero, map_zero]
    rw [hl0, zero_mul, map_zero]
  have hfin1 := hu2 D.toDet.ker.ringCon.Quotient hl ψ hψker
  rw [← hK, ← mk_eq]
  exact hfin1
