import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.LocalH1Finiteness

theorem finite_cocycles_of_finite_h1 {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [Finite M] (rho : Representation R G M) (h : Finite (H1 rho)) :
    Finite (Z1 rho) := by
  have hB : Finite (B1 rho) := Finite.of_surjective _ (d0 rho).surjective_rangeRestrict
  have hB' : Finite ((B1 rho).comap (Z1 rho).subtype) :=
    Finite.of_injective (fun x : (B1 rho).comap (Z1 rho).subtype => (⟨x.1.1, x.2⟩ : B1 rho))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : B1 rho => x.1) hab)))
  exact @Finite.of_addSubgroup_quotient _ _ ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup hB' h

section General

variable {G V : Type} [Group G] [NormedAddCommGroup V] [IsUltrametricDist V]
  {L : Type} [Field L] [Module L V]

def cball (V : Type) [NormedAddCommGroup V] [IsUltrametricDist V] (R : ℝ) (hR : 0 ≤ R) :
    AddSubgroup V where
  carrier := Metric.closedBall 0 R
  zero_mem' := Metric.mem_closedBall_self hR
  add_mem' := fun {a b} ha hb => by
    rw [mem_closedBall_zero_iff] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by simpa using ha

def oball (V : Type) [NormedAddCommGroup V] [IsUltrametricDist V] (R : ℝ) (hR : 0 ≤ R) :
    AddSubgroup (cball V R hR) where
  carrier := {x | ‖(x : V)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max (a : V) b).trans_lt (max_lt ha hb)
  neg_mem' := fun {a} ha => by simpa using ha

variable (ρ : Representation L G V) (hn : ∀ g v, ‖ρ g v‖ ≤ ‖v‖) (R : ℝ) (hR : 0 ≤ R)

def actBall (g : G) : cball V R hR →+ cball V R hR where
  toFun x := ⟨ρ g x, mem_closedBall_zero_iff.2 ((hn g x).trans (mem_closedBall_zero_iff.1 x.2))⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def actQuot (g : G) : cball V R hR ⧸ oball V R hR →+ cball V R hR ⧸ oball V R hR :=
  QuotientAddGroup.map _ _ (actBall ρ hn R hR g) fun x hx => (hn g x).trans_lt hx

def repQuot (n : ℕ) [Module (ZMod n) (cball V R hR ⧸ oball V R hR)] :
    Representation (ZMod n) G (cball V R hR ⧸ oball V R hR) where
  toFun g := (actQuot ρ hn R hR g).toZModLinearMap n
  map_one' := by
    apply LinearMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change ((actBall ρ hn R hR 1 x : cball V R hR) : cball V R hR ⧸ oball V R hR) = x
      congr 1
      apply Subtype.ext
      change ρ 1 x = x
      simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change ((actBall ρ hn R hR (g * h) x : cball V R hR) : cball V R hR ⧸ oball V R hR) =
        ((actBall ρ hn R hR g (actBall ρ hn R hR h x) : cball V R hR) : cball V R hR ⧸ oball V R hR)
      congr 1
      apply Subtype.ext
      change ρ (g * h) x = ρ g (ρ h x)
      simp

end General

theorem _root_.GlobalTheory.LocalH1Finiteness.finite_cocycles_of_compact_cover {l : ℕ} [Fact l.Prime] {G H V : Type} [Group G]
    [TopologicalSpace G] [Group H] [TopologicalSpace H] [CompactSpace H] [NormedAddCommGroup V]
    [IsUltrametricDist V] [NormedSpace ℚ_[l] V] [FiniteDimensional ℚ_[l] V] {L : Type} [Field L]
    [Algebra ℚ_[l] L] [Module L V] [IsScalarTower ℚ_[l] L V] [ContinuousConstSMul L V]
    (ρ : Representation L G V) (hρ : _root_.ReciprocityTheory.Gal.ContAction ρ) (hn : ∀ g v, ‖ρ g v‖ ≤ ‖v‖)
    (φ : H →* G) (hφ : Continuous φ) (hφs : Function.Surjective φ)
    (hfin : ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
      [Finite M] [TopologicalSpace M] [DiscreteTopology M]
      (rho : Representation (ZMod (l ^ r)) H M), 0 < r → _root_.ReciprocityTheory.Gal.ContAction rho →
        Finite (_root_.ReciprocityTheory.Gal.H1 rho)) :
    Module.Finite L (_root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hlR : (0 : ℝ) ≤ l := hl0.le
  have hlQ : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hnorm : ‖(l : ℚ_[l])‖ = (l : ℝ)⁻¹ := Padic.norm_p
  have hρc : Continuous fun p : G × V => ρ p.1 p.2 := hρ
  set T := _root_.GlobalTheory.LocalH1Finiteness.cball V l hlR with hT
  set U := _root_.GlobalTheory.LocalH1Finiteness.oball V l hlR with hU
  have hkill : ∀ x : T ⧸ U, (l ^ 2) • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      show ‖((l ^ 2) • (y : V))‖ < 1
      rw [← Nat.cast_smul_eq_nsmul ℚ_[l], norm_smul, Nat.cast_pow, norm_pow, hnorm]
      have hy : ‖(y : V)‖ ≤ l := mem_closedBall_zero_iff.1 y.2
      calc (l : ℝ)⁻¹ ^ 2 * ‖(y : V)‖ ≤ (l : ℝ)⁻¹ ^ 2 * l := by gcongr
        _ = (l : ℝ)⁻¹ := by field_simp
        _ < 1 := inv_lt_one_of_one_lt₀ hl1
  letI : Module (ZMod (l ^ 2)) (T ⧸ U) := AddCommGroup.zmodModule hkill
  letI : TopologicalSpace (T ⧸ U) := ⊥
  haveI : DiscreteTopology (T ⧸ U) := ⟨rfl⟩
  haveI : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
  haveI : Finite (T ⧸ U) := by
    obtain ⟨t, htT, htf, hcov⟩ :=
      (isCompact_closedBall (0 : V) l).finite_cover_balls (e := 1) one_pos
    let f : V → T ⧸ U := fun x => if hx : x ∈ T then QuotientAddGroup.mk ⟨x, hx⟩ else 0
    refine Set.finite_univ_iff.1 ((htf.image f).subset fun q _ => ?_)
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨x, hxt, hxy⟩ := Set.mem_iUnion₂.1 (hcov y.2)
      refine ⟨x, hxt, ?_⟩
      have hxT : x ∈ T := htT hxt
      simp only [f, dif_pos hxT]
      rw [QuotientAddGroup.eq]
      show ‖(-(x : V) + y)‖ < 1
      rw [neg_add_eq_sub]
      exact mem_ball_iff_norm.1 hxy
  have hπ : Continuous (QuotientAddGroup.mk : T → T ⧸ U) := by
    rw [continuous_discrete_rng]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H z =>
      have hpre : (QuotientAddGroup.mk : T → T ⧸ U) ⁻¹' {QuotientAddGroup.mk z} =
          {w : T | ‖(w : V) - z‖ < 1} := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
          QuotientAddGroup.eq_iff_sub_mem]
        exact Iff.rfl
      rw [hpre]
      exact isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const))
        continuous_const
  let rho : Representation (ZMod (l ^ 2)) H (T ⧸ U) :=
    (_root_.GlobalTheory.LocalH1Finiteness.repQuot ρ hn (l : ℝ) hlR (l ^ 2)).comp φ

  have hcont : _root_.ReciprocityTheory.Gal.ContAction rho := by
    unfold _root_.ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      exact hπ.comp (Continuous.subtype_mk (f := fun h => ρ (φ h) y)
        (hρc.comp (hφ.prodMk continuous_const)) _)
  have hZ : Finite ↥(_root_.ReciprocityTheory.Gal.Z1 rho) := by
    have hH1 : Finite (_root_.ReciprocityTheory.Gal.H1 rho) := hfin 2 (T ⧸ U) rho two_pos hcont
    set N := Submodule.comap (_root_.ReciprocityTheory.Gal.Z1 rho).subtype (_root_.ReciprocityTheory.Gal.B1 rho)
    haveI hQ : Finite (↥(_root_.ReciprocityTheory.Gal.Z1 rho) ⧸ N.toAddSubgroup) := hH1
    haveI : Finite ↥(LinearMap.range (_root_.ReciprocityTheory.Gal.d0 rho)) :=
      Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (_root_.ReciprocityTheory.Gal.d0 rho))
    haveI hN : Finite ↥N.toAddSubgroup :=
      Finite.of_injective (fun x : N.toAddSubgroup =>
        (⟨x.1.1, x.2⟩ : LinearMap.range (_root_.ReciprocityTheory.Gal.d0 rho)))
        (fun a b hab => by
          simp only [Subtype.mk.injEq] at hab
          exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab)))
    apply Nat.finite_of_card_ne_zero
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
    exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  let A : Set (G → V) := {c | c ∈ _root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ ∧ ∀ g, ‖c g‖ ≤ l}
  let Ψ : (G → V) → H → T ⧸ U := fun c h =>
    if hc : ‖c (φ h)‖ ≤ l then QuotientAddGroup.mk ⟨c (φ h), mem_closedBall_zero_iff.2 hc⟩ else 0
  have hΨmem : ∀ c ∈ A, Ψ c ∈ (_root_.ReciprocityTheory.Gal.Z1 rho : Set (H → T ⧸ U)) := by
    rintro c ⟨hc, hcl⟩
    have hc' : Continuous c ∧ ∀ g h, c (g * h) = c g + ρ g (c h) := hc
    have hΨc : Ψ c = fun h =>
        QuotientAddGroup.mk (⟨c (φ h), mem_closedBall_zero_iff.2 (hcl (φ h))⟩ : T) := by
      funext h
      simp only [Ψ, dif_pos (hcl (φ h))]
    rw [hΨc]
    refine ⟨hπ.comp (Continuous.subtype_mk (hc'.1.comp hφ) _), fun h h' => ?_⟩
    have hval : (⟨c (φ (h * h')), mem_closedBall_zero_iff.2 (hcl _)⟩ : T) =
        ⟨c (φ h), mem_closedBall_zero_iff.2 (hcl _)⟩ +
          _root_.GlobalTheory.LocalH1Finiteness.actBall ρ hn l hlR (φ h)
            ⟨c (φ h'), mem_closedBall_zero_iff.2 (hcl _)⟩ := by
      apply Subtype.ext
      show c (φ (h * h')) = c (φ h) + ρ (φ h) (c (φ h'))
      rw [map_mul]
      exact hc'.2 _ _
    exact (congrArg QuotientAddGroup.mk hval).trans (QuotientAddGroup.mk_add _ _ _)
  have hΨeq : ∀ c ∈ A, ∀ c' ∈ A, Ψ c = Ψ c' → ∀ g, ‖c g - c' g‖ < 1 := by
    rintro c ⟨-, hcl⟩ c' ⟨-, hcl'⟩ hcc g
    obtain ⟨h, rfl⟩ := hφs g
    have := congrFun hcc h
    simp only [Ψ, dif_pos (hcl (φ h)), dif_pos (hcl' (φ h)), QuotientAddGroup.eq_iff_sub_mem] at this
    exact this
  have himg : (Ψ '' A).Finite :=
    (Set.toFinite (_root_.ReciprocityTheory.Gal.Z1 rho : Set (H → T ⧸ U))).subset (by
      rintro _ ⟨c, hcA, rfl⟩
      exact hΨmem c hcA)
  let B : Set (G → V) := Function.invFunOn Ψ A '' (Ψ '' A)
  have hBfin : B.Finite := himg.image _
  have hBA : ∀ c ∈ A, Function.invFunOn Ψ A (Ψ c) ∈ A ∧
      Ψ (Function.invFunOn Ψ A (Ψ c)) = Ψ c := fun c hc =>
    ⟨Function.invFunOn_mem ⟨c, hc, rfl⟩, Function.invFunOn_eq ⟨c, hc, rfl⟩⟩
  set S := Submodule.span ℚ_[l] B
  haveI : FiniteDimensional ℚ_[l] S := FiniteDimensional.span_of_finite ℚ_[l] hBfin
  have hind : ∀ c ∈ A, ∀ n : ℕ, ∃ s ∈ S, ∃ a ∈ A, c = s + ((l : ℚ_[l]) ^ n) • a := by
    intro c hc n
    induction n with
    | zero => exact ⟨0, S.zero_mem, c, hc, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs, a, ha, rfl⟩ := ih
      obtain ⟨hbA, hbΨ⟩ := hBA a ha
      set b := Function.invFunOn Ψ A (Ψ a)
      have hlt := hΨeq a ha b hbA hbΨ.symm
      refine ⟨s + ((l : ℚ_[l]) ^ n) • b, S.add_mem hs (S.smul_mem _
        (Submodule.subset_span (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ ha)))),
        (l : ℚ_[l])⁻¹ • (a - b), ⟨?_, fun g => ?_⟩, ?_⟩
      · exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ ha.1 hbA.1)
      · rw [Pi.smul_apply, Pi.sub_apply, norm_smul, norm_inv, hnorm, inv_inv]
        exact (mul_lt_mul_of_pos_left (hlt g) hl0).le.trans (by rw [mul_one])
      · rw [smul_smul, pow_succ, mul_assoc, mul_inv_cancel₀ hlQ, mul_one, smul_sub]
        abel
  have hAS : ∀ c ∈ A, c ∈ S := by
    intro c hc
    choose s hs a ha hca using hind c hc
    refine (Submodule.closed_of_finiteDimensional S).mem_of_tendsto (f := s) (b := Filter.atTop) ?_
      (Filter.Eventually.of_forall hs)
    refine tendsto_pi_nhds.2 fun g => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hlR)
        (inv_lt_one_of_one_lt₀ hl1)).mul_const (l : ℝ)).trans (by rw [zero_mul]))
    have h1 : s n g - c g = -(((l : ℚ_[l]) ^ n) • a n g) := by
      have := congrFun (hca n) g
      simp only [Pi.add_apply, Pi.smul_apply] at this
      rw [this]
      abel
    rw [h1, norm_neg, norm_smul, norm_pow, hnorm]
    exact mul_le_mul_of_nonneg_left ((ha n).2 g) (pow_nonneg (inv_nonneg.2 hlR) _)
  have hle : (_root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ).restrictScalars ℚ_[l] ≤ S := by
    intro c hc
    have hc' : Continuous c ∧ ∀ g h, c (g * h) = c g + ρ g (c h) := hc
    obtain ⟨C, hC⟩ := (isCompact_univ.image (hc'.1.comp hφ)).isBounded.exists_norm_le
    obtain ⟨n, hnC⟩ := pow_unbounded_of_one_lt C hl1
    have hmem : ((l : ℚ_[l]) ^ n) • c ∈ A := by
      refine ⟨Submodule.smul_of_tower_mem _ _ hc, fun g => ?_⟩
      obtain ⟨h, rfl⟩ := hφs g
      rw [Pi.smul_apply, norm_smul, norm_pow, hnorm]
      have hCg : ‖c (φ h)‖ ≤ C := hC _ ⟨h, Set.mem_univ _, rfl⟩
      have hpos : (0 : ℝ) < (l : ℝ) ^ n := pow_pos hl0 n
      calc (l : ℝ)⁻¹ ^ n * ‖c (φ h)‖ ≤ (l : ℝ)⁻¹ ^ n * (l : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left (hCg.trans hnC.le) (pow_nonneg (inv_nonneg.2 hlR) _)
        _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
        _ ≤ l := hl1.le
    have := S.smul_mem ((l : ℚ_[l]) ^ n)⁻¹ (hAS _ hmem)
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hlQ), one_smul] at this
  haveI : FiniteDimensional ℚ_[l] ((_root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ).restrictScalars ℚ_[l]) :=
    Submodule.finiteDimensional_of_le hle
  haveI : Module.Finite ℚ_[l] (_root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ) :=
    (inferInstance : FiniteDimensional ℚ_[l] ((_root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ).restrictScalars ℚ_[l]))
  exact Module.Finite.of_restrictScalars_finite ℚ_[l] L (_root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles ρ)

section Bridge

open Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : _root_.Formalism.BasicNotions.LocBridge l E Ω Gw O) in
theorem _root_.GlobalTheory.LocalH1Finiteness.norm_toLL_le (x : O) : ‖Bw.toLL x‖ ≤ 1 :=
  (_root_.GlobalTheory.mem_integralClosure_padicInt_iff (Bw.LL : IntermediateField ℚ_[l] (PadicAlgCl l)) _).1
    (Bw.eO x).2

theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (v : Fin m → ↥Bw.LL.1)
    (a : Fin m) :
    Bw.rep r g v a = ∑ b, Bw.toLL ((r (Bw.e.symm g) : Matrix (Fin m) (Fin m) O) a b) * v b := rfl

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : _root_.Formalism.BasicNotions.LocBridge l E Ω Gw O) in

theorem _root_.GlobalTheory.LocalH1Finiteness.finite_continuous_cocycles_localGaloisRep (hK : _root_.Formalism.GaloisCohomology.LocalFinitenessK) {m : ℕ}
    (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => (r g : Matrix (Fin m) (Fin m) O)) :
    Module.Finite ↥Bw.LL.1 (_root_.Formalism.WeaklyAdmissibleFiltrations.continuousCocycles (Bw.rep r)) := by
  haveI : FiniteDimensional ℚ_[l] ↥Bw.LL.1 := Bw.LL.2
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have htoLL : Continuous Bw.toLL := by
    show Continuous (fun x => ((Bw.eO x : _) : ↥Bw.LL.1))
    exact continuous_subtype_val.comp Bw.eO_cont
  let φ : _root_.Formalism.GaloisCohomology.GK l Bw.Kw.1 →* ↥(_root_.Formalism.BasicNotions.Loc.GK Bw.Kw) :=
    (Bw.Kw.1.fixingSubgroupEquiv.symm : _ ≃* _).toMonoidHom
  refine _root_.GlobalTheory.LocalH1Finiteness.finite_cocycles_of_compact_cover (l := l) (Bw.rep r) ?_ ?_ φ ?_ ?_ ?_
  · unfold _root_.ReciprocityTheory.Gal.ContAction
    have hent : ∀ a b, Continuous fun g : ↥(_root_.Formalism.BasicNotions.Loc.GK Bw.Kw) =>
        Bw.toLL ((r (Bw.e.symm g) : Matrix (Fin m) (Fin m) O) a b) := fun a b =>
      htoLL.comp ((hr.comp Bw.e_symm_cont).matrix_elem a b)
    refine continuous_pi fun a => ?_
    simp only [_root_.GlobalTheory.LocalH1Finiteness.rep_apply]
    exact continuous_finset_sum _ fun b _ =>
      ((hent a b).comp continuous_fst).mul ((continuous_apply b).comp continuous_snd)
  · intro g v
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_
    rw [_root_.GlobalTheory.LocalH1Finiteness.rep_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg v) fun b _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (_root_.GlobalTheory.LocalH1Finiteness.norm_toLL_le Bw _)).trans
      (norm_le_pi_norm v b)
  · exact (_root_.GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ Bw.Kw.1).2
  · exact Bw.Kw.1.fixingSubgroupEquiv.symm.surjective
  · intro r' M _ _ _ _ _ rho hr' hc
    exact (hK l Bw.Kw.1 Bw.Kw.2 r' M rho hr' hc).2.1

end Bridge

end GlobalTheory.LocalH1Finiteness
