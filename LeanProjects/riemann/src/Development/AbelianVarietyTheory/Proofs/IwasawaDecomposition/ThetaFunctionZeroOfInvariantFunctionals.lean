import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsAlt

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

noncomputable section

namespace GlobalTheory.ThetaStalk

theorem exists_char_form {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : AddChar G (Module.End ℂ V)) (g : V) (hg : g ≠ 0) (ht : ∀ u, ∃ N, 0 < N ∧ ρ (N • u) g = g) :
    ∃ (χ : AddChar G ℂ) (ℓ : V →ₗ[ℂ] ℂ), ℓ g ≠ 0 ∧ (∀ u, ρ u g = g → χ u = 1) ∧
      ∀ u f N, 0 < N → ρ (N • u) f = f → ℓ (ρ u f) = χ u * ℓ f := by
  classical
  let A := AddMonoidAlgebra ℂ G
  let π : A →ₐ[ℂ] Module.End ℂ V := AddMonoidAlgebra.lift ℂ (Module.End ℂ V) G ρ.toMonoidHom
  let x : G → A := fun u => AddMonoidAlgebra.single u 1
  have hπ : ∀ u, π (x u) = ρ u := fun u => by
    simp [π, x, A]
  have hx0 : x 0 = 1 := rfl
  have hxa : ∀ u w, x (u + w) = x u * x w := fun u w => by
    simp [x, A, AddMonoidAlgebra.single_mul_single]
  have hxn : ∀ (n : ℕ) u, x (n • u) = x u ^ n := fun n u => by
    simp [x, A, AddMonoidAlgebra.single_pow]
  let I : Ideal A :=
    { carrier := {a | π a g = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_eq_mul, map_mul, Module.End.mul_apply, ha, map_zero] }
  have hI : I ≠ ⊤ := fun h => hg (by
    have : π 1 g = 0 := (h.ge Submodule.mem_top : (1 : A) ∈ I)
    simpa using this)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  have hfix : ∀ u, ρ u g = g → Ideal.Quotient.mk m (x u) = 1 := fun u hu => by
    rw [← map_one (Ideal.Quotient.mk m), Ideal.Quotient.eq]
    refine hIm ?_
    show π (x u - 1) g = 0
    rw [map_sub, map_one, hπ, LinearMap.sub_apply, hu, Module.End.one_apply, sub_self]
  have hint : Algebra.IsIntegral ℂ (A ⧸ m) := ⟨fun y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction a using AddMonoidAlgebra.induction_on with
    | of u =>
      obtain ⟨N, hN, h⟩ := ht u
      refine IsIntegral.of_pow hN ?_
      have := hfix _ h
      rw [hxn, map_pow] at this
      change IsIntegral ℂ (Ideal.Quotient.mk m (x u) ^ N)
      rw [this]
      exact isIntegral_one
    | add a b ha hb => rw [map_add]; exact ha.add hb
    | smul r a ha => exact ha.smul r⟩
  let φ : ℂ ≃ₐ[ℂ] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let c : A →ₐ[ℂ] ℂ := φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m)
  have hc : ∀ a, π a g = 0 → c a = 0 := fun a ha => by
    have : Ideal.Quotient.mk m a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hIm ha)
    show φ.symm (Ideal.Quotient.mk m a) = 0
    rw [this, map_zero]
  let χ : AddChar G ℂ :=
    { toFun := fun u => c (x u)
      map_zero_eq_one' := by rw [hx0, map_one]
      map_add_eq_mul' := fun u w => by rw [hxa, map_mul] }
  have hχ : ∀ u, ρ u g = g → χ u = 1 := fun u hu => by
    show φ.symm (Ideal.Quotient.mk m (x u)) = 1
    rw [hfix u hu, map_one]
  let S : Submodule ℂ V :=
    { carrier := {f | ∃ a, c a ≠ 0 ∧ π a f = 0}
      add_mem' := by
        rintro f f' ⟨a, ha, haf⟩ ⟨b, hb, hbf⟩
        refine ⟨a * b, by rw [map_mul]; exact mul_ne_zero ha hb, ?_⟩
        have h1 : π (a * b) f = 0 := by rw [mul_comm, map_mul, Module.End.mul_apply, haf, map_zero]
        rw [map_add, h1, map_mul, Module.End.mul_apply, hbf, map_zero, add_zero]
      zero_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, map_zero _⟩
      smul_mem' := by
        rintro r f ⟨a, ha, haf⟩
        exact ⟨a, ha, by rw [map_smul, haf, smul_zero]⟩ }
  have hgS : g ∉ S := by
    rintro ⟨a, ha, hag⟩
    exact ha (hc a hag)
  obtain ⟨ℓ, hℓ, hℓS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hgS inferInstance
  refine ⟨χ, ℓ, hℓ, hχ, fun u f N hN hf => ?_⟩
  obtain ⟨N₀, hN₀, h₀⟩ := ht u
  have hz : χ u ^ (N * N₀) = 1 := by
    rw [mul_comm, pow_mul, ← AddChar.map_nsmul_eq_pow, hχ _ h₀, one_pow]
  have hM : 0 < N * N₀ := Nat.mul_pos hN hN₀
  have hz0 : χ u ≠ 0 := fun h => by
    rw [h, zero_pow hM.ne'] at hz
    exact zero_ne_one hz
  have hxf : π (x u ^ (N * N₀)) f = f := by
    rw [pow_mul, ← hxn, map_pow, hπ, Module.End.pow_apply]
    exact Function.iterate_fixed hf _
  have hmem : ρ u f - χ u • f ∈ S := by
    refine ⟨∑ i ∈ Finset.range (N * N₀), x u ^ i * algebraMap ℂ A (χ u) ^ (N * N₀ - 1 - i), ?_, ?_⟩
    · have h1 : c (x u) = χ u := rfl
      simp only [map_sum, map_mul, map_pow, AlgHom.commutes, h1, Algebra.algebraMap_self, RingHom.id_apply]
      rw [geom_sum₂_self]
      exact mul_ne_zero (Nat.cast_ne_zero.2 hM.ne') (pow_ne_zero _ hz0)
    · have h2 : ρ u f - χ u • f = π (x u - algebraMap ℂ A (χ u)) f := by
        rw [map_sub, hπ, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply]
      rw [h2, ← Module.End.mul_apply, ← map_mul, geom_sum₂_mul, map_sub, LinearMap.sub_apply, hxf, ← map_pow, hz,
        map_one, map_one, Module.End.one_apply, sub_self]
  have h3 : ℓ (ρ u f - χ u • f) = 0 := by
    have := Submodule.mem_map_of_mem (f := ℓ) hmem
    rwa [hℓS, Submodule.mem_bot] at this
  rwa [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3

theorem eq_top_of_separates {Q : Type} [AddCommGroup Q] [Finite Q] (H : AddSubgroup (AddChar Q ℂ))
    (h : ∀ x : Q, x ≠ 0 → ∃ χ ∈ H, χ x ≠ 1) (χ : AddChar Q ℂ) : χ ∈ H := by
  by_contra hχ
  have h0 : (QuotientAddGroup.mk χ : AddChar Q ℂ ⧸ H) ≠ 0 := fun e => hχ ((QuotientAddGroup.eq_zero_iff _).1 e)
  obtain ⟨Λ, hΛ⟩ := AddChar.exists_apply_ne_zero.2 h0
  obtain ⟨x, hx⟩ := (AddChar.doubleDualEquiv (α := Q)).surjective (Λ.compAddMonoidHom (QuotientAddGroup.mk' H))
  have hev : ∀ φ : AddChar Q ℂ, φ x = Λ (QuotientAddGroup.mk φ) := fun φ => DFunLike.congr_fun hx φ
  by_cases hx0 : x = 0
  · exact hΛ (by rw [← hev, hx0, AddChar.map_zero_eq_one])
  · obtain ⟨φ, hφ, hφx⟩ := h x hx0
    exact hφx (by rw [hev, (QuotientAddGroup.eq_zero_iff _).2 hφ, AddChar.map_zero_eq_one])

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.KeyLemmaTwo.main
  | exact _root_.GlobalTheory.KeyLemmaTwo.main
  | (apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KeyLemmaTwo.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KeyLemmaTwo.main ..)

theorem exists_nsmul_mem_open {G : Type} [NormedAddCommGroup G] [IsUltrametricDist G] [ProperSpace G]
    (U : AddSubgroup G) (hU : IsOpen (U : Set G)) (x : G) : ∃ N, 0 < N ∧ N • x ∈ U := by
  have : DiscreteTopology (G ⧸ U) := QuotientAddGroup.discreteTopology hU
  have hfin : ((QuotientAddGroup.mk : G → G ⧸ U) '' Metric.closedBall 0 ‖x‖).Finite :=
    ((isCompact_closedBall _ _).image QuotientAddGroup.continuous_mk).finite_of_discrete
  obtain ⟨a, b, hab, e⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => (QuotientAddGroup.mk (n • x) : G ⧸ U))
    (fun n => Set.mem_image_of_mem _ (mem_closedBall_zero_iff.2 (IsUltrametricDist.norm_nsmul_le x n)))
  refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
  have := QuotientAddGroup.eq.1 e
  rwa [sub_nsmul _ hab.le, add_comm]

theorem exists_eq_dilate {K : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K] (ψ : AddChar K ℂ)
    (hc : Continuous ψ) (hne : ∃ y, ψ y ≠ 1) (χ : AddChar K ℂ) {r : ℝ} (hr : 0 < r)
    (hχ : ∀ x, ‖x‖ < r → χ x = 1) : ∃ a, ∀ x, χ x = ψ (a * x) := by
  classical
  obtain ⟨δ, hδ, hψδ⟩ : ∃ δ > 0, ∀ x : K, ‖x‖ < δ → ψ x = 1 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun x hx => eq_one_of_pow_near fun n => ?_⟩
    have := h (x := n • x) (by
      rw [dist_zero_right]; exact (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx)
    rwa [AddChar.map_zero_eq_one, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this
  have hZ : IsClosed {y : K | ψ y ≠ 1} := by
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    refine fun y hy => ⟨δ, hδ, fun y' hy' => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hy ⊢
    rw [← add_sub_cancel y y', AddChar.map_add_eq_mul, hy, one_mul]
    exact hψδ _ (mem_ball_iff_norm.1 hy')
  obtain ⟨y₀, hy₀, hd⟩ := hZ.exists_infDist_eq_dist hne 0
  have hmin : ∀ y, ‖y‖ < ‖y₀‖ → ψ y = 1 := fun y hy => by
    by_contra h
    have := Metric.infDist_le_dist_of_mem (x := (0 : K)) (s := {y : K | ψ y ≠ 1}) h
    rw [hd, dist_zero_left, dist_zero_left] at this
    exact absurd hy (not_lt.2 this)
  have hy0 : 0 < ‖y₀‖ := norm_pos_iff.2 fun h => hy₀ (by rw [h, AddChar.map_zero_eq_one])
  let U : AddSubgroup K :=
    { carrier := Metric.ball 0 r
      add_mem' := fun {a b} ha hb => mem_ball_zero_iff.2
        ((IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt (mem_ball_zero_iff.1 ha) (mem_ball_zero_iff.1 hb)))
      zero_mem' := Metric.mem_ball_self hr
      neg_mem' := fun {a} ha => by simpa using ha }
  have hU : ∀ x, x ∈ U ↔ ‖x‖ < r := fun x => mem_ball_zero_iff
  have hlift : ∀ φ : AddChar K ℂ, (∀ x ∈ U, φ x = 1) → ∃ Λ : AddChar (K ⧸ U) ℂ, ∀ x : K, Λ x = φ x := by
    intro φ hφ
    refine ⟨⟨Quotient.lift φ fun a b hab => ?_, φ.map_zero_eq_one, ?_⟩, fun x => rfl⟩
    · have := hφ _ (QuotientAddGroup.leftRel_apply.1 hab)
      rw [← add_neg_cancel_left a b, AddChar.map_add_eq_mul, this, mul_one]
    · rintro ⟨a⟩ ⟨b⟩
      exact φ.map_add_eq_mul a b
  let B : Set K := {a | ∀ u ∈ U, ψ (a * u) = 1}
  have hB : IsCompact B := by
    refine (isCompact_closedBall (0 : K) (‖y₀‖ / r)).of_isClosed_subset ?_ fun a ha => ?_
    · simp only [B, Set.setOf_forall]
      exact isClosed_iInter fun u => isClosed_iInter fun _ =>
        isClosed_eq (hc.comp (continuous_id.mul continuous_const)) continuous_const
    · by_contra hn
      rw [mem_closedBall_zero_iff, not_le] at hn
      have hpos : 0 < ‖a‖ := lt_of_le_of_lt (by positivity) hn
      refine hy₀ ?_
      have := ha (y₀ / a) ((hU _).2 (by
        rw [norm_div, div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hr] at hn
        linarith))
      rwa [mul_div_cancel₀ _ (norm_pos_iff.1 hpos)] at this
  obtain ⟨a, -, ha⟩ := hB.inter_iInter_nonempty (fun x : K => {a | χ x = ψ (a * x)})
    (fun x => isClosed_eq continuous_const (hc.comp (continuous_id.mul continuous_const))) fun s => by
    let P : AddSubgroup (K ⧸ U) := AddSubgroup.closure (s.image (QuotientAddGroup.mk : K → K ⧸ U) : Finset (K ⧸ U))
    have : Finite P := AddCommGroup.finite_of_fg_torsion P (by
      rintro ⟨⟨x⟩, hx⟩
      obtain ⟨N, hN, h⟩ := exists_nsmul_mem_open U Metric.isOpen_ball x
      exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, Subtype.ext ((QuotientAddGroup.eq_zero_iff _).2 h)⟩)
    let H : AddSubgroup (AddChar P ℂ) :=
      { carrier := {Λ | ∃ a ∈ B, ∀ (x : K) (hx : (x : K ⧸ U) ∈ P), Λ ⟨x, hx⟩ = ψ (a * x)}
        add_mem' := by
          rintro Λ Λ' ⟨a, ha, h⟩ ⟨b, hb, h'⟩
          refine ⟨a + b, fun u hu => ?_, fun x hx => ?_⟩
          · rw [add_mul, AddChar.map_add_eq_mul, ha u hu, hb u hu, mul_one]
          · rw [add_mul, AddChar.map_add_eq_mul, AddChar.add_apply, h, h']
        zero_mem' := ⟨0, fun u _ => by simp, fun x _ => by simp⟩
        neg_mem' := by
          rintro Λ ⟨a, ha, h⟩
          refine ⟨-a, fun u hu => ?_, fun x hx => ?_⟩
          · rw [neg_mul, ← mul_neg]; exact ha _ (U.neg_mem hu)
          · rw [neg_mul, ← mul_neg, AddChar.neg_apply]
            exact h (-x) (P.neg_mem hx) }
    obtain ⟨Λ, hΛ⟩ := hlift χ fun x hx => hχ x ((hU x).1 hx)
    obtain ⟨a, ha, h⟩ := eq_top_of_separates H (by
      rintro ⟨⟨x⟩, hx⟩ hx0
      have hxr : r ≤ ‖x‖ := not_lt.1 fun h => hx0 (Subtype.ext ((QuotientAddGroup.eq_zero_iff _).2 ((hU x).2 h)))
      have hxp : 0 < ‖x‖ := hr.trans_le hxr
      have hb : y₀ / x ∈ B := fun u hu => hmin _ (by
        rw [norm_mul, norm_div, div_mul_eq_mul_div, div_lt_iff₀ hxp]
        exact mul_lt_mul_of_pos_left (((hU u).1 hu).trans_le hxr) hy0)
      obtain ⟨Λ', hΛ'⟩ := hlift (ψ.mulShift (y₀ / x)) hb
      refine ⟨Λ'.compAddMonoidHom P.subtype, ⟨_, hb, fun z _ => hΛ' z⟩, fun h => hy₀ ?_⟩
      have := (hΛ' x).symm.trans h
      rwa [AddChar.mulShift_apply, div_mul_cancel₀ _ (norm_pos_iff.1 hxp)] at this) (Λ.compAddMonoidHom P.subtype)
    refine ⟨a, ha, Set.mem_iInter₂.2 fun x hx => ?_⟩
    exact (hΛ x).symm.trans (h x (AddSubgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))))
  exact ⟨a, fun x => Set.mem_iInter.1 ha x⟩

section Heis

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem hO_smul_smul (a b : AE D) (x y : WO S T) : hO S T (a • x) (b • y) = a * cA D b * hO S T x y := by
  simp only [hO, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem heisO_comm (u t : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T t f) = ψ (symplO S T u t) • heisO ψ S T t (heisO ψ S T u f) := by
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, add_comm t u]
  congr 2
  have h : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add, add_halves, map_one]
  rw [symplOH, symplOH, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.2.1 t u]
  linear_combination symplO S T u t * h

def heisL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f f' := funext fun w => mul_add _ _ _
  map_smul' c f := funext fun w => mul_left_comm _ _ _

theorem exists_hO_eq (S T : HSp D) (i : Fin T.rank) (j : Fin S.rank) (e : D.host.E) :
    ∃ γ : WO S T, ∀ x, hO S T x γ = incA D e * x i j := by
  refine ⟨ratW T S fun c b => star ((S.gram * Matrix.single j i e * T.gram⁻¹) b c), fun x => ?_⟩
  rw [← GlobalTheory.RatAnnih.sum_single (incA D) S.gram T.gram (GlobalTheory.LatVac.gram_det_isUnit S)
    (GlobalTheory.LatVac.gram_det_isUnit T) j i e x, hO]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  exact congrArg (fun t => incA D (S.gram⁻¹ a b) * t * incA D (T.gram c d) * x d a)
    ((GlobalTheory.DualPairCheck.cA_incA _).trans (congrArg (incA D) (star_star _)))

end Heis

set_option maxHeartbeats 1000000 in
open GlobalTheory.IdemModTwo in

theorem eq_zero_of_invariant_forms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ g, IsThetaFunO ψ S T g → (∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) → ∀ t, IsHalf e t → ℓ (heisO ψ S T t g) = 0) → g = 0 := by
  intro D ψ hψ S T e hε g hg H
  classical
  by_contra hg0
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  have he' := he.conj
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let sg : Fv D.host.F v →+ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := AddMonoidHom.ofMapSub (singleV D.host.F v) (singleV_sub D v)
  let ι : Fv D.host.F v →+ AF D.host.F := AddMonoidHom.mk' (fun y => pairA D.host.F 0 (sg y)) fun a b => by
    rw [map_add]; exact Prod.ext (add_zero _).symm rfl
  have hι : Continuous ι := Continuous.prodMk continuous_const (GlobalTheory.SplitAnnihilator.continuous_singleV D.host.F v)
  let G := Fin T.rank × Fin S.rank → Fv D.host.F v
  let J : G →+ WO S T := AddMonoidHom.mk' (fun y => Matrix.of fun i k => fj D (sg (y (i, k))) * cA D e) fun a b => by
    ext i k
    simp only [G, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul]
  have hJ : Continuous J := continuous_matrix fun i k =>
    ((IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))).comp
      (hι.comp (continuous_apply (i, k)))).mul continuous_const
  have hJe : ∀ y, cA D e • J y = J y := fun y => Matrix.ext fun i k => by
    show cA D e * (_ * cA D e) = _ * cA D e
    rw [mul_left_comm, he'.1]
  have hJinf : ∀ y, (J y).map (infPart D) = 0 := fun y => Matrix.ext fun i k => by
    show infPart D (_ * _) = 0
    have : infPart D (fj D (sg (y (i, k)))) = 0 := TensorProduct.zero_tmul _ _
    rw [map_mul, this, zero_mul]
  have hJs : ∀ u : WO S T, IsHalf (cA D e) u → ∃ y, J y = u := fun u hu => by
    choose y hy using fun p : Fin T.rank × Fin S.rank => he'.exists_scalar (u p.1 p.2)
    exact ⟨y, Matrix.ext fun i k => (hy (i, k)).symm.trans (hu i k)⟩
  let ρ : AddChar G (Module.End ℂ (WO S T → ℂ)) :=
    { toFun := fun y => heisL ψ S T (J y)
      map_zero_eq_one' := LinearMap.ext fun f => by
        rw [map_zero]; exact GlobalTheory.OrientedHeis.heisO_zero f
      map_add_eq_mul' := fun y y' => LinearMap.ext fun f => by
        have h0 : hO S T (J y) (J y') = 0 := by
          rw [← hJe y, ← hJe y', hO_smul_smul, he'.2.1, zero_mul]
        show heisO ψ S T _ f = heisO ψ S T _ (heisO ψ S T _ f)
        rw [GlobalTheory.OrientedHeis.heisO_heisO, symplOH, symplO, h0, mul_zero, map_zero, mul_zero,
          AddChar.map_zero_eq_one, one_smul, map_add] }
  have hlev : ∀ f, IsThetaFunO ψ S T f → ∃ U : AddSubgroup G, IsOpen (U : Set G) ∧ ∀ y ∈ U, ρ y f = f := fun f hf => by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U.comap J, hU.preimage hJ, fun y hy => h _ hy (hJinf y)⟩
  obtain ⟨U, hU, hUg⟩ := hlev g hg
  obtain ⟨χ, ℓ, hℓ, hχ, hℓχ⟩ := exists_char_form ρ g hg0 fun y => by
    obtain ⟨N, hN, h⟩ := exists_nsmul_mem_open U hU y
    exact ⟨N, hN, hUg _ h⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU 0 U.zero_mem
  choose a ha using fun p : Fin T.rank × Fin S.rank =>
    exists_eq_dilate (ψ.compAddMonoidHom ι) (hψ.1.1.comp hι) (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v)
      (χ.compAddMonoidHom (AddMonoidHom.single (fun _ => Fv D.host.F v) p)) hr fun x hx =>
        hχ _ (hUg _ (hball (mem_ball_zero_iff.2 (by
          show ‖(Pi.single p x : G)‖ < r
          rwa [Pi.norm_single]))))
  choose γ hγ using fun p : Fin T.rank × Fin S.rank => exists_hO_eq S T p.1 p.2 D.host.xi0⁻¹
  let t : WO S T := ∑ p, (fj D (sg (a p)) * e) • γ p
  have hte : IsHalf e (-t) := fun i k => by
    simp only [t, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by rw [← mul_assoc, mul_left_comm e, he.1]
  have hχt : ∀ y, χ y = ψ (symplO S T (J y) t) := fun y => by
    let B : WO S T →+ AF D.host.F := AddMonoidHom.mk' (symplO S T (J y)) ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 _)
    have h1 : ∀ p, B ((fj D (sg (a p)) * e) • γ p) = ι (a p * y p) := fun p => by
      show Algebra.trace _ _ (_ * hO S T _ _) = _
      rw [← one_smul (AE D) (J y), hO_smul_smul, hγ, one_mul, mul_left_comm, ← mul_assoc (incA D _), ← map_mul (incA D),
        mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, map_mul (cA D), cA_fj]
      exact GlobalTheory.SplitAnnihilator.trace_split he' _ _
    have h2 : symplO S T (J y) t = ∑ p, ι (a p * y p) := by
      rw [← Finset.sum_congr rfl fun p _ => h1 p, ← map_sum]
      rfl
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [h2]
    refine Finset.induction_on (motive := fun s => χ (∑ p ∈ s, Pi.single p (y p)) = ψ (∑ p ∈ s, ι (a p * y p)))
      Finset.univ (by simp) fun p s hp ih => ?_
    rw [Finset.sum_insert hp, Finset.sum_insert hp, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ih]
    exact congrArg (· * _) (ha p (y p))
  have hne : ∀ x, ψ x ≠ 0 := fun x h => by simpa [h] using hψ.1.2.1 x
  have hcomm : ∀ y f, ρ y (heisO ψ S T t f) = χ y • heisO ψ S T t (ρ y f) := fun y f => by
    rw [hχt]; exact heisO_comm _ _ _
  have h := H (ℓ.comp (heisL ψ S T t)) (fun u hu f hf => by
    obtain ⟨y, rfl⟩ := hJs u hu
    obtain ⟨U', hU', hUf⟩ := hlev f hf
    obtain ⟨N, hN, h⟩ := exists_nsmul_mem_open (U ⊓ U') (hU.inter hU') y
    have h1 := hℓχ y (heisO ψ S T t f) N hN (by rw [hcomm, hχ _ (hUg _ h.1), hUf _ h.2, one_smul])
    rw [hcomm, map_smul, smul_eq_mul] at h1
    exact mul_left_cancel₀ (hχt y ▸ hne _) h1) (-t) hte
  change ℓ (heisO ψ S T t (heisO ψ S T (-t) g)) = 0 at h
  rw [GlobalTheory.OrientedHeis.heisO_heisO, add_neg_cancel, GlobalTheory.OrientedHeis.heisO_zero, map_smul, smul_eq_mul] at h
  exact mul_ne_zero (hne _) hℓ h

end GlobalTheory.ThetaStalk

end
