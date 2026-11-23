import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SchrodingerModelSelfDualLatticeStatement

noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology

namespace GlobalTheory.CompanionTheory.StdLattice

theorem exists_nhds_invariant {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {f : G → ℂ}
    (hf : f ∈ SB G) : ∀ᶠ u in 𝓝 (0 : G), ∀ y ∈ tsupport f, f (y + u) = f y := by
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
  obtain ⟨hlc, hcs⟩ := hf'
  have hg : IsLocallyConstant (fun z : G × G => f (z.2 + z.1)) :=
    hlc.comp_continuous (continuous_snd.add continuous_fst)
  have hg2 : IsLocallyConstant (fun z : G × G => f z.2) := hlc.comp_continuous continuous_snd
  refine hcs.isCompact.eventually_forall_of_forall_eventually fun y _ => ?_
  filter_upwards [hg.eventually_eq (0, y), hg2.eventually_eq (0, y)] with z hz1 hz2
  exact hz1.trans ((congrArg f (add_zero y)).trans hz2.symm)

theorem mem_span_cosets {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {f : G → ℂ}
    (hf : HasCompactSupport f) (H : AddSubgroup G) (hH : IsOpen (H : Set G))
    (hinv : ∀ y ∈ tsupport f, ∀ u ∈ H, f (y + u) = f y) :
    f ∈ Submodule.span ℂ (Set.range fun a : G => fun x : G => (H : Set G).indicator (fun _ => (1 : ℂ)) (x + a)) := by
  classical
  haveI : DiscreteTopology (G ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hfin : ((QuotientAddGroup.mk : G → G ⧸ H) '' tsupport f).Finite :=
    (hf.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have key : ∀ c ∈ hfin.toFinset, ∀ x : G, (QuotientAddGroup.mk x : G ⧸ H) = c →
      f x = f (Quotient.out c) := by
    intro c hc x hx
    rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    have h1 : ∀ z : G, (QuotientAddGroup.mk z : G ⧸ H) = QuotientAddGroup.mk k → f z = f k := by
      intro z hz
      have hm : -k + z ∈ H := QuotientAddGroup.eq.1 hz.symm
      have h2 := hinv k hk (-k + z) hm
      rwa [add_neg_cancel_left] at h2
    rw [h1 x hx, h1 _ (QuotientAddGroup.out_eq' _)]
  have hfeq : f = ∑ c ∈ hfin.toFinset, f (Quotient.out c) •
      (fun x : G => (H : Set G).indicator (fun _ => (1 : ℂ)) (x + -Quotient.out c)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hind : ∀ c : G ⧸ H, (H : Set G).indicator (fun _ => (1 : ℂ)) (x + -Quotient.out c) =
        if c = (QuotientAddGroup.mk x : G ⧸ H) then 1 else 0 := by
      intro c
      have hiff : x + -Quotient.out c ∈ H ↔ c = (QuotientAddGroup.mk x : G ⧸ H) := by
        rw [add_comm, ← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
      simp only [Set.indicator_apply, SetLike.mem_coe, hiff]
    simp only [hind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with hx
    · exact key _ hx x rfl
    · apply image_eq_zero_of_notMem_tsupport
      intro hxK
      apply hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, hxK, rfl⟩
  rw [hfeq]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨-Quotient.out c, rfl⟩)

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]

def box (O : Subring R) (v : Rˣ) (κ : Type) : AddSubgroup (κ → R) where
  carrier := {x | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O}
  zero_mem' := fun i => by simp
  add_mem' := fun hx hy i => by simpa [mul_add] using O.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => by simpa using O.neg_mem (hx i)

def ind (O : Subring R) (κ : Type) : (κ → R) → ℂ := Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ)

variable [TopologicalSpace R]

theorem ind_mem_SB [T2Space R] {O : Subring R} (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R)) :
    ind O κ ∈ SB (κ → R) := by
  have hO : IsClosed (O : Set R) := hc.isClosed
  have hset : {x : κ → R | ∀ i, x i ∈ O} = Set.univ.pi (fun _ => (O : Set R)) := by
    ext x
    simp [Set.mem_pi]
  have hS : IsOpen {x : κ → R | ∀ i, x i ∈ O} := by
    rw [hset]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => ho)
  have hS' : IsClosed {x : κ → R | ∀ i, x i ∈ O} := by
    rw [hset]
    exact isClosed_set_pi (fun _ _ => hO)
  show IsLocallyConstant (ind O κ) ∧ HasCompactSupport (ind O κ)
  refine ⟨fun t => ?_, ?_⟩
  · show IsOpen (Set.indicator {x : κ → R | ∀ i, x i ∈ O} (fun _ => (1 : ℂ)) ⁻¹' t)
    rw [Set.indicator_preimage]
    exact ((IsLocallyConstant.const (1 : ℂ) t).inter hS).union
      ((IsLocallyConstant.const (0 : ℂ) t).sdiff hS')
  · exact HasCompactSupport.of_support_subset_isCompact
      (by rw [hset]; exact isCompact_univ_pi fun _ => hc) Set.support_indicator_subset

theorem psi_dot {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) {x y : κ → R} (hx : ∀ i, x i ∈ O)
    (hy : y ∈ box O u κ) : ψ (x ⬝ᵥ y) = 1 := by
  have hy' : ∀ i, ((u⁻¹ : Rˣ) : R) * y i ∈ O := hy
  have hxy : ∀ i, ψ (x i * y i) = 1 := fun i => by
    rw [mul_comm]
    exact (h.ann (y i)).2 (hy' i) (x i) (hx i)
  show ψ (∑ i, x i * y i) = 1
  exact Finset.sum_induction _ (fun z => ψ z = 1)
    (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, one_mul])
    (AddChar.map_zero_eq_one ψ) (fun i _ => hxy i)

variable [IsTopologicalRing R] [Invertible (2 : R)]

theorem mem_span_schr [LocallyCompactSpace R] [T2Space R] {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ}
    (h : GoodChar ψ O u) {f : (κ → R) → ℂ} (hf : f ∈ SB (κ → R)) :
    f ∈ Submodule.span ℂ (Set.range fun w => schr ψ w (ind O κ)) := by
  classical
  set V := Submodule.span ℂ (Set.range fun w => schr ψ w (ind O κ)) with hV
  have htr : ∀ g ∈ Submodule.span ℂ {g : (κ → R) → ℂ | ∃ y, g = schr ψ (0, y) (ind O κ)},
      ∀ a : κ → R, (fun x => g (x + a)) ∈ V := by
    intro g hg a
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨y, rfl⟩ := hg
      have heq : (fun x => schr ψ (0, y) (ind O κ) (x + a)) =
          ψ (a ⬝ᵥ y - ⅟2 * (a ⬝ᵥ y)) • schr ψ (a, y) (ind O κ) := by
        funext x
        simp only [schr, Pi.smul_apply, smul_eq_mul, add_zero, zero_dotProduct, mul_zero]
        rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct,
          show x ⬝ᵥ y + a ⬝ᵥ y = a ⬝ᵥ y - ⅟2 * (a ⬝ᵥ y) + (x ⬝ᵥ y + ⅟2 * (a ⬝ᵥ y)) by ring]
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, y), rfl⟩)
    | zero => exact V.zero_mem
    | add g1 g2 _ _ h1 h2 => exact V.add_mem h1 h2
    | smul c g _ h => exact V.smul_mem c h
  have hsb : IsLocallyConstant f ∧ HasCompactSupport f := hf
  have hA := exists_nhds_invariant hf
  rw [nhds_pi] at hA
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 hA
  have hU' : (⋂ i, t i) ∈ 𝓝 (0 : R) := Filter.iInter_mem.2 fun i => ht i
  obtain ⟨v, hv⟩ := h.basis _ (Filter.inter_mem hU' (h.isOpen.mem_nhds O.zero_mem))
  have hvO : ((v : Rˣ) : R) ∈ O := by
    have h1 := (hv 1 O.one_mem).2
    rwa [mul_one] at h1
  have hboxU : ∀ w ∈ box O v κ, ∀ y ∈ tsupport f, f (y + w) = f y := by
    intro w hw
    have hw' : ∀ i, ((v⁻¹ : Rˣ) : R) * w i ∈ O := hw
    have hwI : w ∈ (↑I : Set κ).pi t := fun i _ => by
      have h2 := (hv _ (hw' i)).1
      rw [Units.mul_inv_cancel_left] at h2
      exact Set.mem_iInter.1 h2 i
    exact hIt hwI
  have hbox_open : IsOpen ((box O v κ : AddSubgroup (κ → R)) : Set (κ → R)) := by
    show IsOpen {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O}
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      h.isOpen.preimage (continuous_const.mul (continuous_apply i))
  have hmem := mem_span_cosets hsb.2 (box O v κ) hbox_open (fun y hy w hw => hboxU w hw y hy)
  refine Submodule.span_le.2 ?_ hmem
  rintro _ ⟨a, rfl⟩
  exact htr _ (GlobalTheory.T.indicator_in_schrodinger_span ψ O u v h hvO) a

theorem exists_std : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R))), GoodChar ψ O u → IsModel ψ d μ S → ∃ (Γ : AddSubgroup W) (al : W → ℂ) (φ : SB (κ → R)), SelfDual S Γ ∧ IsSemi S al Γ ∧ Law S al Γ φ ∧ Cyclic S φ ∧ φ ≠ 0 := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ S h hM
  classical
  obtain ⟨hrho, -, hc⟩ := hM
  let Γ : AddSubgroup W :=
    AddSubgroup.comap d.e.toLinearMap.toAddMonoidHom ((box O 1 κ).prod (box O u κ))
  have hΓ : ∀ w, w ∈ Γ ↔ (∀ i, (d.e w).1 i ∈ O) ∧ (∀ i, ((u⁻¹ : Rˣ) : R) * (d.e w).2 i ∈ O) := by
    intro w
    show ((∀ i, ((1⁻¹ : Rˣ) : R) * (d.e w).1 i ∈ O) ∧ (∀ i, ((u⁻¹ : Rˣ) : R) * (d.e w).2 i ∈ O)) ↔ _
    simp only [inv_one, Units.val_one, one_mul]
  have hsq : ∀ z : R, ψ (⅟2 * z) ^ 2 = ψ z := by
    intro z
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, mul_invOf_self, one_mul]
  have hB1 : ∀ γ x, S.c γ x ^ 2 = ψ ((d.e γ).1 ⬝ᵥ (d.e x).2 - (d.e x).1 ⬝ᵥ (d.e γ).2) := by
    intro γ x
    rw [hc, hsq, d.form]
  refine ⟨Γ, fun x => ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))),
    ⟨ind O κ, ind_mem_SB h.compact h.isOpen⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx γ hγ
      obtain ⟨hxa, hxb⟩ := (hΓ x).1 hx
      obtain ⟨hga, hgb⟩ := (hΓ γ).1 hγ
      rw [hB1, AddChar.map_sub_eq_div, psi_dot h hga hxb, psi_dot h hxa hgb, div_one]
    · intro hall
      rw [hΓ]
      constructor
      · intro i
        have key : ∀ z ∈ O, ψ (((u : Rˣ) : R) * (d.e x).1 i * z) = 1 := by
          intro z hz
          have hγ : d.e.symm (0, Pi.single i (((u : Rˣ) : R) * z)) ∈ Γ := by
            rw [hΓ, LinearEquiv.apply_symm_apply]
            refine ⟨fun j => by simp, fun j => ?_⟩
            by_cases hj : j = i <;> simp [Pi.single_apply, hj, hz]
          have h3 := hall _ hγ
          rw [hB1, LinearEquiv.apply_symm_apply] at h3
          simp only [zero_dotProduct, dotProduct_single, zero_sub] at h3
          rw [AddChar.map_neg_eq_inv, inv_eq_one] at h3
          rw [mul_comm ((u : Rˣ) : R) _, mul_assoc]
          exact h3
        have h4 := (h.ann _).1 key
        rwa [← mul_assoc, Units.inv_mul, one_mul] at h4
      · intro i
        apply (h.ann _).1
        intro z hz
        have hγ : d.e.symm (Pi.single i z, 0) ∈ Γ := by
          rw [hΓ, LinearEquiv.apply_symm_apply]
          refine ⟨fun j => ?_, fun j => by simp⟩
          by_cases hj : j = i <;> simp [Pi.single_apply, hj, hz]
        have h3 := hall _ hγ
        rw [hB1, LinearEquiv.apply_symm_apply] at h3
        simp only [single_dotProduct, dotProduct_zero, sub_zero] at h3
        rw [mul_comm]
        exact h3
  · refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · obtain ⟨hxa, hxb⟩ := (hΓ x).1 hx
      have h2 : ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))) * ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))) = 1 := by
        rw [← pow_two, ← mul_neg, hsq, AddChar.map_neg_eq_inv, psi_dot h hxa hxb, inv_one]
      exact mul_self_eq_one_iff.1 h2
    · obtain ⟨hxa, hxb⟩ := (hΓ x).1 hx
      obtain ⟨hya, hyb⟩ := (hΓ y).1 hy
      show ψ (-(⅟2 * ((d.e (x + y)).1 ⬝ᵥ (d.e (x + y)).2))) =
        ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))) * ψ (-(⅟2 * ((d.e y).1 ⬝ᵥ (d.e y).2))) * S.c x y
      have h0 : ψ (-(2 * ⅟2 * ((d.e x).1 ⬝ᵥ (d.e y).2))) = 1 := by
        rw [mul_invOf_self, one_mul, AddChar.map_neg_eq_inv, psi_dot h hxa hyb, inv_one]
      have hX : -(⅟2 * ((d.e x + d.e y).1 ⬝ᵥ (d.e x + d.e y).2)) =
          (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2)) + -(⅟2 * ((d.e y).1 ⬝ᵥ (d.e y).2)) +
            ⅟2 * ((d.e x).1 ⬝ᵥ (d.e y).2 - (d.e y).1 ⬝ᵥ (d.e x).2)) +
          -(2 * ⅟2 * ((d.e x).1 ⬝ᵥ (d.e y).2)) := by
        simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
        ring
      rw [hc, d.form, map_add, hX, AddChar.map_add_eq_mul, h0, mul_one, AddChar.map_add_eq_mul,
        AddChar.map_add_eq_mul]
  · intro γ hγ
    obtain ⟨ha, hb⟩ := (hΓ γ).1 hγ
    apply Subtype.ext
    rw [hrho, Submodule.coe_smul]
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ind, Set.indicator_apply,
      Set.mem_setOf_eq, AddChar.map_neg_eq_inv, inv_inv]
    by_cases hx : ∀ i, x i ∈ O
    · have hxa : ∀ i, (x + (d.e γ).1) i ∈ O := fun i => O.add_mem (hx i) (ha i)
      rw [if_pos hxa, if_pos hx, AddChar.map_add_eq_mul, psi_dot h hx hb, one_mul]
    · have hxa : ¬ ∀ i, (x + (d.e γ).1) i ∈ O := fun h' => hx fun i => by
        simpa using O.sub_mem (h' i) (ha i)
      rw [if_neg hxa, if_neg hx, mul_zero, mul_zero]
  · show Submodule.span ℂ (Set.range fun x => S.rho x ⟨ind O κ, ind_mem_SB h.compact h.isOpen⟩) = ⊤
    rw [eq_top_iff]
    rintro g -
    have hg := mem_span_schr h g.2
    have hmap : Submodule.span ℂ (Set.range fun w => schr ψ w (ind O κ)) =
        (Submodule.span ℂ (Set.range fun x => S.rho x ⟨ind O κ, ind_mem_SB h.compact h.isOpen⟩)).map
          (GlobalTheory.WeilM.SB (κ → R)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext f
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨d.e.symm w, ?_⟩
        simp [hrho, GlobalTheory.WeilM.Darboux.rho]
      · rintro ⟨x, rfl⟩
        exact ⟨d.e x, by simp [hrho, GlobalTheory.WeilM.Darboux.rho]⟩
    rw [hmap] at hg
    obtain ⟨y, hy, hyg⟩ := Submodule.mem_map.1 hg
    have hyg' : y = g := Subtype.ext hyg
    rwa [← hyg']
  · intro h0
    have h5 := congrArg (fun g : GlobalTheory.WeilM.SB (κ → R) => (g : (κ → R) → ℂ) 0) h0
    simp [ind, Set.indicator_apply] at h5

end GlobalTheory.CompanionTheory.StdLattice
