import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero

noncomputable section

namespace GlobalTheory.LevelType

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SmGL.DepthZero ValuativeRel Matrix

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {p : ℕ}
  {n : Type} [Fintype n] [DecidableEq n]

def IsLift (g : GL n (ZMod p)) (h : GL n F) : Prop :=
  ∀ a b, valuation F (h.val a b - ((g.val a b).val : F)) < 1

def TypeVec {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n F) W)
    (z : MonoidAlgebra ℂ (GL n (ZMod p))) (v : W) : Prop :=
  (∀ h ∈ KOne F n, π h v = v) ∧
    ∃ ℓ : GL n (ZMod p) → GL n F, (∀ g, IsLift g (ℓ g)) ∧ (z.coeff.sum fun g c => c • π (ℓ g) v) ≠ 0

def CharLift (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) : Prop :=
  ∀ (a : (ZMod p)ˣ) (x : Fˣ), valuation F ((x : F) - ((a : ZMod p).val : F)) < 1 → χ x = θ a

def red [Fact p.Prime] (hp : resCard F = p) : 𝒪[F] →+* ZMod p :=
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  (ZMod.ringEquivOfPrime 𝓀[F] Fact.out (by rw [← hp, resCard, Nat.card_eq_fintype_card])).symm.toRingHom.comp
    (IsLocalRing.residue 𝒪[F])

variable [Fact p.Prime]

private theorem residue_eq_zero_iff_valuation_lt_one' (y : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] y = 0 ↔ valuation F (y : F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]

theorem red_eq_iff (hp : resCard F = p) (x y : 𝒪[F]) : red hp x = red hp y ↔ valuation F ((x : F) - y) < 1 := by
  have key : ∀ z : 𝒪[F], red hp z = 0 ↔ IsLocalRing.residue 𝒪[F] z = 0 := by
    intro z
    unfold red
    simp
  rw [← sub_eq_zero, ← map_sub, key, residue_eq_zero_iff_valuation_lt_one']
  push_cast
  exact Iff.rfl

theorem red_eq_iff_val (hp : resCard F = p) (x : 𝒪[F]) (a : ZMod p) :
    red hp x = a ↔ valuation F ((x : F) - (a.val : F)) < 1 := by
  have h1 : red hp ((a.val : ℕ) : 𝒪[F]) = a := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  rw [show red hp x = a ↔ red hp x = red hp ((a.val : ℕ) : 𝒪[F]) by rw [h1], red_eq_iff]
  push_cast
  exact Iff.rfl

theorem isUnit_of_red_ne_zero (hp : resCard F = p) {x : 𝒪[F]} (h : red hp x ≠ 0) : IsUnit x := by
  by_contra hu
  apply h
  rw [red_eq_iff_val]
  simpa using Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hu

private theorem valuation_le_one_of_near_integral {x c : F} (hcv : valuation F c ≤ 1) (h : valuation F (x - c) < 1) :
    valuation F x ≤ 1 := by
  have := (valuation F).map_add (x - c) c
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.le hcv)

private theorem valuation_natCast_le_one_inertia_eigenvalues (k : ℕ) : valuation F (k : F) ≤ 1 := by
  have := ((k : 𝒪[F])).2
  rw [Valuation.mem_integer_iff] at this
  simpa using this

private theorem exists_gl_lift_of_reduction (hp : resCard F = p) (M : Matrix n n 𝒪[F]) (g : GL n (ZMod p))
    (hM : ∀ a b, red hp (M a b) = g.val a b) :
    ∃ κ : GL n 𝒪[F], κ.val = M ∧ GeneralLinearGroup.map (red hp) κ = g := by
  have hmap : (red hp).mapMatrix M = g.val := by
    ext a b
    exact hM a b
  have hdet : IsUnit M.det := by
    apply isUnit_of_red_ne_zero hp
    rw [RingHom.map_det, hmap]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  refine ⟨Matrix.nonsingInvUnit M hdet, rfl, ?_⟩
  ext a b
  exact hM a b

theorem isLift_iff (hp : resCard F = p) (g : GL n (ZMod p)) (h : GL n F) :
    IsLift g h ↔ ∃ κ : GL n 𝒪[F], GeneralLinearGroup.map (algebraMap 𝒪[F] F) κ = h ∧
      GeneralLinearGroup.map (red hp) κ = g := by
  constructor
  · intro H
    have hint : ∀ a b, valuation F (h.val a b) ≤ 1 := fun a b =>
      valuation_le_one_of_near_integral (valuation_natCast_le_one_inertia_eigenvalues _) (H a b)
    let M : Matrix n n 𝒪[F] := Matrix.of fun a b => ⟨h.val a b, hint a b⟩
    obtain ⟨κ, hκ, hred⟩ := exists_gl_lift_of_reduction hp M g (fun a b => (red_eq_iff_val hp _ _).2 (H a b))
    refine ⟨κ, ?_, hred⟩
    ext a b
    change ((κ.val a b : 𝒪[F]) : F) = h.val a b
    rw [hκ]
    rfl
  · rintro ⟨κ, hκ, hred⟩ a b
    have e1 : (GeneralLinearGroup.map (red hp) κ).val a b = g.val a b := by rw [hred]
    change red hp (κ.val a b) = g.val a b at e1
    rw [← hκ]
    exact (red_eq_iff_val hp _ _).1 e1

theorem IsLift.mem_KO (hp : resCard F = p) {g : GL n (ZMod p)} {h : GL n F} (H : IsLift g h) : h ∈ KO F n := by
  obtain ⟨κ, hκ, -⟩ := (isLift_iff hp g h).1 H
  exact ⟨κ, hκ⟩

theorem exists_isLift_of_mem_KO (hp : resCard F = p) {h : GL n F} (H : h ∈ KO F n) : ∃ g : GL n (ZMod p), IsLift g h := by
  obtain ⟨κ, rfl⟩ := H
  exact ⟨GeneralLinearGroup.map (red hp) κ, (isLift_iff hp _ _).2 ⟨κ, rfl, rfl⟩⟩

theorem IsLift.mul (hp : resCard F = p) {g g' : GL n (ZMod p)} {h h' : GL n F} (H : IsLift g h) (H' : IsLift g' h') :
    IsLift (g * g') (h * h') := by
  obtain ⟨κ, hκ, hr⟩ := (isLift_iff hp g h).1 H
  obtain ⟨κ', hκ', hr'⟩ := (isLift_iff hp g' h').1 H'
  exact (isLift_iff hp _ _).2 ⟨κ * κ', by rw [map_mul, hκ, hκ'], by rw [map_mul, hr, hr']⟩

theorem IsLift.inv (hp : resCard F = p) {g : GL n (ZMod p)} {h : GL n F} (H : IsLift g h) : IsLift g⁻¹ h⁻¹ := by
  obtain ⟨κ, hκ, hr⟩ := (isLift_iff hp g h).1 H
  exact (isLift_iff hp _ _).2 ⟨κ⁻¹, by rw [map_inv, hκ], by rw [map_inv, hr]⟩

private theorem coe_one_matrix_integers_apply (a b : n) :
    (((1 : Matrix n n 𝒪[F]) a b : 𝒪[F]) : F) = (1 : Matrix n n F) a b := by
  by_cases hab : a = b
  · subst hab
    simp
  · simp [Matrix.one_apply_ne hab]

private theorem valuation_one_matrix_apply_le_one (a b : n) : valuation F ((1 : Matrix n n F) a b) ≤ 1 := by
  rw [← coe_one_matrix_integers_apply a b]
  exact ((1 : Matrix n n 𝒪[F]) a b).2

private theorem residue_one_matrix_apply (a b : n) :
    IsLocalRing.residue 𝒪[F] ((1 : Matrix n n 𝒪[F]) a b) = (1 : Matrix n n 𝓀[F]) a b := by
  by_cases hab : a = b
  · subst hab
    simp
  · simp [Matrix.one_apply_ne hab]

theorem isLift_one_iff (h : GL n F) : IsLift (1 : GL n (ZMod p)) h ↔ h ∈ KOne F n := by
  have hδ : ∀ a b : n, ((((1 : GL n (ZMod p)).val a b).val : ℕ) : F) = (1 : Matrix n n F) a b := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp [ZMod.val_one]
    · simp [Matrix.one_apply_ne hab]
  have hfix : IsLift (1 : GL n (ZMod p)) h ↔
      ∀ a b, valuation F (h.val a b - (1 : Matrix n n F) a b) < 1 := by
    unfold IsLift
    simp only [hδ]
  rw [hfix]
  constructor
  · intro H
    have hint : ∀ a b, valuation F (h.val a b) ≤ 1 := fun a b => valuation_le_one_of_near_integral (valuation_one_matrix_apply_le_one a b) (H a b)
    let M : Matrix n n 𝒪[F] := Matrix.of fun a b => ⟨h.val a b, hint a b⟩
    have hres : (IsLocalRing.residue 𝒪[F]).mapMatrix M = 1 := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← residue_one_matrix_apply a b, ← sub_eq_zero, ← map_sub,
        residue_eq_zero_iff_valuation_lt_one']
      have h2 : ((M a b - (1 : Matrix n n 𝒪[F]) a b : 𝒪[F]) : F) = h.val a b - (1 : Matrix n n F) a b := by
        rw [← coe_one_matrix_integers_apply a b]
        rfl
      rw [h2]
      exact H a b
    have hdet : IsUnit M.det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, Matrix.det_one]
      exact one_ne_zero
    refine ⟨Matrix.nonsingInvUnit M hdet, ?_, ?_⟩
    · change GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) _ = 1
      ext a b
      exact congrFun (congrFun hres a) b
    · ext a b
      rfl
  · rintro ⟨κ, hκ, rfl⟩ a b
    replace hκ : GeneralLinearGroup.map (IsLocalRing.residue 𝒪[F]) κ = 1 := hκ
    have e1 : IsLocalRing.residue 𝒪[F] (κ.val a b) = (1 : Matrix n n 𝓀[F]) a b := by
      have := congrArg (fun u : GL n 𝓀[F] => u.val a b) hκ
      exact this
    rw [← residue_one_matrix_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff_valuation_lt_one'] at e1
    have h2 : ((κ.val a b - (1 : Matrix n n 𝒪[F]) a b : 𝒪[F]) : F) =
        (GeneralLinearGroup.map (algebraMap 𝒪[F] F) κ).val a b - (1 : Matrix n n F) a b := by
      rw [← coe_one_matrix_integers_apply a b]
      rfl
    rw [← h2]
    exact e1

theorem IsLift.inv_mul_mem (hp : resCard F = p) {g : GL n (ZMod p)} {h h' : GL n F} (H : IsLift g h) (H' : IsLift g h') :
    h⁻¹ * h' ∈ KOne F n := by
  have H2 := (H.inv hp).mul hp H'
  rw [inv_mul_cancel] at H2
  exact (isLift_one_iff _).1 H2

theorem IsLift.apply_eq (hp : resCard F = p) {W : Type} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL n F) W}
    {v : W} (hv : ∀ h ∈ KOne F n, π h v = v) {g : GL n (ZMod p)} {h h' : GL n F} (H : IsLift g h) (H' : IsLift g h') :
    π h v = π h' v := by
  have hk := H.inv_mul_mem hp H'
  calc π h v = π h (π (h⁻¹ * h') v) := by rw [hv _ hk]
    _ = π (h * (h⁻¹ * h')) v := by rw [map_mul π h (h⁻¹ * h'), Module.End.mul_apply]
    _ = π h' v := by rw [mul_inv_cancel_left]

theorem exists_canon_lift (hp : resCard F = p) (g : GL n (ZMod p)) :
    ∃ h : GL n F, (∀ a b, h.val a b = ((g.val a b).val : F)) ∧ IsLift g h := by
  let M : Matrix n n 𝒪[F] := Matrix.of fun a b => (((g.val a b).val : ℕ) : 𝒪[F])
  obtain ⟨κ, hκ, -⟩ := exists_gl_lift_of_reduction hp M g (fun a b => by
    change red hp (((g.val a b).val : ℕ) : 𝒪[F]) = g.val a b
    rw [map_natCast, ZMod.natCast_zmod_val])
  have hvl1 : ∀ a b, (GeneralLinearGroup.map (algebraMap 𝒪[F] F) κ).val a b = ((g.val a b).val : F) := by
    intro a b
    change ((κ.val a b : 𝒪[F]) : F) = _
    rw [hκ]
    exact map_natCast (algebraMap 𝒪[F] F) _
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[F] F) κ, hvl1, fun a b => ?_⟩
  rw [hvl1, sub_self, map_zero]
  exact zero_lt_one

theorem CharLift.det (hp : resCard F = p) {θ : (ZMod p)ˣ →* ℂˣ} {χ : Fˣ →* ℂˣ} (hθ : CharLift θ χ) {g : GL n (ZMod p)}
    {h : GL n F} (H : IsLift g h) : χ (GeneralLinearGroup.det h) = θ (GeneralLinearGroup.det g) := by
  obtain ⟨κ, rfl, hr⟩ := (isLift_iff hp g h).1 H
  apply hθ
  have e1 : red hp κ.val.det = ((GeneralLinearGroup.det g : (ZMod p)ˣ) : ZMod p) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← hr, RingHom.map_det]
    rfl
  have e3 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[F] F) κ) : Fˣ) : F) =
      ((κ.val.det : 𝒪[F]) : F) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (algebraMap 𝒪[F] F) κ.val).symm
  rw [e3]
  exact (red_eq_iff_val hp _ _).1 e1

private theorem image_compact_orbit_finite_of_open_stabilizer {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (s : W) (hs : IsOpen {g | ρ g s = s})
    {K : Set G} (hK : IsCompact K) : ((fun g => ρ g s) '' K).Finite := by
  letI : TopologicalSpace W := ⊥
  haveI : DiscreteTopology W := ⟨rfl⟩
  apply IsCompact.finite_of_discrete
  apply hK.image
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg
  refine ⟨(fun k => g⁻¹ * k) ⁻¹' {k | ρ k s = s}, ?_, hs.preimage (continuous_const.mul continuous_id), ?_⟩
  · intro k hk
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change ρ (g⁻¹ * k) s = s at hk
    rw [← hg, show k = g * (g⁻¹ * k) by group, map_mul, Module.End.mul_apply, hk]
  · change ρ (g⁻¹ * g) s = s
    rw [inv_mul_cancel, map_one, Module.End.one_apply]

private theorem isOpen_valuation_sub_lt_one (c : F) : IsOpen {x : F | valuation F (x - c) < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨1, fun z hz => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_one] at hz hx ⊢
  have := (valuation F).map_add (z - x) (x - c)
  rw [sub_add_sub_cancel] at this
  exact this.trans_lt (max_lt hz hx)

private theorem isCompact_KOne' (p : ℕ) [Fact p.Prime] :
    IsCompact (KOne F n : Set (GL n F)) := by
  haveI : CompactSpace (Matrix n n 𝒪[F]) := inferInstanceAs (CompactSpace (n → n → 𝒪[F]))
  haveI : T1Space (Matrix n n 𝒪[F]) := inferInstanceAs (T1Space (n → n → 𝒪[F]))
  have hcm : Continuous (GeneralLinearGroup.map (n := n) (algebraMap 𝒪[F] F)) := by
    have hcs : Continuous (algebraMap 𝒪[F] F) := continuous_subtype_val
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · change Continuous fun κ : GL n 𝒪[F] => (κ.val).map (algebraMap 𝒪[F] F)
      exact Continuous.matrix_map Units.continuous_val hcs
    · change Continuous fun κ : GL n 𝒪[F] => ((κ⁻¹ : GL n 𝒪[F]).val).map (algebraMap 𝒪[F] F)
      exact Continuous.matrix_map Units.continuous_coe_inv hcs
  have hKO : IsCompact (KO F n : Set (GL n F)) := by
    rw [KO, MonoidHom.coe_range]
    exact isCompact_range hcm
  have hset : (KOne F n : Set (GL n F)) = {h | IsLift (1 : GL n (ZMod p)) h} := by
    ext h
    exact (isLift_one_iff h).symm
  have hopen : IsOpen (KOne F n : Set (GL n F)) := by
    rw [hset]
    simp only [IsLift, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact (isOpen_valuation_sub_lt_one _).preimage (Units.continuous_val.matrix_elem a b)
  have hsub : (KOne F n : Set (GL n F)) ⊆ KO F n := by
    rintro h ⟨κ, -, rfl⟩
    exact ⟨κ, rfl⟩
  exact hKO.of_isClosed_subset ((KOne F n).isClosed_of_isOpen hopen) hsub

theorem TypeVec.up {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ (GL n F) W} {π : Representation ℂ (GL n F) V} (hπ : IsSmooth π) (h : IsSubquotient τ π)
    {z : MonoidAlgebra ℂ (GL n (ZMod p))} {y : W} (hy : TypeVec τ z y) : ∃ x, TypeVec π z x := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨hyfix, ℓ, hℓ, hyne⟩ := hy
  obtain ⟨s, hs⟩ := hf y
  let ρS := S.toRepresentation
  have hopen : IsOpen {g : GL n F | ρS g s = s} := by
    convert hπ (s : V) using 1
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hfin := image_compact_orbit_finite_of_open_stabilizer ρS s hopen (isCompact_KOne' p)
  let O := hfin.toFinset
  have hmemO : ∀ u, u ∈ O ↔ ∃ g ∈ (KOne F n : Set (GL n F)), ρS g s = u := by
    intro u
    simp [O]
  let x' : S.toSubmodule := ∑ u ∈ O, u
  have hx'fix : ∀ k ∈ KOne F n, ρS k x' = x' := by
    intro k hk
    simp only [x', map_sum]
    refine Finset.sum_nbij' (fun u => ρS k u) (fun u => ρS k⁻¹ u) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro u hu
      obtain ⟨g, hg, rfl⟩ := (hmemO u).1 hu
      exact (hmemO _).2 ⟨k * g, (KOne F n).mul_mem hk hg, by rw [map_mul]; rfl⟩
    · intro u hu
      obtain ⟨g, hg, rfl⟩ := (hmemO u).1 hu
      exact (hmemO _).2 ⟨k⁻¹ * g, (KOne F n).mul_mem ((KOne F n).inv_mem hk) hg, by rw [map_mul]; rfl⟩
    · intro u _
      change (ρS k⁻¹ * ρS k) u = u
      rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · intro u _
      change (ρS k * ρS k⁻¹) u = u
      rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hfx' : f x' = (O.card : ℂ) • y := by
    simp only [x', map_sum]
    have : ∀ u ∈ O, f u = y := by
      intro u hu
      obtain ⟨g, hg, rfl⟩ := (hmemO u).1 hu
      rw [f.isIntertwining, hs, hyfix g hg]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hcard : (O.card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.2 ⟨s, (hmemO s).2 ⟨1, (KOne F n).one_mem, by rw [map_one]; rfl⟩⟩
  refine ⟨(x' : V), fun k hk => ?_, ℓ, hℓ, ?_⟩
  · exact congrArg Subtype.val (hx'fix k hk)
  · intro h0
    let T : S.toSubmodule := z.coeff.sum fun g c => c • ρS (ℓ g) x'
    have hT : T = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_zero, ← h0]
      simp only [T, Finsupp.sum]
      rw [Submodule.coe_sum]
      rfl
    have hfT : f T = (O.card : ℂ) • z.coeff.sum fun g c => c • τ (ℓ g) y := by
      simp only [T, Finsupp.sum, map_sum, map_smul, f.isIntertwining, hfx', Finset.smul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [f.isIntertwining, hfx', map_smul]
      exact smul_comm _ _ _
    rw [hT, map_zero] at hfT
    exact hyne ((smul_eq_zero.1 hfT.symm).resolve_left hcard)

theorem TypeVec.factor {α : Type} [Fintype α] [DecidableEq α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α)
    {z : MonoidAlgebra ℂ (GL (m a) (ZMod p))} {y : PiTensorProduct ℂ X}
    (hy : TypeVec ((piTensor ρ).comp (MonoidHom.mulSingle (fun j => GL (m j) F) a)) z y) : ∃ x, TypeVec (ρ a) z x := by
  obtain ⟨hfix, ℓ, hℓ, hne⟩ := hy
  classical
  let B : ∀ b, Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ (X b)) ℂ (X b) := fun b => Module.Basis.ofVectorSpace ℂ (X b)
  set w := z.coeff.sum fun g c =>
    c • ((piTensor ρ).comp (MonoidHom.mulSingle (fun j => GL (m j) F) a)) (ℓ g) y with hw
  obtain ⟨q, hq⟩ : ∃ q, (Basis.piTensorProduct B).repr w q ≠ 0 := by
    by_contra hq0
    push_neg at hq0
    apply hne
    apply (Basis.piTensorProduct B).repr.injective
    ext r
    simp [hq0 r]
  let Φm : MultilinearMap ℂ X (X a) :=
    { toFun := fun x => (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (x b)) • x a
      map_update_add' := by
        intro _ x i u v
        by_cases hi : i = a
        · subst hi
          have hP : ∀ u' : X i, (∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (Function.update x i u' b)) =
              ∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (x b) := by
            intro u'
            apply Finset.prod_congr rfl
            intro b hb
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
          have key : (∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (Function.update x i (u + v) b)) • Function.update x i (u + v) i = (∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (Function.update x i (u) b)) • Function.update x i (u) i + (∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (Function.update x i (v) b)) • Function.update x i (v) i := by
            rw [hP, hP, hP, Function.update_self, Function.update_self, Function.update_self, smul_add]
          convert key
        · have hia : i ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩
          have hR : ∀ u' : X i, (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (Function.update x i u' b)) =
              (B i).coord (q i) u' * ∏ b ∈ (Finset.univ.erase a).erase i, (B b).coord (q b) (x b) := by
            intro u'
            rw [← Finset.mul_prod_erase _ _ hia, Function.update_self]
            congr 1
            apply Finset.prod_congr rfl
            intro b hb
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
          have hxa : ∀ u' : X i, Function.update x i u' a = x a := fun u' => Function.update_of_ne (Ne.symm hi) _ _
          have key : (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (Function.update x i (u + v) b)) • Function.update x i (u + v) a = (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (Function.update x i (u) b)) • Function.update x i (u) a + (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (Function.update x i (v) b)) • Function.update x i (v) a := by
            rw [hR, hR, hR, hxa, hxa, hxa, map_add, add_mul, add_smul]
          convert key
      map_update_smul' := by
        intro _ x i c u
        by_cases hi : i = a
        · subst hi
          have hP : ∀ u' : X i, (∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (Function.update x i u' b)) =
              ∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (x b) := by
            intro u'
            apply Finset.prod_congr rfl
            intro b hb
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
          have key : (∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (Function.update x i (c • u) b)) • Function.update x i (c • u) i = c • (∏ b ∈ Finset.univ.erase i, (B b).coord (q b) (Function.update x i (u) b)) • Function.update x i (u) i := by
            rw [hP, hP, Function.update_self, Function.update_self, smul_comm]
          convert key
        · have hia : i ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩
          have hR : ∀ u' : X i, (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (Function.update x i u' b)) =
              (B i).coord (q i) u' * ∏ b ∈ (Finset.univ.erase a).erase i, (B b).coord (q b) (x b) := by
            intro u'
            rw [← Finset.mul_prod_erase _ _ hia, Function.update_self]
            congr 1
            apply Finset.prod_congr rfl
            intro b hb
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
          have hxa : ∀ u' : X i, Function.update x i u' a = x a := fun u' => Function.update_of_ne (Ne.symm hi) _ _
          have key : (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (Function.update x i (c • u) b)) • Function.update x i (c • u) a = c • (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (Function.update x i (u) b)) • Function.update x i (u) a := by
            rw [hR, hR, hxa, hxa, map_smul, smul_eq_mul, mul_assoc, mul_smul]
          convert key }
  let Φ : (PiTensorProduct ℂ X) →ₗ[ℂ] X a := PiTensorProduct.lift Φm
  have hΦt : ∀ x : ∀ b, X b, Φ (PiTensorProduct.tprod ℂ x) =
      (∏ b ∈ Finset.univ.erase a, (B b).coord (q b) (x b)) • x a := by
    intro x
    simp only [Φ, PiTensorProduct.lift.tprod]
    rfl
  have hequiv : ∀ (k : GL (m a) F) (t : PiTensorProduct ℂ X),
      Φ (((piTensor ρ).comp (MonoidHom.mulSingle (fun j => GL (m j) F) a)) k t) = ρ a k (Φ t) := by
    intro k t
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply, map_smul, piTensor_tprod, hΦt]
      congr 1
      rw [Pi.mulSingle_eq_same]
      congr 1
      apply Finset.prod_congr rfl
      intro b hb
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb), map_one, Module.End.one_apply]
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hcoord : ∀ t : PiTensorProduct ℂ X, (B a).coord (q a) (Φ t) = (Basis.piTensorProduct B).repr t q := by
    intro t
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, map_smul, hΦt, map_smul, map_smul, Finsupp.smul_apply, Basis.piTensorProduct_repr_tprod_apply]
      simp only [Finsupp.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, Finsupp.add_apply]
  refine ⟨Φ y, fun k hk => ?_, ℓ, hℓ, ?_⟩
  · rw [← hequiv, hfix k hk]
  · intro h0
    apply hq
    rw [← hcoord]
    have : Φ w = z.coeff.sum fun g c => c • ρ a (ℓ g) (Φ y) := by
      simp only [hw, Finsupp.sum, map_sum, map_smul, hequiv]
    rw [this, h0, map_zero]

end Local

section Finite

theorem exists_eigen_of_map {G V Y : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (H : Subgroup G) (ψ : G →* ℂˣ) (Λ : V →ₗ[ℂ] Y) (h0 : Λ ≠ 0)
    (h : ∀ x ∈ H, ∀ w, Λ (ρ x w) = (ψ x : ℂ) • Λ w) : ∃ v, v ≠ 0 ∧ ∀ x ∈ H, ρ x v = (ψ x : ℂ) • v := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨w, hw⟩ : ∃ w, Λ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (LinearMap.ext hcon)
  refine ⟨∑ x : H, ((ψ x : ℂ))⁻¹ • ρ x w, ?_, ?_⟩
  · intro hP
    apply hw
    have hΛ : Λ (∑ x : H, ((ψ x : ℂ))⁻¹ • ρ x w) = (Fintype.card H : ℂ) • Λ w := by
      rw [map_sum]
      have : ∀ x : H, Λ (((ψ x : ℂ))⁻¹ • ρ x w) = Λ w := by
        intro x
        rw [map_smul, h x x.2, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
      simp only [this, Finset.sum_const, Finset.card_univ]
      rw [Nat.cast_smul_eq_nsmul]
    rw [hP, map_zero] at hΛ
    exact (smul_eq_zero.1 hΛ.symm).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · intro y hy
    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨y, hy⟩ : H)) _ _ ?_
    intro x
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Units.val_mul, map_smul,
      Module.End.mul_apply, smul_smul]
    congr 1
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

variable {p : ℕ} {n α : Type} [Fintype n] [DecidableEq n] [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)]

def ParVec {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL n (ZMod p)) V) (e : (Σ a, m a) ≃ n) (a : α)
    (θ : (ZMod p)ˣ →* ℂˣ) (v : V) : Prop :=
  ∀ x : parab (ZMod p) e, (∀ b, b ≠ a → leviProj (ZMod p) e x b = 1) →
    ρ x v = (θ (GeneralLinearGroup.det (x : GL n (ZMod p))) : ℂ) • v

def StdBlock {r : ℕ} (a : ℕ) (x : GL (Fin r) (ZMod p)) : Prop :=
  ∀ i j : Fin r, ¬ (i.val ≤ a ∧ a ≤ j.val) → x.val i j = if i = j then 1 else 0

def StdVec {r : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) V) (a : ℕ)
    (θ : (ZMod p)ˣ →* ℂˣ) (v : V) : Prop :=
  ∀ x : GL (Fin r) (ZMod p), StdBlock a x → ρ x v = (θ (GeneralLinearGroup.det x) : ℂ) • v

open Classical in

def stdTrace [Fact p.Prime] {r : ℕ} (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ψ : GL (Fin r) (ZMod p) → ℂ) : ℂ :=
  ∑ x : GL (Fin r) (ZMod p), if StdBlock a x then (((θ (GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ x else 0

end Finite

def reix (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    GL m R →* GL n R :=
  Units.map (Matrix.reindexAlgEquiv R R e).toRingEquiv.toMonoidHom

theorem val_reix (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m R) (i j : n) : (reix R e g).val i j = g.val (e.symm i) (e.symm j) := rfl

end GlobalTheory.LevelType

end
