import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualSelmerClassFromCoeffsKilledByMulStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.DualClass

section Algebra

noncomputable def chr {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n) (y' : B') :
    AddChar B ℂ := (ZMod.stdAddChar (N := n)).compAddMonoidHom (P.flip y')

theorem chr_injective {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n)
    (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Function.Injective (chr P) := by
  intro u v huv
  refine sub_eq_zero.1 (h _ fun y => ?_)
  rw [map_sub, sub_eq_zero]
  exact ZMod.injective_stdAddChar (DFunLike.congr_fun huv y)

theorem card_addChar (B : Type) [AddCommGroup B] [Finite B] : Nat.card (AddChar B ℂ) = Nat.card B := by
  classical
  have := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card (α := AddChar B ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]

theorem card_le_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Nat.card B' ≤ Nat.card B := by
  rw [← card_addChar B]
  exact Nat.card_le_card_of_injective _ (chr_injective P h)

theorem left_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) (hc : Nat.card B ≤ Nat.card B') (y : B)
    (hy : ∀ y', P y y' = 0) : y = 0 := by
  have hb := (chr_injective P h).bijective_of_nat_card_le (by rw [card_addChar]; exact hc)
  refine AddChar.forall_apply_eq_zero.1 fun ψ => ?_
  obtain ⟨y', rfl⟩ := hb.2 ψ
  change ZMod.stdAddChar (P y y') = 1
  rw [hy, AddChar.map_zero_eq_one]

variable {A : Type} [CommRing A]

theorem card_ker_eq_coker {M : Type} [AddCommGroup M] [Module A M] [Finite M] (f : M →ₗ[A] M) :
    Nat.card (LinearMap.ker f) = Nat.card (M ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h3 : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right h3 ?_
  rw [← h1, mul_comm, ← h2]

abbrev Quo (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Type := Y ⧸ LinearMap.range (LinearMap.lsmul A Y c)

abbrev Tor (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Submodule A Y := LinearMap.ker (LinearMap.lsmul A Y c)

variable {n : ℕ} {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y']

theorem exists_induced (β : Y →+ Y' →+ ZMod n) (hβ : Bal A β) (c : A) :
    ∃ β₂ : Quo c Y →+ Tor c Y' →+ ZMod n, ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1 := by
  let P : Y →+ Tor c Y' →+ ZMod n := (β.flip.comp (Tor c Y').subtype.toAddMonoidHom).flip
  refine ⟨QuotientAddGroup.lift (LinearMap.range (LinearMap.lsmul A Y c)).toAddSubgroup P ?_, fun y y' => rfl⟩
  rintro _ ⟨y, rfl⟩
  refine AddMonoidHom.mem_ker.2 (AddMonoidHom.ext fun y' => ?_)
  change β (c • y) y'.1 = 0
  have h : c • y'.1 = 0 := y'.2
  rw [hβ, h, map_zero]

theorem perf_induced [NeZero n] [Finite Y] [Finite Y'] (β : Y →+ Y' →+ ZMod n) (hβ : Perf A β) (c : A)
    (β₂ : Quo c Y →+ Tor c Y' →+ ZMod n) (h : ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1) : Perf A β₂ := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have : Finite (Quo c Y') := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hr : ∀ y', (∀ y, β₂ y y' = 0) → y' = 0 := fun y' hy =>
    Subtype.ext (hβ.2.2 _ fun y => by rw [← h, hy])
  refine ⟨fun a y y' => ?_, left_of_right β₂ hr ?_, hr⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, h, h, hβ.1]
    rfl
  · obtain ⟨γ, hγ⟩ := exists_induced (A := A) β.flip (fun a y' y => (hβ.1 a y y').symm) c
    rw [← card_ker_eq_coker, card_ker_eq_coker (LinearMap.lsmul A Y' c)]
    exact card_le_of_right γ fun y hy => Subtype.ext (hβ.2.1 _ fun y' => by
      have := hy (Submodule.Quotient.mk y')
      rwa [hγ] at this)

theorem smul_mem_range [Finite Y] {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : Nat.card (LinearMap.ker (matAct (M := Y) Φ)) ≤ Nat.card (LinearMap.ker (matAct (M := Quo c Y) Φ)))
    (w : Fin a → Y) : c • w ∈ LinearMap.range (matAct (M := Y) Φ) := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [card_ker_eq_coker, card_ker_eq_coker] at h
  let f : (Fin a → Y) →ₗ[A] (Fin a → Quo c Y) := (Submodule.mkQ _).compLeft (Fin a)
  have hf : LinearMap.range (matAct (M := Y) Φ) ≤ (LinearMap.range (matAct (M := Quo c Y) Φ)).comap f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨f x, funext fun b => ?_⟩
    simp [f, matAct, map_sum]
  have hs : Function.Surjective (Submodule.mapQ _ _ f hf) := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    choose u hu using fun b => Submodule.Quotient.mk_surjective _ (x b)
    exact ⟨Submodule.Quotient.mk u, by rw [Submodule.mapQ_apply]; exact congrArg _ (funext hu)⟩
  have : Finite ((Fin a → Y) ⧸ LinearMap.range (matAct (M := Y) Φ)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hb := hs.bijective_of_nat_card_le h
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hb.1
  rw [map_zero, Submodule.mapQ_apply]
  have h0 : f (c • w) = 0 := funext fun b => (Submodule.Quotient.mk_eq_zero _).2 ⟨w b, rfl⟩
  rw [h0, Submodule.Quotient.mk_zero]

theorem mul_eq_zero_of_range (β : Y →+ A →+ ZMod n) (hβ : Perf A β) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : ∀ w : Fin a → Y, c • w ∈ LinearMap.range (matAct (M := Y) Φ)) (y₀ : Fin a → A) (h0 : Matrix.vecMul y₀ Φ = 0)
    (j : Fin a) : c * y₀ j = 0 := by
  refine hβ.2.2 _ fun w => ?_
  obtain ⟨x, hx⟩ := h (Pi.single j w)
  have h1 : ∑ b, y₀ b • matAct Φ x b = 0 := by
    change ∑ b, y₀ b • ∑ k, Φ b k • x k = 0
    simp only [Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h2 : ∑ b, y₀ b * Φ b k = 0 := congrFun h0 k
    rw [← Finset.sum_smul, h2, zero_smul]
  rw [hx, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)] at h1
  have h3 : (c * y₀ j) • w = 0 := by
    rw [mul_comm, mul_smul]
    simpa using h1
  have h4 := hβ.1 (c * y₀ j) w 1
  rw [h3, smul_eq_mul, mul_one] at h4
  rw [← h4]
  simp

end Algebra

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host))

theorem card_selOn {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (Z : GE N → Matrix (Fin D.R.r) (Fin a) A)
    (h : Univ bkP i s κ Q Φ Z) (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] :
    Nat.card (LinearMap.ker (matAct (M := Y) Φ)) = Nat.card (selOn bkP i (Tgl i s) κ Y Q) := by
  obtain ⟨h1, h2, h3⟩ := h Y
  choose z hz hz' using fun x : LinearMap.ker (matAct (M := Y) Φ) => h1 x.1 x.2
  refine Nat.card_eq_of_bijective (fun x => ⟨_, hz' x⟩) ⟨fun x x' hx => ?_, fun q => ?_⟩
  · have e := (Submodule.Quotient.eq _).1 (congrArg Subtype.val hx)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 e
    refine sub_eq_zero.1 (Subtype.ext (h2 _ (x - x').2 ⟨m, fun g => ?_⟩))
    rw [← hm g]
    change _ = (z x).1 g - (z x').1 g
    rw [hz, hz]
    funext b
    simp [rect, smul_sub]
  · obtain ⟨q, hq⟩ := q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx, m, hm⟩ := h3 y.1 ⟨y, rfl, hq⟩
    refine ⟨⟨x, hx⟩, Subtype.ext (Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)))⟩
    rw [← hm g]
    change y.1 g - (z ⟨x, hx⟩).1 g = _
    rw [hz]

omit [Algebra (X.O0 i) A] in

theorem card_invariants_torsion_submodule {Γ O : Type} [Group Γ] [CommRing O] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ)
    (U : Subgroup Γ) (Y' : Type) [AddCommGroup Y'] [Module A Y'] (c : A)
    (h : ∀ m, (∀ g ∈ U, repOn ρ κ Y' g m = m) → c • m = 0) :
    Nat.card (H0 ((repOn ρ κ (Tor c Y')).comp U.subtype)) = Nat.card (H0 ((repOn ρ κ Y').comp U.subtype)) := by
  refine Nat.card_eq_of_bijective (fun m => ⟨(Tor c Y').subtype.compLeft (Fin r) m.1, fun g => ?_⟩)
    ⟨fun m m' hm => ?_, fun m => ?_⟩
  · exact (repOn_map ρ κ (Tor c Y').subtype g.1 m.1).symm.trans (congrArg _ (m.2 g))
  · exact Subtype.ext (funext fun b => Subtype.ext (congrFun (congrArg Subtype.val hm) b))
  · have h0 := h m.1 fun g hg => m.2 ⟨g, hg⟩
    refine ⟨⟨fun b => ⟨m.1 b, congrFun h0 b⟩, fun g => funext fun b => Subtype.ext ?_⟩, rfl⟩
    exact (congrFun (repOn_map ρ κ (Tor c Y').subtype g.1 _) b).trans (congrFun (m.2 g) b)

theorem exists_not_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))), Perf A β → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (c t : A) (y₀ : Fin a → A) (j : Fin a), (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ A g m = m) → t • m = 0) → Matrix.vecMul y₀ Φ = 0 → c * t * y₀ j ≠ 0 → ∃ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y ∧ ¬ Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) := by
  intro D N X bkP i s A _ _ _ _ _ _ κ Q ρ hS hK hD hN hO Y _ _ _ _ _ β hβ a Φ Z hU c t y₀ j ht h0 hne
  by_contra hcon
  have hcob : ∀ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) :=
    fun y hy => by_contra fun h => hcon ⟨y, hy, h⟩
  haveI : NeZero (X.l i ^ (nu X i + 1)) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  letI : TopologicalSpace (Quo (c * t) Y) := ⊥
  haveI : DiscreteTopology (Quo (c * t) Y) := ⟨rfl⟩
  haveI : Finite (Quo (c * t) Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  obtain ⟨β₂, hβ₂⟩ := exists_induced β hβ.1 (c * t)
  have hP := perf_induced β hβ (c * t) β₂ hβ₂
  obtain ⟨-, e1⟩ := hO Y A β hβ
  obtain ⟨f2, e2⟩ := hO (Quo (c * t) Y) (Tor (c * t) A) β₂ hP
  have hsub : DualCl bkP i s κ ρ β Q ⊆ h1Map ρ κ⁻¹ (Tor (c * t) A).subtype '' DualCl bkP i s κ ρ β₂ Q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y₂, hy₂, m, hm⟩ := GlobalTheory.T.dualSelmerClass_from_coeffsKilledBy_mul D N X bkP i s A κ Q ρ hS hK hD hN Y A (Quo (c * t) Y) (Tor (c * t) A) β β₂
      (Submodule.mkQ _) (Tor (c * t) A).subtype c t hβ.1 hP.1 (Submodule.mkQ_surjective _) (Submodule.injective_subtype _)
      (fun y' h => ⟨⟨y', h⟩, rfl⟩) hβ₂ ht y hy (hcob y hy)
    exact ⟨_, ⟨y₂, hy₂, rfl⟩, Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, hm⟩))⟩
  have hfin : (DualCl bkP i s κ ρ β₂ Q).Finite := f2
  have hle : Nat.card (DualCl bkP i s κ ρ β Q) ≤ Nat.card (DualCl bkP i s κ ρ β₂ Q) :=
    (Set.ncard_le_ncard hsub (hfin.image _)).trans (Set.ncard_image_le hfin)
  have hprod : ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ (Tor (c * t) A)).comp (DecV N v).subtype)) =
      ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ A).comp (DecV N v).subtype)) :=
    Finset.prod_congr rfl fun v hv => card_invariants_torsion_submodule ρ κ⁻¹ (DecV N v) A (c * t) fun m hm => by
      rw [mul_smul, ht v (Or.inr hv) m hm, smul_zero]
  refine hne (mul_eq_zero_of_range β hβ Φ (c * t) (smul_mem_range Φ (c * t) ?_) y₀ h0 j)
  rw [card_selOn bkP i s κ Q Φ Z hU, card_selOn bkP i s κ Q Φ Z hU, e1, e2, hprod]
  exact Nat.mul_le_mul_right _ hle

end GlobalTheory.NewPrime.DualClass
