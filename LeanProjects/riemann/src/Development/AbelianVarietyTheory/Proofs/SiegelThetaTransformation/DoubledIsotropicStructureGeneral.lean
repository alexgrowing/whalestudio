import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPairingAlgebra
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.DifferentiableToContinuousLinearMap

namespace GlobalTheory

open Module

namespace DoubledSpace

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}

theorem finrank_add_finrank_orthogonal [FiniteDimensional E W] {h : W →ₗ[E] W →ₛₗ[σ] E}
    (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (S : Submodule E W) :
    finrank E S + finrank E (S.orthogonalBilin h) = finrank E W := by
  haveI : RingHomSurjective σ := ⟨hσ.surjective⟩
  have hrefl : ∀ x y, h x y = 0 → h y x = 0 := fun x y e => by rw [← hh, e, map_zero]
  have e1 : S.orthogonalBilin h = (S.map h.flip).dualCoannihilator := by
    ext m
    rw [Submodule.mem_dualCoannihilator, Submodule.mem_orthogonalBilin_iff]
    constructor
    · rintro H _ ⟨s, hs, rfl⟩
      exact hrefl _ _ (H s hs)
    · intro H s hs
      exact hrefl _ _ (H _ ⟨s, hs, rfl⟩)
  have hinj : Function.Injective h.flip := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn x fun y => hrefl _ _ (LinearMap.congr_fun hx y)
  let j : S →+ S.map h.flip := (h.flip.submoduleMap S).toAddMonoidHom
  have hj : Function.Bijective j :=
    ⟨fun a b e => Subtype.ext (hinj (congrArg Subtype.val e)),
      fun ⟨_, s, hs, e⟩ => ⟨⟨s, hs⟩, Subtype.ext e⟩⟩
  have e2 : finrank E S = finrank E (S.map h.flip) := by
    have := lift_rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective j hj) hσ.bijective
      (fun r m => Subtype.ext (h.flip.map_smulₛₗ r (m : W)))
    simpa [finrank] using congrArg Cardinal.toNat this
  rw [e1, e2, Subspace.finrank_add_finrank_dualCoannihilator_eq]

def form (h : W →ₗ[E] W →ₛₗ[σ] E) : (W × W) →ₗ[E] (W × W) →ₛₗ[σ] E :=
  LinearMap.mk₂'ₛₗ (RingHom.id E) σ (fun p q => h p.1 q.1 - h p.2 q.2)
    (fun p p' q => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun c p q => by simp [mul_sub])
    (fun p q q' => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c p q => by simp [mul_sub])

@[simp] theorem form_apply (h : W →ₗ[E] W →ₛₗ[σ] E) (p q : W × W) :
    form h p q = h p.1 q.1 - h p.2 q.2 := rfl

def left (I : Submodule E (W × W)) : Submodule E W := I.comap (LinearMap.inl E W W)

def right (I : Submodule E (W × W)) : Submodule E W := I.comap (LinearMap.inr E W W)

@[simp] theorem mem_left {I : Submodule E (W × W)} {x : W} : x ∈ left I ↔ (x, 0) ∈ I := Iff.rfl

@[simp] theorem mem_right {I : Submodule E (W × W)} {y : W} : y ∈ right I ↔ (0, y) ∈ I := Iff.rfl

theorem finrank_map_fst_add [FiniteDimensional E W] (I : Submodule E (W × W)) :
    finrank E (I.map (LinearMap.fst E W W)) + finrank E (right I) = finrank E I := by
  have h1 := LinearMap.finrank_range_add_finrank_ker ((LinearMap.fst E W W).domRestrict I)
  rw [LinearMap.range_domRestrict] at h1
  rw [← h1]
  congr 1
  refine LinearEquiv.finrank_eq
    { toFun := fun y => ⟨⟨(0, y.1), y.2⟩, rfl⟩
      invFun := fun p => ⟨p.1.1.2, ?_⟩
      map_add' := fun a b => by ext <;> simp
      map_smul' := fun a b => by ext <;> simp
      left_inv := fun a => rfl
      right_inv := fun p => ?_ }
  · have e : p.1.1.1 = 0 := p.2
    rw [mem_right, ← e]; exact p.1.2
  · have e : p.1.1.1 = 0 := p.2
    ext <;> simp [e]

theorem finrank_map_snd_add [FiniteDimensional E W] (I : Submodule E (W × W)) :
    finrank E (I.map (LinearMap.snd E W W)) + finrank E (left I) = finrank E I := by
  have h1 := LinearMap.finrank_range_add_finrank_ker ((LinearMap.snd E W W).domRestrict I)
  rw [LinearMap.range_domRestrict] at h1
  rw [← h1]
  congr 1
  refine LinearEquiv.finrank_eq
    { toFun := fun y => ⟨⟨(y.1, 0), y.2⟩, rfl⟩
      invFun := fun p => ⟨p.1.1.1, ?_⟩
      map_add' := fun a b => by ext <;> simp
      map_smul' := fun a b => by ext <;> simp
      left_inv := fun a => rfl
      right_inv := fun p => ?_ }
  · have e : p.1.1.2 = 0 := p.2
    rw [mem_left, ← e]; exact p.1.2
  · have e : p.1.1.2 = 0 := p.2
    ext <;> simp [e]

section Isotropic

variable {h : W →ₗ[E] W →ₛₗ[σ] E} {I : Submodule E (W × W)}

theorem left_isotropic (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0) :
    ∀ x ∈ left I, ∀ x' ∈ left I, h x x' = 0 := fun x hx x' hx' => by
  simpa using hI _ hx _ hx'

theorem right_isotropic (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0) :
    ∀ y ∈ right I, ∀ y' ∈ right I, h y y' = 0 := fun y hy y' hy' => by
  simpa using hI _ hy _ hy'

theorem map_fst_le (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0) :
    I.map (LinearMap.fst E W W) ≤ (left I).orthogonalBilin h := by
  rintro _ ⟨p, hp, rfl⟩ x hx
  simpa using hI _ hx _ hp

theorem map_snd_le (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0) :
    I.map (LinearMap.snd E W W) ≤ (right I).orthogonalBilin h := by
  rintro _ ⟨p, hp, rfl⟩ y hy
  simpa using hI _ hy _ hp

variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
  (hd : finrank E I = finrank E W)

include hσ hh hn hI hd

theorem finrank_left_eq_finrank_right : finrank E (left I) = finrank E (right I) := by
  have a := finrank_map_fst_add I
  have b := finrank_map_snd_add I
  have c := Submodule.finrank_mono (map_fst_le hI)
  have d := Submodule.finrank_mono (map_snd_le hI)
  have e := finrank_add_finrank_orthogonal hσ hh hn (left I)
  have f := finrank_add_finrank_orthogonal hσ hh hn (right I)
  omega

theorem map_fst_eq : I.map (LinearMap.fst E W W) = (left I).orthogonalBilin h := by
  refine Submodule.eq_of_le_of_finrank_eq (map_fst_le hI) ?_
  have a := finrank_map_fst_add I
  have e := finrank_add_finrank_orthogonal hσ hh hn (left I)
  have f := finrank_left_eq_finrank_right hσ hh hn hI hd
  omega

theorem map_snd_eq : I.map (LinearMap.snd E W W) = (right I).orthogonalBilin h := by
  refine Submodule.eq_of_le_of_finrank_eq (map_snd_le hI) ?_
  have a := finrank_map_snd_add I
  have e := finrank_add_finrank_orthogonal hσ hh hn (right I)
  have f := finrank_left_eq_finrank_right hσ hh hn hI hd
  omega

theorem left_eq_bot_iff :
    left I = ⊥ ↔ ∃! γ : W ≃ₗ[E] W,
      (∀ x y, h (γ x) (γ y) = h x y) ∧ I = (γ : W →ₗ[E] W).graph := by
  constructor
  · intro hX
    have hX' : right I = ⊥ := by
      rw [← Submodule.finrank_eq_zero, ← finrank_left_eq_finrank_right hσ hh hn hI hd, hX,
        finrank_bot]
    have b1 : Function.Bijective (Prod.fst ∘ I.subtype) := by
      refine ⟨fun p q e => ?_, fun x => ?_⟩
      · have e1 : p.1.1 = q.1.1 := e
        have : p.1.2 - q.1.2 ∈ right I := by
          rw [mem_right]
          convert I.sub_mem p.2 q.2 using 1
          ext <;> simp [e1]
        rw [hX', Submodule.mem_bot, sub_eq_zero] at this
        exact Subtype.ext (Prod.ext e1 this)
      · have : x ∈ I.map (LinearMap.fst E W W) := by
          rw [map_fst_eq hσ hh hn hI hd, hX]
          intro n hn; simp [(Submodule.mem_bot E).1 hn]
        obtain ⟨p, hp, rfl⟩ := this
        exact ⟨⟨p, hp⟩, rfl⟩
    have b2 : Function.Bijective (Prod.snd ∘ I.subtype) := by
      refine ⟨fun p q e => ?_, fun x => ?_⟩
      · have e1 : p.1.2 = q.1.2 := e
        have : p.1.1 - q.1.1 ∈ left I := by
          rw [mem_left]
          convert I.sub_mem p.2 q.2 using 1
          ext <;> simp [e1]
        rw [hX, Submodule.mem_bot, sub_eq_zero] at this
        exact Subtype.ext (Prod.ext this e1)
      · have : x ∈ I.map (LinearMap.snd E W W) := by
          rw [map_snd_eq hσ hh hn hI hd, hX']
          intro n hn; simp [(Submodule.mem_bot E).1 hn]
        obtain ⟨p, hp, rfl⟩ := this
        exact ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨γ, hγ⟩ := Submodule.exists_equiv_eq_graph b1 b2
    refine ⟨γ, ⟨fun x y => ?_, hγ⟩, ?_⟩
    · have := hI (x, γ x) (by rw [hγ]; rfl) (y, γ y) (by rw [hγ]; rfl)
      rw [form_apply, sub_eq_zero] at this
      exact this.symm
    · rintro γ' ⟨-, hγ'⟩
      ext x
      have : (x, γ' x) ∈ I := by rw [hγ']; rfl
      rw [hγ] at this
      exact this
  · rintro ⟨γ, ⟨-, rfl⟩, -⟩
    rw [eq_bot_iff]
    intro x hx
    have : (0 : W) = γ x := hx
    exact γ.map_eq_zero_iff.1 this.symm

omit hσ hh hn hd [FiniteDimensional E W] in
theorem apply_left_mem {u : W → W}
    (hu : ∀ x ∈ (left I).orthogonalBilin h, u x - x ∈ left I) {x y : W} (hp : (x, y) ∈ I) :
    (u x, y) ∈ I := by
  have := I.add_mem hp (hu x (map_fst_le hI ⟨_, hp, rfl⟩))
  simpa using this

omit hσ hh hn hd [FiniteDimensional E W] in
theorem apply_right_mem {u : W → W}
    (hu : ∀ y ∈ (right I).orthogonalBilin h, u y - y ∈ right I) {x y : W} (hp : (x, y) ∈ I) :
    (x, u y) ∈ I := by
  have := I.add_mem hp (hu y (map_snd_le hI ⟨_, hp, rfl⟩))
  simpa using this

omit hσ hh hn hd in

theorem map_prodMap_left {u : W →ₗ[E] W} (hi : Function.Injective u)
    (hu : ∀ x ∈ (left I).orthogonalBilin h, u x - x ∈ left I) :
    I.map (u.prodMap LinearMap.id) = I := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact apply_left_mem hI hu hp
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (hi.prodMap Function.injective_id) I)).symm

omit hσ hh hn hd in

theorem map_prodMap_right {u : W →ₗ[E] W} (hi : Function.Injective u)
    (hu : ∀ y ∈ (right I).orthogonalBilin h, u y - y ∈ right I) :
    I.map (LinearMap.id.prodMap u) = I := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact apply_right_mem hI hu hp
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (Function.injective_id.prodMap hi) I)).symm

omit hσ hh hn hd in

theorem map_prodMap_transvection {ξ : W} (hξ : ξ ∈ left I) (b : E) {u : W →ₗ[E] W}
    (hu : ∀ v, u v = v + (b * h v ξ) • ξ) : I.map (u.prodMap LinearMap.id) = I := by
  refine map_prodMap_left hI ?_ fun x _ => ?_
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : h (u v) ξ = 0 := by simp [hv]
    rw [hu, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      left_isotropic hI ξ hξ ξ hξ, smul_zero, add_zero] at h0
    rw [hu, h0] at hv
    simpa using hv
  · rw [hu, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hξ

end Isotropic

abbrev Reduced (h : W →ₗ[E] W →ₛₗ[σ] E) (X : Submodule E W) : Type _ :=
  X.orthogonalBilin h ⧸ X.submoduleOf (X.orthogonalBilin h)

def reducedForm (h : W →ₗ[E] W →ₛₗ[σ] E) (hh : ∀ x y, σ (h x y) = h y x) (X : Submodule E W) :
    Reduced h X →ₗ[E] Reduced h X →ₛₗ[σ] E :=
  (h.domRestrict₁₂ (X.orthogonalBilin h) (X.orthogonalBilin h)).liftQ₂ _ _
    (fun x hx => LinearMap.ext fun y => y.2 x.1 hx)
    (fun y hy => LinearMap.ext fun x => by
      have : h y.1 x.1 = 0 := x.2 y.1 hy
      change h x.1 y.1 = 0
      rw [← hh, this, map_zero])

@[simp] theorem reducedForm_mk (h : W →ₗ[E] W →ₛₗ[σ] E) (hh : ∀ x y, σ (h x y) = h y x)
    (X : Submodule E W) (x y : X.orthogonalBilin h) :
    reducedForm h hh X (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = h x y := rfl

def glue (h : W →ₗ[E] W →ₛₗ[σ] E) (X X' : Submodule E W) (φ : Reduced h X →ₗ[E] Reduced h X') :
    Submodule E (W × W) :=
  (φ.graph.comap ((Submodule.mkQ _).prodMap (Submodule.mkQ _))).map
    ((X.orthogonalBilin h).subtype.prodMap (X'.orthogonalBilin h).subtype)

theorem mem_glue {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
    {φ : Reduced h X →ₗ[E] Reduced h X'} {x y : W} :
    (x, y) ∈ glue h X X' φ ↔ ∃ (hx : x ∈ X.orthogonalBilin h) (hy : y ∈ X'.orthogonalBilin h),
      φ (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk ⟨y, hy⟩ := by
  constructor
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hp, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 e
    exact ⟨ha, hb, Eq.symm hp⟩
  · rintro ⟨hx, hy, e⟩
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), e.symm, rfl⟩

section Glue

variable {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}

theorem mk_mem_glue {φ : Reduced h X →ₗ[E] Reduced h X'} (x : X.orthogonalBilin h)
    (y : X'.orthogonalBilin h) :
    (x.1, y.1) ∈ glue h X X' φ ↔ φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  rw [mem_glue]
  exact ⟨fun ⟨_, _, e⟩ => e, fun e => ⟨x.2, y.2, e⟩⟩

theorem glue_injective : Function.Injective (glue h X X') := by
  intro φ ψ e
  refine LinearMap.ext fun a => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk x))
  have := (mk_mem_glue x y).2 hy.symm
  rw [e, mk_mem_glue] at this
  rw [this, hy]

theorem left_glue (hX : ∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) (φ : Reduced h X ≃ₗ[E] Reduced h X') :
    left (glue h X X' φ) = X := by
  ext x
  rw [mem_left, mem_glue]
  constructor
  · rintro ⟨hx, hy, e⟩
    have e0 : (Submodule.Quotient.mk ⟨0, hy⟩ : Reduced h X') = 0 := rfl
    rw [e0, LinearEquiv.coe_coe, φ.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at e
    exact e
  · intro hx
    have hx' : x ∈ X.orthogonalBilin h := fun n hn => hX n hn x hx
    refine ⟨hx', Submodule.zero_mem _, ?_⟩
    have e1 : (Submodule.Quotient.mk ⟨x, hx'⟩ : Reduced h X) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hx
    rw [e1, map_zero]; rfl

theorem right_glue (hX' : ∀ x ∈ X', ∀ x' ∈ X', h x x' = 0) (φ : Reduced h X →ₗ[E] Reduced h X') :
    right (glue h X X' φ) = X' := by
  ext y
  rw [mem_right, mem_glue]
  constructor
  · rintro ⟨hx, hy, e⟩
    have e0 : (Submodule.Quotient.mk ⟨0, hx⟩ : Reduced h X) = 0 := rfl
    rw [e0, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at e
    exact e
  · intro hy
    have hy' : y ∈ X'.orthogonalBilin h := fun n hn => hX' n hn y hy
    refine ⟨Submodule.zero_mem _, hy', ?_⟩
    have e1 : (Submodule.Quotient.mk ⟨y, hy'⟩ : Reduced h X') = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hy
    rw [e1]; exact map_zero φ

theorem map_fst_glue (φ : Reduced h X →ₗ[E] Reduced h X') :
    (glue h X X' φ).map (LinearMap.fst E W W) = X.orthogonalBilin h := by
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, hp, rfl⟩
    exact (mem_glue.1 hp).1
  · intro x hx
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk ⟨x, hx⟩))
    exact ⟨(x, y.1), (mk_mem_glue ⟨x, hx⟩ y).2 hy.symm, rfl⟩

theorem glue_isotropic (hh : ∀ x y, σ (h x y) = h y x) {φ : Reduced h X →ₗ[E] Reduced h X'}
    (hφ : ∀ a b, reducedForm h hh X' (φ a) (φ b) = reducedForm h hh X a b) :
    ∀ p ∈ glue h X X' φ, ∀ q ∈ glue h X X' φ, form h p q = 0 := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq
  obtain ⟨hx, hy, e⟩ := mem_glue.1 hp
  obtain ⟨hx', hy', e'⟩ := mem_glue.1 hq
  have := hφ (Submodule.Quotient.mk ⟨x, hx⟩) (Submodule.Quotient.mk ⟨x', hx'⟩)
  rw [e, e', reducedForm_mk, reducedForm_mk] at this
  rw [form_apply, sub_eq_zero]
  exact this.symm

variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0)

include hσ hh hn

theorem finrank_reduced (hX : ∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) :
    finrank E (Reduced h X) + 2 * finrank E X = finrank E W := by
  have a := (X.submoduleOf (X.orthogonalBilin h)).finrank_quotient_add_finrank
  have b := (Submodule.submoduleOfEquivOfLe
    (show X ≤ X.orthogonalBilin h from fun x hx n hn => hX n hn x hx)).finrank_eq
  have c := finrank_add_finrank_orthogonal hσ hh hn X
  change finrank E (Reduced h X) + _ = _ at a
  omega

theorem finrank_glue (hX : ∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) (hX' : ∀ x ∈ X', ∀ x' ∈ X', h x x' = 0)
    (φ : Reduced h X ≃ₗ[E] Reduced h X') : finrank E (glue h X X' φ) = finrank E W := by
  have a := finrank_map_fst_add (glue h X X' φ)
  rw [map_fst_glue, right_glue hX'] at a
  have b := finrank_reduced hσ hh hn hX
  have c := finrank_reduced hσ hh hn hX'
  have d := φ.finrank_eq
  have e := finrank_add_finrank_orthogonal hσ hh hn X
  omega

theorem existsUnique_glue {I : Submodule E (W × W)} (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
    (hd : finrank E I = finrank E W) :
    ∃! φ : Reduced h (left I) ≃ₗ[E] Reduced h (right I),
      (∀ a b, reducedForm h hh (right I) (φ a) (φ b) = reducedForm h hh (left I) a b) ∧
        I = glue h (left I) (right I) φ := by
  have m1 : ∀ p : I, p.1.1 ∈ (left I).orthogonalBilin h := fun p => map_fst_le hI ⟨_, p.2, rfl⟩
  have m2 : ∀ p : I, p.1.2 ∈ (right I).orthogonalBilin h := fun p => map_snd_le hI ⟨_, p.2, rfl⟩
  let f₁ : I →ₗ[E] Reduced h (left I) := (Submodule.mkQ _).comp
    (((LinearMap.fst E W W).domRestrict I).codRestrict _ m1)
  let f₂ : I →ₗ[E] Reduced h (right I) := (Submodule.mkQ _).comp
    (((LinearMap.snd E W W).domRestrict I).codRestrict _ m2)
  have d1 : ∀ p, f₁ p = Submodule.Quotient.mk ⟨p.1.1, m1 p⟩ := fun _ => rfl
  have d2 : ∀ p, f₂ p = Submodule.Quotient.mk ⟨p.1.2, m2 p⟩ := fun _ => rfl
  have s1 : Function.Surjective f₁ := fun a => by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    have hx' := hx
    rw [← map_fst_eq hσ hh hn hI hd] at hx'
    obtain ⟨p, hp, rfl⟩ := hx'
    exact ⟨⟨p, hp⟩, rfl⟩
  have s2 : Function.Surjective f₂ := fun a => by
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    have hx' := hx
    rw [← map_snd_eq hσ hh hn hI hd] at hx'
    obtain ⟨p, hp, rfl⟩ := hx'
    exact ⟨⟨p, hp⟩, rfl⟩
  have key : ∀ p q, f₁ p = f₁ q ↔ f₂ p = f₂ q := fun p q => by
    rw [d1, d1, d2, d2, Submodule.Quotient.eq, Submodule.Quotient.eq]
    change (p.1.1 - q.1.1, 0) ∈ I ↔ (0, p.1.2 - q.1.2) ∈ I
    have hpq := I.sub_mem p.2 q.2
    constructor
    · intro H
      convert I.sub_mem hpq H using 1
      ext <;> simp
    · intro H
      convert I.sub_mem hpq H using 1
      ext <;> simp
  obtain ⟨φ, hφ⟩ := LinearMap.exists_linearEquiv_eq_graph (f := f₁.prod f₂) s1 s2 key
  have hf : ∀ p, φ (f₁ p) = f₂ p := fun p => by
    have : (f₁.prod f₂) p ∈ φ.toLinearMap.graph := hφ ▸ LinearMap.mem_range_self _ p
    exact Eq.symm this
  have hg : I = glue h (left I) (right I) φ := by
    refine Submodule.eq_of_le_of_finrank_eq (fun p hp => ?_) ?_
    · exact mem_glue.2 ⟨m1 ⟨p, hp⟩, m2 ⟨p, hp⟩, hf ⟨p, hp⟩⟩
    · rw [hd, finrank_glue hσ hh hn (left_isotropic hI) (right_isotropic hI)]
  refine ⟨φ, ⟨fun a b => ?_, hg⟩, ?_⟩
  · obtain ⟨p, rfl⟩ := s1 a
    obtain ⟨q, rfl⟩ := s1 b
    rw [hf, hf, d1, d1, d2, d2, reducedForm_mk, reducedForm_mk]
    exact (sub_eq_zero.1 (hI _ p.2 _ q.2)).symm
  · rintro ψ ⟨-, hψ⟩
    exact LinearEquiv.toLinearMap_injective (glue_injective (hψ.symm.trans hg))

end Glue

end DoubledSpace

open DoubledSpace

theorem doubled_isotropic_structure_general {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {σ : E →+* E} (hσ : Function.Involutive σ)
    {h : W →ₗ[E] W →ₛₗ[σ] E} (hh : ∀ x y, σ (h x y) = h y x)
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) :
    (∀ I : Submodule E (W × W), (∀ p ∈ I, ∀ q ∈ I, h p.1 q.1 - h p.2 q.2 = 0) →
      finrank E I = finrank E W →
      (∀ x ∈ left I, ∀ x' ∈ left I, h x x' = 0) ∧
      (∀ y ∈ right I, ∀ y' ∈ right I, h y y' = 0) ∧
      finrank E (left I) = finrank E (right I) ∧
      I.map (LinearMap.fst E W W) = (left I).orthogonalBilin h ∧
      I.map (LinearMap.snd E W W) = (right I).orthogonalBilin h ∧
      (left I = ⊥ ↔ ∃! γ : W ≃ₗ[E] W,
        (∀ x y, h (γ x) (γ y) = h x y) ∧ I = (γ : W →ₗ[E] W).graph) ∧
      (∀ u : W →ₗ[E] W, Function.Injective u →
        (∀ x ∈ (left I).orthogonalBilin h, u x - x ∈ left I) →
        I.map (u.prodMap LinearMap.id) = I) ∧
      (∀ u : W →ₗ[E] W, Function.Injective u →
        (∀ y ∈ (right I).orthogonalBilin h, u y - y ∈ right I) →
        I.map (LinearMap.id.prodMap u) = I) ∧
      (∀ ξ ∈ left I, ∀ (b : E) (u : W →ₗ[E] W), (∀ v, u v = v + (b * h v ξ) • ξ) →
        I.map (u.prodMap LinearMap.id) = I) ∧
      (∃! φ : Reduced h (left I) ≃ₗ[E] Reduced h (right I),
        (∀ a b, reducedForm h hh (right I) (φ a) (φ b) = reducedForm h hh (left I) a b) ∧
          I = glue h (left I) (right I) φ)) ∧
    (∀ X X' : Submodule E W, (∀ x ∈ X, ∀ x' ∈ X, h x x' = 0) → (∀ y ∈ X', ∀ y' ∈ X', h y y' = 0) →
      ∀ φ : Reduced h X ≃ₗ[E] Reduced h X',
        (∀ a b, reducedForm h hh X' (φ a) (φ b) = reducedForm h hh X a b) →
        (∀ p ∈ glue h X X' φ, ∀ q ∈ glue h X X' φ, h p.1 q.1 - h p.2 q.2 = 0) ∧
        finrank E (glue h X X' φ) = finrank E W ∧
        left (glue h X X' φ) = X ∧ right (glue h X X' φ) = X') :=
  ⟨fun _ hI hd => ⟨left_isotropic hI, right_isotropic hI,
      finrank_left_eq_finrank_right hσ hh hn hI hd, map_fst_eq hσ hh hn hI hd,
      map_snd_eq hσ hh hn hI hd, left_eq_bot_iff hσ hh hn hI hd,
      fun _ hi hu => map_prodMap_left hI hi hu, fun _ hi hu => map_prodMap_right hI hi hu,
      fun _ hξ b _ hu => map_prodMap_transvection hI hξ b hu,
      existsUnique_glue hσ hh hn hI hd⟩,
    fun _ _ hX hX' φ hφ => ⟨glue_isotropic hh hφ, finrank_glue hσ hh hn hX hX' φ,
      left_glue hX φ, right_glue hX' _⟩⟩

section CM

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix LocalLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem transvMat_mulVec_eq (G : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (α : E)
    (v : Fin N → E) : transvMat G ξ α *ᵥ v = v + (α * herm G v ξ) • ξ := by
  funext a
  simp only [transvMat, herm, Matrix.mulVec, dotProduct, of_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem hermPairing_conj {G : Matrix (Fin N) (Fin N) E} (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin N → E) :
    (IsCMField.complexConj E : E →+* E) (hermPairing G x y) = hermPairing G y x :=
  HermitianPairingAlgebra.herm_symm hG x y

theorem doubled_isotropic_structure (G : Matrix (Fin N) (Fin N) E)
    (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0) :
    (∀ I : Submodule E ((Fin N → E) × (Fin N → E)),
      (∀ p ∈ I, ∀ q ∈ I, herm G p.1 q.1 - herm G p.2 q.2 = 0) → finrank E I = N →
      (∀ x ∈ left I, ∀ x' ∈ left I, herm G x x' = 0) ∧
      (∀ y ∈ right I, ∀ y' ∈ right I, herm G y y' = 0) ∧
      finrank E (left I) = finrank E (right I) ∧
      I.map (LinearMap.fst E _ _) = (left I).orthogonalBilin (hermPairing G) ∧
      I.map (LinearMap.snd E _ _) = (right I).orthogonalBilin (hermPairing G) ∧
      (left I = ⊥ ↔ ∃! γ : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ x y, herm G (γ x) (γ y) = herm G x y) ∧ I = γ.toLinearMap.graph) ∧
      (left I = ⊥ ↔ ∃! γ : GL (Fin N) E,
        (∀ x y, herm G (γ.1 *ᵥ x) (γ.1 *ᵥ y) = herm G x y) ∧
          ∀ x y, (x, y) ∈ I ↔ y = γ.1 *ᵥ x) ∧
      (∀ u : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ x ∈ (left I).orthogonalBilin (hermPairing G), u x - x ∈ left I) →
        I.map (u.toLinearMap.prodMap LinearMap.id) = I) ∧
      (∀ u : (Fin N → E) ≃ₗ[E] (Fin N → E),
        (∀ y ∈ (right I).orthogonalBilin (hermPairing G), u y - y ∈ right I) →
        I.map (LinearMap.id.prodMap u.toLinearMap) = I) ∧
      (∀ ξ ∈ left I, ∀ α : E,
        I.map ((Matrix.toLin' (transvMat G ξ α)).prodMap LinearMap.id) = I) ∧
      (∃! φ : Reduced (hermPairing G) (left I) ≃ₗ[E] Reduced (hermPairing G) (right I),
        (∀ a b, reducedForm (hermPairing G) (hermPairing_conj hG) (right I) (φ a) (φ b)
          = reducedForm (hermPairing G) (hermPairing_conj hG) (left I) a b) ∧
        I = glue (hermPairing G) (left I) (right I) φ)) ∧
    (∀ X X' : Submodule E (Fin N → E), (∀ x ∈ X, ∀ x' ∈ X, herm G x x' = 0) →
      (∀ y ∈ X', ∀ y' ∈ X', herm G y y' = 0) →
      ∀ φ : Reduced (hermPairing G) X ≃ₗ[E] Reduced (hermPairing G) X',
        (∀ a b, reducedForm (hermPairing G) (hermPairing_conj hG) X' (φ a) (φ b)
          = reducedForm (hermPairing G) (hermPairing_conj hG) X a b) →
        (∀ p ∈ glue (hermPairing G) X X' φ, ∀ q ∈ glue (hermPairing G) X X' φ,
          herm G p.1 q.1 - herm G p.2 q.2 = 0) ∧
        finrank E (glue (hermPairing G) X X' φ) = N ∧
        left (glue (hermPairing G) X X' φ) = X ∧ right (glue (hermPairing G) X X' φ) = X') := by
  have hσ : Function.Involutive (IsCMField.complexConj E : E →+* E) :=
    fun a => IsCMField.complexConj_apply_apply E a
  obtain ⟨A, B⟩ := doubled_isotropic_structure_general hσ (hermPairing_conj hG)
    (hermPairing_separating hdet)
  rw [Module.finrank_fin_fun] at A B
  refine ⟨fun I hI hd => ?_, B⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := A I hI hd
  refine ⟨a1, a2, a3, a4, a5, a6, ?_, fun u => a7 _ u.injective, fun u => a8 _ u.injective,
    fun ξ hξ α => a9 ξ hξ α _ fun v => by
      rw [Matrix.toLin'_apply, transvMat_mulVec_eq, hermPairing_apply], a10⟩
  constructor
  · intro hX
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := a6.1 hX
    let g : GL (Fin N) E :=
      ⟨LinearMap.toMatrix' γ.toLinearMap, LinearMap.toMatrix' γ.symm.toLinearMap,
        by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
    have hg : ∀ x, g.1 *ᵥ x = γ x := fun x => LinearMap.toMatrix'_mulVec _ x
    have hm : ∀ x y, (x, y) ∈ I ↔ y = g.1 *ᵥ x := fun x y => by rw [hg, h2]; rfl
    refine ⟨g, ⟨fun x y => by rw [hg, hg]; exact h1 x y, hm⟩, ?_⟩
    rintro g' ⟨-, h3⟩
    refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (hm _ _).1 ((h3 x _).2 rfl)
  · rintro ⟨g, ⟨-, h3⟩, -⟩
    rw [eq_bot_iff]
    intro x hx
    have e : (0 : Fin N → E) = g.1 *ᵥ x := (h3 _ _).1 hx
    have : (g⁻¹).1 *ᵥ (g.1 *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [Submodule.mem_bot, ← this, ← e, Matrix.mulVec_zero]

end CM

end GlobalTheory
