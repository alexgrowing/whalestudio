import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocallyCompactSpaceOfIsClosed

noncomputable section

open GlobalTheory.Mt.Adelic

namespace GlobalTheory.HkPart

section Fix

variable {E G V : Type} [Field E] [Group G] [AddCommGroup V] [Module E V]

def fix (π : Representation E G V) (K : Subgroup G) : Submodule E V :=
  Representation.invariants (π.comp K.subtype)

variable (π : Representation E G V) {K : Subgroup G}

theorem mem_fix {v : V} : v ∈ fix π K ↔ ∀ k ∈ K, π k v = v :=
  by rw [fix, Representation.mem_invariants]; exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

theorem apply_eq_of_coset {v : V} (hv : v ∈ fix π K) {x y : G} (h : (x : G ⧸ K) = y) :
    π x v = π y v := by
  rw [QuotientGroup.eq] at h
  rw [show y = x * (x⁻¹ * y) by group, map_mul, Module.End.mul_apply, (mem_fix π).1 hv _ h]

theorem sum_mem_fix {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) {v : V} (hv : v ∈ fix π K) :
    (∑ i, π (z i) v) ∈ fix π K := by
  rw [mem_fix]
  intro k hk
  let F : G ⧸ K → V := fun y => π y.out v
  have hF : ∀ x : G, π x v = F (x : G ⧸ K) := fun x =>
    apply_eq_of_coset π hv (QuotientGroup.out_eq' (x : G ⧸ K)).symm
  rw [map_sum]
  calc ∑ i, π k (π (z i) v) = ∑ i, F ((k * z i : G) : G ⧸ K) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Module.End.mul_apply, ← map_mul, hF]
    _ = ∑ i, F ((z i : G) : G ⧸ K) := sum_heckeFam hz F hk
    _ = ∑ i, π (z i) v := Finset.sum_congr rfl fun i _ => (hF _).symm

def op {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) : Module.End E (fix π K) :=
  (∑ i, π (z i)).restrict fun v hv => by
    rw [LinearMap.sum_apply]; exact sum_mem_fix π hz hv

theorem coe_op {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) (v : fix π K) :
    ((op π hz v : fix π K) : V) = ∑ i, π (z i) v := by
  simp [op, LinearMap.restrict_apply]

theorem isHeckeFam_one (K : Subgroup G) : IsHeckeFam K (fun _ : Fin 1 => (1 : G)) := by
  intro k hk
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [mul_one]
  exact QuotientGroup.eq.2 (by simpa using hk)

theorem op_one : op π (isHeckeFam_one K) = LinearMap.id := by
  ext v
  simp [coe_op]

end Fix

section Part

variable {E G V M M' M'' : Type} [Field E] [Group G] [AddCommGroup V] [Module E V]
  [AddCommGroup M] [Module E M] [AddCommGroup M'] [Module E M'] [AddCommGroup M''] [Module E M'']

variable (E) in

abbrev HeckeRel (K : Subgroup G) (M : Type) [AddCommGroup M] [Module E M] : Type :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G), IsHeckeFam K z → Module.End E M → Prop

def HeckeRel.ofFun {K : Subgroup G} (t : ∀ {n : ℕ} (z : Fin n → G), IsHeckeFam K z → Module.End E M) :
    HeckeRel E K M :=
  fun _ z hz T => T = t z hz

def part (π : Representation E G V) (K : Subgroup G) (R : HeckeRel E K M) :
    Submodule E (fix π K →ₗ[E] M) where
  carrier := {φ | ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M),
    R z hz T → φ ∘ₗ op π hz = T ∘ₗ φ}
  add_mem' {a b} ha hb n z hz T hT := by
    rw [LinearMap.add_comp, LinearMap.comp_add, ha z hz T hT, hb z hz T hT]
  zero_mem' n z hz T hT := by simp
  smul_mem' c a ha n z hz T hT := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ha z hz T hT]

variable {π : Representation E G V} {K : Subgroup G} {R : HeckeRel E K M}

theorem mem_part {φ : fix π K →ₗ[E] M} : φ ∈ part π K R ↔
    ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T → φ ∘ₗ op π hz = T ∘ₗ φ :=
  Iff.rfl

theorem mem_part_iff_apply {φ : fix π K →ₗ[E] M} : φ ∈ part π K R ↔
    ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T →
      ∀ v, φ (op π hz v) = T (φ v) := by
  refine ⟨fun h n z hz T hT v => LinearMap.congr_fun (h z hz T hT) v, fun h n z hz T hT => ?_⟩
  ext v
  exact h z hz T hT v

theorem part_apply_op (φ : part π K R) {n : ℕ} {z : Fin n → G} {hz : IsHeckeFam K z} {T : Module.End E M}
    (hT : R z hz T) (v : fix π K) : (φ : fix π K →ₗ[E] M) (op π hz v) = T ((φ : fix π K →ₗ[E] M) v) :=
  mem_part_iff_apply.1 φ.2 z hz T hT v

theorem mem_part_ofFun {t : ∀ {n : ℕ} (z : Fin n → G), IsHeckeFam K z → Module.End E M} {φ : fix π K →ₗ[E] M} :
    φ ∈ part π K (HeckeRel.ofFun t) ↔ ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z), φ ∘ₗ op π hz = t z hz ∘ₗ φ :=
  ⟨fun h _ z hz => h z hz _ rfl, fun h _ z hz _ hT => hT ▸ h z hz⟩

def Intertw (R : HeckeRel E K M) (R' : HeckeRel E K M') (f : M →ₗ[E] M') : Prop :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T' : Module.End E M'), R' z hz T' →
    ∃ T, R z hz T ∧ f ∘ₗ T = T' ∘ₗ f

theorem Intertw.comp {R : HeckeRel E K M} {R' : HeckeRel E K M'} {R'' : HeckeRel E K M''} {f : M →ₗ[E] M'}
    {g : M' →ₗ[E] M''} (hf : Intertw R R' f) (hg : Intertw R' R'' g) : Intertw R R'' (g ∘ₗ f) := by
  intro n z hz T'' hT''
  obtain ⟨T', hT', e'⟩ := hg z hz T'' hT''
  obtain ⟨T, hT, e⟩ := hf z hz T' hT'
  refine ⟨T, hT, ?_⟩
  rw [LinearMap.comp_assoc, e, ← LinearMap.comp_assoc, e', LinearMap.comp_assoc]

variable (π) in

def map {R : HeckeRel E K M} {R' : HeckeRel E K M'} (f : M →ₗ[E] M') (hf : Intertw R R' f) :
    part π K R →ₗ[E] part π K R' where
  toFun φ := ⟨f ∘ₗ (φ : fix π K →ₗ[E] M), fun _ z hz T' hT' => by
    obtain ⟨T, hT, e⟩ := hf z hz T' hT'
    rw [LinearMap.comp_assoc, mem_part.1 φ.2 z hz T hT, ← LinearMap.comp_assoc, e, LinearMap.comp_assoc]⟩
  map_add' a b := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' c a := Subtype.ext (LinearMap.comp_smul _ _ _)

@[simp] theorem coe_map {R' : HeckeRel E K M'} (f : M →ₗ[E] M') (hf : Intertw R R' f) (φ : part π K R) :
    ((map π f hf φ : part π K R') : fix π K →ₗ[E] M') = f ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

def Commutes (R : HeckeRel E K M) (f : Module.End E M) : Prop :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T → f ∘ₗ T = T ∘ₗ f

theorem Commutes.intertw {f : Module.End E M} (hf : Commutes R f) : Intertw R R f :=
  fun _ z hz T hT => ⟨T, hT, hf z hz T hT⟩

variable (π) in

def endo (f : Module.End E M) (hf : Commutes R f) : Module.End E (part π K R) :=
  map π f hf.intertw

@[simp] theorem coe_endo (f : Module.End E M) (hf : Commutes R f) (φ : part π K R) :
    ((endo π f hf φ : part π K R) : fix π K →ₗ[E] M) = f ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

variable (π) in

def partRep {Γ : Type} [Group Γ] (ρ : Representation E Γ M) (hρ : ∀ γ, Commutes R (ρ γ)) :
    Representation E Γ (part π K R) where
  toFun γ := endo π (ρ γ) (hρ γ)
  map_one' := by
    ext φ : 1
    exact Subtype.ext (by ext v; simp)
  map_mul' a b := by
    ext φ : 1
    exact Subtype.ext (by simp [LinearMap.comp_assoc]; rfl)

@[simp] theorem coe_partRep {Γ : Type} [Group Γ] (ρ : Representation E Γ M) (hρ : ∀ γ, Commutes R (ρ γ)) (γ : Γ)
    (φ : part π K R) :
    ((partRep π ρ hρ γ φ : part π K R) : fix π K →ₗ[E] M) = ρ γ ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

instance [FiniteDimensional E (fix π K)] [FiniteDimensional E M] : FiniteDimensional E (part π K R) :=
  inferInstance

end Part

section Pi

variable {E G V ι : Type} [Field E] [Group G] [AddCommGroup V] [Module E V] [DecidableEq ι]
  {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module E (M i)] {K : Subgroup G}

def piRel (R : ∀ i, HeckeRel E K (M i)) : HeckeRel E K (∀ i, M i) :=
  fun _ z hz T => ∃ Ts : ∀ i, Module.End E (M i), (∀ i, R i z hz (Ts i)) ∧
    T = LinearMap.pi fun i => Ts i ∘ₗ LinearMap.proj i

variable (π : Representation E G V) (R : ∀ i, HeckeRel E K (M i))

def partPi (hR : ∀ i {n : ℕ} (z : Fin n → G) (hz : IsHeckeFam K z), ∃ T, R i z hz T) :
    part π K (piRel R) ≃ₗ[E] ∀ i, part π K (R i) where
  toFun φ i := ⟨LinearMap.proj i ∘ₗ (φ : fix π K →ₗ[E] ∀ i, M i), by
    rw [mem_part_iff_apply]
    intro n z hz T hT v
    classical
    let Ts : ∀ j, Module.End E (M j) := Function.update (fun j => (hR j z hz).choose) i T
    have hTs : ∀ j, R j z hz (Ts j) := by
      intro j
      by_cases h : j = i
      · subst h; simpa [Ts] using hT
      · simpa [Ts, h] using (hR j z hz).choose_spec
    have := part_apply_op φ (T := LinearMap.pi fun j => Ts j ∘ₗ LinearMap.proj j) ⟨Ts, hTs, rfl⟩ v
    have := congrFun this i
    simpa [Ts] using this⟩
  invFun ψ := ⟨LinearMap.pi fun i => ((ψ i : part π K (R i)) : fix π K →ₗ[E] M i), by
    rw [mem_part_iff_apply]
    rintro n z hz T ⟨Ts, hTs, rfl⟩ v
    funext i
    simpa using part_apply_op (ψ i) (hTs i) v⟩
  map_add' a b := by ext i : 1; exact Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' c a := by ext i : 1; exact Subtype.ext (LinearMap.comp_smul _ _ _)
  left_inv φ := by
    apply Subtype.ext
    ext v i
    rfl
  right_inv ψ := by
    funext i
    apply Subtype.ext
    ext v
    rfl

end Pi

section Transport

variable {E' E : Type} [Field E'] [Field E]

def Tr (_ι : E' ≃+* E) (V : Type) : Type := V

variable (ι : E' ≃+* E) {V : Type} [AddCommGroup V] [Module E V]

instance : AddCommGroup (Tr ι V) := inferInstanceAs (AddCommGroup V)

instance : Module E' (Tr ι V) := Module.compHom V (ι : E' →+* E)

def Tr.of : V ≃+ Tr ι V := AddEquiv.refl V

variable {G : Type} [Group G]

def trRep (π : Representation E G V) : Representation E' G (Tr ι V) where
  toFun g :=
    { toFun := fun v => Tr.of ι (π g ((Tr.of ι).symm v))
      map_add' := fun v w => (π g).map_add v w
      map_smul' := fun c v => (π g).map_smul (ι c) v }
  map_one' := by ext v; simp [Tr.of]; rfl
  map_mul' a b := by
    ext v
    change Tr.of ι (π (a * b) _) = Tr.of ι (π a (π b _))
    rw [map_mul]; rfl

end Transport

section Inhabitant

variable {E G M : Type} [Field E] [Group G] [AddCommGroup M] [Module E M] (K : Subgroup G)

variable (E) in

def mulRel (M : Type) [AddCommGroup M] [Module E M] : HeckeRel E K M :=
  fun n _ _ T => T = (n : E) • LinearMap.id

variable (E) in

def zeroRel (M : Type) [AddCommGroup M] [Module E M] : HeckeRel E K M :=
  fun _ _ _ T => T = 0

theorem fix_trivial : fix (Representation.trivial E G E) K = ⊤ :=
  eq_top_iff.2 fun v _ => (mem_fix _).2 fun _ _ => rfl

theorem op_trivial {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) :
    op (Representation.trivial E G E) hz = (n : E) • LinearMap.id := by
  ext v
  simp [coe_op, Finset.sum_const, Finset.card_univ]

theorem part_trivial_mulRel : part (Representation.trivial E G E) K (mulRel E K M) = ⊤ := by
  refine eq_top_iff.2 fun φ _ => mem_part.2 fun n z hz T hT => ?_
  rw [op_trivial, show T = (n : E) • LinearMap.id from hT]
  ext v
  simp

theorem finrank_part_trivial_mulRel :
    Module.finrank E (part (Representation.trivial E G E) K (mulRel E K E)) = 1 := by
  rw [part_trivial_mulRel, finrank_top, Module.finrank_linearMap, fix_trivial, finrank_top,
    Module.finrank_self, one_mul]

theorem part_zeroRel {V : Type} [AddCommGroup V] [Module E V] (π : Representation E G V) :
    part π K (zeroRel E K M) = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ => ?_
  have h := mem_part.1 hφ (fun _ : Fin 1 => (1 : G)) (isHeckeFam_one K) 0 rfl
  rw [op_one, LinearMap.comp_id, LinearMap.zero_comp] at h
  exact (Submodule.mem_bot E).2 h

example (v : fix (Representation.trivial ℚ G ℚ) K) : op (Representation.trivial ℚ G ℚ) (isHeckeFam_one K) v = v := by
  rw [op_one]; rfl

example : FiniteDimensional ℚ (part (Representation.trivial ℚ G ℚ) K (mulRel ℚ K ℚ)) := inferInstance

example : Module.finrank ℚ (part (Representation.trivial ℚ G ℚ) K (mulRel ℚ K ℚ)) = 1 :=
  finrank_part_trivial_mulRel K

example : part (Representation.trivial ℚ G ℚ) K (zeroRel ℚ K ℚ) = ⊥ := part_zeroRel K _

end Inhabitant

end GlobalTheory.HkPart
