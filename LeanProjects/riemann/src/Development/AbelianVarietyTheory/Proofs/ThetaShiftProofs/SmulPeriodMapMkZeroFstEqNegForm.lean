import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal

noncomputable section

open scoped TensorProduct

namespace GlobalTheory

theorem eq_zero_of_forall_smul_mem_countable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Set V}
    (hS : S.Countable) {z : V} (hz : ∀ s : ℂ, s • z ∈ S) : z = 0 := by
  by_contra h
  have hinj : Function.Injective fun s : ℂ => s • z := smul_left_injective ℂ h
  have h1 : (Set.univ : Set ℂ).Countable :=
    (hS.preimage_of_injOn hinj.injOn).mono fun s _ => hz s
  exact not_countable_complex h1

namespace KerPerp

variable {O L Y : Type*} [Ring O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {bar : O → O} {EF : LinearMap.BilinForm ℤ L}

def kerPerp (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')) (y : L →ₗ[O] Y) : Submodule O L where
  carrier := {t | ∀ v, y v = 0 → EF t v = 0}
  zero_mem' v _ := by simp
  add_mem' {t t'} ht ht' v hv := by simp [ht v hv, ht' v hv]
  smul_mem' a t ht v hv := by rw [hadj]; exact ht _ (by simp [hv])

variable {hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')} {y : L →ₗ[O] Y}

theorem mem_kerPerp {t : L} : t ∈ kerPerp hadj y ↔ ∀ v, y v = 0 → EF t v = 0 := Iff.rfl

theorem isotropic (hle : kerPerp hadj y ≤ LinearMap.ker y) {t t' : L} (ht : t ∈ kerPerp hadj y)
    (ht' : t' ∈ kerPerp hadj y) : EF t t' = 0 := ht t' (hle ht')

theorem apply_eq_of_eq {t : L} (ht : t ∈ kerPerp hadj y) {v v' : L} (h : y v = y v') : EF t v = EF t v' := by
  rw [← sub_eq_zero, ← map_sub]
  exact ht _ (by rw [map_sub, h, sub_self])

theorem exists_of_dual (hs : Function.Surjective EF) (φ : Module.Dual ℤ Y) :
    ∃ t ∈ kerPerp hadj y, ∀ v, -EF t v = φ (y v) := by
  obtain ⟨t, ht⟩ := hs (-(φ ∘ₗ y.toAddMonoidHom.toIntLinearMap))
  exact ⟨t, fun v hv => by simp [ht, hv], fun v => by simp [ht]⟩

theorem ker_iff [Module.Projective ℤ Y] (hs : Function.Surjective EF) (v : L) :
    y v = 0 ↔ ∀ t ∈ kerPerp hadj y, EF t v = 0 := by
  refine ⟨fun hv t ht => ht v hv, fun h => (Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_⟩
  obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hs φ
  rw [← hφ, h t ht, neg_zero]

variable (hadj)

def toDual (hy : Function.Surjective y) : kerPerp hadj y →ₗ[ℤ] Module.Dual ℤ Y :=
  LinearMap.mk₂ ℤ (fun t x => -EF t (Function.surjInv hy x))
    (fun _ _ _ => by simp [add_comm]) (fun _ _ _ => by simp)
    (fun t x x' => by
      rw [← neg_add, ← map_add]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))
    (fun k t x => by
      rw [smul_neg, ← map_zsmul]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))

@[simp] theorem toDual_apply (hy : Function.Surjective y) (t : kerPerp hadj y) (v : L) :
    toDual hadj hy t (y v) = -EF t v :=
  congrArg Neg.neg (apply_eq_of_eq t.2 (Function.surjInv_eq hy _))

theorem toDual_bijective (hb : Function.Bijective EF) (hy : Function.Surjective y) :
    Function.Bijective (toDual hadj hy) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    refine Subtype.ext (hb.1 (LinearMap.ext fun v => ?_))
    have := toDual_apply hadj hy t v
    rw [ht] at this
    simpa using this
  · intro φ
    obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hb.2 φ
    refine ⟨⟨t, ht⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨v, rfl⟩ := hy x
    rw [toDual_apply, hφ]

def equivDual (hb : Function.Bijective EF) (hy : Function.Surjective y) : kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y :=
  LinearEquiv.ofBijective _ (toDual_bijective hadj hb hy)

@[simp] theorem equivDual_apply (hb : Function.Bijective EF) (hy : Function.Surjective y) (t : kerPerp hadj y)
    (v : L) : equivDual hadj hb hy t (y v) = -EF t v := toDual_apply hadj hy t v

theorem neg_apply_equivDual_symm (hb : Function.Bijective EF) (hy : Function.Surjective y) (φ : Module.Dual ℤ Y)
    (v : L) : -EF ((equivDual hadj hb hy).symm φ) v = φ (y v) := by
  rw [← equivDual_apply hadj hb hy, LinearEquiv.apply_symm_apply]

theorem equivDual_smul (hb : Function.Bijective EF) (hy : Function.Surjective y) (a : O) (t : kerPerp hadj y)
    (x : Y) : equivDual hadj hb hy (a • t) x = equivDual hadj hb hy t (bar a • x) := by
  obtain ⟨v, rfl⟩ := hy x
  rw [← map_smul y, equivDual_apply, equivDual_apply, Submodule.coe_smul, hadj]

theorem finrank_kerPerp [Module.Free ℤ Y] [Module.Finite ℤ Y] (hb : Function.Bijective EF)
    (hy : Function.Surjective y) : Module.finrank ℤ (kerPerp hadj y) = Module.finrank ℤ Y := by
  rw [(equivDual hadj hb hy).finrank_eq, Module.finrank_linearMap_self]

variable {be : LinearMap.BilinForm ℤ Y}

def nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) : L →ₗ[O] kerPerp hadj y where
  toFun a := (equivDual hadj hb hy).symm (be (y a))
  map_add' a b := by simp
  map_smul' c a := (equivDual hadj hb hy).injective (LinearMap.ext fun x => by
    rw [RingHom.id_apply, equivDual_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul, hbe])

theorem neg_apply_nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) (a b : L) :
    -EF (nilTo hadj hb hy hbe a) b = be (y a) (y b) := neg_apply_equivDual_symm hadj hb hy _ b

variable {hadj}

section Nil

variable {nn : L → L}

theorem nil_eq_zero (hi : Function.Injective EF) (h : ∀ a b, -EF (nn a) b = be (y a) (y b)) {a : L}
    (ha : y a = 0) : nn a = 0 :=
  hi (LinearMap.ext fun b => by simpa [ha] using h a b)

end Nil

end KerPerp

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem orth_ker_iff (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ v.l = 0 := by
  constructor
  · intro h
    refine ⟨(Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_, A.Ef_bij.1 (LinearMap.ext fun l => ?_)⟩
    · simpa [EF_apply] using h (La.mk 0 φ.toAddMonoidHom 0) rfl
    · simpa [EF_apply] using h (La.mk 0 0 l) rfl
  · rintro ⟨hy, hl⟩ v' hv'
    simp [EF_apply, hy, hl, hv']

theorem y_l_eq_zero_iff (v : A.La) : v.y = 0 ∧ v.l = 0 ↔ ∃ n, v = La.mk 0 n 0 :=
  ⟨fun h => ⟨v.n, La.ext h.1 rfl h.2⟩, by rintro ⟨n, rfl⟩; exact ⟨rfl, rfl⟩⟩

theorem orth_ker_iff_exists (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ ∃ n, v = La.mk 0 n 0 :=
  (A.orth_ker_iff v).trans (A.y_l_eq_zero_iff v)

theorem smul_periodMap_mk_zero_fst_eq_neg_form (s : ℂ) (n : A.X →+ ℤ) (v' : A.La) :
    (s • A.P0 (La.mk 0 n 0)).1 v'.y = -(s * A.EF (La.mk 0 n 0) v') := by
  simp [EF_n_left]

theorem l_eq_zero_of_forall_smul_mem {v : A.La} (hv : v.y = 0) (h : ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂) : v.l = 0 := by
  have hc : Countable A.abelian₂ := Finsupp.Countable.of_moduleFinite (R := ℤ)
  refine Subtype.ext (eq_zero_of_forall_smul_mem_countable (S := (A.abelian₂ : Set _)) (Set.countable_coe_iff.1 hc) fun s => ?_)
  simpa [hv] using h s

theorem orth_ker_iff_forall_smul_mem (v : A.La) :
    (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂ := by
  rw [orth_ker_iff]
  refine and_congr_right fun hv => ⟨fun hl s => ?_, A.l_eq_zero_of_forall_smul_mem hv⟩
  simp [hv, hl]

theorem smul_periodMap_of_orthogonal_ker {v : A.La} (h : ∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) (s : ℂ) :
    (s • A.P0 v).2 = 0 ∧ ∀ v' : A.La, (s • A.P0 v).1 v'.y = -(s * A.EF v v') := by
  obtain ⟨n, rfl⟩ := (A.orth_ker_iff_exists v).1 h
  exact ⟨by simp, A.smul_periodMap_mk_zero_fst_eq_neg_form s n⟩

theorem nilTo_ne_zero {a : A.La} (ha : a.y ≠ 0) :
    KerPerp.nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a ≠ 0 := fun h => by
  have h1 := KerPerp.neg_apply_nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a a
  rw [h] at h1
  have h2 : (0 : ℤ) = A.be a.y a.y := by simpa using h1
  exact (A.be_pos _ ha).ne h2

example (c τ₀ : ℂ) : KerPerp.nilTo (gaussCM c τ₀).EF_smul (gaussCM c τ₀).EF_bijective
    (gaussCM c τ₀).yLin_surjective (gaussCM c τ₀).be_adj
    (La.mk (A := gaussCM c τ₀) (1 : GaussianInt) 0 0) ≠ 0 :=
  (gaussCM c τ₀).nilTo_ne_zero (one_ne_zero (α := GaussianInt))

end AnArc

end GlobalTheory
