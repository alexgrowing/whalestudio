import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom

open CategoryTheory

universe v v' u u'

noncomputable section

namespace GlobalTheory.CompanionTheory.AltCech

open GlobalTheory GlobalTheory.PD

section Signs

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

def invSign (τ : κ → ι) (s : Finset κ) (x : κ) : ℤ :=
  (∏ b ∈ s, if x < b ∧ τ b < τ x then -1 else 1) * ∏ a ∈ s, if a < x ∧ τ x < τ a then -1 else 1

theorem sortSign_insert (τ : κ → ι) {s : Finset κ} {x : κ} (hx : x ∉ s) :
    sortSign τ (insert x s) = sortSign τ s * invSign τ s x := by
  unfold sortSign invSign
  rw [Finset.prod_insert hx]
  simp only [Finset.prod_insert hx, Finset.prod_mul_distrib, lt_irrefl, false_and, if_false,
    one_mul]
  ring

theorem cubeSign_eq_prod (t : Finset ι) (i : ι) :
    cubeSign t i = ∏ j ∈ t, if j < i then -1 else 1 := by
  rw [cubeSign, Finset.prod_ite]
  simp

theorem invSign_eq (τ : κ → ι) {s : Finset κ} {x : κ} (hs : Set.InjOn τ s)
    (hx : ∀ a ∈ s, τ a ≠ τ x) :
    invSign τ s x = cubeSign s x * cubeSign (s.image τ) (τ x) := by
  have hxs : ∀ a ∈ s, a ≠ x := fun a ha e => hx a ha (congrArg τ e)
  rw [cubeSign_eq_prod, cubeSign_eq_prod, Finset.prod_image hs, invSign,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a ha => ?_
  have h1 := hx a ha
  have h2 := hxs a ha
  rcases lt_or_gt_of_ne h1 with h3 | h3 <;> rcases lt_or_gt_of_ne h2 with h4 | h4 <;>
    simp [h3, h4, h3.le, h4.le, not_lt.2 h3.le, not_lt.2 h4.le]

theorem image_erase_of_injOn (τ : κ → ι) {t : Finset κ} {i : κ} (hi : i ∈ t)
    (ht : Set.InjOn τ t) : (t.erase i).image τ = (t.image τ).erase (τ i) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨fun e => h1 (ht h2 hi e), a, h2, rfl⟩
  · rintro ⟨h1, a, h2, rfl⟩
    exact ⟨a, ⟨fun e => h1 (congrArg τ e), h2⟩, rfl⟩

theorem sign_erase (τ : κ → ι) {t : Finset κ} {i : κ} (hi : i ∈ t) (ht : Set.InjOn τ t) :
    cubeSign t i * sortSign τ (t.erase i) = sortSign τ t * cubeSign (t.image τ) (τ i) := by
  have hs : Set.InjOn τ (t.erase i : Finset κ) := ht.mono (by simp [Finset.erase_subset])
  have hx : ∀ a ∈ t.erase i, τ a ≠ τ i := fun a ha e =>
    (Finset.mem_erase.1 ha).1 (ht (Finset.mem_erase.1 ha).2 hi e)
  have h1 : sortSign τ t = sortSign τ (t.erase i) * invSign τ (t.erase i) i := by
    rw [← sortSign_insert τ (Finset.notMem_erase i t), Finset.insert_erase hi]
  rw [h1, invSign_eq τ hs hx, image_erase_of_injOn τ hi ht,
    cubeSign_erase_of_le t le_rfl, cubeSign_erase_of_le (t.image τ) le_rfl]
  have h2 := cubeSign_mul_self (t.image τ) (τ i)
  linear_combination (-(cubeSign t i * sortSign τ (t.erase i))) * h2

theorem injOn_erase_swap (τ : κ → ι) {t : Finset κ} {a b : κ} (hab : a ≠ b)
    (hτ : τ a = τ b) (hb : b ∈ t) (hi : Set.InjOn τ (t.erase a : Finset κ)) :
    Set.InjOn τ (t.erase b : Finset κ) := by
  intro u hu w hw e
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hu hw hi
  have mem : ∀ c, c ∈ t → c ≠ b → (if c = a then b else c) ∈ (t : Set κ) \ {a} := by
    intro c hc hcb
    by_cases h : c = a
    · simp [h, hb, hab.symm]
    · simp [h, hc]
  have val : ∀ c, τ (if c = a then b else c) = τ c := by
    intro c
    by_cases h : c = a
    · simp [h, hτ]
    · simp [h]
  have := hi (by simpa using mem u hu.1 hu.2) (by simpa using mem w hw.1 hw.2)
    (by rw [val, val, e])
  by_cases h1 : u = a <;> by_cases h2 : w = a
  · rw [h1, h2]
  · simp only [h1, h2, if_true, if_false] at this
    exact absurd this.symm hw.2
  · simp only [h1, h2, if_true, if_false] at this
    exact absurd this hu.2
  · simpa [h1, h2] using this

theorem sign_collision (τ : κ → ι) {t : Finset κ} {a b : κ} (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    (hτ : τ a = τ b) (hi : Set.InjOn τ (t.erase a : Finset κ)) :
    cubeSign t a * sortSign τ (t.erase a) + cubeSign t b * sortSign τ (t.erase b) = 0 := by
  set r := (t.erase a).erase b with hr
  have hr' : r = (t.erase b).erase a := Finset.erase_right_comm
  have hbm : b ∈ t.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have ham : a ∈ t.erase b := Finset.mem_erase.2 ⟨hab, ha⟩
  have hs : Set.InjOn τ (r : Finset κ) := hi.mono (by simp [hr, Finset.erase_subset])
  have hx : ∀ c ∈ r, τ c ≠ τ b := fun c hc e => by
    have h1 := Finset.mem_erase.1 hc
    exact h1.1 (hi h1.2 hbm e)
  have hx' : ∀ c ∈ r, τ c ≠ τ a := fun c hc => hτ ▸ hx c hc
  have e1 : sortSign τ (t.erase a) = sortSign τ r * invSign τ r b := by
    rw [← sortSign_insert τ (Finset.notMem_erase b _), Finset.insert_erase hbm]
  have e2 : sortSign τ (t.erase b) = sortSign τ r * invSign τ r a := by
    rw [← sortSign_insert τ (by rw [hr']; exact Finset.notMem_erase a _), hr', Finset.insert_erase ham]
  have e3 : cubeSign r b = cubeSign (t.erase a) b := cubeSign_erase_of_le _ le_rfl
  have e4 : cubeSign r a = cubeSign (t.erase b) a := by rw [hr']; exact cubeSign_erase_of_le _ le_rfl
  have e5 := cubeSign_mul_erase ha hb hab
  rw [e1, e2, invSign_eq τ hs hx, invSign_eq τ hs hx', e3, e4, hτ]
  linear_combination (sortSign τ r * cubeSign (r.image τ) (τ b)) * e5

end Signs

section AltHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} {S : Type u'} [Ring R] [Ring S]

structure AltHom (τ : κ → ι) (σ : R →+* S) (A : Cube.{v} ι R) (B : Cube.{v'} κ S) where

  app : ∀ t : Finset κ, A.obj (t.image τ) →ₛₗ[σ] B.obj t

  app_res : ∀ {s t : Finset κ} (h : s ⊆ t) (x : A.obj (s.image τ)),
    app t (Cube.res A (Finset.image_subset_image h) x) = Cube.res B h (app s x)

namespace AltHom

variable {τ : κ → ι} {σ : R →+* S} {A : Cube.{v} ι R} {B : Cube.{v'} κ S} (P : AltHom τ σ A B)

def total : (∀ s, A.obj s) →ₛₗ[σ] ∀ t, B.obj t where
  toFun X t := if (t.image τ).card = t.card then sortSign τ t • P.app t (X (t.image τ)) else 0
  map_add' X Y := by
    funext t
    by_cases h : (t.image τ).card = t.card <;> simp [h, smul_add]
  map_smul' r X := by
    funext t
    by_cases h : (t.image τ).card = t.card <;> simp [h, smul_comm (sortSign τ t) (σ r)]

theorem total_of_inj (X : ∀ s, A.obj s) {t : Finset κ} (h : Set.InjOn τ (t : Set κ)) :
    P.total X t = sortSign τ t • P.app t (X (t.image τ)) :=
  if_pos (Finset.card_image_iff.2 h)

theorem total_of_not (X : ∀ s, A.obj s) {t : Finset κ} (h : ¬ Set.InjOn τ (t : Set κ)) :
    P.total X t = 0 :=
  if_neg fun e => h (Finset.card_image_iff.1 e)

theorem totalD_total (X : ∀ s, A.obj s) (t : Finset κ) :
    Cube.totalD B (P.total X) t = P.total (Cube.totalD A X) t := by
  rw [Cube.totalD_apply]
  by_cases ht : Set.InjOn τ (t : Set κ)
  · rw [total_of_inj _ _ ht, Cube.totalD_apply, Finset.sum_image ht, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hs : Set.InjOn τ (t.erase i : Finset κ) := ht.mono (by simp [Finset.erase_subset])
    rw [total_of_inj _ _ hs, map_zsmul, ← P.app_res (Finset.erase_subset i t), map_zsmul,
      Cube.res_congr A X (image_erase_of_injOn τ hi ht) _ (Finset.erase_subset _ _),
      smul_smul, smul_smul, sign_erase τ hi ht]
  · rw [total_of_not _ _ ht]
    obtain ⟨a, ha, b, hb, hτab, hab⟩ : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      simpa [Set.InjOn] using ht
    rw [Finset.sum_eq_add_of_mem a b ha hb hab]
    · by_cases hi : Set.InjOn τ (t.erase a : Finset κ)
      · have hj := injOn_erase_swap τ hab hτab hb hi
        have e : (t.erase a).image τ = (t.erase b).image τ := by
          ext y
          simp only [Finset.mem_image, Finset.mem_erase]
          constructor
          · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
            by_cases h : c = b
            · exact ⟨a, ⟨hab, ha⟩, by rw [h, hτab]⟩
            · exact ⟨c, ⟨h, h2⟩, rfl⟩
          · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
            by_cases h : c = a
            · exact ⟨b, ⟨hab.symm, hb⟩, by rw [h, hτab]⟩
            · exact ⟨c, ⟨h, h2⟩, rfl⟩
        rw [total_of_inj _ _ hi, total_of_inj _ _ hj, map_zsmul, map_zsmul,
          ← P.app_res (Finset.erase_subset a t), ← P.app_res (Finset.erase_subset b t),
          Cube.res_congr A X e _ (Finset.image_subset_image (Finset.erase_subset b t)),
          smul_smul, smul_smul, ← add_smul, sign_collision τ ha hb hab hτab hi, zero_smul]
      · have hj : ¬ Set.InjOn τ (t.erase b : Finset κ) := fun h =>
          hi (injOn_erase_swap τ hab.symm hτab.symm ha h)
        rw [total_of_not _ _ hi, total_of_not _ _ hj]
        simp
    · intro c hc hcab
      have : ¬ Set.InjOn τ (t.erase c : Finset κ) := fun h =>
        hab (h (by simp [ha, Ne.symm hcab.1]) (by simp [hb, Ne.symm hcab.2]) hτab)
      rw [total_of_not _ _ this]
      simp

def term (p : ℕ) : Cube.Term A p →ₛₗ[σ] Cube.Term B p where
  toFun x t := P.total (Cube.extend A p x) t.1
  map_add' x y := funext fun t => by rw [map_add, map_add]; rfl
  map_smul' r x := funext fun t => by rw [map_smul, map_smulₛₗ]; rfl

theorem term_of_card {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : (t.1.image τ).card = p) :
    P.term p x t = sortSign τ t.1 • P.app t.1 (x ⟨t.1.image τ, h⟩) := by
  change P.total (Cube.extend A p x) t.1 = _
  rw [total_of_inj _ _ (Finset.card_image_iff.1 (h.trans t.2.symm)), Cube.extend_apply_of_eq A x h]

theorem term_of_not {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : (t.1.image τ).card ≠ p) : P.term p x t = 0 :=
  total_of_not _ _ fun e => h ((Finset.card_image_iff.2 e).trans t.2)

theorem term_d (p : ℕ) (x : Cube.Term A p) :
    P.term (p + 1) (Cube.d A p x) = Cube.d B p (P.term p x) := by
  funext t
  rw [Cube.d_apply_eq_totalD B (P.term p x) (P.total (Cube.extend A p x)) (fun _ => rfl),
    totalD_total]
  by_cases h : (t.1.image τ).card = p + 1
  · rw [term_of_card _ _ _ h, total_of_inj _ _ (Finset.card_image_iff.1 (h.trans t.2.symm)),
      Cube.d_apply_eq_totalD A x (Cube.extend A p x)
        (fun s => (Cube.extend_apply_of_eq A x s.2).symm)]
  · rw [term_of_not _ _ _ h, total_of_not _ _ fun e => h ((Finset.card_image_iff.2 e).trans t.2)]

def cocycle (p : ℕ) : LinearMap.ker (Cube.d A p) →ₛₗ[σ] LinearMap.ker (Cube.d B p) :=
  ((P.term p).domRestrict _).codRestrict _ fun x => by
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, ← term_d, x.2, map_zero]

@[simp]
theorem coe_cocycle (p : ℕ) (x : LinearMap.ker (Cube.d A p)) :
    (P.cocycle p x).1 = P.term p x.1 := rfl

theorem cechClass_cocycle_eq_zero (p : ℕ) (x : LinearMap.ker (Cube.d A (p + 1)))
    (h : cechClass A p x = 0) : cechClass B p (P.cocycle (p + 1) x) = 0 := by
  cases p with
  | zero => rw [(cechClass_zero_eq_zero_iff A x).1 h, map_zero, map_zero]
  | succ p =>
    obtain ⟨y, hy⟩ := (cechClass_succ_eq_zero_iff A p x).1 h
    exact (cechClass_succ_eq_zero_iff B p _).2 ⟨P.term _ y, by rw [← term_d, hy, coe_cocycle]⟩

def homology (p : ℕ) : (cechComplex A).homology p →ₛₗ[σ] (cechComplex B).homology p :=
  ((LinearMap.ker (cechClass A p)).liftQ ((cechClass B p).comp (P.cocycle (p + 1)))
    (P.cechClass_cocycle_eq_zero p)).comp
    ((cechClass A p).quotKerEquivOfSurjective (cechClass_surjective A p)).symm.toLinearMap

@[simp]
theorem homology_cechClass (p : ℕ) (x : LinearMap.ker (Cube.d A (p + 1))) :
    P.homology p (cechClass A p x) = cechClass B p (P.cocycle (p + 1) x) := by
  have h : ((cechClass A p).quotKerEquivOfSurjective (cechClass_surjective A p)).symm
      (cechClass A p x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  exact congrArg ((LinearMap.ker (cechClass A p)).liftQ ((cechClass B p).comp (P.cocycle (p + 1)))
    (P.cechClass_cocycle_eq_zero p)) h

end AltHom

theorem AltHom.homology_δ {τ : κ → ι} {σ : R →+* S}
    {C : ShortComplex (Cube.{v} ι R)} {D : ShortComplex (Cube.{v'} κ S)}
    (hC : (C.map (cechFunctor ι R)).ShortExact) (hD : (D.map (cechFunctor κ S)).ShortExact)
    (ψ₁ : AltHom τ σ C.X₁ D.X₁) (ψ₂ : AltHom τ σ C.X₂ D.X₂) (ψ₃ : AltHom τ σ C.X₃ D.X₃)
    (hf : ∀ t x, ψ₂.app t ((C.f.app (t.image τ)).hom x) = (D.f.app t).hom (ψ₁.app t x))
    (hg : ∀ t x, ψ₃.app t ((C.g.app (t.image τ)).hom x) = (D.g.app t).hom (ψ₂.app t x))
    (p : ℕ) (x : (cechComplex C.X₃).homology p) :
    ψ₁.homology (p + 1) ((hC.δ p (p + 1) rfl).hom x) =
      (hD.δ p (p + 1) rfl).hom (ψ₃.homology p x) := by
  have tf : ∀ (q : ℕ) (y : Cube.Term C.X₁ q),
      ψ₂.term q (Cube.termMap C.f q y) = Cube.termMap D.f q (ψ₁.term q y) := by
    intro q y
    funext t
    by_cases h : (t.1.image τ).card = q
    · rw [Cube.termMap_apply, AltHom.term_of_card _ _ _ h, AltHom.term_of_card _ _ _ h, map_zsmul]
      exact congrArg _ (hf t.1 _)
    · rw [Cube.termMap_apply, AltHom.term_of_not _ _ _ h, AltHom.term_of_not _ _ _ h, map_zero]
  have tg : ∀ (q : ℕ) (y : Cube.Term C.X₂ q),
      ψ₃.term q (Cube.termMap C.g q y) = Cube.termMap D.g q (ψ₂.term q y) := by
    intro q y
    funext t
    by_cases h : (t.1.image τ).card = q
    · rw [Cube.termMap_apply, AltHom.term_of_card _ _ _ h, AltHom.term_of_card _ _ _ h, map_zsmul]
      exact congrArg _ (hg t.1 _)
    · rw [Cube.termMap_apply, AltHom.term_of_not _ _ _ h, AltHom.term_of_not _ _ _ h, map_zero]
  obtain ⟨x₃, rfl⟩ := cechClass_surjective C.X₃ p x
  obtain ⟨x₂, x₁, h₂, h₁⟩ := exists_lift_cechCocycle hC p x₃
  rw [δ_cechClass hC p x₃ x₂ x₁ h₂ h₁, AltHom.homology_cechClass, AltHom.homology_cechClass]
  refine (δ_cechClass hD p _ (ψ₂.term _ x₂) _ ?_ ?_).symm
  · rw [AltHom.coe_cocycle, ← h₂, tg]
  · rw [AltHom.coe_cocycle, ← AltHom.term_d, ← h₁, tf]

end AltHom

section Ab

variable {T T' : TopCat.{u}} {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

open SheafPull TopologicalSpace Opposite

theorem map_map_thin (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {A B C : (Opens T)ᵒᵖ} (a : A ⟶ B)
    (b : B ⟶ C) (c : A ⟶ C) (y : P.obj A) : P.map b (P.map a y) = P.map c y := by
  have : a ≫ b = c := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [← this, Functor.map_comp]
  rfl

def altAb (f : T' ⟶ T) {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G)
    {V : Opens T} {W : Opens T'} {U : ι → Opens T} {U' : κ → Opens T'} (τ : κ → ι)
    (hτ : ∀ t : Finset κ, cechOpen W U' t ≤ (Opens.map f).obj (cechOpen V U (t.image τ))) :
    AltHom τ (RingHom.id ℤ) (cechAbCube F.obj V U) (cechAbCube G.obj W U') where
  app t :=
    (((G.obj.map (homOfLE (hτ t)).op).hom.comp
      (φ.hom.app (op (cechOpen V U (t.image τ)))).hom).toIntLinearMap :
        F.obj.obj (op (cechOpen V U (t.image τ))) →ₗ[ℤ] G.obj.obj (op (cechOpen W U' t)))
  app_res {s t} h x := by
    change G.obj.map _ (φ.hom.app _ (F.obj.map _ x)) = G.obj.map _ (G.obj.map _ (φ.hom.app _ x))
    refine (congrArg (G.obj.map _) (ConcreteCategory.congr_hom (φ.hom.naturality _) x)).trans ?_
    exact (map_map_thin _ _ _ (homOfLE ((cechOpen_anti W U' h).trans (hτ s))).op _).trans
      (map_map_thin _ _ _ _ _).symm

theorem altAb_app (f : T' ⟶ T) {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G)
    {V : Opens T} {W : Opens T'} {U : ι → Opens T} {U' : κ → Opens T'} (τ : κ → ι)
    (hτ : ∀ t : Finset κ, cechOpen W U' t ≤ (Opens.map f).obj (cechOpen V U (t.image τ)))
    (t : Finset κ) (x : F.obj.obj (op (cechOpen V U (t.image τ)))) :
    (altAb f φ τ hτ).app t x =
      G.obj.map (homOfLE (hτ t)).op (φ.hom.app (op (cechOpen V U (t.image τ))) x) := rfl

theorem altAb_comm (f : T' ⟶ T) {A B : AbSheaf T} {A' B' : AbSheaf T'} (a : A ⟶ B) (b : A' ⟶ B')
    (φ₁ : A ⟶ (push f).obj A') (φ₂ : B ⟶ (push f).obj B') (h : a ≫ φ₂ = φ₁ ≫ (push f).map b)
    {V : Opens T} {W : Opens T'} {U : ι → Opens T} {U' : κ → Opens T'} (τ : κ → ι)
    (hτ : ∀ t : Finset κ, cechOpen W U' t ≤ (Opens.map f).obj (cechOpen V U (t.image τ)))
    (t : Finset κ) (x : (cechAbCube A.obj V U).obj (t.image τ)) :
    (altAb f φ₂ τ hτ).app t (((cechAbCubeMap V U a.hom).app (t.image τ)).hom x) =
      ((cechAbCubeMap W U' b.hom).app t).hom ((altAb f φ₁ τ hτ).app t x) := by
  change B'.obj.map _ (φ₂.hom.app _ (a.hom.app _ x)) = b.hom.app _ (A'.obj.map _ (φ₁.hom.app _ x))
  have h₁ : ∀ y : A.obj.obj (op (cechOpen V U (t.image τ))),
      φ₂.hom.app (op (cechOpen V U (t.image τ))) (a.hom.app (op (cechOpen V U (t.image τ))) y) =
        b.hom.app (op ((Opens.map f).obj (cechOpen V U (t.image τ))))
          (φ₁.hom.app (op (cechOpen V U (t.image τ))) y) := fun y =>
    ConcreteCategory.congr_hom
      (congrArg (fun m : A ⟶ (push f).obj B' => m.hom.app (op (cechOpen V U (t.image τ)))) h) y
  refine (congrArg _ (h₁ x)).trans ?_
  exact (ConcreteCategory.congr_hom (b.hom.naturality (homOfLE (hτ t)).op) _).symm

theorem sortSign_singleton (τ : κ → ι) (j : κ) : sortSign τ ({j} : Finset κ) = 1 := by
  simp [sortSign]

theorem altAb_homology_toCechAbH (f : T' ⟶ T) {F : AbSheaf T} {G : AbSheaf T'}
    (φ : F ⟶ (push f).obj G) {V : Opens T} {W : Opens T'} {U : ι → Opens T} {U' : κ → Opens T'}
    (τ : κ → ι)
    (hτ : ∀ t : Finset κ, cechOpen W U' t ≤ (Opens.map f).obj (cechOpen V U (t.image τ)))
    (hW : W ≤ (Opens.map f).obj V) (y : F.obj.obj (op V)) :
    (altAb f φ τ hτ).homology 0 (toCechAbH F.obj V U y) =
      toCechAbH G.obj W U' (G.obj.map (homOfLE hW).op (φ.hom.app (op V) y)) := by
  refine (congrArg _ (presheafToCechH_apply (F.obj ⋙ abToIntModule) V U y)).trans (Eq.trans ?_
    (presheafToCechH_apply (G.obj ⋙ abToIntModule) W U' _).symm)
  refine (AltHom.homology_cechClass _ 0 ⟨_, _⟩).trans (congrArg _ (Subtype.ext (funext fun t => ?_)))
  obtain ⟨t, ht⟩ := t
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 ht
  have hc : (({j} : Finset κ).image τ).card = 0 + 1 := by simp
  refine (AltHom.term_of_card _ _ ⟨_, ht⟩ hc).trans ?_
  rw [sortSign_singleton, one_smul]
  change G.obj.map _ (φ.hom.app _ (F.obj.map _ y)) = G.obj.map _ (G.obj.map _ (φ.hom.app _ y))
  refine (congrArg (G.obj.map _) (ConcreteCategory.congr_hom (φ.hom.naturality _) y)).trans ?_
  exact (map_map_thin _ _ _ (homOfLE ((hτ {j}).trans ((Opens.map f).map (homOfLE (cechOpen_le V U _))).le)).op _).trans
    (map_map_thin _ _ _ _ _).symm

theorem altAb_comparison [Finite ι] [Finite κ] (f : T' ⟶ T) {V : Opens T} {W : Opens T'}
    {U : ι → Opens T} {U' : κ → Opens T'} (hc : V ≤ ⨆ i, U i) (hc' : W ≤ ⨆ j, U' j)
    (hW : W ≤ (Opens.map f).obj V) (τ : κ → ι)
    (hτ : ∀ t : Finset κ, cechOpen W U' t ≤ (Opens.map f).obj (cechOpen V U (t.image τ)))
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G)
    (hF : CechAcyclic V U F) (hG : CechAcyclic W U' G) (n : ℕ) (x : cechAbH F.obj V U n) :
    cechAbHEquivH' hc' hG n ((altAb f φ τ hτ).homology n x) =
      SheafPull.pull.{u, u} f φ n (homOfLE hW) (cechAbHEquivH' hc hF n x) := by
  induction n generalizing F G with
  | zero =>
    obtain ⟨y, rfl⟩ := (cechAbHZeroEquiv F.property hc).symm.surjective x
    refine (congrArg _ (altAb_homology_toCechAbH f φ τ hτ hW y)).trans
      ((cechAbHEquivH'_toCechAbH hc' hG _).trans (Eq.trans ?_
        (congrArg _ (cechAbHEquivH'_toCechAbH hc hF y).symm)))
    apply (SheafLES.equivZero G W).injective
    rw [AddEquiv.apply_symm_apply, SheafPull.equivZero_pull, AddEquiv.apply_symm_apply]
  | succ n ih =>
    have hS := Flasque.injectiveShortComplex_shortExact F
    have hS' := Flasque.injectiveShortComplex_shortExact G
    have inj : Injective (Flasque.injectiveShortComplex F).X₂ :=
      inferInstanceAs (Injective (Injective.under F))
    have a₃ := CechAcyclic.of_shortExact₃ hS hF (cechAcyclic_of_injective _)
    have a₃' := CechAcyclic.of_shortExact₃ hS' hG (cechAcyclic_of_injective _)
    obtain ⟨ψ, rfl⟩ := exists_hom_injectiveShortComplex f φ
    obtain ⟨y, rfl⟩ := cechAbδ_surjective hS hF n x
    have key := AltHom.homology_δ
      (C := (Flasque.injectiveShortComplex F).map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor V U))
      (D := (Flasque.injectiveShortComplex G).map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor W U'))
      (cechAbSheafFunctor_shortExact hS hF) (cechAbSheafFunctor_shortExact hS' hG)
      (altAb f ψ.τ₁ τ hτ) (altAb f ψ.τ₂ τ hτ) (altAb f ψ.τ₃ τ hτ)
      (fun t x => altAb_comm f _ _ _ _ ψ.comm₁₂.symm τ hτ t x)
      (fun t x => altAb_comm f _ _ _ _ ψ.comm₂₃.symm τ hτ t x) n y
    refine (congrArg _ key).trans ((cechAbHEquivH'_δ hc' hS' hG a₃' n _).trans ?_)
    refine (congrArg _ (ih ψ.τ₃ a₃ a₃' y)).trans ?_
    refine (SheafPull.pull_δ f n hS hS' ψ (homOfLE hW) _).symm.trans ?_
    exact congrArg _ (cechAbHEquivH'_δ hc hS hF a₃ n y).symm

end Ab

section Scheme

open AlgebraicGeometry

variable {X : Scheme.{u}} {ι : Type} [LinearOrder ι]

theorem exists_ab_cocycle (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (F : X.Modules)
    (V : X.Opens) (U : ι → X.Opens) (n : ℕ)
    (z : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1))) :
    ∃ w : LinearMap.ker (Cube.d (cechAbCube F.presheaf V U) (n + 1)),
      (cechAbCubeToCube R F V U).cocycle (n + 1) w = z := by
  have hb := (cechAbCubeToCube R F V U).term_bijective (fun _ _ => Function.bijective_id)
  obtain ⟨w, hw⟩ := (hb n).2 z.1
  have hd : Cube.d (cechAbCube F.presheaf V U) (n + 1) w = 0 := by
    apply (hb (n + 1)).1
    rw [Cube.SemiHom.term_d, hw, map_zero]
    exact z.2
  exact ⟨⟨w, hd⟩, Subtype.ext hw⟩

theorem toΓ_eq_zsmul (G : X.Modules) (O : X.Opens) {a b : sectionsOn G O} (m : ℤ) (h : a = m • b) :
    sectionsOn.toΓ G O a = m • sectionsOn.toΓ G O b := by
  rw [h, map_zsmul]

theorem toΓ_eq_zero (G : X.Modules) (O : X.Opens) {a : sectionsOn G O} (h : a = 0) :
    sectionsOn.toΓ G O a = 0 := by
  rw [h, map_zero]

end Scheme

section Main

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cechHEquivCohOn_altPull : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) (ι κ : Type) [LinearOrder ι] [Finite ι] [LinearOrder κ] [Finite κ]
    (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] (S : Type) [CommRing S] [Algebra S Γ(Y, ⊤)] (σ : R →+* S)
    (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
    (V : X.Opens) (W : Y.Opens) (U : ι → X.Opens) (U' : κ → Y.Opens)
    (hc : V ≤ ⨆ i, U i) (hc' : W ≤ ⨆ j, U' j) (hW : W ≤ g ⁻¹ᵁ V) (τ : κ → ι)
    (hτ : ∀ t : Finset κ, cechOpen W U' t ≤ g ⁻¹ᵁ cechOpen V U (t.image τ))
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)
    (hF : CechAcyclicMod V U F) (hG : CechAcyclicMod W U' G) (n : ℕ)
    (z : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1)))
    (z' : LinearMap.ker (Cube.d (cechCube S G W U') (n + 1))),
    (∀ (t : {s : Finset κ // s.card = n + 1}) (ht : (t.1.image τ).card = n + 1),
      (z'.1 t : sectionsOn G (cechOpen W U' t.1)) = sortSign τ t.1 • sectionsOn.res S G (hτ t.1)
        (sectionsOn.mapOver hσ φ (cechOpen V U (t.1.image τ))
          (z.1 ⟨t.1.image τ, ht⟩ : sectionsOn F (cechOpen V U (t.1.image τ))))) →
    (∀ t : {s : Finset κ // s.card = n + 1}, (t.1.image τ).card ≠ n + 1 → z'.1 t = 0) →
    cechHEquivCohOn S hc' hG n (cechClass _ n z') = cohOn.pull hσ φ hW n (cechHEquivCohOn R hc hF n (cechClass _ n z)) := by
  intro X Y g ι κ _ _ _ _ R _ _ S _ _ σ hσ V W U U' hc hc' hW τ hτ F G φ hF hG n z z' h1 h2
  obtain ⟨w, rfl⟩ := exists_ab_cocycle R F V U n z
  obtain ⟨w', rfl⟩ := exists_ab_cocycle S G W U' n z'
  have hcoc : (altAb g.base (toAbSheafPush φ) τ hτ).cocycle (n + 1) w = w' := by
    refine Subtype.ext (funext fun t => ?_)
    by_cases ht : (t.1.image τ).card = n + 1
    · exact (AltHom.term_of_card _ _ t ht).trans (toΓ_eq_zsmul G _ _ (h1 t ht)).symm
    · exact (AltHom.term_of_not _ _ t ht).trans (toΓ_eq_zero G _ (h2 t ht)).symm
  have e (R' : Type) [CommRing R'] {Z : Scheme.{0}} [Algebra R' Γ(Z, ⊤)] (F' : Z.Modules) (V' : Z.Opens)
      {ι' : Type} [LinearOrder ι'] (U' : ι' → Z.Opens)
      (w : LinearMap.ker (Cube.d (cechAbCube F'.presheaf V' U') (n + 1))) :
      cechClass _ n ((cechAbCubeToCube R' F' V' U').cocycle (n + 1) w) =
        cechAbHEquiv R' F' V' U' n (cechClass _ n w) :=
    ((cechAbCubeToCube R' F' V' U').homology_cechClass n w).symm
  apply (cohOn.toH' G W n).injective
  rw [e, e]
  refine (toH'_cechHEquivCohOn S hc' hG n _).trans ?_
  refine Eq.trans ?_ (cohOn.toH'_pull hσ φ hW _).symm
  refine Eq.trans ?_ (congrArg _ (toH'_cechHEquivCohOn R hc hF n _).symm)
  have k := altAb_comparison g.base hc hc' hW τ hτ (toAbSheafPush φ) (cechAcyclicMod_iff.1 hF)
    (cechAcyclicMod_iff.1 hG) n (cechClass _ n w)
  exact (congrArg _ ((congrArg (cechClass _ n) hcoc).symm.trans
    (AltHom.homology_cechClass _ n w).symm)).trans k

end Main

end GlobalTheory.CompanionTheory.AltCech
