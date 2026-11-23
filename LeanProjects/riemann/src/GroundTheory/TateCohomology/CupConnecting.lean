import Mathlib
import GroundTheory.TateCohomology.CupProduct
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G]

section Whisker

variable {A A' B B' : Rep k G} {p q n : ℕ}

theorem whiskerRight_tmul (φ : A ⟶ A') (a : A) (b : B) :
    (φ ▷ B).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = φ.hom a ⊗ₜ[k] b :=
  rfl

theorem whiskerLeft_tmul (ψ : B ⟶ B') (a : A) (b : B) :
    (A ◁ ψ).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = a ⊗ₜ[k] ψ.hom b :=
  rfl

theorem whiskerRight_cupCochain (φ : A ⟶ A') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (φ ▷ B).hom (cupCochain h f g x) = cupCochain h (fun v => φ.hom (f v)) g x := by
  rw [cupCochain_apply, whiskerRight_tmul, cupCochain_apply]

theorem whiskerLeft_cupCochain (ψ : B ⟶ B') (h : p + q = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    (A ◁ ψ).hom (cupCochain h f g x) = cupCochain h f (fun v => ψ.hom (g v)) x := by
  rw [cupCochain_apply, whiskerLeft_tmul, cupCochain_apply, Rep.hom_comm_apply]

end Whisker

section Connecting

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

theorem comp_d_apply {A A' : Rep k G} (φ : A ⟶ A') (i : ℕ) (y : (Fin i → G) → A)
    (v : Fin (i + 1) → G) :
    φ.hom ((inhomogeneousCochains.d A i).hom y v) =
      (inhomogeneousCochains.d A' i).hom (fun u => φ.hom (y u)) v := by
  simp only [inhomogeneousCochains.d_hom_apply, map_add, map_sum, map_smul, Rep.hom_comm_apply]

include hX in

theorem δ_π_eq {p : ℕ} (z : cocycles X.X₃ p) (y : (Fin p → G) → X.X₂)
    (hy : ∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) (x : cocycles X.X₁ (p + 1))
    (hx : ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) = (inhomogeneousCochains.d X.X₂ p).hom y v) :
    δ hX p (p + 1) rfl (π X.X₃ p z) = π X.X₁ (p + 1) x := by
  have h1 := δ_apply hX rfl (iCocycles X.X₃ p z) (by simpa using d_iCocycles z) y
    (funext hy) (iCocycles X.X₁ (p + 1) x) (funext fun v => by simpa using hx v)
  have e1 : cocyclesMk (iCocycles X.X₃ p z) (d_iCocycles z) = z := cocycles_ext (iCocycles_mk _ _)
  rw [e1] at h1
  rw [h1]
  congr 1
  exact cocycles_ext (iCocycles_mk _ _)

include hX in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem exists_f_eq_of_g_eq_zero (e : X.X₂) (he : X.g.hom e = 0) : ∃ a : X.X₁, X.f.hom a = e := by
  have : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hmem : e ∈ LinearMap.range X.f.hom.toLinearMap := this ▸ LinearMap.mem_ker.2 he
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩

include hX in

theorem exists_lift_of_cocycle {p : ℕ} (z : cocycles X.X₃ p) :
    ∃ (y : (Fin p → G) → X.X₂) (x : cocycles X.X₁ (p + 1)),
      (∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) ∧
        ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) =
          (inhomogeneousCochains.d X.X₂ p).hom y v := by
  have hg : Function.Surjective X.g.hom := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective X.f).1 hX.mono_f
  choose y hy using fun v => hg (iCocycles X.X₃ p z v)
  have hdy : ∀ v, X.g.hom ((inhomogeneousCochains.d X.X₂ p).hom y v) = 0 := fun v => by
    rw [comp_d_apply, show (fun u => X.g.hom (y u)) = iCocycles X.X₃ p z from funext hy,
      d_iCocycles]
    rfl
  choose x hx using fun v => exists_f_eq_of_g_eq_zero hX _ (hdy v)
  have hdx : (inhomogeneousCochains.d X.X₁ (p + 1)).hom x = 0 := by
    funext v
    apply hf
    rw [comp_d_apply, show (fun u => X.f.hom (x u)) = (inhomogeneousCochains.d X.X₂ p).hom y
      from funext hx, Pi.zero_apply, map_zero]
    exact congr(($(inhomogeneousCochains.d_comp_d (n := p) (A := X.X₂))).hom y v)
  exact ⟨y, cocyclesMk x hdx, hy, fun v => by rw [iCocycles_mk]; exact hx v⟩

variable (B : Rep k G)

theorem δ_cupH_left (hXB : (X.map (tensorRight B)).ShortExact) {p q n : ℕ} (h : p + q = n)
    (h' : p + 1 + q = n + 1) (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n (n + 1) rfl (cupH h a b) = cupH h' (δ hX p (p + 1) rfl a) b := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π]
  subst h
  refine δ_π_eq hXB (cupCocycles rfl z w) (cupCochain rfl y (iCocycles B q w)) (fun v => ?_)
    (cupCocycles h' x w) (fun v => ?_)
  · change (X.g ▷ B).hom (cupCochain rfl y (iCocycles B q w) v) =
      iCocycles (X.X₃ ⊗ B) (p + q) (cupCocycles rfl z w) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain]
    exact congrArg (fun f => cupCochain rfl f (iCocycles B q w) v) (funext hy)
  · change (X.f ▷ B).hom (iCocycles (X.X₁ ⊗ B) (p + q + 1) (cupCocycles h' x w) v) =
      (inhomogeneousCochains.d (X.X₂ ⊗ B) (p + q)).hom (cupCochain rfl y (iCocycles B q w)) v
    rw [iCocycles_cupCocycles, whiskerRight_cupCochain, d_cupCochain, d_iCocycles,
      cupCochain_zero_right, smul_zero, add_zero]
    exact congrArg (fun f => cupCochain h' f (iCocycles B q w) v) (funext hx)

theorem δ_cupH_right (hBX : (X.map (tensorLeft B)).ShortExact) {p q n : ℕ} (h : q + p = n)
    (h' : q + (p + 1) = n + 1) (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n (n + 1) rfl (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p (p + 1) rfl a) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hX z
  rw [δ_π_eq hX z y hy x hx, cupH_π, cupH_π, ← map_smul]
  subst h
  refine δ_π_eq hBX (cupCocycles rfl w z) (cupCochain rfl (iCocycles B q w) y) (fun v => ?_)
    ((-1 : k) ^ q • cupCocycles h' w x) (fun v => ?_)
  · change (B ◁ X.g).hom (cupCochain rfl (iCocycles B q w) y v) =
      iCocycles (B ⊗ X.X₃) (q + p) (cupCocycles rfl w z) v
    rw [iCocycles_cupCocycles, whiskerLeft_cupCochain]
    exact congrArg (fun f => cupCochain rfl (iCocycles B q w) f v) (funext hy)
  · change (B ◁ X.f).hom
        (iCocycles (B ⊗ X.X₁) (q + p + 1) ((-1 : k) ^ q • cupCocycles h' w x) v) =
      (inhomogeneousCochains.d (B ⊗ X.X₂) (q + p)).hom (cupCochain rfl (iCocycles B q w) y) v
    rw [map_smul, Pi.smul_apply, map_smul, iCocycles_cupCocycles, whiskerLeft_cupCochain,
      d_cupCochain, d_iCocycles, cupCochain_zero_left, zero_add, Pi.smul_apply]
    exact congrArg (fun f => (-1 : k) ^ q • cupCochain h' (iCocycles B q w) f v) (funext hx)

theorem δ_cupH_left' (hXB : (X.map (tensorRight B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : p + q = n) (h' : p' + q = m)
    (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n m hm (cupH h a b) = cupH h' (δ hX p p' hp a) b := by
  subst hp hm
  exact δ_cupH_left hX B hXB h h' a b

theorem δ_cupH_right' (hBX : (X.map (tensorLeft B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : q + p = n) (h' : q + p' = m)
    (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n m hm (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p p' hp a) := by
  subst hp hm
  exact δ_cupH_right hX B hBX h h' b a

end Connecting

end GroundTheory.GroupCoh
