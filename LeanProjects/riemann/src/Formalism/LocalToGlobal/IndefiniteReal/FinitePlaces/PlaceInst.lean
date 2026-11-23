import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceHeis

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem isSBHalf_iff {e : AE D} {Λ : AddSubgroup (WO S T)} {Φ : WO S T → ℂ} :
    IsSBHalf e Λ Φ ↔ Four.IsSB Λ (halfSub S T e) Φ := by
  constructor
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu t => hi u (AddSubgroup.mem_inf.1 hu).1 (AddSubgroup.mem_inf.1 hu).2 t, hl⟩
  · rintro ⟨hs, k, hk, hi, hl⟩
    exact ⟨hs, k, hk, fun u hu hue t => hi u (AddSubgroup.mem_inf.2 ⟨hu, hue⟩) t, hl⟩

theorem finite_qt_of {H : AddSubgroup (WO S T)} {k : ℕ} (R : Finset (WO S T))
    (hR : ∀ u ∈ H, ∃ r ∈ R, ∃ v ∈ H, u = r + k • v) : Finite (Four.Qt k H) := by
  classical
  let R' : Finset (WO S T) := R.filter (· ∈ H)
  let f : R' → Four.Qt k H := fun r => QuotientAddGroup.mk ⟨r.1, (Finset.mem_filter.1 r.2).2⟩
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H u =>
    obtain ⟨r, hr, v, hv, huv⟩ := hR u u.2
    have hrH : r ∈ H := by
      have := H.sub_mem u.2 (H.nsmul_mem hv k)
      rwa [huv, add_sub_cancel_right] at this
    refine ⟨⟨r, Finset.mem_filter.2 ⟨hr, hrH⟩⟩, ?_⟩
    apply QuotientAddGroup.eq.2
    rw [AddSubgroup.mem_addSubgroupOf]
    refine Four.mem_smulSub.2 ⟨v, hv, ?_⟩
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [huv]
    abel

theorem nsmul_eq_zero_WO {k : ℕ} (hk : 0 < k) {t : WO S T} (h : k • t = 0) : t = 0 := by
  have hu : IsUnit (k : AE D) := by
    have e1 : (k : AE D) = algebraMap D.host.F (AE D) (k : D.host.F) := by simp
    rw [e1]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hk.ne')).map _
  ext i j
  have := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] at this
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 this

open Classical in
theorem exists_placeModel (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ)
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoX : ∀ x, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ Λ)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hvX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u f₀ = f₀)
    (hvY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u f₀ = f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e₁ Λ 1 f₀ Tm ∧
      ∀ Φ, IsSBHalf e₁ Λ Φ → Tm Φ = Four.tfun (heisL ψ S T) (fun t y => ψ (symplO S T t y)) Λ
        (halfSub S T e₁) (halfSub S T (cA D e₁)) f₀ Φ := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  obtain ⟨Tm, hTe, htr, hmo, hva⟩ := Four.exists_model (ρ := heisL ψ S T) (χ := fun t y => ψ (symplO S T t y))
    (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁)) (f₀ := f₀)
    (hX := fun x hx x' hx' => heisL_add_half ψ S T he hx hx')
    (hY := fun y hy y' hy' => heisL_add_half ψ S T (cA_half_orth he) hy hy')
    (hXY := fun x _ y _ => heisL_comm ψ S T x y)
    (hχl := fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
    (hχr := fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
    (hχ0 := fun t y => psi_ne_zero ψ _)
    (hLL := fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
    (hdY := fun y hy h => hdY y hy fun x hx hxe => h x (AddSubgroup.mem_inf.2 ⟨hx, hxe⟩))
    (hfinX := fun k hk => by
      obtain ⟨R, hR⟩ := hfX k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (hfinY := fun k hk => by
      obtain ⟨R, hR⟩ := hfY k hk
      exact finite_qt_of S T R fun u hu => by
        obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
        exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
    (htf := fun k hk t h => nsmul_eq_zero_WO S T hk h)
    (hoX := fun x hx => hoX x hx) (hoY := fun y hy => hoY y hy)
    (hfX := fun u hu => hvX u (mi hu).1 (mi hu).2)
    (hfY := fun u hu => hvY u (mi hu).1 (mi hu).2)
  refine ⟨Tm, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ hΦ => hTe Φ ((isSBHalf_iff S T).1 hΦ)⟩
  · exact htr Φ ((isSBHalf_iff S T).1 hΦ) x hx
  · exact hmo Φ ((isSBHalf_iff S T).1 hΦ) y hy
  · rw [one_smul]
    exact hva

end Formalism.IndefR.Fin

end
