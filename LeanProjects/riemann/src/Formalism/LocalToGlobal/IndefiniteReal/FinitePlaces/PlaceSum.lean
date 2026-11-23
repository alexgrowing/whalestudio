import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceInst

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IdemSumOrth (D : D7) : Prop :=
  ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∃ es : Formalism.L2.DIV.Pl D.host.E → AE D, (∀ PP ∈ P, IsSplitIdem D (es PP)) ∧ e = ∑ PP ∈ P, es PP ∧
      ∀ PP ∈ P, ∀ PP' ∈ P, PP ≠ PP' → es PP * es PP' = 0 ∧ es PP * cA D (es PP') = 0

theorem isSplitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem psi_neg_one (ψ : AddChar (AF D.host.F) ℂ) {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

variable (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem symplO_orth {a b : AE D} (hab : a * cA D b = 0) {x y : WO S T} (hx : IsHalf a x) (hy : IsHalf b y) :
    symplO S T x y = 0 := by
  have hz : ∀ i j c d, incA D (S.gram⁻¹ i j) * cA D (y c j) * incA D (T.gram c d) * x d i = 0 := by
    intro i j c d
    rw [← hy c j, ← hx d i, map_mul]
    linear_combination (incA D (S.gram⁻¹ i j) * cA D (y c j) * incA D (T.gram c d) * x d i) * hab
  simp [symplO, hO, hz]

theorem symplO_sum_right {ι : Type*} (x : WO S T) (s : Finset ι) (y : ι → WO S T) :
    symplO S T x (∑ i ∈ s, y i) = ∑ i ∈ s, symplO S T x (y i) :=
  map_sum (AddMonoidHom.mk' (fun y => symplO S T x y) (fun y y' => symplO_add_right S T x y y')) y s

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO_zero_right]

theorem vac_of_sum (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ) {ι : Type*} (P : Finset ι) (es : ι → AE D)
    (hes : ∀ i ∈ P, es i * es i = es i)
    (horth : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → es i * cA D (es j) = 0)
    (hΛ : ∀ i ∈ P, ∀ u ∈ Λ, u.map (fun a => es i * a) ∈ Λ)
    (hvac : ∀ i ∈ P, ∀ u ∈ Λ, IsHalf (es i) u → heisO ψ S T u f₀ = f₀) :
    ∀ u ∈ Λ, IsHalf (∑ i ∈ P, es i) u → heisO ψ S T u f₀ = f₀ := by
  classical
  have hhalf : ∀ i ∈ P, ∀ u : WO S T, IsHalf (es i) (u.map (fun a => es i * a)) := by
    intro i hi u k l
    simp only [Matrix.map_apply]
    rw [← mul_assoc, hes i hi]
  have key : ∀ s : Finset ι, s ⊆ P → ∀ u ∈ Λ,
      heisO ψ S T (∑ i ∈ s, u.map (fun a => es i * a)) f₀ = f₀ := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _ u _
      rw [Finset.sum_empty, heisO_zero]
    · intro i s his ih hsub u hu
      have hiP : i ∈ P := hsub (Finset.mem_insert_self _ _)
      have hs' : s ⊆ P := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.sum_insert his]
      have hsym : symplOH S T (u.map (fun a => es i * a)) (∑ j ∈ s, u.map (fun a => es j * a)) = 0 := by
        rw [symplOH, symplO_sum_right, Finset.sum_eq_zero, mul_zero]
        intro j hj
        exact symplO_orth S T (horth i hiP j (hs' hj) fun h => his (h ▸ hj)) (hhalf i hiP u) (hhalf j (hs' hj) u)
      have h1 := heisO_heisO ψ S T (u.map (fun a => es i * a)) (∑ j ∈ s, u.map (fun a => es j * a)) f₀
      rw [hsym, AddChar.map_zero_eq_one, one_smul, ih hs' u hu,
        hvac i hiP _ (hΛ i hiP u hu) (hhalf i hiP u)] at h1
      exact h1.symm
  intro u hu hue
  have hdec : u = ∑ i ∈ P, u.map (fun a => es i * a) := by
    ext k l
    rw [Matrix.sum_apply]
    simp only [Matrix.map_apply]
    rw [← Finset.sum_mul, hue k l]
  rw [hdec]
  exact key P subset_rfl u hu

theorem placeModelExistsSum_of (h : PlaceLatDual D) (hO : IdemSumOrth D) : PlaceModelExistsSum D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he f₀ hf₀ hlat
  obtain ⟨hi, -, hP⟩ := h ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hd2, hd3, hfin, hop⟩ := hP P e he
  obtain ⟨es, hes, hsum, horth⟩ := hO P e he
  have vacE : ∀ u ∈ latAll S T ΛS ΛT, IsHalf e u → heisO ψ S T u f₀ = f₀ := by
    rw [hsum]
    exact vac_of_sum ψ S T _ f₀ P es (fun i hi' => (hes i hi').1) (fun i hi' j hj hij => (horth i hi' j hj hij).2)
      (fun i hi' u hu => hi (es i) (hes i hi') u hu) (fun i hi' u hu hue => hlat.2 (es i) (hes i hi') u hu hue)
  have vacC : ∀ u ∈ latAll S T ΛS ΛT, IsHalf (cA D e) u → heisO ψ S T u f₀ = f₀ := by
    rw [hsum, map_sum]
    refine vac_of_sum ψ S T _ f₀ P (fun i => cA D (es i)) (fun i hi' => (isSplitIdem_cA (hes i hi')).1)
      (fun i hi' j hj hij => ?_) (fun i hi' u hu => hi _ (isSplitIdem_cA (hes i hi')) u hu)
      (fun i hi' u hu hue => hlat.2 _ (isSplitIdem_cA (hes i hi')) u hu hue)
    rw [← map_mul, (horth i hi' j hj hij).2, map_zero]
  have hcc : cA D (cA D e) = e := cA_cA e
  refine ⟨?_, ?_⟩
  · obtain ⟨Tm, hTm, -⟩ := exists_placeModel ψ S T e he.2 (latAll S T ΛS ΛT) f₀
      (fun x hx hxe y hy hye => (hd2 y hye).2 hy x hx hxe)
      (fun y hye h' => (hd2 y hye).1 h')
      (fun k hk => hfin k hk e (Or.inl rfl)) (fun k hk => hfin k hk (cA D e) (Or.inr rfl))
      (fun x hx => hop e (Or.inl rfl) x hx) (fun y hy => hop (cA D e) (Or.inr rfl) y hy)
      vacE vacC
    exact ⟨Tm, hTm⟩
  · obtain ⟨Tm, hTm, -⟩ := exists_placeModel ψ S T (cA D e) (cA_half_orth he.2) (latAll S T ΛS ΛT) f₀
      (by
        rw [hcc]
        intro x hx hxe y hy hye
        rw [symplO_swap S T y x]
        exact psi_neg_one ψ ((hd2 x hxe).2 hx y hy hye))
      (by
        rw [hcc]
        intro y hye h'
        refine (hd3 y hye).1 fun y' hy' hy'e => ?_
        have := psi_neg_one ψ (h' y' hy' hy'e)
        rwa [symplO_swap S T y y', neg_neg] at this)
      (fun k hk => hfin k hk (cA D e) (Or.inr rfl))
      (by rw [hcc]; exact fun k hk => hfin k hk e (Or.inl rfl))
      (fun x hx => hop (cA D e) (Or.inr rfl) x hx)
      (by rw [hcc]; exact fun y hy => hop e (Or.inl rfl) y hy)
      vacC
      (by rw [hcc]; exact vacE)
    exact ⟨Tm, hTm⟩

end Formalism.IndefR.Fin

end
