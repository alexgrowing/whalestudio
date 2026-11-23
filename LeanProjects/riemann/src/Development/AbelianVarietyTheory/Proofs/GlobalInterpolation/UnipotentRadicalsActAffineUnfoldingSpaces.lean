import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces

variable {F : Type} [Field F] {n' c' n c : ℕ}

theorem hom_ext {a b : ℕ} {x y : (Fin a → F) →ₗ[F] (Fin b → F)}
    (h : ∀ s l, x (Pi.single s 1) l = y (Pi.single s 1) l) : x = y := by
  ext s l
  simpa using h s l

noncomputable def linPart (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) :
    (Loc.FC n' c' n c → F) →ₗ[F] ((Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) where
  toFun t := Loc.xx1 xj t - Loc.xx1 xj 0
  map_add' t u := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply, Pi.add_apply, linearMap_unfolding_apply_single]
    split_ifs <;> simp
  map_smul' a t := hom_ext fun s l => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, linearMap_unfolding_apply_single, RingHom.id_apply]
    split_ifs <;> simp

theorem unfoldingAffineLinearMap_apply_freeEntry (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (p : Loc.FC n' c' n c) :
    Loc.xx1 xj t (Pi.single p.1.2 1) p.1.1 = t p := by
  rw [linearMap_unfolding_apply_single, dif_pos p.2]

theorem map_Ufl {xj : (Fin n' → F) →ₗ[F] (Fin n → F)} {x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v))
    (h3 : ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)
    (s : ℕ) {v : Fin (n' + c') → F} (hv : v ∈ Loc.Ufl F n' c' s) : x v ∈ Loc.Ufl F n c s := by
  have key : ∀ l : Fin (n' + c'), l.1 < n' + s → x (Pi.single l 1) ∈ Loc.Ufl F n c s := by
    intro l hl
    by_cases hln : l.1 < n'
    · have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) =
          Loc.inX F n' c' (Pi.single (⟨l.1, hln⟩ : Fin n') 1) := by
        funext m
        rw [inX_apply]
        split_ifs with hm
        · by_cases hml : m = l
          · subst hml
            simp
          · have hne : (⟨m.1, hm⟩ : Fin n') ≠ ⟨l.1, hln⟩ := fun he => hml (Fin.ext (by simpa using he))
            simp [hml, hne]
        · have hml : m ≠ l := fun he => hm (he ▸ hln)
          simp [hml]
      rw [hsingle, h1]
      exact inX_mem_Ufl s _
    · have hle : n' ≤ l.1 := not_lt.1 hln
      have hsingle : (Pi.single l (1 : F) : Fin (n' + c') → F) = Loc.eN F (n' + c') (n' + (l.1 - n')) := by
        funext m
        rw [Nat.add_sub_cancel' hle]
        by_cases hml : m = l
        · subst hml
          simp [Loc.eN]
        · have hv : m.1 ≠ l.1 := fun he => hml (Fin.ext he)
          simp [Loc.eN, hml, hv]
      rw [hsingle, ← sub_add_cancel (x (Loc.eN F (n' + c') (n' + (l.1 - n'))))
        (Loc.eN F (n + c) (n + (l.1 - n')))]
      exact Submodule.add_mem _ (Ufl_mono (by omega) (h3 (l.1 - n'))) (eN_mem_Ufl (by omega))
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hl : l.1 < n' + s
  · have hsm : (Pi.single l (v l) : Fin (n' + c') → F) = v l • Pi.single l 1 := by
      funext m
      by_cases hml : m = l
      · subst hml
        simp
      · simp [hml]
    rw [hsm, map_smul]
    exact Submodule.smul_mem _ _ (key l hl)
  · have hz : v l = 0 := (mem_Ufl.1 hv) l hl
    rw [hz, Pi.single_zero, map_zero]
    exact Submodule.zero_mem _

theorem affine_action : (∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s)) → ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ r' ∈ Loc.R1 F n' c', ∀ xj' : (Fin n' → F) →ₗ[F] (Fin n → F), ∃ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (T : (Loc.FC n' c' n c → F) ≃ₗ[F] (Loc.FC n' c' n c → F)) (b : Loc.FC n' c' n c → F), ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (T t + b) := by
  intro H F _ n' c' n c hc hc' r hr r' hr' xj'
  have hR : Loc.R1cond F n c r := hr.1
  have hR' : Loc.R1cond F n' c' r' := hr'.1
  obtain ⟨γ, hγ⟩ := exists_res hr
  obtain ⟨γ', hγ'⟩ := exists_res hr'
  obtain ⟨xj, hxj⟩ : ∃ xj : (Fin n' → F) →ₗ[F] (Fin n → F),
      xj = γ.symm.toLinearMap ∘ₗ xj' ∘ₗ γ'.symm.toLinearMap := ⟨_, rfl⟩
  have hy : ∀ t, ∃ t', r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' t' := by
    intro t
    obtain ⟨c1, c2, c3⟩ := (H F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
    refine (H F n' c' n c hc hc' xj' _).2 ⟨?_, ?_, ?_⟩
    · intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hγ', c1, hγ, hxj]
      simp
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hR'.2.1, c2, hR.2.1]
    · intro s
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hsplit : r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)))) - Loc.eN F (n + c) (n + s) =
          r (Loc.xx1 xj t (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s)) +
            (r (Loc.eN F (n + c) (n + s)) - Loc.eN F (n + c) (n + s)) +
            r (Loc.xx1 xj t (r' (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n' + c') (n' + s))) := by
        simp only [map_sub]
        abel
      rw [hsplit]
      exact Submodule.add_mem _ (Submodule.add_mem _ (hR.1 s _ (c3 s)) (hR.2.2 s))
        (hR.1 s _ (map_Ufl c1 c3 s (hR'.2.2 s)))
  obtain ⟨f, hf⟩ : ∃ f : (Loc.FC n' c' n c → F) → (Loc.FC n' c' n c → F), ∀ t p,
      f t p = (r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨_, fun _ _ => rfl⟩
  have hyf : ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap = Loc.xx1 xj' (f t) := by
    intro t
    obtain ⟨t', ht'⟩ := hy t
    have hft : f t = t' := by
      funext p
      rw [hf, ht', unfoldingAffineLinearMap_apply_freeEntry]
    rw [hft, ht']
  obtain ⟨L, hL⟩ : ∃ L : (Loc.FC n' c' n c → F) →ₗ[F] (Loc.FC n' c' n c → F), ∀ t p,
      L t p = (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1 :=
    ⟨{ toFun := fun t p => (r.toLinearMap ∘ₗ linPart xj t ∘ₗ r'.toLinearMap) (Pi.single p.1.2 1) p.1.1
       map_add' := fun t u => by
         funext p
         simp only [map_add, LinearMap.add_comp, LinearMap.comp_add, LinearMap.add_apply, Pi.add_apply]
       map_smul' := fun a t => by
         funext p
         simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_apply, Pi.smul_apply,
           RingHom.id_apply] }, fun _ _ => rfl⟩
  have hxx : ∀ t : Loc.FC n' c' n c → F, Loc.xx1 xj t = linPart xj t + Loc.xx1 xj 0 := by
    intro t
    simp only [linPart, LinearMap.coe_mk, AddHom.coe_mk, sub_add_cancel]
  have hLf : ∀ t, L t + f 0 = f t := by
    intro t
    funext p
    rw [Pi.add_apply, hL, hf, hf, hxx t]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_apply, Pi.add_apply]
  have hinj : Function.Injective L := by
    intro t u htu
    have hfe : f t = f u := by rw [← hLf t, ← hLf u, htu]
    have hyy : r.toLinearMap ∘ₗ Loc.xx1 xj t ∘ₗ r'.toLinearMap =
        r.toLinearMap ∘ₗ Loc.xx1 xj u ∘ₗ r'.toLinearMap := by rw [hyf t, hyf u, hfe]
    have hx : Loc.xx1 xj t = Loc.xx1 xj u := by
      refine LinearMap.ext fun v => ?_
      have hv := congrArg (fun g => r.symm (g (r'.symm v))) hyy
      simpa using hv
    funext p
    rw [← unfoldingAffineLinearMap_apply_freeEntry xj t p, ← unfoldingAffineLinearMap_apply_freeEntry xj u p, hx]
  refine ⟨xj, LinearEquiv.ofInjectiveEndo L hinj, f 0, fun t => ?_⟩
  rw [hyf t]
  congr 1
  exact (hLf t).symm

end GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces
