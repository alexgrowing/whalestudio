import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRLinDual

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti flat_lam)
open Formalism.L2.G.Model.TS

def fockL {τ K : Type} [CommRing K] (Q : MvPolynomial τ K) : MvPolynomial τ K →ₗ[K] K where
  toFun P := fockR P Q
  map_add' a b := tsact_add_left a b Q
  map_smul' c a := by simpa using tsact_smul_left c a Q

theorem fockR_add_right {τ K : Type} [CommRing K] (g f f' : MvPolynomial τ K) :
    fockR g (f + f') = fockR g f + fockR g f' := by
  simp only [Formalism.L2.G.Model.TS.fockR, coeff_add, mul_add, add_mul, Finset.sum_add_distrib]

section Pair

variable {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

def LatM (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (d : Fin n' → ℕ)
    (M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    Submodule O (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (vecE n' s)) (M s))

theorem VS_eq (Kf : Type) [Field Kf] {n' m : ℕ} (d : Fin n' → ℕ) :
    VS Kf m (vecE n') d = Vsp Kf (flW (m := m) d) := by
  unfold VS Vsp
  congr 1
  funext s
  rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s, if_pos (letterWt_anti _ _ _)]

theorem Hten_flW (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (d : Fin n' → ℕ)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) :
    Hten O (flW (m := m) d) Λ = tensorLat O Kf (fun x => H0 O m (letterWt m (d x) (vecE n' x)) (Λ x)) := by
  unfold Hten
  congr 1
  funext s
  rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s]

theorem exists_thK (Kf : Type) [Field Kf] {n' m : ℕ} (hm : 1 ≤ m) (d : Fin n' → ℕ) :
    ∃ thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)),
      ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf) := by
  have hV : ∀ P : ↥(Pol Kf (ι := Fin n') (m + 1) d),
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf) ∈ Vsp Kf (flW (m := m) d) := by
    intro P
    rw [← VS_eq]
    exact (mem_tens_dw Kf m hm (vecE n') d _).mpr ⟨P, P.2, rfl⟩
  let f : ↥(Pol Kf (ι := Fin n') (m + 1) d) →ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)) :=
    LinearMap.codRestrict _ ((Th0 Kf m (vecE n')).toLinearMap.comp (Pol Kf (ι := Fin n') (m + 1) d).subtype) hV
  have hinj : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact Th0_inj Kf m hm (vecE n') d _ _ P.2 Q.2 h'
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ VS Kf m (vecE n') d := by
      rw [VS_eq]
      exact y.2
    obtain ⟨F, hF, hFy⟩ := (mem_tens_dw Kf m hm (vecE n') d _).mp hy
    exact ⟨⟨F, hF⟩, Subtype.ext hFy.symm⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩

variable {d : Fin n' → ℕ} (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

def TY (c : Kf) : ↥(Vsp Kf (flW (m := m) d)) →ₗ[Kf] Module.Dual Kf ↥(Vsp Kf (flW (m := m) d)) where
  toFun y := c • ((fockL ((thK.symm y : ↥(Pol Kf (ι := Fin n') (m + 1) d)) :
      MvPolynomial (Fin n' × Fin (m + 1)) Kf)).comp
    ((Pol Kf (ι := Fin n') (m + 1) d).subtype.comp thK.symm.toLinearMap))
  map_add' y y' := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply, fockL, LinearMap.coe_mk,
      AddHom.coe_mk, map_add, Submodule.coe_add, smul_eq_mul]
    rw [fockR_add_right, mul_add]
  map_smul' a y := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, fockL, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
      Submodule.coe_smul, smul_eq_mul, RingHom.id_apply]
    rw [tsact_smul_right]
    ring

theorem TY_apply (c : Kf) (P Q : ↥(Pol Kf (ι := Fin n') (m + 1) d)) :
    TY thK c (thK Q) (thK P) = c * fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)
      (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf) := by
  simp [TY, fockL]

theorem int_pair (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d) (G : MvPolynomial (Fin n' × Fin (m + 1)) O)
    (hG : G ∈ Pol O (m + 1) d) (E : MvPolynomial (Fin n' × Fin (m + 1)) O) :
    ∃ z : O, ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) *
      fockR (map (algebraMap O Kf) G) (map (algebraMap O Kf) E) = algebraMap O Kf z := by
  classical
  by_cases hD0 : (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf) = 0
  · refine ⟨0, ?_⟩
    rw [hD0, div_zero, zero_mul, map_zero]
  have hw : ∀ μ : Fin n' × Fin (m + 1) →₀ ℕ, ∃ w : O, μ ∈ G.support →
      (p : O) ^ κ * ((∏ j ∈ μ.support, (μ j).factorial : ℕ) : O) = ((∏ s, (d s).factorial : ℕ) : O) * w := by
    intro μ
    by_cases hμ : μ ∈ G.support
    · obtain ⟨w, hw⟩ := hMD μ ((mem_Pol.mp hG) μ hμ)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose w hw using hw
  refine ⟨∑ μ ∈ G.support, coeff μ G * coeff μ E * w μ, ?_⟩
  rw [fockR_eq_sum _ _ G.support (support_map_subset _ _), Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro μ hμ
  have h := congrArg (algebraMap O Kf) (hw μ hμ)
  simp only [map_mul, map_pow, map_natCast] at h
  simp only [coeff_map, map_mul]
  rw [div_mul_eq_mul_div, div_eq_iff hD0]
  linear_combination (algebraMap O Kf (coeff μ G) * algebraMap O Kf (coeff μ E)) * h

theorem sandwich (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf))
    (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d)
    (M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (u y : ↥(Vsp Kf (flW (m := m) d)))
    (hu : (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O d M)
    (hy : (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O d (fun s => ((M s)⁻¹).transpose)) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y u ∈ Set.range (algebraMap O Kf) := by
  obtain ⟨F, hF, hFu⟩ := (mem_tens_nabla O Kf m hm (vecE n') d M hM _).mp hu
  have hM' : ∀ s, IsUnit (((M s)⁻¹).transpose).det := fun s => by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det _ (hM s)
  obtain ⟨G, hG, hGy⟩ := (mem_tens_nabla O Kf m hm (vecE n') d _ hM' _).mp hy
  have hP : ((thK.symm u : ↥(Pol Kf (ι := Fin n') (m + 1) d)) : MvPolynomial (Fin n' × Fin (m + 1)) Kf) =
      Lin (fun s => Aa (vecE n' s) (M s)⁻¹) (map (algebraMap O Kf) F) := by
    apply Th0_inj Kf m hm (vecE n') d _ _ (thK.symm u).2 (Lin_Pol _ _ (map_Pol _ _ hF))
    rw [← hthK, LinearEquiv.apply_symm_apply, ← hFu]
  have hQ : ((thK.symm y : ↥(Pol Kf (ι := Fin n') (m + 1) d)) : MvPolynomial (Fin n' × Fin (m + 1)) Kf) =
      Lin (fun s => Aa (vecE n' s) (((M s)⁻¹).transpose)⁻¹) (map (algebraMap O Kf) G) := by
    apply Th0_inj Kf m hm (vecE n') d _ _ (thK.symm y).2 (Lin_Pol _ _ (map_Pol _ _ hG))
    rw [← hthK, LinearEquiv.apply_symm_apply, ← hGy]
  have e := TY_apply thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (thK.symm u) (thK.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
  obtain ⟨z, hz⟩ := int_pair (Kf := Kf) p κ hMD F hF G
  refine ⟨z, ?_⟩
  rw [e, hP, hQ, fockR_Lin_dual _ _ (fun s => Aa_dual (vecE n' s) (M s) (hM s))]
  exact hz.symm

end Pair

end Formalism.MainNotions.TestSideCounting
