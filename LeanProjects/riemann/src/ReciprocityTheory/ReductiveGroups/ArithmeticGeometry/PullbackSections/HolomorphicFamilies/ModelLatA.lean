import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD FractionalIdeal

variable {r : ℕ}

abbrev Dinv (D : D7) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem cc_eq_conj (D : D7) (x : D.host.E) : cc x = D.host.conj x := by
  apply D.host.φ₀.injective
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [IsCMField.complexEmbedding_complexConj]
  exact (D.host.toHostAx.conjE_apply _ _).symm

theorem cc_cc (D : D7) (x : D.host.E) : cc (cc x) = x := by
  rw [cc_eq_conj, cc_eq_conj]
  exact Formalism.L2.Pj.conj_conj D x

theorem cc_mul (D : D7) (x y : D.host.E) : cc (x * y) = cc x * cc y := by
  simp only [cc, map_mul]

theorem int_cc (D : D7) {b : D.host.E} (hb : IsIntegral ℤ b) : IsIntegral ℤ (cc b) := by
  have h := hb.map ((D.host.conj : D.host.E →ₐ[ℚ] D.host.E).restrictScalars ℤ)
  rw [cc_eq_conj]
  exact h

theorem mem_one_of_int (D : D7) {z : D.host.E} (hz : IsIntegral ℤ z) :
    z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
  (mem_one_iff _).2 ⟨⟨z, hz⟩, rfl⟩

theorem int_of_mem_one (D : D7) {z : D.host.E}
    (hz : z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : IsIntegral ℤ z := by
  obtain ⟨c, rfl⟩ := (mem_one_iff _).1 hz
  exact NumberField.RingOfIntegers.isIntegral_coe c

theorem herm_smul_left {D : D7} (G : Matrix (Fin r) (Fin r) D.host.E) (c : D.host.E) (x y : Fin r → D.host.E) :
    herm G (c • x) y = c * herm G x y := by
  unfold herm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem herm_smul_right {D : D7} (G : Matrix (Fin r) (Fin r) D.host.E) (c : D.host.E) (x y : Fin r → D.host.E) :
    herm G x (c • y) = cc c * herm G x y := by
  unfold herm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring

theorem herm_add_left {D : D7} (G : Matrix (Fin r) (Fin r) D.host.E) (x x' y : Fin r → D.host.E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  unfold herm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.add_apply]
  ring

theorem herm_add_right {D : D7} (G : Matrix (Fin r) (Fin r) D.host.E) (x y y' : Fin r → D.host.E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  unfold herm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.add_apply, cc, map_add]
  ring

theorem AA_mul_inv (hP : FactPrincipalDatum) (D : D7) : D.host.AA * D.host.AA⁻¹ = 1 :=
  mul_inv_cancel₀ (AA_ne_zero hP D)

theorem int_of_AA_mul (hP : FactPrincipalDatum) (D : D7) {a b : D.host.E} (ha : a ∈ D.host.AA)
    (hb : b ∈ D.host.AA⁻¹) : ∃ c : 𝓞 D.host.E, algebraMap _ _ c = a * b := by
  have h := mul_mem_mul ha hb
  rw [AA_mul_inv hP D] at h
  exact (mem_one_iff _).1 h

theorem int_of_mul_Dinv (D : D7) {w : D.host.E} (hw : ∀ u ∈ Dinv D, w * u ∈ Dinv D) : IsIntegral ℤ w := by
  have h0 : Dinv D ≠ 0 := dual_ne_zero ℤ ℚ one_ne_zero
  have hle : spanSingleton (nonZeroDivisors (𝓞 D.host.E)) w * Dinv D ≤ Dinv D := by
    rw [mul_le]
    intro i hi j hj
    obtain ⟨c, rfl⟩ := (mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact mem_coe.1 (Submodule.smul_mem _ c (mem_coe.2 (hw j hj)))
  have h2 := mul_le_mul_left hle (Dinv D)⁻¹
  rw [mul_assoc, mul_inv_cancel₀ h0, mul_one] at h2
  exact int_of_mem_one D (h2 (mem_spanSingleton_self _ w))

theorem mem_AA_of (hP : FactPrincipalDatum) (D : D7) {w : D.host.E}
    (hw : ∀ b ∈ D.host.AA⁻¹, IsIntegral ℤ (b * w)) : w ∈ D.host.AA := by
  have hle : spanSingleton (nonZeroDivisors (𝓞 D.host.E)) w * D.host.AA⁻¹ ≤ 1 := by
    rw [mul_le]
    intro i hi j hj
    obtain ⟨c, rfl⟩ := (mem_spanSingleton _).1 hi
    rw [smul_mul_assoc, mul_comm w j]
    exact mem_coe.1 (Submodule.smul_mem _ c (mem_coe.2 (mem_one_of_int D (hw j hj))))
  have h2 := mul_le_mul_left hle D.host.AA
  rw [mul_assoc, inv_mul_cancel₀ (AA_ne_zero hP D), mul_one, one_mul] at h2
  exact h2 (mem_spanSingleton_self _ w)

theorem xi_mem_Dinv (hP : FactPrincipalDatum) (D : D7) {a w : D.host.E} (ha : a ∈ D.host.AA)
    (hw : w ∈ D.host.AAbar) : D.host.xi0 * (a * w) ∈ Dinv D := by
  rw [show Dinv D = _ from (dual_eq hP D).symm, ← mul_assoc]
  exact mul_mem_mul (mul_mem_mul (mem_spanSingleton_self _ _) ha) hw

theorem int_of_xi (hP : FactPrincipalDatum) (D : D7) {w : D.host.E}
    (hw : ∀ a ∈ D.host.AA, ∀ j ∈ D.host.AAbar, D.host.xi0 * (a * (j * w)) ∈ Dinv D) : IsIntegral ℤ w := by
  apply int_of_mul_Dinv D
  intro u hu
  rw [show Dinv D = _ from (dual_eq hP D).symm] at hu
  refine FractionalIdeal.mul_induction_on (C := fun u => w * u ∈ Dinv D) hu ?_ ?_
  · intro m hm n hn
    show w * (m * n) ∈ Dinv D
    refine FractionalIdeal.mul_induction_on (C := fun m => w * (m * n) ∈ Dinv D) hm ?_ ?_
    · intro s hs a ha
      obtain ⟨c, rfl⟩ := (mem_spanSingleton _).1 hs
      show w * (c • D.host.xi0 * a * n) ∈ Dinv D
      have h1 := hw a ha n hn
      have e : w * (c • D.host.xi0 * a * n) = c • (D.host.xi0 * (a * (n * w))) := by
        rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
        congr 1
        ring
      rw [e]
      exact mem_coe.1 (Submodule.smul_mem _ c (mem_coe.2 h1))
    · intro x y hx hy
      show w * ((x + y) * n) ∈ Dinv D
      rw [add_mul, mul_add]
      exact (Dinv D).coeToSubmodule.add_mem hx hy
  · intro x y hx hy
    show w * (x + y) ∈ Dinv D
    rw [mul_add]
    exact (Dinv D).coeToSubmodule.add_mem hx hy

def lattice₂ (D : D7) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) : Submodule (𝓞 D.host.E) (Fin r → D.host.E) where
  carrier := {v | ∀ a ∈ D.host.AA, a • v ∈ Λ}
  add_mem' := by
    intro v w hv hw a ha
    rw [smul_add]
    exact Λ.add_mem (hv a ha) (hw a ha)
  zero_mem' := by
    intro a _
    rw [smul_zero]
    exact Λ.zero_mem
  smul_mem' := by
    intro c v hv a ha
    show a • (c • v) ∈ Λ
    rw [← algebraMap_smul D.host.E c v, smul_smul, mul_comm a, ← smul_smul, algebraMap_smul]
    exact Λ.smul_mem c (hv a ha)

theorem mem_latP {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)} {v : Fin r → D.host.E} :
    v ∈ lattice₂ D Λ ↔ ∀ a ∈ D.host.AA, a • v ∈ Λ := Iff.rfl

theorem smul_mem_latP (hP : FactPrincipalDatum) {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)}
    {b : D.host.E} (hb : b ∈ D.host.AA⁻¹) {z : Fin r → D.host.E} (hz : z ∈ Λ) : b • z ∈ lattice₂ D Λ := by
  refine mem_latP.2 fun a ha => ?_
  obtain ⟨c, hc⟩ := int_of_AA_mul hP D ha hb
  rw [smul_smul, ← hc, algebraMap_smul]
  exact Λ.smul_mem c hz

section Dual

variable (hP : FactPrincipalDatum) {D : D7} (G : Matrix (Fin r) (Fin r) D.host.E)
  (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
  (hF : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, D.host.xi0 * herm G y z ∈ Dinv D)
include hP hF

theorem localLattice_form_integral {x y : Fin r → D.host.E} (hx : x ∈ lattice₂ D Λ) (hy : y ∈ lattice₂ D Λ) :
    IsIntegral ℤ (herm G x y) := by
  apply int_of_xi hP D
  intro a ha j hj
  have hj' : cc j ∈ D.host.AA := by rw [cc_eq_conj]; exact conj_mem_AA D hj
  have h1 := (hF (a • x)).1 (mem_latP.1 hx a ha) (cc j • y) (mem_latP.1 hy _ hj')
  rw [herm_smul_left, herm_smul_right, cc_cc] at h1
  exact h1

theorem mem_dual_localLattice_of_forall {x : Fin r → D.host.E} (hx : ∀ y ∈ lattice₂ D Λ, IsIntegral ℤ (herm G x y)) : x ∈ lattice₂ D Λ := by
  refine mem_latP.2 fun a ha => ?_
  refine (hF (a • x)).2 fun z hz => ?_
  have hcc : cc (herm G x z) ∈ D.host.AA := by
    apply mem_AA_of hP D
    intro b hb
    have h1 := int_cc D (hx _ (smul_mem_latP hP hb hz))
    rwa [herm_smul_right, cc_mul, cc_cc] at h1
  have hbar : herm G x z ∈ D.host.AAbar := by
    have h2 := conj_mem_AAbar D hcc
    rwa [← cc_eq_conj, cc_cc] at h2
  rw [herm_smul_left]
  exact xi_mem_Dinv hP D ha hbar

end Dual

theorem lat_eq_span (hP : FactPrincipalDatum) {D : D7} (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) :
    Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ lattice₂ D Λ, v = a • u} := by
  apply le_antisymm
  · intro z hz
    have h1 : (1 : D.host.E) ∈ D.host.AA * D.host.AA⁻¹ := by
      rw [AA_mul_inv hP D]; exact one_mem_one _
    have key := FractionalIdeal.mul_induction_on
      (C := fun w : D.host.E => w • z ∈ Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ lattice₂ D Λ, v = a • u})
      h1 (fun a ha b hb => by
        show (a * b) • z ∈ _
        rw [mul_smul]
        exact Submodule.subset_span ⟨a, ha, b • z, smul_mem_latP hP hb hz, rfl⟩)
      (fun x y hx hy => by
        show (x + y) • z ∈ _
        rw [add_smul]
        exact Submodule.add_mem _ hx hy)
    simpa using key
  · rw [Submodule.span_le]
    rintro v ⟨a, ha, u, hu, rfl⟩
    exact mem_latP.1 hu a ha

theorem normCc_mem_AA (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  obtain ⟨hB, -⟩ := bB_ne D
  have h1 : (1 : D.host.E) ∈ D.host.AA0 := by
    show (1 : D.host.E) ∈ ((D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹
    rw [mem_inv_iff hB]
    intro y hy
    rw [one_mul]
    exact coeIdeal_le_one hy
  have h2 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  have h3 := mul_mem_mul (mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) (P := D.host.E) h2) h1
  rw [map_natCast, mul_one] at h3
  exact h3

theorem int_of_mem_b (D : D7) {n : ℕ} (hn : (n : 𝓞 D.host.E) ∈ D.host.𝔟) {a : D.host.E} (ha : a ∈ D.host.AA) :
    ∃ c : 𝓞 D.host.E, algebraMap _ _ c = a * n := by
  obtain ⟨hB, -⟩ := bB_ne D
  have h1 := mul_mem_mul ha (mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) (P := D.host.E) hn)
  rw [map_natCast] at h1
  have e : D.host.AA * (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) =
      (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    show (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      ((D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ * _ = _
    rw [mul_assoc, inv_mul_cancel₀ hB, mul_one]
  rw [e] at h1
  exact (mem_one_iff _).1 (coeIdeal_le_one h1)

theorem localLattice_fg (D : D7) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (hΛ : Λ.FG) : (lattice₂ D Λ).FG := by
  set N : ℕ := Ideal.absNorm D.host.ccK
  have hN : (N : D.host.E) ≠ 0 := by
    have : N ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  let f : (Fin r → D.host.E) →ₗ[𝓞 D.host.E] (Fin r → D.host.E) := (N : 𝓞 D.host.E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (N : D.host.E) • x = (N : D.host.E) • y := by
      have e : ∀ z : Fin r → D.host.E, f z = (N : D.host.E) • z := fun z => by
        show (N : 𝓞 D.host.E) • z = _
        rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E) z, map_natCast]
      rw [← e, ← e]; exact hxy
    exact smul_right_injective _ hN h1
  apply Submodule.fg_of_fg_map_injective f hf
  have hI := isNoetherian_of_fg_of_noetherian Λ hΛ
  refine isNoetherian_submodule.1 hI _ ?_
  rintro _ ⟨v, hv, rfl⟩
  show (N : 𝓞 D.host.E) • v ∈ Λ
  rw [← algebraMap_smul D.host.E (N : 𝓞 D.host.E) v, map_natCast]
  exact mem_latP.1 hv _ (normCc_mem_AA D)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA
