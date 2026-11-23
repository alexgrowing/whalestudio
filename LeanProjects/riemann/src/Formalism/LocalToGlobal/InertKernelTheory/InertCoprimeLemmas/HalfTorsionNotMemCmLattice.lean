import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementCurve
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDedekindZeta.LocOdd

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert.CurveGen

open PI.ClassNumImQ.ZetaNonvanishing₂.Loc (om om_coe basis coeff_unique)

variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}

theorem om_sq (hq : PI.ClassNumImQ.QuadData d K b) (m : ℤ) (hm : (d : ℤ) + 1 = 4 * m) :
    om hq * om hq = om hq - (m : 𝓞 K) := by
  have hb : b ^ 2 = -(d : K) := hq.2.2.2.1
  have hmK : (d : K) + 1 = 4 * (m : K) := by
    have h := congrArg (Int.cast : ℤ → K) hm
    push_cast at h
    exact h
  have ho' : algebraMap (𝓞 K) K (om hq) = (1 + b) / 2 := om_coe hq
  apply RingOfIntegers.ext
  have hc : ∀ y : 𝓞 K, (y : K) = algebraMap (𝓞 K) K y := fun _ => rfl
  rw [hc, hc, map_mul, map_sub, map_intCast, ho']
  linear_combination (1 / 4 : K) * hb - (1 / 4 : K) * hmK

theorem li (hq : PI.ClassNumImQ.QuadData d K b) : LinearIndependent ℤ ![(1 : 𝓞 K), om hq] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h : ((s : ℤ) : 𝓞 K) + ((t : ℤ) : 𝓞 K) * om hq = ((0 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * om hq := by
    simp only [zsmul_eq_mul, mul_one] at hst
    simpa using hst
  exact coeff_unique hq h

theorem sp (hq : PI.ClassNumImQ.QuadData d K b) :
    ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), om hq]) := by
  intro x _
  obtain ⟨m, n, rfl⟩ := basis hq x
  have h1 : (1 : 𝓞 K) ∈ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), om hq]) := Submodule.subset_span ⟨0, rfl⟩
  have h2 : om hq ∈ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), om hq]) := Submodule.subset_span ⟨1, rfl⟩
  have := add_mem (Submodule.smul_mem _ m h1) (Submodule.smul_mem _ n h2)
  simpa [zsmul_eq_mul] using this

def bw (hq : PI.ClassNumImQ.QuadData d K b) : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.Basis.mk (li hq) (sp hq)

theorem bw_repr (hq : PI.ClassNumImQ.QuadData d K b) (u v : ℤ) :
    (bw hq).repr ((u : 𝓞 K) + (v : 𝓞 K) * om hq) 0 = u ∧ (bw hq).repr ((u : 𝓞 K) + (v : 𝓞 K) * om hq) 1 = v := by
  have hx : ((u : 𝓞 K) + (v : 𝓞 K) * om hq) = u • (bw hq) 0 + v • (bw hq) 1 := by
    simp [bw, Module.Basis.mk_apply, zsmul_eq_mul]
  rw [hx, map_add, map_zsmul, map_zsmul, Module.Basis.repr_self, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

theorem hnf (hq : PI.ClassNumImQ.QuadData d K b) (m : ℤ) (hm : (d : ℤ) + 1 = 4 * m) (cc : Ideal (𝓞 K)) (hcc : cc ≠ ⊥) :
    ∃ (g a : ℕ) (k : ℤ), 0 < g ∧ 0 < a ∧ (a : ℤ) ∣ k * k + k + m ∧
      (∀ x : 𝓞 K, x ∈ cc ↔ ∃ u v : ℤ, x = (g : 𝓞 K) * ((u : 𝓞 K) * a + (v : 𝓞 K) * ((k : 𝓞 K) + om hq))) ∧
      Ideal.absNorm cc = g ^ 2 * a := by
  classical
  have hω : om hq * om hq = om hq - (m : 𝓞 K) := om_sq hq m hm
  have hN0 : Ideal.absNorm cc ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hcc
  have hNmem : ((Ideal.absNorm cc : ℕ) : 𝓞 K) ∈ cc := Ideal.absNorm_mem cc
  have hP1 : ∃ n : ℕ, 0 < n ∧ ∃ r : ℤ, ((r : 𝓞 K) + (n : 𝓞 K) * om hq) ∈ cc :=
    ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero hN0, 0, by simpa using cc.mul_mem_right (om hq) hNmem⟩
  obtain ⟨g, ⟨hg, r₀, hx₀⟩, hgmin⟩ : ∃ g : ℕ, (0 < g ∧ ∃ r : ℤ, ((r : 𝓞 K) + (g : 𝓞 K) * om hq) ∈ cc) ∧
      ∀ n < g, ¬ (0 < n ∧ ∃ r : ℤ, ((r : 𝓞 K) + (n : 𝓞 K) * om hq) ∈ cc) :=
    ⟨Nat.find hP1, Nat.find_spec hP1, fun n hn => Nat.find_min hP1 hn⟩
  have claim1 : ∀ r s : ℤ, ((r : 𝓞 K) + (s : 𝓞 K) * om hq) ∈ cc → (g : ℤ) ∣ s := by
    intro r s hx
    have hgz : (0 : ℤ) < g := by exact_mod_cast hg
    have ht0 : 0 ≤ s % g := Int.emod_nonneg _ hgz.ne'
    have ht1 : s % g < g := Int.emod_lt_of_pos _ hgz
    have hs' : s = s % (g : ℤ) + (g : ℤ) * (s / (g : ℤ)) := by
      exact (EuclideanDomain.mod_add_div s (g : ℤ)).symm
    have hsK : ((s : ℤ) : 𝓞 K) = ((s % g : ℤ) : 𝓞 K) + ((g : ℤ) : 𝓞 K) * ((s / g : ℤ) : 𝓞 K) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hs'
    have hmem : ((r - s / g * r₀ : ℤ) : 𝓞 K) + ((s % g : ℤ) : 𝓞 K) * om hq ∈ cc := by
      have h := cc.sub_mem hx (cc.mul_mem_left ((s / g : ℤ) : 𝓞 K) hx₀)
      convert h using 1
      push_cast at hsK ⊢
      linear_combination (-(om hq)) * hsK
    by_contra hndvd
    have ht_pos : 0 < s % g := by
      rcases ht0.lt_or_eq with h | h
      · exact h
      · exact absurd (Int.dvd_of_emod_eq_zero h.symm) hndvd
    have e : (((s % g).toNat : ℕ) : 𝓞 K) = ((s % g : ℤ) : 𝓞 K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg ht0]
    exact hgmin (s % g).toNat (by omega) ⟨by omega, r - s / g * r₀, by rw [e]; exact hmem⟩
  have hP2 : ∃ n : ℕ, 0 < n ∧ (n : 𝓞 K) ∈ cc := ⟨_, Nat.pos_of_ne_zero hN0, hNmem⟩
  obtain ⟨A, ⟨hA, hAmem⟩, hAmin⟩ : ∃ A : ℕ, (0 < A ∧ (A : 𝓞 K) ∈ cc) ∧ ∀ n < A, ¬ (0 < n ∧ (n : 𝓞 K) ∈ cc) :=
    ⟨Nat.find hP2, Nat.find_spec hP2, fun n hn => Nat.find_min hP2 hn⟩
  have claim2 : ∀ r : ℤ, ((r : ℤ) : 𝓞 K) ∈ cc → (A : ℤ) ∣ r := by
    intro r hr
    have hAz : (0 : ℤ) < A := by exact_mod_cast hA
    have ht0 : 0 ≤ r % A := Int.emod_nonneg _ hAz.ne'
    have ht1 : r % A < A := Int.emod_lt_of_pos _ hAz
    have hr' : r = r % (A : ℤ) + (A : ℤ) * (r / (A : ℤ)) := by
      exact (EuclideanDomain.mod_add_div r (A : ℤ)).symm
    have hrK : ((r : ℤ) : 𝓞 K) = ((r % A : ℤ) : 𝓞 K) + ((A : ℤ) : 𝓞 K) * ((r / A : ℤ) : 𝓞 K) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hr'
    have hmem : ((r % A : ℤ) : 𝓞 K) ∈ cc := by
      have h := cc.sub_mem hr (cc.mul_mem_left ((r / A : ℤ) : 𝓞 K) hAmem)
      convert h using 1
      push_cast at hrK ⊢
      linear_combination (-1 : 𝓞 K) * hrK
    by_contra hndvd
    have ht_pos : 0 < r % A := by
      rcases ht0.lt_or_eq with h | h
      · exact h
      · exact absurd (Int.dvd_of_emod_eq_zero h.symm) hndvd
    have e : (((r % A).toNat : ℕ) : 𝓞 K) = ((r % A : ℤ) : 𝓞 K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg ht0]
    exact hAmin (r % A).toNat (by omega) ⟨by omega, by rw [e]; exact hmem⟩
  have hgA : (g : ℤ) ∣ (A : ℤ) := claim1 0 A (by simpa using cc.mul_mem_right (om hq) hAmem)
  have hgr : (g : ℤ) ∣ r₀ := by
    have h := cc.mul_mem_left (om hq) hx₀
    have h2 : ((-(g * m) : ℤ) : 𝓞 K) + ((r₀ + g : ℤ) : 𝓞 K) * om hq ∈ cc := by
      convert h using 1
      push_cast
      linear_combination (-(g : 𝓞 K)) * hω
    have h3 := claim1 _ _ h2
    have h4 : (g : ℤ) ∣ (r₀ + g) - g := dvd_sub h3 (dvd_refl _)
    simpa using h4
  have hgA' : g ∣ A := by exact_mod_cast hgA
  obtain ⟨a, rfl⟩ := hgA'
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hA)
  obtain ⟨k, rfl⟩ := hgr
  have hmemiff : ∀ x : 𝓞 K, x ∈ cc ↔
      ∃ u v : ℤ, x = (g : 𝓞 K) * ((u : 𝓞 K) * a + (v : 𝓞 K) * ((k : 𝓞 K) + om hq)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, s, rfl⟩ := basis hq x
      obtain ⟨v, rfl⟩ := claim1 r s hx
      have hr : ((r - v * (g * k) : ℤ) : 𝓞 K) ∈ cc := by
        have h := cc.sub_mem hx (cc.mul_mem_left ((v : ℤ) : 𝓞 K) hx₀)
        convert h using 1
        push_cast
        ring
      obtain ⟨u, hu⟩ := claim2 _ hr
      refine ⟨u, v, ?_⟩
      have hr2 : r = (g : ℤ) * a * u + v * (g * k) := by
        push_cast at hu
        linear_combination hu
      rw [hr2]
      push_cast
      ring
    · rintro ⟨u, v, rfl⟩
      have h := cc.add_mem (cc.mul_mem_left ((u : ℤ) : 𝓞 K) hAmem) (cc.mul_mem_left ((v : ℤ) : 𝓞 K) hx₀)
      convert h using 1
      push_cast
      ring
  have hdiv : (a : ℤ) ∣ k * k + k + m := by
    have h := cc.mul_mem_left (om hq) hx₀
    obtain ⟨u, v, huv⟩ := (hmemiff _).1 h
    have e1 : ((g * (-m) : ℤ) : 𝓞 K) + ((g * (k + 1) : ℤ) : 𝓞 K) * om hq =
        ((g * (u * a + v * k) : ℤ) : 𝓞 K) + ((g * v : ℤ) : 𝓞 K) * om hq := by
      push_cast at huv ⊢
      linear_combination huv - (g : 𝓞 K) * hω
    obtain ⟨e2, e3⟩ := coeff_unique hq e1
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    have e4 : -m = u * a + v * k := mul_left_cancel₀ hg0 e2
    have e5 : k + 1 = v := mul_left_cancel₀ hg0 e3
    subst e5
    exact ⟨-u, by linear_combination (-1 : ℤ) * e4⟩
  set w : Fin 2 → cc := ![⟨((g * a : ℕ) : 𝓞 K), hAmem⟩, ⟨((g * k : ℤ) : 𝓞 K) + (g : 𝓞 K) * om hq, hx₀⟩] with hw
  have hli : LinearIndependent ℤ w := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg Subtype.val hst
    simp [zsmul_eq_mul] at h
    have e : ((s * (g * a) + t * (g * k) : ℤ) : 𝓞 K) + ((t * g : ℤ) : 𝓞 K) * om hq =
        ((0 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * om hq := by
      push_cast at h ⊢
      linear_combination h
    obtain ⟨e1, e2⟩ := coeff_unique hq e
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have ht : t = 0 := by
      rcases mul_eq_zero.mp e2 with h5 | h5
      · exact h5
      · exact absurd h5 hg0
    subst ht
    refine ⟨?_, rfl⟩
    have h6 : s * (g * a) = 0 := by simpa using e1
    rcases mul_eq_zero.mp h6 with h7 | h7
    · exact h7
    · exact absurd h7 (mul_ne_zero hg0 ha0)
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range w) := by
    rintro ⟨y, hy⟩ -
    obtain ⟨u, v, rfl⟩ := (hmemiff y).1 hy
    have h1 : w 0 ∈ Submodule.span ℤ (Set.range w) := Submodule.subset_span (Set.mem_range_self 0)
    have h2 : w 1 ∈ Submodule.span ℤ (Set.range w) := Submodule.subset_span (Set.mem_range_self 1)
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ u h1) (Submodule.smul_mem _ v h2)
    convert h3 using 1
    apply Subtype.ext
    simp [hw, zsmul_eq_mul]
    ring
  have hbI0 : ((Module.Basis.mk hli hsp 0 : cc) : 𝓞 K) = ((g * a : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * om hq := by
    simp [hw]
  have hbI1 : ((Module.Basis.mk hli hsp 1 : cc) : 𝓞 K) = ((g * k : ℤ) : 𝓞 K) + ((g : ℤ) : 𝓞 K) * om hq := by
    simp [hw]
  have hdet := Ideal.natAbs_det_basis_change (bw hq) cc (Module.Basis.mk hli hsp)
  have hdet2 : (bw hq).det (Subtype.val ∘ Module.Basis.mk hli hsp) = ((g * a : ℤ)) * g := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp only [Module.Basis.toMatrix_apply, Function.comp_apply]
    rw [hbI0, hbI1, (bw_repr hq _ _).1, (bw_repr hq _ _).2, (bw_repr hq _ _).1, (bw_repr hq _ _).2]
    ring
  have hnorm : Ideal.absNorm cc = g ^ 2 * a := by
    rw [← hdet, hdet2]
    rw [show ((g * a : ℤ)) * g = ((g ^ 2 * a : ℕ) : ℤ) by push_cast; ring]
    exact Int.natAbs_cast _
  exact ⟨g, a, k, hg, ha, hdiv, hmemiff, hnorm⟩

private theorem cmL_omega1_eq (a₁ : ℕ) (b₁ : ℤ) (d₁ : ℕ) (ha₁ : 0 < a₁) (hd₁ : 0 < d₁) (l₁ : ℂ) (hl₁ : l₁ ≠ 0) :
    (Formalism.L2.Th1.H.cmL a₁ b₁ d₁ ha₁ hd₁ l₁ hl₁).ω₁ = l₁ * a₁ := rfl

private theorem cmL_omega2_eq (a₁ : ℕ) (b₁ : ℤ) (d₁ : ℕ) (ha₁ : 0 < a₁) (hd₁ : 0 < d₁) (l₁ : ℂ) (hl₁ : l₁ ≠ 0) :
    (Formalism.L2.Th1.H.cmL a₁ b₁ d₁ ha₁ hd₁ l₁ hl₁).ω₂ = l₁ * Formalism.L2.Th1.F.cmTheta b₁ d₁ := rfl

theorem lat_eq (hq : PI.ClassNumImQ.QuadData d K b) (φ : K →+* ℂ) (hφ : φ b = Complex.I * (Real.sqrt d : ℂ))
    (hd : 0 < d) (cc : Ideal (𝓞 K)) (g a : ℕ) (k : ℤ) (ha : 0 < a)
    (hmem : ∀ x : 𝓞 K, x ∈ cc ↔ ∃ u v : ℤ, x = (g : 𝓞 K) * ((u : 𝓞 K) * a + (v : 𝓞 K) * ((k : 𝓞 K) + om hq)))
    (δ : ℂ) (hl : (g : ℂ) * δ ≠ 0) :
    AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} =
      (Formalism.L2.Th1.H.cmL a (2 * k + 1) d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup := by
  have ho' : algebraMap (𝓞 K) K (om hq) = (1 + b) / 2 := om_coe hq
  have hψ : ∀ y : 𝓞 K, φ (y : K) = (φ.comp (algebraMap (𝓞 K) K)) y := fun _ => rfl
  have hω : (φ.comp (algebraMap (𝓞 K) K)) (om hq) = (1 + Complex.I * (Real.sqrt d : ℂ)) / 2 := by
    rw [RingHom.comp_apply, ho', map_div₀, map_add, map_one, hφ, map_ofNat]
  have key : ∀ u v : ℤ, δ * φ ((((g : 𝓞 K) * ((u : 𝓞 K) * a + (v : 𝓞 K) * ((k : 𝓞 K) + om hq))) : 𝓞 K) : K) =
      (u : ℂ) * ((g : ℂ) * δ * a) + (v : ℂ) * ((g : ℂ) * δ * Formalism.L2.Th1.F.cmTheta (2 * k + 1) d) := by
    intro u v
    rw [hψ]
    simp only [map_mul, map_add, map_intCast, map_natCast, hω, Formalism.L2.Th1.F.cmTheta]
    push_cast
    ring
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    obtain ⟨u, v, rfl⟩ := (hmem c).1 hc
    rw [key u v]
    show _ ∈ (Formalism.L2.Th1.H.cmL a (2 * k + 1) d ha hd ((g : ℂ) * δ) hl).lattice
    rw [PeriodPair.mem_lattice]
    exact ⟨u, v, by rw [cmL_omega1_eq, cmL_omega2_eq]⟩
  · intro x hx
    obtain ⟨u, v, rfl⟩ := PeriodPair.mem_lattice.mp hx
    rw [cmL_omega1_eq, cmL_omega2_eq, ← key u v]
    exact AddSubgroup.subset_closure ⟨_, (hmem _).2 ⟨u, v, rfl⟩, rfl⟩

theorem form_eq (m k : ℤ) (a : ℕ) (hm : (d : ℤ) + 1 = 4 * m) (hdiv : (a : ℤ) ∣ k * k + k + m) :
    ∃ c₀ : ℤ, 4 * (a : ℤ) * c₀ = (2 * k + 1) ^ 2 + d := by
  obtain ⟨c, hc⟩ := hdiv
  exact ⟨c, by linear_combination (-4 : ℤ) * hc - hm⟩

end Formalism.L2.KerInert.CurveGen

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.FrobeniusOrbits
open Formalism.L2.Th1.H (cmL CmOK)

section Host

variable {R : Ranks}

theorem adjGen_top' {E : Type*} [Field E] [Algebra ℚ E] (x : E) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ x} = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ (y : E)).mp y.2
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨r, s, ?_⟩
  apply Subtype.ext
  have h1 : ∀ p : Polynomial ℚ, ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ x) p :
      IntermediateField.adjoin ℚ ({x} : Set E)) : E) = Polynomial.aeval x p :=
    fun p => by
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  rw [hrs, ← h1 r, ← h1 s]
  rfl

theorem quadK (H : Host R) :
    PI.ClassNumImQ.QuadData H.d ↥H.K (IntermediateField.AdjoinSimple.gen ℚ (H.sqd)) := by
  obtain ⟨-, hdp, -, hd16, -⟩ := H.hyp
  refine ⟨hdp, by omega, by omega, ?_, adjGen_top' H.sqd⟩
  exact Subtype.ext H.sqd_sq

theorem tie_host (H : Host R) (cc : Ideal (𝓞 H.K)) (δ : ℂ) (hcc : cc ≠ ⊥) (hodd : Odd (Ideal.absNorm cc)) (hδ : δ ≠ 0) :
    ∃ (a₀ g : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < H.d) (hl : (g : ℂ) * δ ≠ 0),
      CmOK a₀ b₀ c₀ H.d ∧ Ideal.absNorm cc = g ^ 2 * a₀ ∧ cc ≤ Ideal.span {(g : 𝓞 H.K)} ∧
      AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * H.φ₀ (((c : H.K) : H.E))} =
        (cmL a₀ b₀ H.d ha hd ((g : ℂ) * δ) hl).lattice.toAddSubgroup := by
  obtain ⟨-, hdp, -, hd16, -⟩ := H.hyp
  have hq := quadK H
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (H.d : ℤ) + 1 = 4 * m := ⟨((H.d : ℤ) + 1) / 4, by omega⟩
  obtain ⟨g, a, k, hg, ha, hdiv, hmem, hnorm⟩ := CurveGen.hnf hq m hm cc hcc
  obtain ⟨c₀, hc₀⟩ := CurveGen.form_eq m k a hm hdiv
  have hd : 0 < H.d := hdp.pos
  have hl : (g : ℂ) * δ ≠ 0 := mul_ne_zero (by exact_mod_cast hg.ne') hδ
  have hφ : (H.φ₀.comp (algebraMap H.K H.E)) (IntermediateField.AdjoinSimple.gen ℚ H.sqd) =
      Complex.I * (Real.sqrt H.d : ℂ) := by
    exact Formalism.L2.Ker.phi_b H
  have hodd' : Odd (g ^ 2 * a) := hnorm ▸ hodd
  have hcm : CmOK a (2 * k + 1) c₀ H.d := by
    unfold Formalism.L2.Th1.H.CmOK
    exact ⟨hc₀, (Nat.odd_mul.mp hodd').2, by omega, hdp⟩
  refine ⟨a, g, 2 * k + 1, c₀, ha, hd, hl, hcm, hnorm, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, v, rfl⟩ := (hmem x).1 hx
    exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
  · exact CurveGen.lat_eq hq (H.φ₀.comp (algebraMap H.K H.E)) hφ hd cc g a k ha hmem δ hl

end Host

theorem curve_lattice_compatible : CurveTie := by
  intro D cc δ hcc hodd hδ
  exact tie_host D.host cc δ hcc hodd hδ

end Formalism.L2.KerInert

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.FrobeniusOrbits
open Formalism.L2.Th1.H (cmL CmOK)

theorem delta_ne_of_base {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) : δ ≠ 0 := by
  intro hδ
  subst hδ
  obtain ⟨h1, h2, -⟩ : _ ∧ _ ∧ _ := B.t0
  have hle : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    show AddSubgroup.closure _ ≤ ⊥
    rw [AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  have h0 : 2 * (B.ω₀ / 2) = 0 := AddSubgroup.mem_bot.mp (hle h1)
  have h00 : B.ω₀ / 2 = 0 := (mul_eq_zero.mp h0).resolve_left two_ne_zero
  apply h2
  rw [h00, mul_zero]
  exact AddSubgroup.zero_mem _

end Formalism.L2.KerInert
