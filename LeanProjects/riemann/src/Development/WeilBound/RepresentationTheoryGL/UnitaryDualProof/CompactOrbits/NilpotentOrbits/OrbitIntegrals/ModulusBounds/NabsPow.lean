import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.ModulEq
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.Imports
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetSurj
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.LaurentCoeffZero

noncomputable section

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

theorem nabs_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b : kˣ) : GlobalTheory.SplitWeil.nabs k (a * b) = GlobalTheory.SplitWeil.nabs k a * GlobalTheory.SplitWeil.nabs k b := by
  simp [GlobalTheory.SplitWeil.nabs, map_mul]

theorem nabs_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : kˣ) (m : ℕ) : GlobalTheory.SplitWeil.nabs k (a ^ m) = GlobalTheory.SplitWeil.nabs k a ^ m := by
  simp [GlobalTheory.SplitWeil.nabs, map_pow]

theorem nabs_pos {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : kˣ) : 0 < GlobalTheory.SplitWeil.nabs k a :=
  NNReal.coe_pos.2 distribHaarChar_pos

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem modBound [CharZero k] : ModBound (k := k) := by
  intro n Z hCR hdB c hc p P w hp hnil hv hT hU
  set x := p.1 - c with hx_def
  have hcB : c ∈ Bz Z := fun a ha => hCR.1 a ha c hc
  have hxB : x ∈ Bz Z := by
    intro a ha
    have h1 : a * p.1 = p.1 * a := hp a ha
    have h2 : a * c = c * a := hcB a ha
    rw [hx_def, mul_sub, sub_mul, h1, h2]
  let Dg : kˣ → GL (Fin n) k := fun t => P * ⟨diagonal (fun i => ((t ^ w i : kˣ) : k)),
    diagonal (fun i => (((t ^ w i)⁻¹ : kˣ) : k)),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact Units.mul_inv _,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact Units.inv_mul _⟩ * P⁻¹
  have hDg : ∀ t, ((Dg t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((P : Matrix (Fin n) (Fin n) k) * diagonal fun i => ((t ^ w i : kˣ) : k)) *
        ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := fun t => rfl
  have hGz : ∀ t, Dg t ∈ Gz Z := fun t a ha => (hT t).1 a ha
  have hgx : ∀ t : kˣ, ((Dg t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * x *
      (((Dg t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = (t : k) • x := by
    intro t
    have h2 : ((Dg t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * x =
        (t : k) • (x * ((Dg t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := (hT t).2.1
    rw [h2, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  have hgv : ∀ t, ((Dg t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ p.2 = p.2 := fun t => (hT t).2.2
  obtain ⟨m, hm⟩ := wt P w (cAv Z x p.2)
    (fun t y hy => cAv_inv Z x p.2 (Dg t) (hGz t) t t.ne_zero (hgx t) (hgv t) y hy) (by
      intro y hy
      rw [cAv, Submodule.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      have ha1 : a ∈ Bz Z := ha.1
      have ha2 : a * x = x * a := ha.2
      have hac : a * c = c * a := (ha1 c hc).symm
      have hap : a * p.1 = p.1 * a := by
        have h3 := ha2
        rw [hx_def, mul_sub, sub_mul, hac] at h3
        exact sub_left_inj.mp h3
      obtain ⟨u, hu1, hu2⟩ := hU a (fun z hz => ha1 z hz) hap
      exact ⟨u, by simpa [mulVecR] using hu1, hu2⟩)
  have hZA : Subalgebra.toSubmodule Z ≤ cA Z x := fun z hz => ⟨fun a ha => hCR.1 a ha z hz, hxB z hz⟩
  have hAC : cA Z x ≤ Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
    fun a ha => (mem_C_iff Z a).mpr ha.1
  have hfA := Submodule.finrank_mono hAC
  rw [Subalgebra.finrank_toSubmodule] at hfA
  have hd0 : 0 < dB0 Z := hdB
  unfold dB0 at hd0
  have hlt : finrank k (Subalgebra.toSubmodule Z) < finrank k (cA Z x) := by
    by_cases hx0 : x = 0
    · have hCA : Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) ≤ cA Z x :=
        fun a ha => ⟨(mem_C_iff Z a).mp ha, by simp [hx0]⟩
      have h1 := Submodule.finrank_mono hCA
      rw [Subalgebra.finrank_toSubmodule] at h1
      rw [Subalgebra.finrank_toSubmodule]
      omega
    · apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne hZA ?_
      intro heq
      have hxA : x ∈ cA Z x := ⟨hxB, rfl⟩
      rw [← heq] at hxA
      have hxZ : x ∈ Z := hxA
      haveI := hCR.2
      have hnZ : IsNilpotent (⟨x, hxZ⟩ : Z) := by
        obtain ⟨N, hN⟩ := hnil
        exact ⟨N, Subtype.ext (by simpa using hN)⟩
      exact hx0 (congrArg Subtype.val hnZ.eq_zero)
  rw [Subalgebra.finrank_toSubmodule] at hlt
  set D := finrank k ↥(Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) - finrank k ↥(cA Z x) with hD_def
  have hD : D < dB0 Z := by
    unfold dB0
    omega
  have hDr : (D : ℝ) < (dB0 Z : ℝ) := by exact_mod_cast hD
  refine ⟨(D : ℝ) / 2 - m, ?_, ?_⟩
  · have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  intro t _
  obtain ⟨K, L, u, hu, hK1, hK2, hK3, hL1, hL2, hL3, hL4, hmod⟩ :=
    modul_eq (fun V γ hγ φ X Y hX hY => ratio V γ hγ φ X Y hX hY) Z hCR c hc p hp (Dg t) (hGz t) t
      t.ne_zero (hgx t) (hgv t)
  refine ⟨K, L, Dg t, hK1, hK2, hK3, hL1, hL2, hL3, hL4, hDg t, ?_⟩
  rw [hmod]
  have hsplit := det_split Z x p.2 (Dg t) (hGz t) t t.ne_zero (hgx t) (hgv t)
  have hsq := det_sq Z hCR x hxB (Dg t) (hGz t) t t.ne_zero (hgx t)
  have hw : LinearMap.det ((toLin' ((Dg t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).restrict
      (cAv_inv Z x p.2 (Dg t) (hGz t) t t.ne_zero (hgx t) (hgv t))) = (t : k) ^ m := hm t
  rw [hsplit, ← hu, hw] at hsq
  have hunit : (u * t ^ m) ^ 2 = t ^ D := Units.ext (by push_cast; exact hsq)
  have hn := congrArg (GlobalTheory.SplitWeil.nabs k) hunit
  rw [nabs_pow, nabs_mul, nabs_pow, nabs_pow] at hn
  have hr := nabs_pos t
  have hs := nabs_pos u
  have key : GlobalTheory.SplitWeil.nabs k u * GlobalTheory.SplitWeil.nabs k t ^ m =
      GlobalTheory.SplitWeil.nabs k t ^ ((D : ℝ) / 2) := by
    rw [← pow_left_inj₀ (by positivity) (by positivity) two_ne_zero, hn,
      ← Real.rpow_natCast (GlobalTheory.SplitWeil.nabs k t ^ ((D : ℝ) / 2)) 2, ← Real.rpow_mul hr.le,
      ← Real.rpow_natCast (GlobalTheory.SplitWeil.nabs k t) D]
    congr 1
    push_cast
    ring
  rw [Real.inv_rpow hr.le, Real.rpow_sub hr, Real.rpow_natCast, ← key]
  field_simp

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
