import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.DetSqT
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.ModulEqT
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.WtI
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.NabsPow

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound PositivityTheory.RgUd.TP.Nil.Orb.Mod

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem det_restrict_toLin_congr {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) (h : A = B)
    (W : Submodule k (Fin n → k)) (hA : ∀ y ∈ W, Matrix.toLin' A y ∈ W)
    (hB : ∀ y ∈ W, Matrix.toLin' B y ∈ W) :
    LinearMap.det ((Matrix.toLin' A).restrict hA) = LinearMap.det ((Matrix.toLin' B).restrict hB) := by
  subst h
  rfl

theorem modBoundT (hT : PositivityTheory.RgUd.TP.TraceForm k) : ModBound (k := k) := by
  intro n Z hZ hd c hc p P w hp hnil hv hg hcent
  obtain ⟨τ, h1, h2, -⟩ := hT n Z hZ
  have hτ : PositivityTheory.RgUd.TP.Nil.Orb.Mod.IsTau Z τ := ⟨h1, h2⟩
  have hR : PositivityTheory.RgUd.T.Nil.Orb.BModbound.RatioP k n :=
    fun V γ hγ φ X Y hX hY => PositivityTheory.RgUd.T.Nil.Orb.BModbound.ratio V γ hγ φ X Y hX hY
  haveI : Infinite k := PositivityTheory.RgUd.TP.Nil.Orb.Mod.infinite_local
  have hxB : p.1 - c ∈ Bz Z := by
    intro a ha
    rw [mul_sub, sub_mul, hp a ha, hZ.1 a ha c hc]
  let gt : kˣ → GL (Fin n) k := fun t => P * ⟨diagonal (fun i => ((t ^ w i : kˣ) : k)),
    diagonal (fun i => (((t ^ w i)⁻¹ : kˣ) : k)),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact Units.mul_inv _,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact Units.inv_mul _⟩ * P⁻¹
  have hval : ∀ t : kˣ, ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val := fun t => rfl
  have hgZ : ∀ t : kˣ, gt t ∈ Gz Z := by
    intro t a ha
    have h : a * ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * a := (hg t).1 a ha
    exact h
  have hgx : ∀ t : kˣ, ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (p.1 - c) *
      (((gt t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = (t : k) • (p.1 - c) := by
    intro t
    have h : ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (p.1 - c) =
        (t : k) • ((p.1 - c) * ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := (hg t).2.1
    rw [h, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  have hgv : ∀ t : kˣ, ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ p.2 = p.2 :=
    fun t => (hg t).2.2
  have hinv : ∀ t : kˣ, ∀ y ∈ cAv Z (p.1 - c) p.2,
      (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)) y ∈
        cAv Z (p.1 - c) p.2 :=
    fun t => cAv_inv Z (p.1 - c) p.2 (gt t) (hgZ t) (t : k) t.ne_zero (hgx t) (hgv t)
  have hW : ∀ y ∈ cAv Z (p.1 - c) p.2, ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
    rintro y ⟨a, ⟨haB, hax⟩, rfl⟩
    have hap : a * p.1 = p.1 * a := by
      have hca : c * a = a * c := haB c hc
      have h3 := hax
      rw [mul_sub, sub_mul, hca] at h3
      exact sub_left_inj.mp h3
    obtain ⟨u, hu1, hu2⟩ := hcent a (fun z hz => haB z hz) hap
    exact ⟨u, hu1, hu2⟩
  obtain ⟨m, hm⟩ := PositivityTheory.RgUd.TP.Nil.Orb.Mod.wtI P w (cAv Z (p.1 - c) p.2) hinv hW
  have hZle : Subalgebra.toSubmodule Z ≤ cA Z (p.1 - c) := by
    intro a ha
    exact ⟨fun z hz => hZ.1 z hz a ha, hxB a ha⟩
  have hcAle : cA Z (p.1 - c) ≤
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) := by
    intro a ha
    exact (PositivityTheory.RgUd.T.Nil.Orb.BModbound.mem_C_iff Z a).2 ha.1
  have hdB : dB0 Z = finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) -
      finrank k Z := rfl
  have hlt : finrank k Z < finrank k (cA Z (p.1 - c)) := by
    rw [← Subalgebra.finrank_toSubmodule]
    rcases (Submodule.finrank_mono hZle).lt_or_eq with h | h
    · exact h
    · exfalso
      have heq := Submodule.eq_of_le_of_finrank_eq hZle h
      have hxZ : p.1 - c ∈ Z := by
        have h4 : p.1 - c ∈ cA Z (p.1 - c) := ⟨hxB, rfl⟩
        rw [← heq] at h4
        exact h4
      have hx0 : p.1 - c = 0 := by
        have hn : IsNilpotent (⟨p.1 - c, hxZ⟩ : Z) := by
          obtain ⟨j, hj⟩ := hnil
          exact ⟨j, Subtype.ext (by simpa using hj)⟩
        haveI := hZ.2
        have h5 := hn.eq_zero
        simpa using congrArg Subtype.val h5
      have hCle : Subalgebra.toSubmodule
          (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) ≤ cA Z (p.1 - c) := by
        intro a ha
        refine ⟨(PositivityTheory.RgUd.T.Nil.Orb.BModbound.mem_C_iff Z a).1 ha, ?_⟩
        rw [hx0, mul_zero, zero_mul]
      have h6 := Submodule.finrank_mono hCle
      rw [← heq, Subalgebra.finrank_toSubmodule, Subalgebra.finrank_toSubmodule] at h6
      omega
  have h7 := Submodule.finrank_mono hcAle
  rw [Subalgebra.finrank_toSubmodule] at h7
  set D := finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) -
    finrank k (cA Z (p.1 - c)) with hD
  have hDlt : D < dB0 Z := by omega
  refine ⟨(D : ℝ) / 2 - m, ?_, ?_⟩
  · have h8 : (D : ℝ) < (dB0 Z : ℝ) := by exact_mod_cast hDlt
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · intro t _
    obtain ⟨K, L, u, hu, hK1, hK2, hK3, hL1, hL2, hL3, hL4, hmod⟩ :=
      PositivityTheory.RgUd.TP.Nil.Orb.Mod.modul_eqT hR Z hZ τ hτ c hc p hp (gt t) (hgZ t) (t : k) t.ne_zero
        (hgx t) (hgv t)
    refine ⟨K, L, gt t, hK1, hK2, hK3, hL1, hL2, hL3, hL4, hval t, ?_⟩
    rw [hmod]
    have hs := det_split Z (p.1 - c) p.2 (gt t) (hgZ t) (t : k) t.ne_zero (hgx t) (hgv t)
    have hq := PositivityTheory.RgUd.TP.Nil.Orb.Mod.det_sqT Z τ hτ (p.1 - c) hxB (gt t) (hgZ t) (t : k)
      t.ne_zero (hgx t)
    have hw : LinearMap.det ((Matrix.toLin' ((gt t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).restrict
        (cAv_inv Z (p.1 - c) p.2 (gt t) (hgZ t) (t : k) t.ne_zero (hgx t) (hgv t))) = (t : k) ^ m := by
      rw [← hm t]
      exact det_restrict_toLin_congr k _ _ (hval t) _ _ _
    rw [hw, ← hu] at hs
    rw [hs] at hq
    have hU : (u * t ^ m) ^ 2 = t ^ D := Units.ext (by push_cast; exact hq)
    have hN := congrArg (nabs k) hU
    rw [PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pow, PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_mul,
      PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pow, PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pow] at hN
    have hv0 := PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pos u
    have hs0 := PositivityTheory.RgUd.T.Nil.Orb.BModbound.nabs_pos t
    have hlog := congrArg Real.log hN
    rw [Real.log_pow, Real.log_mul hv0.ne' (pow_pos hs0 m).ne', Real.log_pow, Real.log_pow] at hlog
    rw [Real.rpow_def_of_pos (inv_pos.2 hs0), Real.log_inv]
    rw [← Real.exp_log (inv_pos.2 hv0), Real.log_inv]
    congr 1
    push_cast at hlog
    linear_combination (-1 / 2) * hlog

theorem modBound0 (hT : PositivityTheory.RgUd.TP.TraceForm k) :
    ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → 0 < dB0 Z → ∀ (p : Sp k n) (P : GL (Fin n) k)
    (w : Fin n → ℤ), p.1 ∈ Bz Z → IsNilpotent p.1 → p.2 ≠ 0 →
    (∀ t : kˣ, let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * p.1 = (t : k) • (p.1 * g) ∧ g *ᵥ p.2 = p.2) →
    (∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) →
    ∃ a : ℝ, 2 * a < dB0 Z ∧ ∀ t : kˣ, nabs k t < 1 → ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
      IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧ L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧
      L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      g.val = P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a := by
  intro n Z hZ hd p P w hp hnil hv hg hcent
  have h0 : (0 : Matrix (Fin n) (Fin n) k) ∈ Z := Z.zero_mem
  exact modBoundT k hT n Z hZ hd 0 h0 p P w hp (by simpa using hnil) hv (by simpa using hg) hcent

end PositivityTheory.RgUd.TP.Nil.Orb
