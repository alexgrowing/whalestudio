import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightInvariantFormGroupConj
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold.OrbitSumGen

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ)
  (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1))

theorem posV_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have := z.2
  rw [h] at this
  simp at this

def lineOf (z : Fin G.n → ℂ) (hz : z ≠ 0) : PLv G v β := Projectivization.mk ℂ z hz

def pairOfDat (d : Dat G v β) : Ys G v β x t hx Kf K' :=
  (LeftCosets.mk _ _ d.1, lineOf G v β d.2.1 (posV_ne_zero G v β d.2))

variable {G v β}

theorem smul_line_mk (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz =
      lineOf G v β ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
        (fun h => hz (toV_injective G v β y (by rw [Matrix.toLin'_apply, h, map_zero]))) := by
  change Projectivization.map _ _ (Projectivization.mk ℂ z hz) = _
  rw [Projectivization.map_mk]
  congr 1

theorem smul_line_eq_iff (y : grp G β) (z : Fin G.n → ℂ) (hz : z ≠ 0) :
    y • lineOf G v β z hz = lineOf G v β z hz ↔
      FixL G v β y z := by
  rw [smul_line_mk]
  change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ ↔ _
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [← hu, Units.smul_def]⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hz
      apply toV_injective G v β y
      rw [Matrix.toLin'_apply, hc, zero_smul, map_zero]
    exact ⟨Units.mk0 c hc0, by rw [Units.smul_def, Units.val_mk0, hc]⟩

theorem fixL_smul_iff (y : grp G β) (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [Matrix.mulVec_smul, smul_smul] at he
    have := congrArg (fun w => c⁻¹ • w) he
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [this]
    congr 1
    field_simp
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [Matrix.mulVec_smul, he, smul_comm]⟩

variable (G v β)

theorem same_iff_smul (a b : Dat G v β) :
    Same G v β x t hx Kf K' a b ↔ ∃ y : grp G β, y • pairOfDat G v β x t hx Kf K' a = pairOfDat G v β x t hx Kf K' b := by
  constructor
  · rintro ⟨y, k, c, hk1, hk2, hc, h1, h2⟩
    refine ⟨y, Prod.ext ?_ ?_⟩
    · change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1
      rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1]
      change (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * (((toAfF G β x t hx).prod (toP1 G β)) y * a.1 * k) ∈ _
      rw [inv_mul_cancel_left]
      exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
    · change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _
      rw [smul_line_mk]
      change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
      rw [h2, Units.smul_def, smul_smul]
      simp [hc]
  · rintro ⟨y, hy⟩
    have h1 := congrArg Prod.fst hy
    have h2 := congrArg Prod.snd hy
    change y • LeftCosets.mk _ _ a.1 = LeftCosets.mk _ _ b.1 at h1
    change y • lineOf G v β a.2.1 _ = lineOf G v β b.2.1 _ at h2
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk] at h1
    rw [smul_line_mk] at h2
    change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ _ _ at h2
    rw [Projectivization.mk_eq_mk_iff] at h2
    obtain ⟨u, hu⟩ := h2
    refine ⟨y, (((toAfF G β x t hx).prod (toP1 G β)) y * a.1)⁻¹ * b.1, ((u⁻¹ : ℂˣ) : ℂ),
      (Subgroup.mem_prod.1 h1).1, (Subgroup.mem_prod.1 h1).2, Units.ne_zero _, ?_, ?_⟩
    · exact (mul_inv_cancel_left _ _).symm
    · rw [← hu, Units.smul_def, smul_smul]
      simp

def ptsToOrbit : Pts G v β x t hx Kf K' → MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quot.lift (fun d => Quotient.mk (MulAction.orbitRel (grp G β) (Ys G v β x t hx Kf K')) (pairOfDat G v β x t hx Kf K' d))
    (fun a b h => by
      obtain ⟨y, hy⟩ := (same_iff_smul G v β x t hx Kf K' a b).1 h
      exact Quotient.sound ⟨y⁻¹, show y⁻¹ • _ = _ by rw [← hy, inv_smul_smul]⟩)

theorem ptsToOrbit_eq (q : Pts G v β x t hx Kf K') :
    ptsToOrbit G v β x t hx Kf K' q = Quotient.mk _ (pairOfDat G v β x t hx Kf K' (Quot.out q)) :=
  (congrArg (ptsToOrbit G v β x t hx Kf K') (Quot.out_eq q)).symm

theorem ptsToOrbit_injective : Function.Injective (ptsToOrbit G v β x t hx Kf K') := by
  intro q₁ q₂ h
  rw [ptsToOrbit_eq, ptsToOrbit_eq] at h
  obtain ⟨g, hg⟩ := Quotient.exact h
  rw [← Quot.out_eq q₁, ← Quot.out_eq q₂]
  exact (Quot.sound ((same_iff_smul G v β x t hx Kf K' _ _).2 ⟨g, hg⟩)).symm

theorem card_stab_eq (d : Dat G v β) :
    Nat.card (Stab G v β x t hx Kf K' d) =
      Nat.card (MulAction.stabilizer (grp G β) (pairOfDat G v β x t hx Kf K' d)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [MulAction.mem_stabilizer_iff, Prod.ext_iff]
  change _ ↔ y • LeftCosets.mk _ _ d.1 = LeftCosets.mk _ _ d.1 ∧
    y • lineOf G v β d.2.1 _ = lineOf G v β d.2.1 _
  rw [smul_line_eq_iff, ← MulAction.mem_stabilizer_iff, ← stab_eq_stabilizer]
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, LeftCosets.mem_map_conj, and_assoc]

theorem cxF_pairOfDat (wt : Polynomial G.F → ℂ) (f : G.GAf → ℂ) (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (f' : Gr G 1 → ℂ) (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) (d : Dat G v β) (y : grp G β) :
    cxF G v wt β x t hx Kf f K' f' (pairOfDat G v β x t hx Kf K' d) y =
      if FixL G v β y d.2.1 then
        f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) *
          wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      else 0 := by
  obtain ⟨k, hk, e⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β)) (K := Kf.prod K') d.1
  have hz := posV_ne_zero G v β d.2
  obtain ⟨u, hu⟩ : ∃ u : ℂˣ, u • d.2.1 = Projectivization.rep (lineOf G v β d.2.1 hz) :=
    (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hz).1
      (Projectivization.mk_rep (lineOf G v β d.2.1 hz))
  have hpos : 0 < (star (Projectivization.rep (lineOf G v β d.2.1 hz)) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (lineOf G v β d.2.1 hz))).re := by
    rw [← hu]
    have := (pos_iff_smul_toV p G v β 1 d.2.1 u u.ne_zero).1 d.2.2
    simpa [Units.smul_def] using this
  have hfix : FixL G v β y (Projectivization.rep (lineOf G v β d.2.1 hz)) ↔ FixL G v β y d.2.1 := by
    rw [← hu, Units.smul_def]
    exact fixL_smul_iff y _ _ u.ne_zero
  simp only [cxF, pairOfDat, hpos, hfix, true_and, e, Prod.fst_mul, Prod.snd_mul]
  split_ifs with hF
  · rw [Subgroup.mem_prod] at hk
    have e1 : (d.1.1 * k.1)⁻¹ * toAfF G β x t hx y * (d.1.1 * k.1) =
        k.1⁻¹ * (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * k.1 := by group
    have e2 : (d.1.2 * k.2)⁻¹ * toP1 G β y * (d.1.2 * k.2) =
        k.2⁻¹ * (d.1.2⁻¹ * toP1 G β y * d.1.2) * k.2 := by group
    rw [e1, e2, hf _ hk.1, hf' _ hk.2]
  · rfl

end GlobalTheory.CxUnfold.OrbitSumGen

namespace GlobalTheory.CxUnfold.OrbitSumGen

end GlobalTheory.CxUnfold.OrbitSumGen
