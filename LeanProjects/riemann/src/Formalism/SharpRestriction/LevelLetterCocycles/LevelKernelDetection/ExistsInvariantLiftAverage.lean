import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.BasisCombinationMemInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

theorem finiteDelta_mul_mem {a b : W.Gam} (ha : a ∈ W.DelF) (hb : b ∈ W.DelF) : a * b ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  obtain ⟨k', hk', hbk⟩ := (W.DelF_def b).1 hb
  refine (W.DelF_def _).2 ⟨k * k', Nat.mul_pos hk hk', ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm k k', pow_mul, hbk, one_pow]

theorem finiteDelta_inv_mem {a : W.Gam} (ha : a ∈ W.DelF) : a⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem exists_basis_Delta_fixed_mem_N (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hs : W.s = 1) (hp2 : PD.p ≠ 2)
    (T : LocLat G Qp LL O) (hcr : IsCrys PD T.ρ) :
    ∃ (r : ℕ) (B : Module.Basis (Fin r) W.EE (W.DD T)),
      (∀ j, ∀ δ ∈ W.DelF, W.γD T δ (B j) = B j) ∧ ∀ j, B j ∈ W.N T := by
  obtain ⟨-, ⟨π', E, -, ⟨r, b, hbΔ, huniq, -⟩, -⟩, -⟩ := hP9 T hcr hs hp2
  have hb : ∀ j, b j ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b j) = b j := fun j =>
    (show b j ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (b j) = b j from hbΔ j)
  obtain ⟨B, hB⟩ := exists_EE_basis_of_lattice hcr b (fun j => (hb j).1) huniq
  exact ⟨r, B, fun j δ hδ => by rw [hB]; exact (hb j).2 δ hδ, fun j => by rw [hB]; exact (hb j).1⟩

theorem isUnit_card_finiteDelta (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hs : W.s = 1) (hp2 : PD.p ≠ 2)
    (T : LocLat G Qp LL O) (hcr : IsCrys PD T.ρ) : IsUnit ((W.DelF.card : ℕ) : W.EE) := by
  have hcard := (hP9 T hcr hs hp2).1
  have h1 : (1 : W.Gam) ∈ W.DelF := (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩
  have hpos : 0 < W.DelF.card := Finset.card_pos.2 ⟨1, h1⟩
  have hp := PD.hp
  have hlt : W.DelF.card < PD.p := by
    rw [hcard]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hp.pos one_pos)
  have hcop : Nat.Coprime W.DelF.card PD.p := Nat.coprime_comm.1
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd hpos hd) (not_le.2 hlt))
  have hb := Nat.gcd_eq_gcd_ab W.DelF.card PD.p
  rw [hcop.gcd_eq_one] at hb
  have hb' : ((W.DelF.card : ℕ) : W.EE) * (Nat.gcdA W.DelF.card PD.p : W.EE) =
      1 - ((PD.p : ℕ) : W.EE) * (Nat.gcdB W.DelF.card PD.p : W.EE) := by
    have h2 := congrArg (Int.cast : ℤ → W.EE) hb
    push_cast at h2
    linear_combination -h2
  have hu : IsUnit (1 - ((PD.p : ℕ) : W.EE) * (Nat.gcdB W.DelF.card PD.p : W.EE)) := by
    have hc := W.EE_complete
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    apply IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)})
    rw [sub_sub_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  rw [← hb'] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem exists_lift_of_onto (hs : W.s = 1) (hLem3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W)
    (hJ : ∀ T : LocLat G Qp LL O, CrysLat PD T → ∃ M h : ZMod n → ℕ, Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂)
    (hon : F.Onto) (y : W.DD T₂) (hy : y ∈ W.N T₂) : ∃ w : W.DD T₁, W.map F w = y := by
  obtain ⟨M, h, hJ'⟩ := hJ T₁ hc₁
  have hL := (hLem3 T₁ T₂ F M h hc₁.2.2.2 hc₂.2.2.2 hon hJ').1
  have hX : W.X = letπ := by
    show (W.φA ^ (W.s - 1)) letπ = letπ
    rw [hs]
    rfl
  have hunit : IsUnit (algebraMap (LetA O n) W.EE (W.X ^ (⨆ j, (M j + h j)))) := by
    rw [hX, map_pow]
    exact W.EE_π.pow _
  have hi : ∀ i : ZMod n, ∃ v : W.DD T₁, W.map F v = (letE i : LetA O n) • y := by
    intro i
    obtain ⟨z, -, hz⟩ := hL i _ (Submodule.mem_map_of_mem (f := (letE i : LetA O n) • LinearMap.id) hy)
    refine ⟨(↑hunit.unit⁻¹ : W.EE) • z, ?_⟩
    have hz' : W.map F z = algebraMap (LetA O n) W.EE (W.X ^ (⨆ j, (M j + h j))) •
        (letE i : LetA O n) • y := by
      rw [algebraMap_smul]
      exact hz
    rw [map_smul, hz', smul_smul, hunit.val_inv_mul, one_smul]
  choose v hv using hi
  refine ⟨∑ i, v i, ?_⟩
  rw [map_sum]
  simp only [hv]
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem exists_invariant_lift_average (hcu : IsUnit ((W.DelF.card : ℕ) : W.EE)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (w : W.DD T₁) (y : W.DD T₂)
    (hy : ∀ δ ∈ W.DelF, W.γD T₂ δ y = y) (hw : W.map F w = y) :
    ∃ w' : W.DD T₁, (∀ δ ∈ W.DelF, W.γD T₁ δ w' = w') ∧ W.map F w' = y := by
  refine ⟨(↑hcu.unit⁻¹ : W.EE) • ∑ δ ∈ W.DelF, W.γD T₁ δ w, fun δ' hδ' => ?_, ?_⟩
  · have hγc : W.γE δ' ((W.DelF.card : ℕ) : W.EE) = ((W.DelF.card : ℕ) : W.EE) := map_natCast _ _
    have h1 : W.γE δ' (↑hcu.unit⁻¹ : W.EE) * ↑hcu.unit = 1 := by
      rw [IsUnit.unit_spec]
      calc W.γE δ' (↑hcu.unit⁻¹ : W.EE) * ((W.DelF.card : ℕ) : W.EE)
          = W.γE δ' (↑hcu.unit⁻¹ : W.EE) * W.γE δ' ((W.DelF.card : ℕ) : W.EE) := by rw [hγc]
        _ = W.γE δ' ((↑hcu.unit⁻¹ : W.EE) * ((W.DelF.card : ℕ) : W.EE)) := (map_mul _ _ _).symm
        _ = 1 := by rw [hcu.val_inv_mul, map_one]
    have hinv : W.γE δ' (↑hcu.unit⁻¹ : W.EE) = ↑hcu.unit⁻¹ := by
      calc W.γE δ' (↑hcu.unit⁻¹ : W.EE)
          = W.γE δ' (↑hcu.unit⁻¹ : W.EE) * (↑hcu.unit * ↑hcu.unit⁻¹) := by rw [Units.mul_inv, mul_one]
        _ = ↑hcu.unit⁻¹ := by rw [← mul_assoc, h1, one_mul]
    rw [W.γD_smul, hinv, map_sum]
    congr 1
    simp only [← W.γD_mul]
    exact Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ)
      (fun δ hδ => finiteDelta_mul_mem hδ' hδ) (fun δ hδ => finiteDelta_mul_mem (finiteDelta_inv_mem hδ') hδ)
      (fun δ _ => by group) (fun δ _ => by group) (fun δ _ => rfl)
  · rw [map_smul, map_sum]
    rw [Finset.sum_congr rfl fun δ hδ => by rw [W.map_γ, hw, hy δ hδ]]
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul W.EE, smul_smul, hcu.val_inv_mul, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
