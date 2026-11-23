import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Poly

variable {K : Type} [Field K]

theorem dualPoly_one (s : K) : dualPoly s (1 : K[X]) = 1 := by
  first
    | (simp [dualPoly]; done)
    | rw [dualPoly, ← C_1, reverse_C, C_comp, leadingCoeff_C, inv_one, C_1, one_mul]

theorem dualPoly_mul (s : K) (R S : K[X]) : dualPoly s (R * S) = dualPoly s R * dualPoly s S := by
  simp only [dualPoly, leadingCoeff_mul, reverse_mul_of_domain, mul_comp, mul_inv, C_mul]
  ring

def dualPolyHom (s : K) : K[X] →* K[X] where
  toFun := dualPoly s
  map_one' := dualPoly_one s
  map_mul' := dualPoly_mul s

private theorem coeff_dualPoly' (s : K) (R : K[X]) (i : ℕ) :
    (dualPoly s R).coeff i = R.leadingCoeff⁻¹ * (R.coeff (revAt R.natDegree i) * s ^ i) := by
  rw [dualPoly, coeff_C_mul, comp_C_mul_X_coeff, coeff_reverse]

end Poly

theorem eta_units : EtaUnits := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z w
  unfold BlockDat.etaU BlockDat.etaW
  rw [Col.lenUW_mul_eW, Col.lenW_toNat]

theorem expW_nonempty {K : Type} [Field K] [NumberField K] {d : ℕ} (w : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) :
    {J : ℕ | ∀ a ∈ w.asIdeal ^ J, ∀ z ∈ A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B}.Nonempty := by
  have htop := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B hB.span_eq_top
  obtain ⟨δ, hδ, hδA⟩ := Formalism.HermitianLatticesTheory.indexBasic_denom (nonZeroDivisors (𝓞 K)) A B hA.fg
    (by rw [htop]; exact le_top)
  have hδ0 : δ ≠ 0 := nonZeroDivisors.ne_zero hδ
  have hI : Ideal.span {δ} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hδ0
  have hwu : ¬ IsUnit w.asIdeal := by
    rw [Ideal.isUnit_iff]; exact w.isPrime.ne_top
  have hfin : FiniteMultiplicity w.asIdeal (Ideal.span {δ}) := FiniteMultiplicity.of_not_isUnit hwu hI
  obtain ⟨c, hc, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hcw : ¬ c ≤ w.asIdeal := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨s, hsc, hsw⟩ := SetLike.not_le_iff_exists.1 hcw
  refine ⟨multiplicity w.asIdeal (Ideal.span {δ}), ?_⟩
  intro a ha z hz
  refine ⟨s, hsw, ?_⟩
  have hmem : a * s ∈ Ideal.span {δ} := by
    rw [hc]; exact Ideal.mul_mem_mul ha hsc
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hmem
  have : s • a • z = e • (δ • z) := by
    rw [smul_smul, smul_smul, mul_comm s a, he]
  rw [this]
  exact B.smul_mem e (hδA z hz)

theorem exponent_weight_spectral : ExpWSpec := by
  unfold ExpWSpec
  intro K _ _ d w A B hA hB
  refine ⟨?_, fun J hJ => ?_⟩
  · exact Nat.sInf_mem (expW_nonempty w A B hA hB)
  · exact Nat.sInf_le hJ

section Alg

variable {K : Type} [Field K] [StarRing K] {n a b d : ℕ}

theorem orthogonal_tower_projection (H : Matrix (Fin n) (Fin n) K) (V : Matrix (Fin n) (Fin b) K) (Vp : Matrix (Fin b) (Fin n) K)
    (Z : Matrix (Fin b) (Fin d) K) (Q : Matrix (Fin d) (Fin b) K) (c : K) (hc : c ≠ 0)
    (b2 : Vᴴ * H * (1 - V * Vp) = 0) (c2 : Zᴴ * (c • (Vᴴ * H * V)) * (1 - Z * Q) = 0) :
    (V * Z)ᴴ * H * (1 - V * Z * Q * Vp) = 0 := by
  have e1 : Vᴴ * H = Vᴴ * H * V * Vp := by
    have h := b2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    rw [Matrix.mul_assoc (Vᴴ * H) V Vp]
    exact h
  have c2' : Zᴴ * (Vᴴ * H * V) * (1 - Z * Q) = 0 := by
    have h : c • (Zᴴ * (Vᴴ * H * V) * (1 - Z * Q)) = 0 := by
      rw [← c2, Matrix.mul_smul, Matrix.smul_mul]
    have h' := congrArg (fun M => c⁻¹ • M) h
    simpa [smul_smul, inv_mul_cancel₀ hc] using h'
  have e2 : Zᴴ * (Vᴴ * H * V) = Zᴴ * (Vᴴ * H * V) * Z * Q := by
    have h := c2'
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    rw [Matrix.mul_assoc (Zᴴ * (Vᴴ * H * V)) Z Q]
    exact h
  rw [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
  calc Zᴴ * Vᴴ * H = Zᴴ * (Vᴴ * H) := Matrix.mul_assoc _ _ _
    _ = Zᴴ * (Vᴴ * H * V * Vp) := by rw [← e1]
    _ = Zᴴ * (Vᴴ * H * V) * Vp := by simp only [Matrix.mul_assoc]
    _ = Zᴴ * (Vᴴ * H * V) * Z * Q * Vp := by rw [← e2]
    _ = Zᴴ * Vᴴ * H * (V * Z * Q * Vp) := by simp only [Matrix.mul_assoc]

theorem lf_orth_tower (H : Matrix (Fin n) (Fin n) K) (L : Matrix (Fin n) (Fin a) K) (Lp : Matrix (Fin a) (Fin n) K)
    (V : Matrix (Fin n) (Fin b) K) (Vp : Matrix (Fin b) (Fin n) K)
    (Z : Matrix (Fin b) (Fin d) K) (Q : Matrix (Fin d) (Fin b) K) (c : K) (hc : c ≠ 0)
    (b2 : Vᴴ * H * (1 - V * Vp) = 0) (c2 : Zᴴ * (c • (Vᴴ * H * V)) * (1 - Z * Q) = 0)
    (hd : L * Lp * V = V) :
    (Lp * (V * Z))ᴴ * (c • (Lᴴ * H * L)) * (1 - (Lp * (V * Z)) * (Q * Vp * L)) = 0 := by
  have hW : L * (Lp * V) = V := by rw [← Matrix.mul_assoc]; exact hd
  have h1 : (Lp * V)ᴴ * (Lᴴ * H * L) = Vᴴ * H * L := by
    conv_rhs => rw [← hW]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e1 : Vᴴ * H * (V * Vp) = Vᴴ * H := by
    have h := b2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  have hb : (Lp * V)ᴴ * (Lᴴ * H * L) * (1 - Lp * V * (Vp * L)) = 0 := by
    rw [h1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
    calc Vᴴ * H * L = Vᴴ * H * (V * Vp) * L := by rw [e1]
      _ = Vᴴ * H * (L * (Lp * V)) * Vp * L := by rw [hW, Matrix.mul_assoc (Vᴴ * H) V Vp]
      _ = Vᴴ * H * L * (Lp * V * (Vp * L)) := by simp only [Matrix.mul_assoc]
  have h2 : (Lp * V)ᴴ * (Lᴴ * H * L) * (Lp * V) = Vᴴ * H * V := by
    rw [h1, Matrix.mul_assoc (Vᴴ * H) L (Lp * V), hW]
  have hc2 : Zᴴ * (c • ((Lp * V)ᴴ * (Lᴴ * H * L) * (Lp * V))) * (1 - Z * Q) = 0 := by
    rw [h2]; exact c2
  have key := orthogonal_tower_projection (Lᴴ * H * L) (Lp * V) (Vp * L) Z Q c hc hb hc2
  have e : (Lp * (V * Z))ᴴ * (c • (Lᴴ * H * L)) * (1 - Lp * (V * Z) * (Q * Vp * L)) =
      c • ((Lp * V * Z)ᴴ * (Lᴴ * H * L) * (1 - Lp * V * Z * Q * (Vp * L))) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  rw [e, key, smul_zero]

end Alg

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lf_lvl_proj (h : BlockHyp B ℓ v0 s) :
    IsOrthProj B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) (B.S.lvlPr B.r ℓ.P ℓ.ψ) ∧
      B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ = B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) := by
  have hP := (level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1
  exact orthogonal_projection_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act _ hP.idem hP.selfAdj

theorem lf_v_proj (h : BlockHyp B ℓ v0 s) :
    IsOrthProj B.S.H (B.vE ℓ) (B.vPr ℓ) ∧ B.vE ℓ * B.vPr ℓ = B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) := by
  have hg := good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ
  exact orthogonal_projection_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act _ hg.idem hg.selfAdj

theorem lf_lvl_mul_good (h : BlockHyp B ℓ v0 s) :
    lvlIdem ℓ.P ℓ.ψ * goodAt ℓ.X ℓ.P ℓ.ψ = goodAt ℓ.X ℓ.P ℓ.ψ := by
  have hP := (level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1
  have hc := (idempotent_spec K v0 h.conj G ℓ.X h.irr).2
  unfold goodAt
  rw [← mul_assoc, hc, mul_assoc, hP.idem]

theorem lf_lvl_vE (h : BlockHyp B ℓ v0 s) :
    B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ = B.vE ℓ := by
  obtain ⟨⟨h1, -⟩, h2⟩ := lf_v_proj h
  have h3 := (group_action_matrix_hom K B.S G B.r).2 (lvlIdem ℓ.P ℓ.ψ) (goodAt ℓ.X ℓ.P ℓ.ψ)
  rw [lf_lvl_mul_good h] at h3
  rw [(lf_lvl_proj h).2]
  calc B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) * B.vE ℓ
      = B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) * (B.vE ℓ * (B.vPr ℓ * B.vE ℓ)) := by rw [h1, Matrix.mul_one]
    _ = (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ) * (B.vE ℓ * B.vPr ℓ)) * B.vE ℓ := by simp only [Matrix.mul_assoc]
    _ = B.vE ℓ * B.vPr ℓ * B.vE ℓ := by rw [h2, ← h3]
    _ = B.vE ℓ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

theorem lf_HV_eq : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl

theorem lf_lvlH_eq : B.S.lvlH B.r ℓ.P ℓ.ψ =
    (Nat.card ℓ.P : K)⁻¹ • ((B.S.lvlE B.r ℓ.P ℓ.ψ)ᴴ * B.S.H * B.S.lvlE B.r ℓ.P ℓ.ψ) := rfl

theorem lf_card_inv_ne : ((Nat.card ℓ.P : K)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

theorem lf_HV_pos (h : BlockHyp B ℓ v0 s) (v : InfinitePlace K) : ((B.HV ℓ).map v.embedding).PosDef :=
  (good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ).2.2 v

theorem lf_zE_inj : Function.Injective (B.zE ℓ Z).mulVec := (subspace_image_spec K _ (B.Z0 ℓ Z)).1

theorem lf_vE_inj : Function.Injective (B.vE ℓ).mulVec := (image_idempotent_spec K _ _).1

theorem lf_lvlE_inj : Function.Injective (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec := (image_idempotent_spec K _ _).1

theorem lf_z_proj (h : BlockHyp B ℓ v0 s) : IsOrthProj (B.HV ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) :=
  (orthogonal_projection_exists K v0 h.conj _ _ (B.HV ℓ) (lf_HV_pos h v0) (B.zE ℓ Z) lf_zE_inj).2.2.2.1

theorem lf_lvlE_lE (h : BlockHyp B ℓ v0 s) : B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z = B.fE ℓ Z := by
  unfold lE fE
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, lf_lvl_vE h]

theorem lf_lPr_lE (h : BlockHyp B ℓ v0 s) : B.lPr ℓ Z * B.lE ℓ Z = 1 := by
  have e : B.lPr ℓ Z * B.lE ℓ Z = B.Pq ℓ Z * B.vPr ℓ * (B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z) := by
    unfold lPr
    simp only [Matrix.mul_assoc]
  rw [e, lf_lvlE_lE (Z := Z) h]
  unfold fE
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), (lf_v_proj h).1.1, Matrix.one_mul, (lf_z_proj (Z := Z) h).1]

theorem lf_l_proj (h : BlockHyp B ℓ v0 s) : IsOrthProj (B.S.lvlH B.r ℓ.P ℓ.ψ) (B.lE ℓ Z) (B.lPr ℓ Z) := by
  refine ⟨lf_lPr_lE (Z := Z) h, ?_⟩
  have c2 := (lf_z_proj (Z := Z) h).2
  rw [lf_HV_eq] at c2
  exact lf_orth_tower B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) (B.S.lvlPr B.r ℓ.P ℓ.ψ) (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ Z) (B.Pq ℓ Z)
    _ lf_card_inv_ne (lf_v_proj h).1.2 c2 (lf_lvl_vE h)

theorem lf_lE_form (h : BlockHyp B ℓ v0 s) : (B.lE ℓ Z)ᴴ * B.S.lvlH B.r ℓ.P ℓ.ψ * B.lE ℓ Z = B.HZ ℓ Z := by
  have e : (B.lE ℓ Z)ᴴ * B.S.lvlH B.r ℓ.P ℓ.ψ * B.lE ℓ Z =
      (Nat.card ℓ.P : K)⁻¹ • ((B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z)ᴴ * B.S.H * (B.S.lvlE B.r ℓ.P ℓ.ψ * B.lE ℓ Z)) := by
    rw [lf_lvlH_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, lf_lvlE_lE (Z := Z) h]
  unfold HZ fE
  rw [lf_HV_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem lf_cutLat_mul {n a d : ℕ} (E : Matrix (Fin n) (Fin a) K) (E' : Matrix (Fin a) (Fin d) K)
    (A : Submodule (𝓞 K) (Fin n → K)) : cutLat E' (cutLat E A) = cutLat (E * E') A := by
  ext y
  simp [cutLat, Matrix.mulVec_mulVec]

theorem lf_cut_nab (h : BlockHyp B ℓ v0 s) : cutLat (B.lE ℓ Z) (B.S.lvlNab B.r ℓ.P ℓ.ψ) = B.cutZ ℓ Z := by
  show cutLat (B.lE ℓ Z) (cutLat (B.S.lvlE B.r ℓ.P ℓ.ψ) B.S.nabLat) = cutLat (B.fE ℓ Z) B.S.nabLat
  rw [lf_cutLat_mul, lf_lvlE_lE (Z := Z) h]

theorem lf_cut_del (h : BlockHyp B ℓ v0 s) : cutLat (B.lE ℓ Z) (B.S.lvlDel B.r ℓ.P ℓ.ψ) = B.delZ ℓ Z := by
  show cutLat (B.lE ℓ Z) (cutLat (B.S.lvlE B.r ℓ.P ℓ.ψ) B.S.delLat) = cutLat (B.fE ℓ Z) B.S.delLat
  rw [lf_cutLat_mul, lf_lvlE_lE (Z := Z) h]

end BlockDat

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem lf_del_isLattice {s : ℕ} (hS : S.Good s) (c : S.Cl) : Submodule.IsLattice K (S.Del c) := by
  refine ⟨(hS.nab_lat c).fg.of_le (hS.del_le c), ?_⟩
  have hD := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K S.V S.pair hS.symm hS.nondeg exponent_index_lattice.hstar (S.Nab c) (hS.nab_lat c)).1
  rw [eq_top_iff, ← hD.span_eq_top, Submodule.span_le]
  intro y hy
  have hs0 : (algebraMap (𝓞 K) K (s : 𝓞 K)) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast hS.s_pos.ne'
  have e : y = (algebraMap (𝓞 K) K (s : 𝓞 K))⁻¹ • ((s : 𝓞 K) • y) := by
    rw [← algebraMap_smul K (s : 𝓞 K) y, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hS.dual_le c y hy))

theorem lf_nabLat_isLattice {s : ℕ} (hS : S.Good s) : Submodule.IsLattice K S.nabLat :=
  ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Nab hS.nab_lat

theorem lf_delLat_isLattice {s : ℕ} (hS : S.Good s) : Submodule.IsLattice K S.delLat :=
  ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Del (S.lf_del_isLattice hS)

theorem lf_delLat_le {s : ℕ} (hS : S.Good s) : S.delLat ≤ S.nabLat := ValuationLatticeField.valLatF_mono S.I hS.del_le

end CSD

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lf_fE_inj : Function.Injective (Matrix.mulVecLin (B.fE ℓ Z)) := by
  intro x y hxy
  simp only [Matrix.mulVecLin_apply, fE, ← Matrix.mulVec_mulVec] at hxy
  exact lf_zE_inj (lf_vE_inj hxy)

theorem lf_lvlNab_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.S.lvlNab B.r ℓ.P ℓ.ψ) :=
  exponent_index_lattice.cut_isLattice _ (fun _ _ hxy => lf_lvlE_inj hxy) _ (B.S.lf_nabLat_isLattice h.ok.good)

theorem lf_lPr_surj (h : BlockHyp B ℓ v0 s) : Function.Surjective (Matrix.mulVecLin (B.lPr ℓ Z)) := by
  intro y
  refine ⟨(B.lE ℓ Z).mulVec y, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, lf_lPr_lE (Z := Z) h, Matrix.one_mulVec]

theorem lf_Tl_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.Tl ℓ Z) :=
  exponent_index_lattice.map_isLattice _ (lf_lPr_surj (Z := Z) h) _ (lf_lvlNab_isLattice h)

theorem lf_cutZ_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.cutZ ℓ Z) :=
  exponent_index_lattice.cut_isLattice _ lf_fE_inj _ (B.S.lf_nabLat_isLattice h.ok.good)

theorem lf_delZ_isLattice (h : BlockHyp B ℓ v0 s) : Submodule.IsLattice K (B.delZ ℓ Z) :=
  exponent_index_lattice.cut_isLattice _ lf_fE_inj _ (B.S.lf_delLat_isLattice h.ok.good)

theorem lf_delZ_le (h : BlockHyp B ℓ v0 s) : B.delZ ℓ Z ≤ B.cutZ ℓ Z :=
  Submodule.comap_mono (B.S.lf_delLat_le h.ok.good)

theorem lf_cutZ_le (h : BlockHyp B ℓ v0 s) : B.cutZ ℓ Z ≤ B.Tl ℓ Z := by
  intro z hz
  rw [← lf_cut_nab (Z := Z) h, exponent_index_lattice.mem_cutLat] at hz
  refine (exponent_index_lattice.mem_matLat _ _ _).2 ⟨_, hz, ?_⟩
  rw [Matrix.mulVec_mulVec, lf_lPr_lE (Z := Z) h, Matrix.one_mulVec]

end BlockDat

theorem lift_lattices : LiftLattices := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h
  exact ⟨BlockDat.lf_Tl_isLattice (Z := Z) h, BlockDat.lf_cutZ_isLattice (Z := Z) h, BlockDat.lf_delZ_isLattice (Z := Z) h, BlockDat.lf_delZ_le (Z := Z) h,
    BlockDat.lf_cutZ_le (Z := Z) h⟩

section Unif

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem lf_exists_unif (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ∈ w.asIdeal ∧ ϖ ≠ 0 ∧ vw w (ϖ : K) = 1 := by
  obtain ⟨ϖ, h1, h2, h3, -⟩ := idxChange_unif (K := K) w
  exact ⟨ϖ, h1, h2, h3⟩

end Unif

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lf_lvlH_pos (h : BlockHyp B ℓ v0 s) (v : InfinitePlace K) :
    ((B.S.lvlH B.r ℓ.P ℓ.ψ).map v.embedding).PosDef := by
  have hP := (level_idempotent_spec K v0 h.conj G ℓ.P ℓ.ψ).1
  have hE : ∀ i j, B.S.lvlE B.r ℓ.P ℓ.ψ i j ∈ cmMax K :=
    image_idempotent_rational K B.S.dim (B.S.gaMat B.r (lvlIdem ℓ.P ℓ.ψ)) (gaMat_rat B.S B.r h.ok.actRat _ hP.rat)
  exact cut_posDef B.S.H (B.S.lvlE B.r ℓ.P ℓ.ψ) lf_lvlE_inj hE (Nat.card ℓ.P) Nat.card_pos v (h.ok.hpos v)

theorem lf_exp_incl (hE : ExpWSpec) (h : BlockHyp B ℓ v0 s) (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K)
    (hϖ : ϖ ∈ w.asIdeal) :
    ∀ z ∈ B.cutZ ℓ Z, (ϖ ^ B.JexpW ℓ Z w) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z) := fun z hz =>
  (hE K _ w (B.cutZ ℓ Z) (B.delZ ℓ Z) (lf_cutZ_isLattice (Z := Z) h) (lf_delZ_isLattice (Z := Z) h)).1 _ (Ideal.pow_mem_pow hϖ _) z hz

end BlockDat

theorem boundsIVAt_of (hE : ExpWSpec) : BoundsIVAt := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h w
  obtain ⟨ϖ, hϖ, -, hv⟩ := lf_exists_unif w
  obtain ⟨hH, hdet, -⟩ := orthogonal_projection_exists K v0 h.conj _ 0 (B.S.lvlH B.r ℓ.P ℓ.ψ) (BlockDat.lf_lvlH_pos h v0) 0
    (by intro x y _; exact Subsingleton.elim _ _)
  obtain ⟨hinj, hCS, hnab, hdel⟩ := level_class_sum K B.S G B.r ℓ.P ℓ.ψ
  have hJ : ∀ z ∈ cutLat (B.lE ℓ Z) (valLatF (B.S.lvlI B.r ℓ.P ℓ.ψ) B.S.Nab),
      (ϖ ^ B.JexpW ℓ Z w) • z ∈
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat (B.lE ℓ Z) (valLatF (B.S.lvlI B.r ℓ.P ℓ.ψ) B.S.Del)) := by
    rw [← hnab, ← hdel, BlockDat.lf_cut_nab (Z := Z) h, BlockDat.lf_cut_del (Z := Z) h]
    exact BlockDat.lf_exp_incl hE h w ϖ hϖ
  have key := (bounds_fourth_class_fixed K _ _ (B.S.lvlH B.r ℓ.P ℓ.ψ) hH hdet (B.lE ℓ Z) (B.lPr ℓ Z) (BlockDat.lf_l_proj (Z := Z) h)
    B.S.Cl B.S.V B.S.pair (B.S.lvlI B.r ℓ.P ℓ.ψ) (fun c => Nat.card ℓ.P * B.S.wt c) hinj
    (fun c => Nat.mul_pos Nat.card_pos (B.S.wt_pos c)) hCS B.S.Nab B.S.Del h.ok.good.nab_lat s h.ok.good.s_pos
    h.ok.good.del_dual (B.DG ℓ) (Nat.mul_pos Nat.card_pos B.S.DGam_pos)
    (fun c => Nat.mul_dvd_mul_left _ (B.S.wt_dvd_DGam c)) w ϖ (B.JexpW ℓ Z w) hv hJ).2
  rw [← hnab, BlockDat.lf_cut_nab (Z := Z) h, BlockDat.lf_lE_form (Z := Z) h] at key
  exact key

theorem local_bounds_from_exponent : BoundsIVAt := boundsIVAt_of exponent_weight_spectral

namespace CyclotomicLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem hv_spec (h : BlockHyp B ℓ v0 s) :
    (∀ i j, B.vE ℓ i j ∈ cmMax K) ∧ (∀ i j, B.HV ℓ i j ∈ cmMax K) ∧
      ∀ v : InfinitePlace K, ((B.HV ℓ).map v.embedding).PosDef :=
  good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ

theorem zE_inj : Function.Injective (B.zE ℓ Z).mulVec := BlockDat.lf_zE_inj

theorem pq_orth (h : BlockHyp B ℓ v0 s) : IsOrthProj (B.HV ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) := BlockDat.lf_z_proj h

theorem xq_rat (h : BlockHyp B ℓ v0 s) (hr : SubHasRatBasis (B.Z0 ℓ Z)) :
    IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) := by
  have hE : ∀ i a, B.zE ℓ Z i a ∈ cmMax K := fun i a => subE_rat (B.Z0 ℓ Z) hr i a
  have e : B.XQ ℓ Z = restrFrame (B.zE ℓ Z) (B.HV ℓ) :=
    quotEqRestrRat K (cmMax K) ConjugateWeightGram.isCMSub_cmMax _ _ (B.HV ℓ) (hv_spec h).2.2 (B.zE ℓ Z) (B.Pq ℓ Z) hE
      (pq_orth (Z := Z) h)
  rw [e]
  exact (restrFrameRatHerm K (cmMax K) ConjugateWeightGram.isCMSub_cmMax (fun a ha => ConjugateWeightGram.star_mem_cmMax ha) _ _ (B.HV ℓ)
    (hv_spec h).2.1 (hv_spec h).2.2 (B.zE ℓ Z) zE_inj hE).1

theorem equivFun_op (i : B.Pl × ℕ) (f : B.S.Forms) :
    B.S.basis.equivFun (B.op i f) = (B.opMat i).mulVec (B.S.basis.equivFun f) := by
  first
  | rw [Basis.equivFun_apply, Basis.equivFun_apply, BlockDat.opMat, LinearMap.toMatrix_mulVec_repr]
  | (simp only [Basis.equivFun_apply, BlockDat.opMat]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)

theorem I_opMat (i : B.Pl × ℕ) (x : Fin B.S.dim → K) :
    B.S.I ((B.opMat i).mulVec x) = (B.op i (B.S.basis.equivFun.symm x) : B.S.Cl → B.S.V) := by
  rw [CSD.I_apply]
  congr 1
  have := equivFun_op (B := B) i (B.S.basis.equivFun.symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [← this, LinearEquiv.symm_apply_apply]

theorem hform_eq_csum (x y : Fin B.S.dim → K) :
    hform B.S.H x y = B.S.csum (B.S.I x) (B.S.I y) := B.S.isClassSum x y

theorem opMat_comm (hc : Col.PairComm B.op) (i j : B.Pl × ℕ) :
    B.opMat i * B.opMat j = B.opMat j * B.opMat i := by
  simp only [BlockDat.opMat]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hc i j).eq]

theorem opMat_actMat (hG : ∀ i g, Commute (B.op i) (B.r g)) (i : B.Pl × ℕ) (g : G) :
    B.opMat i * B.S.actMat B.r g = B.S.actMat B.r g * B.opMat i := by
  simp only [BlockDat.opMat, CSD.actMat]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hG i g).eq]

theorem opMat_gaMat (hG : ∀ i g, Commute (B.op i) (B.r g)) (i : B.Pl × ℕ) (a : MonoidAlgebra K G) :
    B.opMat i * B.S.gaMat B.r a = B.S.gaMat B.r a * B.opMat i := by
  simp only [CSD.gaMat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [opMat_actMat hG i t]

private theorem hform_eq_star_dotProduct_mulVec {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hform H u v = star u ⬝ᵥ (H *ᵥ v) := by
  simp [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  simp only [starRingEnd_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_adj {n : ℕ} {H T T' : Matrix (Fin n) (Fin n) K} (h : Tᴴ * H = H * T') (x y : Fin n → K) :
    hform H (T.mulVec x) y = hform H x (T'.mulVec y) := by
  rw [hform_eq_star_dotProduct_mulVec, hform_eq_star_dotProduct_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h,
    Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

theorem rat_of_mulVec {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (hE : Function.Injective E.mulVec)
    (hrat : ∀ i a, E i a ∈ cmMax K) (x : Fin d → K) (hz : ∀ i, E.mulVec x i ∈ cmMax K) (a : Fin d) :
    x a ∈ cmMax K := by
  rw [ConjugateWeightGram.mem_cmMax_iff_twist]
  intro σ
  have h1 : (E.map σ).mulVec (fun a => twist σ (x a)) = (E.map σ).mulVec (fun a => σ (x a)) := by
    have e1 : E.map (twist σ) = E.map σ := by
      ext i b
      exact (ConjugateWeightGram.mem_cmMax_iff_twist _).1 (hrat i b) σ
    rw [← e1, ← emb_mulVec (twist σ) E x, e1, ← emb_mulVec σ E x]
    funext i
    exact (ConjugateWeightGram.mem_cmMax_iff_twist _).1 (hz i) σ
  exact congrFun (map_injective_of_injective E hE σ h1) a

end CyclotomicLifting

open CyclotomicLifting

theorem DefFam.blockHyp_lift {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ)
    (j : J) (t : T) : BlockHyp (F.L j t) (F.lvlA P ψ) F.v0 s :=
  ⟨h.conj, h.irr, h.lifts j t⟩

namespace CyclotomicLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem equivFun_end (g : Module.End K B.S.Forms) (f : B.S.Forms) :
    B.S.basis.equivFun (g f) = (LinearMap.toMatrix B.S.basis B.S.basis g).mulVec (B.S.basis.equivFun f) := by
  first
  | rw [Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  | (simp only [Basis.equivFun_apply]; exact (LinearMap.toMatrix_mulVec_repr _ _ g f).symm)

def spEnd (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op) : Module.End K B.S.Forms :=
  Col.eigProj hc hs (Col.HasBlocks B.n B.q B.t B.bl)

def spMat (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op) : Matrix (Fin B.S.dim) (Fin B.S.dim) K :=
  LinearMap.toMatrix B.S.basis B.S.basis (spEnd hc hs)

variable (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op)

theorem spEnd_mem (f : B.S.Forms) : spEnd hc hs f ∈ B.ZH := Col.eigProj_apply_mem hc hs _ f

theorem spEnd_of_mem {f : B.S.Forms} (hf : f ∈ B.ZH) : spEnd hc hs f = f :=
  Col.eigProj_apply_of_mem hc hs hf

theorem spMat_idem : spMat hc hs * spMat hc hs = spMat hc hs := by
  have h : spEnd hc hs * spEnd hc hs = spEnd hc hs :=
    LinearMap.ext fun f => spEnd_of_mem hc hs (spEnd_mem hc hs f)
  rw [spMat, ← LinearMap.toMatrix_mul, h]

theorem spMat_comm_of {g : Module.End K B.S.Forms} (hg : ∀ i, Commute (B.op i) g) :
    spMat hc hs * LinearMap.toMatrix B.S.basis B.S.basis g =
      LinearMap.toMatrix B.S.basis B.S.basis g * spMat hc hs := by
  unfold spMat
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  exact (Col.commute_eigProj hc hs _ hg).eq

theorem spMat_opMat (i : B.Pl × ℕ) : spMat hc hs * B.opMat i = B.opMat i * spMat hc hs := spMat_comm_of hc hs (fun j => hc j i)

theorem spMat_gaMat (hG : ∀ i g, Commute (B.op i) (B.r g)) (a : MonoidAlgebra K G) :
    spMat hc hs * B.S.gaMat B.r a = B.S.gaMat B.r a * spMat hc hs := by
  simp only [CSD.gaMat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show B.S.actMat B.r t = LinearMap.toMatrix B.S.basis B.S.basis (B.r t) from rfl,
    spMat_comm_of hc hs (fun i => hG i t)]

theorem spMat_mem (y : Fin B.S.dim → K) : (spMat hc hs).mulVec y ∈ B.coord B.ZH := by
  refine ⟨spEnd hc hs (B.S.basis.equivFun.symm y), spEnd_mem hc hs _, ?_⟩
  have := equivFun_end (B := B) (spEnd hc hs) (B.S.basis.equivFun.symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this

theorem spMat_of_mem {z : Fin B.S.dim → K} (hz : z ∈ B.coord B.ZH) : (spMat hc hs).mulVec z = z := by
  obtain ⟨f, hf, rfl⟩ := hz
  have := equivFun_end (B := B) (spEnd hc hs) f
  rw [spEnd_of_mem hc hs hf] at this
  exact this.symm

theorem opMat_adj (hH : B.OkH) (i : B.Pl × ℕ) : ∃ i', (B.opMat i)ᴴ * B.S.H = B.S.H * B.opMat i' := by
  obtain ⟨i', hi'⟩ := hH.adj i
  refine ⟨i', FinitelyNonzeroLinear.adj_matrix fun x y => ?_⟩
  rw [hform_eq_csum, hform_eq_csum, I_opMat, I_opMat, CSD.I_apply, CSD.I_apply]
  exact hi' _ _

theorem spMat_selfAdj (hv0 : IsConjAt v0) (hpos : (B.S.H.map v0.embedding).PosDef) (hH : B.OkH) :
    (spMat hc hs)ᴴ * B.S.H = B.S.H * spMat hc hs := by
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos hv0 hpos
  have hU : IsUnit B.S.H := FinitelyNonzeroLinear.isUnit_of_pos hpos
  have hdet : IsUnit B.S.H.det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  set H := B.S.H with hHdef
  set Pm := spMat hc hs with hPm
  let Pst : Matrix (Fin B.S.dim) (Fin B.S.dim) K := H⁻¹ * (Pmᴴ * H)
  have ha : Pmᴴ * H = H * Pst := by
    show Pmᴴ * H = H * (H⁻¹ * (Pmᴴ * H))
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hb : ∀ i, Pst * B.opMat i = B.opMat i * Pst := by
    intro i
    obtain ⟨i', hi'⟩ := opMat_adj hH i
    have h2 : H * B.opMat i = (B.opMat i')ᴴ * H := by
      have := congrArg Matrix.conjTranspose hi'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
      exact this
    apply hU.mul_left_cancel
    calc H * (Pst * B.opMat i) = (H * Pst) * B.opMat i := (Matrix.mul_assoc _ _ _).symm
      _ = Pmᴴ * (H * B.opMat i) := by rw [← ha, Matrix.mul_assoc]
      _ = (Pmᴴ * (B.opMat i')ᴴ) * H := by rw [h2, Matrix.mul_assoc]
      _ = (B.opMat i' * Pm)ᴴ * H := by rw [Matrix.conjTranspose_mul]
      _ = (Pm * B.opMat i')ᴴ * H := by rw [spMat_opMat hc hs i']
      _ = (B.opMat i')ᴴ * (Pmᴴ * H) := by rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((B.opMat i')ᴴ * H) * Pst := by rw [ha, Matrix.mul_assoc]
      _ = H * (B.opMat i * Pst) := by rw [← h2, Matrix.mul_assoc]
  have hcm : Pm * Pst = Pst * Pm := by
    let g : Module.End K B.S.Forms := Matrix.toLin B.S.basis B.S.basis Pst
    have hg : ∀ i, Commute (B.op i) g := by
      intro i
      have e : B.op i = Matrix.toLin B.S.basis B.S.basis (B.opMat i) :=
        (Matrix.toLin_toMatrix B.S.basis B.S.basis (B.op i)).symm
      show B.op i * g = g * B.op i
      rw [e, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin_mul, ← Matrix.toLin_mul, hb i]
    have := spMat_comm_of hc hs hg
    rwa [LinearMap.toMatrix_toLin] at this
  have hconj : ∀ A : Matrix (Fin B.S.dim) (Fin B.S.dim) K,
      (A.map v0.embedding)ᴴ = (Aᴴ).map v0.embedding := by
    intro A
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    exact (hv0 (A j i)).symm
  have hE : Pst.map v0.embedding = Pm.map v0.embedding := by
    refine FinitelyNonzeroLinear.normal_idem hpos (Pm.map v0.embedding) (Pst.map v0.embedding) ?_ ?_ ?_
    · rw [← Matrix.map_mul, spMat_idem]
    · rw [hconj, ← Matrix.map_mul, ← Matrix.map_mul, ha]
    · rw [← Matrix.map_mul, ← Matrix.map_mul, hcm]
  have hE' : Pst = Pm := Matrix.map_injective v0.embedding.injective hE
  rw [ha, hE']

end CyclotomicLifting

open CyclotomicLifting

theorem CyclotomicLifting.proj_eq {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} (h : BlockHyp B ℓ v0 s) (hH : B.OkH) :
    B.fE ℓ B.ZH * (B.Pq ℓ B.ZH * B.vPr ℓ) = B.vProj ℓ * spMat h.ok.comm h.ok.split := by
  set Pm := spMat h.ok.comm h.ok.split with hPm
  set ε := B.vProj ℓ with hε
  have hpos := h.ok.hpos v0
  have hsa : Pmᴴ * B.S.H = B.S.H * Pm := spMat_selfAdj h.ok.comm h.ok.split h.conj hpos hH
  have hg := good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ
  have hεadj : εᴴ * B.S.H = B.S.H * ε := by
    have := group_action_matrix_adjoint K B.S G B.r h.ok.act (goodAt ℓ.X ℓ.P ℓ.ψ)
    rwa [hg.selfAdj] at this
  have hcomm : Pm * ε = ε * Pm := spMat_gaMat h.ok.comm h.ok.split h.ok.opG _
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := BlockDat.lf_v_proj h
  obtain ⟨hz1, hz2⟩ := BlockDat.lf_z_proj (Z := B.ZH) h
  have hεv : ε * B.vE ℓ = B.vE ℓ := by
    rw [hε, BlockDat.vProj, ← hv3, Matrix.mul_assoc, hv1, Matrix.mul_one]

  have hinj : Function.Injective (B.fE ℓ B.ZH).mulVec := fun a b hab => BlockDat.lf_fE_inj (B := B) (ℓ := ℓ) hab
  obtain ⟨-, -, -, -, huniq⟩ := orthogonal_projection_exists K v0 h.conj _ _ B.S.H hpos (B.fE ℓ B.ZH) hinj
  have hO : IsOrthProj B.S.H (B.fE ℓ B.ZH) (B.Pq ℓ B.ZH * B.vPr ℓ) := by
    constructor
    · show B.Pq ℓ B.ZH * B.vPr ℓ * (B.vE ℓ * B.zE ℓ B.ZH) = 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), hv1, Matrix.one_mul, hz1]
    · have := orthogonal_tower_projection B.S.H (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ B.ZH) (B.Pq ℓ B.ZH) _ (BlockDat.lf_card_inv_ne (ℓ := ℓ)) hv2 hz2
      show (B.vE ℓ * B.zE ℓ B.ZH)ᴴ * B.S.H * (1 - B.vE ℓ * B.zE ℓ B.ZH * (B.Pq ℓ B.ZH * B.vPr ℓ)) = 0
      rw [← Matrix.mul_assoc (B.vE ℓ * B.zE ℓ B.ZH)]
      exact this
  have hPr := huniq _ hO

  have hfix : (ε * Pm) * B.fE ℓ B.ZH = B.fE ℓ B.ZH := by
    apply FinitelyNonzeroLinear.ext_mulVec
    intro u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hmem : (B.fE ℓ B.ZH).mulVec u ∈ B.coord B.ZH := by
      have h1 : (B.zE ℓ B.ZH).mulVec u ∈ B.Z0 ℓ B.ZH := by
        rw [← (subspace_image_spec K _ (B.Z0 ℓ B.ZH)).2]
        exact ⟨u, rfl⟩
      have h2 : (B.vE ℓ).mulVec ((B.zE ℓ B.ZH).mulVec u) ∈ B.coord B.ZH := h1
      rwa [Matrix.mulVec_mulVec] at h2
    rw [spMat_of_mem _ _ hmem]
    show ε.mulVec ((B.vE ℓ * B.zE ℓ B.ZH).mulVec u) = (B.vE ℓ * B.zE ℓ B.ZH).mulVec u
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hεv]

  have hrange : LinearMap.range (ε * Pm).mulVecLin ≤ LinearMap.range (B.fE ℓ B.ZH).mulVecLin := by
    rintro _ ⟨y, rfl⟩
    have h1 : (ε * Pm).mulVec y ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      have hr : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range ε.mulVecLin :=
        (image_idempotent_spec K B.S.dim (B.vProj ℓ)).2
      rw [hr, ← Matrix.mulVec_mulVec]
      exact ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := h1
    have h2 : (ε * Pm).mulVec y ∈ B.coord B.ZH := by
      rw [← hcomm, ← Matrix.mulVec_mulVec]
      exact spMat_mem _ _ _
    have h3 : u ∈ B.Z0 ℓ B.ZH := by
      show (B.vE ℓ).mulVecLin u ∈ B.coord B.ZH
      rw [hu]; exact h2
    rw [← (subspace_image_spec K _ (B.Z0 ℓ B.ZH)).2] at h3
    obtain ⟨u', hu'⟩ := h3
    refine ⟨u', ?_⟩
    rw [Matrix.mulVecLin_apply] at hu hu' ⊢
    show (B.vE ℓ * B.zE ℓ B.ZH).mulVec u' = _
    rw [← Matrix.mulVec_mulVec]
    show (B.vE ℓ).mulVec ((subE (B.Z0 ℓ B.ZH)).mulVec u') = _
    rw [hu', hu]
    rfl
  obtain ⟨M, hM⟩ := exists_mul_of_range_le hrange
  have hQadj : (ε * Pm)ᴴ * B.S.H = B.S.H * (ε * Pm) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hεadj, ← Matrix.mul_assoc, hsa, Matrix.mul_assoc, hcomm]
  have hk : (B.fE ℓ B.ZH)ᴴ * B.S.H * (ε * Pm) = (B.fE ℓ B.ZH)ᴴ * B.S.H := by
    rw [Matrix.mul_assoc, ← hQadj, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hfix]
  have hPQ : (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm) = B.Pq ℓ B.ZH * B.vPr ℓ := by
    calc (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm)
        = (((B.fE ℓ B.ZH)ᴴ * B.S.H * B.fE ℓ B.ZH)⁻¹ * ((B.fE ℓ B.ZH)ᴴ * B.S.H)) * (ε * Pm) := by rw [← hPr]
      _ = ((B.fE ℓ B.ZH)ᴴ * B.S.H * B.fE ℓ B.ZH)⁻¹ * ((B.fE ℓ B.ZH)ᴴ * B.S.H * (ε * Pm)) := Matrix.mul_assoc _ _ _
      _ = ((B.fE ℓ B.ZH)ᴴ * B.S.H * B.fE ℓ B.ZH)⁻¹ * ((B.fE ℓ B.ZH)ᴴ * B.S.H) := by rw [hk]
      _ = _ := hPr.symm
  have hMeq : M = B.Pq ℓ B.ZH * B.vPr ℓ := by
    have : (B.Pq ℓ B.ZH * B.vPr ℓ) * (ε * Pm) = M := by
      rw [hM, ← Matrix.mul_assoc, hO.1, Matrix.one_mul]
    rw [← this, hPQ]
  rw [hM, hMeq]

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)

theorem jw_le {s : ℕ} (h : F.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (j : J) (t : T)
    (w : HeightOneSpectrum (𝓞 K)) :
    jw ((F.side P ψ Zs).HT j t) w ((F.side P ψ Zs).Tl j t) ≤
      (F.etaJW P ψ Zs j t w : ℤ) + ((F.side P ψ Zs).dZ j t : ℤ) *
        ((F.JJW P ψ Zs j t w : ℤ) + vw w (((F.L j t).DG (F.lvlA P ψ) : ℕ) : K) + vw w (s : K)) :=
  local_bounds_from_exponent K G Pl0 (F.L j t) (F.lvlA P ψ) (Zs.Zl j t) F.v0 s (F.blockHyp_lift h P ψ j t) w

theorem etaJ_units (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    F.etaJ P ψ Zs j t w * (Col.eW w : ℚ) = (F.etaJW P ψ Zs j t w : ℚ) := eta_units _ _ _ (F.L j t) (F.lvlA P ψ) (Zs.Zl j t) w

end DefFam

namespace FamIn

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

theorem side_WF {s : ℕ} (h : A.fam.Ok s) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A.fam.amb)
    (hst : Zs.Stable) (hin : Zs.InBlock) (hsep : A.fam.TypesSep) : (A.side P ψ Zs).WF :=
  A.fam.side_WF h P ψ Zs hst hin hsep

end FamIn

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem lf_plc_eq_prW (w : HeightOneSpectrum (𝓞 K)) : plc w = Col.prW w :=
  Col.eq_prW_of_mem w (plc_prime w) (plc_mem w)

theorem lf_mem_pow_iff (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) (n : ℕ) :
    x ∈ w.asIdeal ^ n ↔ (n : ℤ) ≤ vw w (x : K) := by
  rw [← w.intValuation_le_pow_iff_mem, intValuation_eq_exp' w x hx, WithZero.exp_le_exp, neg_le_neg_iff]

theorem lf_eW_eq_ramw (w : HeightOneSpectrum (𝓞 K)) : ((Col.eW w : ℕ) : ℤ) = ramw w := by
  have hp0 : ((Col.prW w : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Col.prW_prime w).ne_zero
  have hcast : (((Col.prW w : ℕ) : 𝓞 K) : K) = ((Col.prW w : ℕ) : K) := by simp
  have hnn : 0 ≤ vw w (((Col.prW w : ℕ) : 𝓞 K) : K) := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w _
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  have hmap : (w.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((Col.prW w : ℕ) : 𝓞 K)} := by
    conv_lhs => rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ)]
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [Col.prW]
  have hne : w.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmap
    exact hp0 (Ideal.span_singleton_eq_bot.1 hmap.symm)
  have h1 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = n := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmap, Ideal.span_singleton_le_iff_mem, lf_mem_pow_iff w _ hp0, hn]
    · rw [hmap, Ideal.span_singleton_le_iff_mem, lf_mem_pow_iff w _ hp0, hn]
      push_cast
      omega
  have h2 : (w.asIdeal.under ℤ).ramificationIdx' w.asIdeal = w.asIdeal.ramificationIdx ℤ :=
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne
  unfold Col.eW ramw
  rw [← h2, h1, lf_plc_eq_prW, ← hcast, hn]

end Units

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)

theorem etaJ_ramw (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    ((F.etaJ P ψ Zs j t w : ℚ) : ℝ) * (ramw w : ℝ) = (F.etaJW P ψ Zs j t w : ℝ) := by
  rw [← lf_eW_eq_ramw]
  have h := etaJ_units F P ψ Zs j t w
  first
  | exact_mod_cast h
  | (have h' := congrArg (fun x : ℚ => (x : ℝ)) h
     push_cast at h' ⊢
     exact h')

theorem JJ_ramw (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    ((F.JJ P ψ Zs j t w : ℚ) : ℝ) * (ramw w : ℝ) = (F.JJW P ψ Zs j t w : ℝ) := by
  have h : F.JJ P ψ Zs j t w * ((Col.eW w : ℕ) : ℚ) = (F.JJW P ψ Zs j t w : ℚ) :=
    div_mul_cancel₀ _ (Col.eW_ne_zero_rat w)
  have e : ((ramw w : ℤ) : ℝ) = (((Col.eW w : ℕ) : ℚ) : ℝ) := by
    rw [← lf_eW_eq_ramw]; push_cast; rfl
  rw [e, ← Rat.cast_mul, h]
  simp

end DefFam

section Poly

variable {K : Type} [Field K]

theorem coeff_dualPoly (s : K) (R : K[X]) (i : ℕ) :
    (dualPoly s R).coeff i = R.leadingCoeff⁻¹ * (R.coeff (revAt R.natDegree i) * s ^ i) := by
  exact coeff_dualPoly' s R i

theorem coeff_dualPoly_of_le (s : K) (R : K[X]) {i : ℕ} (hi : i ≤ R.natDegree) :
    (dualPoly s R).coeff i = R.leadingCoeff⁻¹ * (R.coeff (R.natDegree - i) * s ^ i) := by
  rw [coeff_dualPoly, revAt_le hi]

theorem coeff_dualPoly_of_lt (s : K) (R : K[X]) {i : ℕ} (hi : R.natDegree < i) :
    (dualPoly s R).coeff i = 0 := by
  rw [coeff_dualPoly]
  have h1 : revAt R.natDegree i = i := by
    first
    | exact revAt_eq_self_of_lt hi
    | (simp [revAt, revAtFun, not_le.mpr hi]; done)
    | (simp only [revAt, revAtFun, Function.Embedding.coeFn_mk]; rw [if_neg (not_le.mpr hi)])
  rw [h1, coeff_eq_zero_of_natDegree_lt hi, zero_mul, mul_zero]

theorem ne_zero_of_coeff_zero {R : K[X]} (h0 : R.coeff 0 = 1) : R ≠ 0 := by
  rintro rfl
  simp at h0

theorem coeff_dualPoly_top {s : K} (R : K[X]) (h0 : R.coeff 0 = 1) :
    (dualPoly s R).coeff R.natDegree = R.leadingCoeff⁻¹ * s ^ R.natDegree := by
  rw [coeff_dualPoly_of_le s R le_rfl, Nat.sub_self, h0, one_mul]

theorem coeff_dualPoly_top_ne {s : K} (hs : s ≠ 0) (R : K[X]) (h0 : R.coeff 0 = 1) :
    (dualPoly s R).coeff R.natDegree ≠ 0 := by
  rw [coeff_dualPoly_top R h0]
  exact mul_ne_zero (inv_ne_zero (leadingCoeff_ne_zero.mpr (ne_zero_of_coeff_zero h0))) (pow_ne_zero _ hs)

theorem natDegree_dualPoly {s : K} (hs : s ≠ 0) (R : K[X]) (h0 : R.coeff 0 = 1) :
    (dualPoly s R).natDegree = R.natDegree := by
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun i hi => coeff_dualPoly_of_lt s R hi) (coeff_dualPoly_top_ne hs R h0)

theorem dualPoly_dualPoly {s : K} (hs : s ≠ 0) (R : K[X]) (h0 : R.coeff 0 = 1) :
    dualPoly s (dualPoly s R) = R := by
  have hR := ne_zero_of_coeff_zero h0
  have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  have hN := natDegree_dualPoly hs R h0
  have hlcD : (dualPoly s R).leadingCoeff = R.leadingCoeff⁻¹ * s ^ R.natDegree := by
    show (dualPoly s R).coeff (dualPoly s R).natDegree = _
    rw [hN]
    exact coeff_dualPoly_top R h0
  ext i
  rcases Nat.lt_or_ge R.natDegree i with hi | hi
  · have hi' : (dualPoly s R).natDegree < i := by rw [hN]; exact hi
    rw [coeff_dualPoly_of_lt s (dualPoly s R) hi', coeff_eq_zero_of_natDegree_lt hi]
  · have hi' : i ≤ (dualPoly s R).natDegree := by rw [hN]; exact hi
    rw [coeff_dualPoly_of_le s (dualPoly s R) hi', hN,
      coeff_dualPoly_of_le s R (Nat.sub_le _ _), Nat.sub_sub_self hi, hlcD]
    have e : s ^ R.natDegree = s ^ (R.natDegree - i) * s ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hi]
    rw [e]
    have ha : s ^ (R.natDegree - i) ≠ 0 := pow_ne_zero _ hs
    have hb : s ^ i ≠ 0 := pow_ne_zero _ hs
    calc _ = (R.leadingCoeff * R.leadingCoeff⁻¹) * (s ^ (R.natDegree - i) * (s ^ (R.natDegree - i))⁻¹) *
          (s ^ i * (s ^ i)⁻¹) * R.coeff i := by rw [mul_inv, inv_inv]; ring
      _ = R.coeff i := by rw [mul_inv_cancel₀ hlc, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb]; ring

theorem dualPoly_inj {s : K} (hs : s ≠ 0) {R R' : K[X]} (h0 : R.coeff 0 = 1) (h0' : R'.coeff 0 = 1)
    (h : dualPoly s R = dualPoly s R') : R = R' := by
  rw [← dualPoly_dualPoly hs R h0, h, dualPoly_dualPoly hs R' h0']

theorem blockPoly_eval_zero (ν : K) (q t : ℕ) : (Col.blockPoly ν q t).eval 0 = 1 := by
  simp [Col.blockPoly, eval_prod]

theorem list_prod_eval_zero (l : List K[X]) (h : ∀ p ∈ l, p.eval 0 = 1) : l.prod.eval 0 = 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.prod_cons, eval_mul, h p (by simp), ih (fun q hq => h q (by simp [hq])), one_mul]

theorem heckePoly_eval_zero {Pl : Type} (n : ℕ) (q : Pl → ℕ) (x : Pl × ℕ → K) (P : Pl) (h1 : x (P, 0) = 1) :
    (Col.heckePoly n q x P).eval 0 = 1 := by
  first
  | (simp only [Col.heckePoly, Col.heckePolyOf]
     rw [eval_finset_sum, Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (fun h => by simp at h)]
     simp [h1])
  | (simp only [Col.heckePoly, Col.heckePolyOf, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
     rw [Finset.sum_range_succ']
     simp [h1])

end Poly

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

theorem lf_blockProd_eval_zero (P : B.Pl) : (B.blockProd P).eval 0 = 1 := by
  have hl : ∀ p ∈ B.bl.map (fun ν => Col.blockPoly (ν P) (B.q P) B.t), p.eval 0 = 1 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨ν, -, rfl⟩ := hp
    exact blockPoly_eval_zero _ _ _
  exact list_prod_eval_zero _ hl

theorem lf_mem_resSet_of_mem_ixFin {X : Finset (G → K)} {Sg : Pl0 → K[X]} (h : Sg ∈ B.ixFin X) :
    Sg ∈ B.resSet X := by
  unfold BlockDat.ixFin at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.1 h
  · simp at h

theorem lf_exists_occurs_of_mem_resSet {X : Finset (G → K)} {Sg : Pl0 → K[X]} (h : Sg ∈ B.resSet X) :
    ∃ x, B.HasRes Sg x ∧ Col.Occurs B.op x := by
  by_contra hcon
  push Not at hcon
  apply h.2
  have hbot : B.partF Sg = ⊥ := by
    unfold BlockDat.partF Col.eigSum
    refine iSup₂_eq_bot.2 fun x hx => ?_
    by_contra hne
    exact hcon x hx hne
  have hinj : Function.Injective (B.vE (Lvl.full X)).mulVec :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt (Lvl.full X).X (Lvl.full X).P (Lvl.full X).ψ))).1
  unfold BlockDat.inV0 BlockDat.coord
  rw [hbot, Submodule.map_bot, eq_bot_iff]
  intro u hu
  have hu' : (B.vE (Lvl.full X)).mulVec u = 0 := (Submodule.mem_bot K).1 hu
  rw [Submodule.mem_bot]
  exact hinj (by rw [hu', Matrix.mulVec_zero])

theorem lf_coeff_zero_of_mem_resSet (h0 : ∀ P, B.op (P, 0) = 1) {X : Finset (G → K)} {Sg : Pl0 → K[X]}
    (h : Sg ∈ B.resSet X) (P0 : Pl0) : (Sg P0).coeff 0 = 1 := by
  by_cases hP : P0 ∈ Set.range B.pl
  swap
  · rw [h.1 P0 hP, coeff_one_zero]
  obtain ⟨P, rfl⟩ := hP
  obtain ⟨x, hres, hocc⟩ := B.lf_exists_occurs_of_mem_resSet h
  have h1 : x (P, 0) = 1 := hocc.eq_one (h0 P)
  have h2 := congrArg (Polynomial.eval 0) (hres P)
  rw [heckePoly_eval_zero _ _ _ _ h1, eval_mul, B.lf_blockProd_eval_zero, mul_one] at h2
  rw [coeff_zero_eq_eval_zero]
  exact h2.symm

end BlockDat

namespace FamIn

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
  {m : ℕ} (A : FamIn K G Pl0 T m)

theorem trScale_ne_zero (hq : ∀ P, A.q P ≠ 0) (P : Pl0) : trScale A.r m A.t A.q A.etaVal P ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Nat.cast_ne_zero.2 (hq P)))

theorem typesSep_of (hq : ∀ P, A.q P ≠ 0)
    (hconst : ∀ Sg ∈ (A.fam.R A.fam.μ0).ixFin A.fam.X, ∀ P, (Sg P).coeff 0 = 1) : A.fam.TypesSep := by
  intro Sg hSg Sg' hSg' hne j
  obtain ⟨P, hP⟩ := (A.fam.R A.fam.μ0).sep_of_mem_ixFin hSg hSg' hne
  exact ⟨P, fun h => hP (dualPoly_inj (A.trScale_ne_zero hq _) (hconst Sg hSg _) (hconst Sg' hSg' _) h)⟩

theorem const_of (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) :
    ∀ Sg ∈ (A.fam.R A.fam.μ0).ixFin A.fam.X, ∀ P, (Sg P).coeff 0 = 1 := by
  intro Sg hSg P
  exact (A.fam.R A.fam.μ0).lf_coeff_zero_of_mem_resSet h0 ((A.fam.R A.fam.μ0).lf_mem_resSet_of_mem_ixFin hSg) P

theorem typesSep_of' (hq : ∀ P, A.q P ≠ 0) (h0 : ∀ P, A.heckeR A.μ0 (P, 0) = 1) : A.fam.TypesSep := typesSep_of A hq (const_of A h0)

end FamIn

end Formalism.L2.DIV

namespace Formalism.L2.DIV.LiftTest

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Col Formalism.L2.DIV.Test

variable (G : Type) [Group G] [Fintype G]

theorem lf_mem_cmMax_rat (a : ℚ) : a ∈ cmMax ℚ := by
  first
  | (show ∀ σ : ℚ →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
     intro σ
     simp [eq_ratCast σ])
  | (intro σ; simp [eq_ratCast σ])
  | (intro σ; rw [star_trivial, eq_ratCast σ]; simp)

def exampleB : BlockDat ℚ G Unit :=
  liftDat (regCSD ℚ G) (regAct ℚ G) Set.univ (fun i => (gaussBin 2 2 i.2 : ℚ) • 1) 1 1 (fun _ => 2)
    (fun _ => 1) (fun _ => 1)

def trivialCharacterLevel (P : Subgroup G) : Lvl ℚ G := ⟨{fun _ => 1}, P, 1⟩

def toyX : (exampleB G).Pl × ℕ → ℚ := fun i => (gaussBin 2 2 i.2 : ℚ)

theorem toy_hasBlocks_gaussBin : HasBlocks (1 + 1) (fun _ : (Set.univ : Set Unit) => 2) 1
    [fun P : (Set.univ : Set Unit) => firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit)]
    (fun i => (gaussBin 2 2 i.2 : ℚ)) := by
  intro P
  have h := heckePolyOf_gaussBin (L := ℚ) 2 2 1
  simp only [one_pow, one_mul] at h
  show ([fun P : (Set.univ : Set Unit) => firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit)].map
    fun ν => blockPoly (ν P) 2 1).prod ∣ heckePolyOf (1 + 1) 2 fun i => (gaussBin 2 2 i : ℚ)
  rw [show (1 + 1 : ℕ) = 2 from rfl, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have e : firstValA (fun _ : Unit => (1 : ℚˣ)) (fun _ => 1) (fun _ => 2) 1 (P : Unit) = 2 := by
    simp [firstValA]
  rw [e, blockPoly_succ' (1 : ℚ) 2 1]
  have e2 : (1 : ℚ) * ((2 : ℕ) : ℚ) = 2 := by norm_num
  rw [e2]
  exact Dvd.intro_left _ rfl

theorem toyB_hasBlocks : HasBlocks (exampleB G).n (exampleB G).q (exampleB G).t (exampleB G).bl (toyX G) := toy_hasBlocks_gaussBin

theorem comm1 {V : Type} [AddCommGroup V] [Module ℚ V] (a : ℚ) (g : Module.End ℚ V) :
    Commute (a • (1 : Module.End ℚ V)) g := by
  first
  | exact (Commute.one_left g).smul_left a
  | exact Commute.smul_left (Commute.one_left g) a
  | (show a • (1 : Module.End ℚ V) * g = g * (a • 1)
     ext x
     simp)

theorem toyB_ZH_eq_top : (exampleB G).ZH = ⊤ := by
  rw [eq_top_iff]
  refine le_trans ?_ (eigAt_le_eigSum (op := (exampleB G).op) (toyB_hasBlocks G))
  intro f _
  exact mem_eigAt_of_forall_apply fun i => rfl

theorem toyB_ok : (exampleB G).Ok 1 where
  good := reg_good ℚ G
  hrat := fun _ _ => lf_mem_cmMax_rat _
  hpos := fun v => reg_H_posDef ℚ G v (rat_isConjAt v)
  act := regAct_good ℚ G
  actRat := fun _ _ _ => lf_mem_cmMax_rat _
  comm := fun i j => comm1 (V := (regCSD ℚ G).Forms) _ _
  split := by
    intro i
    rw [eq_top_iff]
    refine le_trans ?_ (le_iSup _ ((gaussBin 2 2 i.2 : ℚ)))
    exact (Formalism.L2.NCov.maxGen_smul_one (K := ℚ) (V := (regCSD ℚ G).Forms) _).ge
  opG := fun i g => comm1 (V := (regCSD ℚ G).Forms) _ _
  blocks := ⟨le_rfl, List.cons_ne_nil _ _, fun ν hν P => by
    have hν' := List.mem_singleton.1 hν
    subst hν'
    simp [firstValA]⟩
  q_pos _ := show 0 < 2 by norm_num
  pl_inj := Subtype.val_injective

theorem regular_scalar_selfAdjoint (a : ℚ) (f g : (regCSD ℚ G).Forms) :
    (regCSD ℚ G).csum (((a • (1 : Module.End ℚ (regCSD ℚ G).Forms)) f).1 : G → ℚ) (g.1 : G → ℚ) =
      (regCSD ℚ G).csum (f.1 : G → ℚ) (((a • (1 : Module.End ℚ (regCSD ℚ G).Forms)) g).1 : G → ℚ) := by
  rw [reg_csum, reg_csum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    star_trivial]
  ring

theorem toyB_okH : (exampleB G).OkH where
  rat := fun _ _ _ => lf_mem_cmMax_rat _
  adj := fun i => ⟨i, fun f g => regular_scalar_selfAdjoint G _ f g⟩

theorem toyB_blockHyp (P : Subgroup G) (v0 : InfinitePlace ℚ) : BlockHyp (exampleB G) (trivialCharacterLevel G P) v0 1 where
  conj := rat_isConjAt v0
  irr := by
    intro χ hχ
    rw [show (trivialCharacterLevel G P).X = {fun _ => 1} from rfl, Finset.mem_singleton] at hχ
    rw [hχ]
    exact isAbsIrrChar_one ℚ _
  ok := toyB_ok G

theorem example_invariant_subspace_top (P : Subgroup G) : (exampleB G).Z0 (trivialCharacterLevel G P) (exampleB G).ZH = ⊤ := by
  unfold BlockDat.Z0 BlockDat.inV0 BlockDat.coord
  rw [toyB_ZH_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 (LinearEquiv.surjective _), Submodule.comap_top]

theorem toyB_dZ_pos (P : Subgroup G) : 0 < (exampleB G).dZ (trivialCharacterLevel G P) (exampleB G).ZH := by
  unfold BlockDat.dZ subDim
  rw [example_invariant_subspace_top, finrank_top, Module.finrank_fin_fun]
  exact reg_V0dim_pos_lvl ℚ G P

end Formalism.L2.DIV.LiftTest

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem tt_zE_Pq (h : BlockHyp B ℓ v0 s) (hZ : B.Z0 ℓ Z = ⊤) : B.zE ℓ Z * B.Pq ℓ Z = 1 := by
  apply Matrix.mulVec_injective
  funext x
  have hr : LinearMap.range (B.zE ℓ Z).mulVecLin = ⊤ := by
    rw [← hZ]; exact (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  obtain ⟨y, rfl⟩ := LinearMap.range_eq_top.1 hr x
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, (lf_z_proj (Z := Z) h).1, Matrix.mul_one,
    Matrix.one_mulVec]

theorem tt_fE_lPr (h : BlockHyp B ℓ v0 s) (hZ : B.Z0 ℓ Z = ⊤) :
    B.fE ℓ Z * B.lPr ℓ Z = B.vProj ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ := by
  have e : B.fE ℓ Z * B.lPr ℓ Z = B.vE ℓ * (B.zE ℓ Z * B.Pq ℓ Z) * B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ := by
    unfold fE lPr
    simp only [Matrix.mul_assoc]
  rw [e, tt_zE_Pq h hZ, Matrix.mul_one, (lf_v_proj h).2]
  rfl

theorem tt_fix (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    (B.vProj ℓ).mulVec ((B.fE ℓ Z).mulVec z) = (B.fE ℓ Z).mulVec z := by
  have e : B.vProj ℓ * B.fE ℓ Z = B.fE ℓ Z := by
    have h2 : B.vProj ℓ = B.vE ℓ * B.vPr ℓ := (lf_v_proj h).2.symm
    rw [h2]
    unfold fE
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.vPr ℓ), (lf_v_proj h).1.1, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e]

theorem tt_eta (h : BlockHyp B ℓ v0 s) (hZ : B.Z0 ℓ Z = ⊤) (N : ℕ) (hN : 0 < N)
    (ha : ∀ y ∈ B.S.lvlNab B.r ℓ.P ℓ.ψ,
      (N : K) • (B.vProj ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y) ∈ B.S.nabLat)
    (hb : ∀ u : Fin B.S.dim → K, (B.vProj ℓ).mulVec u = u → (N : K) • u ∈ B.S.nabLat →
      ∃ y ∈ B.S.lvlNab B.r ℓ.P ℓ.ψ, (B.vProj ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y) = u)
    (w : HeightOneSpectrum (𝓞 K)) : (B.etaW ℓ Z w : ℤ) = (B.dZ ℓ Z : ℤ) * vw w (N : K) := by
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hfl : ∀ y, (B.fE ℓ Z).mulVec ((B.lPr ℓ Z).mulVec y) =
      (B.vProj ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec y) := by
    intro y
    rw [Matrix.mulVec_mulVec, tt_fE_lPr h hZ, Matrix.mulVec_mulVec]
  have hcut : B.cutZ ℓ Z = exponent_index_lattice.smLat (N : K) (B.Tl ℓ Z) := by
    ext x
    rw [exponent_index_lattice.mem_smLat]
    constructor
    · intro hx
      have hx' : (B.fE ℓ Z).mulVec x ∈ B.S.nabLat := hx
      obtain ⟨y, hy, hyu⟩ := hb ((N : K)⁻¹ • (B.fE ℓ Z).mulVec x)
        (by rw [Matrix.mulVec_smul, tt_fix h]) (by rw [smul_smul, mul_inv_cancel₀ hNK, one_smul]; exact hx')
      refine ⟨(B.lPr ℓ Z).mulVec y, (exponent_index_lattice.mem_matLat _ _ _).2 ⟨y, hy, rfl⟩, ?_⟩
      apply lf_fE_inj (B := B) (ℓ := ℓ)
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_smul, hfl, hyu, smul_smul,
        mul_inv_cancel₀ hNK, one_smul]
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).1 hz
      show (B.fE ℓ Z).mulVec ((N : K) • (B.lPr ℓ Z).mulVec y) ∈ B.S.nabLat
      rw [Matrix.mulVec_smul, hfl]
      exact ha y hy
  have hT := lf_Tl_isLattice (Z := Z) h
  have hC := lf_cutZ_isLattice (Z := Z) h
  have h1 := exponent_index_lattice.idx_smLat w (B.Tl ℓ Z) hT hNK
  rw [← hcut] at h1
  have h2 := (exponent_index_lattice.idxB w (B.Tl ℓ Z) (B.cutZ ℓ Z) (B.Tl ℓ Z) hT hC hT).2.2 (lf_cutZ_le (Z := Z) h)
  unfold etaW
  rw [← h2, h1]

theorem tt_dZ_le_one (h : BlockHyp B ℓ v0 s) (φ : (Fin B.S.dim → K) →ₗ[K] K)
    (hφ : ∀ u, (B.vProj ℓ).mulVec u = u → φ u = 0 → u = 0) : B.dZ ℓ Z ≤ 1 := by
  have hinj : Function.Injective (φ ∘ₗ (B.fE ℓ Z).mulVecLin) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have := hφ _ (tt_fix h z) hz
    apply lf_fE_inj (B := B) (ℓ := ℓ)
    rw [Matrix.mulVecLin_apply, this, map_zero]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end BlockDat

end Formalism.L2.DIV

namespace Formalism.L2.DIV.LiftTest

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Col Formalism.L2.DIV.Test

variable (G : Type) [Group G] [Fintype G]

abbrev regE : Matrix (Fin (regCSD ℚ G).dim) (Fin (regCSD ℚ G).dim) ℚ :=
  (regCSD ℚ G).gaMat (regAct ℚ G) (goodAt ({fun _ => 1} : Finset (G → ℚ)) ⊥ 1)

theorem reg_coeff (t : G) :
    (goodAt ({fun _ => 1} : Finset (G → ℚ)) (⊥ : Subgroup G) 1).coeff t = 1 / (Fintype.card G : ℚ) := by
  unfold goodAt
  rw [lvlIdem_bot ℚ G, mul_one, idemOf_one_coeff]

theorem reg_avg (x : Fin (regCSD ℚ G).dim → ℚ) (c : G) :
    ((regCSD ℚ G).I ((regE G).mulVec x) : G → ℚ) c =
      (Fintype.card G : ℚ)⁻¹ * ∑ g : G, ((regCSD ℚ G).I x : G → ℚ) g := by
  unfold regE CSD.gaMat
  rw [Matrix.sum_mulVec, map_sum, Finset.sum_apply, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft c) (fun g => (Fintype.card G : ℚ)⁻¹ * ((regCSD ℚ G).I x : G → ℚ) g)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.smul_mulVec, map_smul, reg_coeff, CSD.I_actMat]
  show (1 / (Fintype.card G : ℚ)) * (((regAct ℚ G t ((regCSD ℚ G).basis.equivFun.symm x)).1 : G → ℚ) c) = _
  rw [regAct_apply, one_div]
  rfl

theorem mem_one_iff (a : ℚ) : a ∈ (1 : Submodule (𝓞 ℚ) ℚ) ↔ ∃ n : 𝓞 ℚ, (n : ℚ) = a := by
  rw [Submodule.mem_one]

theorem reg_mem_nab (x : Fin (regCSD ℚ G).dim → ℚ) :
    x ∈ (regCSD ℚ G).nabLat ↔ ∀ c : G, ((regCSD ℚ G).I x : G → ℚ) c ∈ (1 : Submodule (𝓞 ℚ) ℚ) :=
  mem_valLatF _ _ x

theorem reg_lvlE_surj : Function.Surjective ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec := by
  have h := (image_idempotent_spec ℚ _ ((regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1))).2
  have e : (regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1) = 1 := by
    rw [lvlIdem_bot ℚ G, (group_action_matrix_hom ℚ (regCSD ℚ G) G (regAct ℚ G)).1]
  have htop : LinearMap.range ((regCSD ℚ G).gaMat (regAct ℚ G) (lvlIdem (⊥ : Subgroup G) 1)).mulVecLin = ⊤ := by
    rw [e]
    exact LinearMap.range_eq_top.2 fun x => ⟨x, by simp⟩
  have h2 := h.trans htop
  intro x
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.1 h2 x
  exact ⟨y, hy⟩

theorem card_ne : (Fintype.card G : ℚ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem reg_const (u : Fin (regCSD ℚ G).dim → ℚ) (hu : (regE G).mulVec u = u) (c : G) :
    ((regCSD ℚ G).I u : G → ℚ) c = ((regCSD ℚ G).I u : G → ℚ) 1 := by
  have h1 := reg_avg G u c
  have h2 := reg_avg G u 1
  rw [hu] at h1 h2
  rw [h1, h2]

theorem reg_ha (y : Fin ((regCSD ℚ G).lvlDim (regAct ℚ G) ⊥ 1) → ℚ)
    (hy : y ∈ (regCSD ℚ G).lvlNab (regAct ℚ G) ⊥ 1) :
    ((Fintype.card G : ℕ) : ℚ) • (regE G).mulVec (((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y) ∈
      (regCSD ℚ G).nabLat := by
  have hy' : ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y ∈ (regCSD ℚ G).nabLat := hy
  rw [reg_mem_nab] at hy' ⊢
  intro c
  rw [map_smul]
  show ((Fintype.card G : ℕ) : ℚ) * ((regCSD ℚ G).I ((regE G).mulVec _) : G → ℚ) c ∈ _
  rw [reg_avg, ← mul_assoc, mul_inv_cancel₀ (card_ne G), one_mul]
  exact Submodule.sum_mem _ fun g _ => hy' g

theorem reg_hb (u : Fin (regCSD ℚ G).dim → ℚ) (hu : (regE G).mulVec u = u)
    (hN : ((Fintype.card G : ℕ) : ℚ) • u ∈ (regCSD ℚ G).nabLat) :
    ∃ y ∈ (regCSD ℚ G).lvlNab (regAct ℚ G) ⊥ 1,
      (regE G).mulVec (((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y) = u := by
  classical
  set a0 : ℚ := ((regCSD ℚ G).I u : G → ℚ) 1 with ha0
  have hint : (Fintype.card G : ℚ) * a0 ∈ (1 : Submodule (𝓞 ℚ) ℚ) := by
    have := (reg_mem_nab G _).1 hN 1
    rw [map_smul] at this
    exact this
  let f : G → ℚ := Pi.single 1 ((Fintype.card G : ℚ) * a0)
  obtain ⟨x, hx⟩ := ((regCSD ℚ G).I_onto f).2 (fun c γ => rfl)
  obtain ⟨y, hy⟩ := reg_lvlE_surj G x
  refine ⟨y, ?_, ?_⟩
  · show ((regCSD ℚ G).lvlE (regAct ℚ G) ⊥ 1).mulVec y ∈ (regCSD ℚ G).nabLat
    rw [hy, reg_mem_nab, hx]
    intro c
    by_cases hc : c = 1
    · subst hc
      simpa [f] using hint
    · have : f c = 0 := by simp [f, hc]
      rw [this]
      exact Submodule.zero_mem _
  · rw [hy]
    apply (regCSD ℚ G).I_injective
    funext c
    rw [reg_avg, hx, reg_const G u hu c]
    have : ∑ g : G, f g = (Fintype.card G : ℚ) * a0 := by simp [f]
    rw [this, ← mul_assoc, inv_mul_cancel₀ (card_ne G), one_mul]

def regPhi : (Fin (regCSD ℚ G).dim → ℚ) →ₗ[ℚ] ℚ :=
  (LinearMap.proj (1 : G) : (G → ℚ) →ₗ[ℚ] ℚ) ∘ₗ (regCSD ℚ G).I

theorem reg_hphi (u : Fin (regCSD ℚ G).dim → ℚ) (hu : (regE G).mulVec u = u)
    (h0 : regPhi G u = 0) : u = 0 := by
  apply (regCSD ℚ G).I_injective
  funext c
  rw [map_zero]
  exact (reg_const G u hu c).trans h0

theorem toyB_dZ_eq_one (v0 : InfinitePlace ℚ) : (exampleB G).dZ (trivialCharacterLevel G ⊥) (exampleB G).ZH = 1 := by
  have h1 : (exampleB G).dZ (trivialCharacterLevel G ⊥) (exampleB G).ZH ≤ 1 :=
    BlockDat.tt_dZ_le_one (toyB_blockHyp G ⊥ v0) (regPhi G) (reg_hphi G)
  have h2 := toyB_dZ_pos G ⊥
  omega

theorem toyB_etaW_eq_vw_card (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((exampleB G).etaW (trivialCharacterLevel G ⊥) (exampleB G).ZH w : ℤ) = vw w ((Fintype.card G : ℕ) : ℚ) := by
  obtain ⟨v0⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  have h := BlockDat.tt_eta (toyB_blockHyp G ⊥ v0) (example_invariant_subspace_top G ⊥) (Fintype.card G) Fintype.card_pos
    (reg_ha G) (reg_hb G) w
  rw [toyB_dZ_eq_one G v0] at h
  simpa using h

theorem toyB_JexpW_eq_zero (P : Subgroup G) (w : HeightOneSpectrum (𝓞 ℚ)) : (exampleB G).JexpW (trivialCharacterLevel G P) (exampleB G).ZH w = 0 := by
  unfold BlockDat.JexpW expW
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  intro a _ z hz
  have hz' : z ∈ (exampleB G).delZ (trivialCharacterLevel G P) (exampleB G).ZH := hz
  exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.smul_mem _ a hz'⟩

end Formalism.L2.DIV.LiftTest
