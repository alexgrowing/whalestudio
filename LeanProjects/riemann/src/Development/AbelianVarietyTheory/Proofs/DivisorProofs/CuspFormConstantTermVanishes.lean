import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToIdeleESymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusInLeviParabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSplitTorusRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitElementIsTorusElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepSumSurjectiveInitialSegmentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormExpCharacterSingleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEqStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PositionPeel

open Matrix GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem eq_of_frame_eigen {n r : ℕ} {K R : Type} [Field K] [CommRing R] (τ : K →+* R) {X Y : Matrix (Fin n) (Fin r) K}
    {P Q : Matrix (Fin r) (Fin n) K} (hPX : P * X = 0) (hPY : P * Y = 1) (hQX : Q * X = 1) (hQY : Q * Y = 0)
    {A : Matrix (Fin n) (Fin n) R} {D D' : Matrix (Fin r) (Fin r) R}
    (hX : A * X.map τ = X.map τ * D) (hY : A * Y.map τ = Y.map τ * D')
    (hz : ∀ z : Fin n → K, P *ᵥ z = 0 → Q *ᵥ z = 0 → A *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) :
    A = 1 + X.map τ * (D - 1) * Q.map τ + Y.map τ * (D' - 1) * P.map τ := by
  set R0 : Matrix (Fin n) (Fin n) K := 1 - X * Q - Y * P with hR0
  have hP : P * R0 = 0 := by
    rw [hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPX, hPY]; simp
  have hQ : Q * R0 = 0 := by
    rw [hR0, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQX, hQY]; simp
  have hA : A * R0.map τ = R0.map τ := by
    ext i j
    have := congrFun (hz (fun k => R0 k j) (funext fun k => congrFun (congrFun hP k) j)
      (funext fun k => congrFun (congrFun hQ k) j)) i
    exact this
  have h1 : (1 : Matrix (Fin n) (Fin n) R) = R0.map τ + X.map τ * Q.map τ + Y.map τ * P.map τ := by
    have e : (1 : Matrix (Fin n) (Fin n) K) = R0 + X * Q + Y * P := by rw [hR0]; abel
    have := congrArg (Matrix.map · τ) e
    rw [Matrix.map_add _ (map_add τ), Matrix.map_add _ (map_add τ), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_one _ (map_zero τ) (map_one τ)] at this
    exact this
  have h2 : R0.map τ = 1 - X.map τ * Q.map τ - Y.map τ * P.map τ := by
    rw [h1]; abel
  calc A = A * 1 := (Matrix.mul_one A).symm
    _ = R0.map τ + X.map τ * D * Q.map τ + Y.map τ * D' * P.map τ := by
      conv_lhs => rw [h1]
      rw [Matrix.mul_add, Matrix.mul_add, hA, ← Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY]
    _ = _ := by
      rw [h2, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one]
      abel

theorem blockCentre_eq (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {i : Fin r}
    {e : (AF F ⊗[F] E)ˣ} {g a : GAd σ J} (hg : GlobalTheory.LeviBlockRealization.IsBlockCentre σ J X Y i e g)
    (ha : IsIdTorusElt σ J X Y (Pi.mulSingle i e) a) : g = a := by
  apply matHom_injective
  apply Units.ext
  rw [GlobalTheory.T.idelicFrameTorusElement_matrix_eq h hJ hW ha]
  have key := eq_of_frame_eigen (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E) (P := cT (σ : E →+* E) X * J)
    (Q := cT (σ : E →+* E) Y * J) hW.xx hW.xy (yx h hJ hW) hW.yy hg.1 hg.2.1 hg.2.2
  have d1 : GlobalTheory.LeviBlockRealization.diagonalMulSingle F i ((e : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 =
      diagonal (fun k => (((Pi.mulSingle i e : Fin r → (AF F ⊗[F] E)ˣ) k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := by
    rw [GlobalTheory.LeviBlockRealization.diagonalMulSingle, ← diagonal_one, diagonal_sub]
    congr 1; funext k
    rcases eq_or_ne k i with rfl | hk
    · simp
    · simp [hk, Pi.mulSingle_eq_of_ne hk]
  have d2 : GlobalTheory.LeviBlockRealization.diagonalMulSingle F i (sigR (AF F) σ (((e⁻¹ : (AF F ⊗[F] E)ˣ)) : AF F ⊗[F] E)) - 1 =
      diagonal (fun k => (((conjUnit σ ((Pi.mulSingle i e : Fin r → (AF F ⊗[F] E)ˣ) k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := by
    rw [GlobalTheory.LeviBlockRealization.diagonalMulSingle, ← diagonal_one, diagonal_sub]
    congr 1; funext k
    rcases eq_or_ne k i with rfl | hk
    · simp [conjUnit]
    · simp [hk, Pi.mulSingle_eq_of_ne hk]
  rw [key, d1, d2]

open GroundTheory.Global GlobalTheory.HeckeAbsArch in
theorem exists_decomp (hσ : IsCMExt F E σ) : ∃ (D : Set (AF F ⊗[F] E)ˣ) (κ : (AF F ⊗[F] E)ˣ → ℝ), IsCompact D ∧
    (∀ a b, κ (a * b) = κ a + κ b) ∧ (∀ y, (absE F E y : ℝ) = Real.exp (2 * Module.finrank ℚ F * κ y)) ∧
    ∀ y, ∃ γ : Eˣ, Units.map (inclR (F := F) (AF F)).toMonoidHom γ * ((archUnit F E (κ y))⁻¹ * y) ∈ D := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  have habs : ∀ z, (absE F E z : ℝ) ≠ 0 := fun z h0 => by
    have := congrArg (fun t : NNReal => (t : ℝ)) (map_mul_eq_one (absE F E) (mul_inv_cancel z))
    simp only [NNReal.coe_mul, NNReal.coe_one, h0, zero_mul] at this
    exact zero_ne_one this
  have hmod : ∀ z : IdeleGroup E, (IdeleGroup.ideleModule E z : ℝ) ≠ 0 := fun z => (IdeleGroup.ideleModule E z).2.ne'
  set gA : (AF F ⊗[F] E)ˣ → ℝ := fun z => Real.log (absE F E z : ℝ) with hgA
  set gM : (AF F ⊗[F] E)ˣ → ℝ := fun z => Real.log (IdeleGroup.ideleModule E (toIdeleE z) : ℝ) with hgM
  have cA : Continuous gA :=
    (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE (F := F) (E := E))).log habs
  have cM : Continuous gM :=
    ((continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := E))).comp continuous_toIdeleE).log
      fun z => hmod _
  have mA : ∀ a b, gA (a * b) = gA a + gA b := fun a b => by
    simp only [hgA, map_mul, NNReal.coe_mul]; exact Real.log_mul (habs a) (habs b)
  have mM : ∀ a b, gM (a * b) = gM a + gM b := fun a b => by
    simp only [hgM, map_mul, Positive.val_mul]; exact Real.log_mul (hmod _) (hmod _)
  have pA : ∀ e : Eˣ, gA (Units.map (inclR (F := F) (AF F)).toMonoidHom e) = 0 := fun e => by
    simp only [hgA, GlobalTheory.Doubling.absE_inclR, NNReal.coe_one, Real.log_one]
  have aA : ∀ c, gA (archUnit F E c) = 2 * Module.finrank ℚ F * c := fun c => by
    simp only [hgA, absE_archUnit hσ, Real.log_exp]
  have normOne : ∀ z, gM z = 0 → toIdeleE z ∈ IdeleGroup.normOneSubgroup E := fun z hz => by
    rw [IdeleGroup.mem_normOneSubgroup]
    have hp := (IdeleGroup.ideleModule E (toIdeleE z)).2
    rw [← Real.exp_log hp]
    exact (congrArg Real.exp hz).trans Real.exp_zero
  let f : ℝ →+ ℝ :=
    { toFun := fun c => gM (archUnit F E c)
      map_zero' := by
        change Real.log ((IdeleGroup.ideleModule E (toIdeleE (archUnit F E 0)) : ℝ)) = 0
        rw [archUnit_zero, map_one, map_one]
        exact Real.log_one
      map_add' := fun c d => by simp only [archUnit_add, mM] }
  have cf : Continuous f := cM.comp continuous_archUnit
  have lin : ∀ c, gM (archUnit F E c) = c * f 1 := fun c => by
    have := map_real_smul f cf c 1
    simp only [smul_eq_mul, mul_one] at this
    exact this
  have hκ : f 1 ≠ 0 := by
    intro h0
    have := eq_zero_of_normOne gA cA mA pA (archUnit F E 1) (normOne _ (by rw [lin, h0, mul_zero]))
    rw [aA, mul_one] at this
    have hn : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
    linarith
  have hz : ∀ y, gM ((archUnit F E (gM y / f 1))⁻¹ * y) = 0 := fun y => by
    have := mM (archUnit F E (gM y / f 1)) ((archUnit F E (gM y / f 1))⁻¹ * y)
    rw [mul_inv_cancel_left, lin, div_mul_cancel₀ _ hκ] at this
    linarith
  refine ⟨toIdeleE.symm '' D, fun y => gM y / f 1, hD.image continuous_toIdeleE_symm,
    fun a b => by simp only [mM, add_div], fun y => ?_, fun y => ?_⟩
  · have zA := eq_zero_of_normOne gA cA mA pA _ (normOne _ (hz y))
    have yA : gA y = 2 * Module.finrank ℚ F * (gM y / f 1) := by
      have := mA (archUnit F E (gM y / f 1)) ((archUnit F E (gM y / f 1))⁻¹ * y)
      rw [mul_inv_cancel_left, zA, aA, add_zero] at this
      exact this
    rw [← yA, hgA]
    exact (Real.exp_log (lt_of_le_of_ne (absE F E y).2 (habs y).symm)).symm
  · obtain ⟨k, hk⟩ := hxD _ (normOne _ (hz y))
    refine ⟨k, _, hk, ?_⟩
    rw [map_mul, ← toIdeleE_inclR (F := F) k, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem polyAt_mem {V : Type} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ v ∈ W, A v ∈ W) : ∀ (L : List ℂ) (v : V), v ∈ W → polyAt A L v ∈ W
  | [], v, hv => by simpa [polyAt] using hv
  | c :: L, v, hv => by
    have e : polyAt A (c :: L) v = A (polyAt A L v) - c • polyAt A L v := by
      simp [polyAt, List.map_cons, List.prod_cons]
    rw [e]
    exact sub_mem (hW _ (polyAt_mem A W hW L v hv)) (W.smul_mem c (polyAt_mem A W hW L v hv))

theorem exists_eigen_of_polyAt {V : Type} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ v ∈ W, A v ∈ W) : ∀ (L : List ℂ) (f : V), f ∈ W → f ≠ 0 → polyAt A L f = 0 →
    ∃ c ∈ L, ∃ G ∈ W, G ≠ 0 ∧ A G = c • G
  | [], f, _, hf, h0 => absurd (by simpa [polyAt] using h0) hf
  | c :: L, f, hfW, hf, h0 => by
    by_cases hz : polyAt A L f = 0
    · obtain ⟨c', hc', G, hG⟩ := exists_eigen_of_polyAt A W hW L f hfW hf hz
      exact ⟨c', List.mem_cons_of_mem _ hc', G, hG⟩
    · refine ⟨c, List.mem_cons_self, _, polyAt_mem A W hW L f hfW, hz, ?_⟩
      have e : polyAt A (c :: L) f = A (polyAt A L f) - c • polyAt A L f := by
        simp [polyAt, List.map_cons, List.prod_cons]
      rw [e, sub_eq_zero] at h0
      exact h0

theorem polyAt_comm {V : Type} [AddCommGroup V] [Module ℂ V] {A B : Module.End ℂ V} (h : Commute A B) (L : List ℂ) :
    Commute (polyAt A L) B := by
  unfold polyAt
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left ((Commute.one_left B).smul_left c)

theorem eq_of_pow_bound {a ρ b M : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hb : 0 < b)
    (h1 : ∀ k : ℕ, a ^ k * b ≤ ρ ^ k * M) (h2 : ∀ k : ℕ, a⁻¹ ^ k * b ≤ ρ⁻¹ ^ k * M) : a = ρ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  ·
    have hq : 1 < ρ / a := (one_lt_div ha).2 hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / b) hq
    have := h2 k
    rw [inv_pow, inv_pow, ← div_eq_inv_mul, ← div_eq_inv_mul, div_le_div_iff₀ (pow_pos ha k) (pow_pos hρ k)] at this
    have h3 : (ρ / a) ^ k * b ≤ M := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos ha k)]; linarith
    have := (div_lt_iff₀ hb).1 hk
    linarith
  · have hq : 1 < a / ρ := (one_lt_div hρ).2 hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / b) hq
    have := h1 k
    have h3 : (a / ρ) ^ k * b ≤ M := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hρ k)]; linarith
    have := (div_lt_iff₀ hb).1 hk
    linarith

end GlobalTheory.PositionPeel

namespace GlobalTheory.PositionPeel

open GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)

theorem abs_root_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (K : Subgroup (GAd σ J)) (S : Finset (Fin r)), (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S,
    ∀ (φc : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J X Y S K φc → ∀ (s : Fin r → ℂ), GlobalTheory.StdPar.IsExponent σ J X Y S φc s →
    ∀ (e : (AF F ⊗[F] E)ˣ) (h : GAd σ J), GlobalTheory.LeviBlockRealization.IsBlockCentre σ J X Y i e h →
    ∀ (L : List ℂ), polyAt (GlobalTheory.LeviBlockRealization.leftTr σ J h)
        (L.map fun c => c * (((GlobalTheory.Doubling.absE F E e : ℝ) ^ (((n : ℝ) - 1) / 2 - (i : ℝ)) : ℝ) : ℂ)) φc = 0 →
      ∃ c ∈ L, ‖c‖ = (GlobalTheory.Doubling.absE F E e : ℝ) ^ (s i).re := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW K S hS i hi φc hφ s hs e h hh L hL
  classical
  obtain ⟨t, htc, ht⟩ := GlobalTheory.T.exists_continuous_split_torus_section hσ hJ hW
  have tu : ∀ {l a}, IsIdTorusElt σ J X Y l a → a = t l := fun ha => GlobalTheory.T.split_torus_element_unique hσ hJ hW ha (ht _)
  have tmul : ∀ l l', t (l * l') = t l * t l' := fun l l' => (tu (GlobalTheory.T.split_torus_element_mul (ht l) (ht l'))).symm
  have tcomm : ∀ l l', t l * t l' = t l' * t l := fun l l' => by rw [← tmul, ← tmul, mul_comm]
  have t1 : t 1 = 1 := (tu (isIdTorusElt_one σ J X Y)).symm
  let ι : (AF F ⊗[F] E)ˣ → Fin r → (AF F ⊗[F] E)ˣ := fun y => Pi.mulSingle i y
  have ιmul : ∀ a b, ι (a * b) = ι a * ι b := fun a b => Pi.mulSingle_mul (f := fun _ : Fin r => (AF F ⊗[F] E)ˣ) i a b
  have ιcont : Continuous ι := continuous_pi fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simpa [ι] using (continuous_id' : Continuous fun a : (AF F ⊗[F] E)ˣ => a)
    · simpa [ι, Pi.mulSingle_eq_of_ne hj] using continuous_const
  have hh' : h = t (ι e) := blockCentre_eq hσ hJ hW hh (ht _)
  have splitT : ∀ u a, IsSplitElt σ J X Y S u a → a = t (fun k => archUnit F E (stepSum S u k)) :=
    fun u a ha => tu (GlobalTheory.T.split_element_is_torus_element hσ hJ hW S u ha)
  let incl : Eˣ →* (AF F ⊗[F] E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom
  have ratLevi : ∀ γ : Eˣ, t (ι (incl γ)) ∈ ratPts σ J ∧ t (ι (incl γ)) ∈ levi σ J X Y S := by
    intro γ
    have ef : (fun j => incl ((Pi.mulSingle i γ : Fin r → Eˣ) j)) = ι (incl γ) := funext fun j => by
      rcases eq_or_ne j i with rfl | hj
      · simp [ι]
      · simp [ι, Pi.mulSingle_eq_of_ne hj]
    refine ⟨GlobalTheory.T.rational_split_torus_rational_points hσ hJ hW (Pi.mulSingle i γ) (ef ▸ ht _),
      (GlobalTheory.T.split_torus_in_levi_parabolic hσ hJ hW hS (l := ι (incl γ)) (fun k hk => ?_) (ht _)).1⟩
    simp [ι, Pi.mulSingle_eq_of_ne (show k ≠ i from fun e => hk (e ▸ hi))]
  let W : Submodule ℂ (GAd σ J → ℂ) :=
    { carrier := {f | Continuous f ∧ (∀ γ : Eˣ, ∀ x, f (t (ι (incl γ)) * x) = f x) ∧
        ∀ u a, IsSplitElt σ J X Y S u a → ∀ x, f (a * x) = expChar F n s (stepSum S u) * f x}
      add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, fun γ x => by simp only [Pi.add_apply, hf.2.1 γ x, hg.2.1 γ x],
        fun u a ha x => by simp only [Pi.add_apply, hf.2.2 u a ha x, hg.2.2 u a ha x]; ring⟩
      zero_mem' := ⟨continuous_const, fun _ _ => rfl, fun _ _ _ _ => by simp⟩
      smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun γ x => by simp only [Pi.smul_apply, hf.2.1 γ x],
        fun u a ha x => by simp only [Pi.smul_apply, smul_eq_mul, hf.2.2 u a ha x]; ring⟩ }
  have memW : ∀ f, f ∈ W ↔ Continuous f ∧ (∀ γ : Eˣ, ∀ x, f (t (ι (incl γ)) * x) = f x) ∧
      ∀ u a, IsSplitElt σ J X Y S u a → ∀ x, f (a * x) = expChar F n s (stepSum S u) * f x := fun _ => Iff.rfl
  set T := GlobalTheory.LeviBlockRealization.leftTr σ J h with hT
  have Tap : ∀ f x, T f x = f (h * x) := fun _ _ => rfl
  have commH : ∀ l, h * t l = t l * h := fun l => by rw [hh', tcomm]
  have stW : ∀ f ∈ W, T f ∈ W := by
    intro f hf
    obtain ⟨hf1, hf2, hf3⟩ := (memW f).1 hf
    refine (memW _).2 ⟨hf1.comp (continuous_const.mul continuous_id), fun γ x => ?_, fun u a ha x => ?_⟩
    · simp only [Tap]; rw [← mul_assoc, commH, mul_assoc, hf2]
    · simp only [Tap]; rw [← mul_assoc, splitT u a ha, commH, mul_assoc, ← splitT u a ha, hf3 u a ha]
  set δ : ℝ := (absE F E e : ℝ) ^ (((n : ℝ) - 1) / 2 - (i : ℝ)) with hδ
  set P := polyAt T (L.map fun c => c * (δ : ℂ)) with hP
  obtain ⟨f', hf'span, hf'0, hf'eig⟩ := hs
  have gen : ∀ f ∈ Submodule.span ℂ {f₁ : GAd σ J → ℂ | ∃ u a, IsSplitElt σ J X Y S u a ∧ f₁ = fun g => φc (a * g)},
      Continuous f ∧ (∀ γ : Eˣ, ∀ x, f (t (ι (incl γ)) * x) = f x) ∧ P f = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f₁ hf₁ =>
      obtain ⟨u, a, ha, rfl⟩ := hf₁
      refine ⟨hφ.1.cont.comp (continuous_const.mul continuous_id), fun γ x => ?_, ?_⟩
      · simp only
        rw [splitT u a ha, ← mul_assoc, tcomm, mul_assoc, hφ.1.leftM _ (ratLevi γ).1 (ratLevi γ).2]
      · have hc : Commute T (GlobalTheory.LeviBlockRealization.leftTr σ J a) := by
          refine LinearMap.ext fun f => funext fun x => ?_
          simp only [Module.End.mul_apply, Tap, GlobalTheory.LeviBlockRealization.leftTr_apply]
          rw [← mul_assoc, ← mul_assoc, splitT u a ha, commH]
        have := congrArg (fun A : Module.End ℂ (GAd σ J → ℂ) => A φc) (polyAt_comm hc (L.map fun c => c * (δ : ℂ))).eq
        simp only [Module.End.mul_apply] at this
        change P (GlobalTheory.LeviBlockRealization.leftTr σ J a φc) = 0
        rw [hP, this, ← hP, hL, map_zero]
    | zero => exact ⟨continuous_const, fun _ _ => rfl, map_zero _⟩
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, fun γ z => by simp only [Pi.add_apply, hx.2.1 γ z, hy.2.1 γ z], by
        rw [map_add, hx.2.2, hy.2.2, add_zero]⟩
    | smul c x _ hx =>
      exact ⟨hx.1.const_smul c, fun γ z => by simp only [Pi.smul_apply, hx.2.1 γ z], by rw [map_smul, hx.2.2, smul_zero]⟩
  obtain ⟨g1, g2, g3⟩ := gen f' hf'span
  have hf'W : f' ∈ W := (memW _).2 ⟨g1, g2, hf'eig⟩
  obtain ⟨c', hc', G, hGW, hG0, hGe⟩ := exists_eigen_of_polyAt T W stW _ f' hf'W hf'0 g3
  obtain ⟨c, hcL, rfl⟩ := List.mem_map.1 hc'
  refine ⟨c, hcL, ?_⟩
  obtain ⟨G1, G2, G3⟩ := (memW G).1 hGW
  have Gh : ∀ x, G (h * x) = (c * δ) * G x := fun x => congrFun hGe x
  obtain ⟨g0, hg0⟩ : ∃ g0, G g0 ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hG0 (funext hne)

  have hlam : c * (δ : ℂ) ≠ 0 := by
    intro h0
    apply hg0
    have := Gh (h⁻¹ * g0)
    rwa [mul_inv_cancel_left, h0, zero_mul] at this
  obtain ⟨D, κ, hDc, κmul, κabs, hdec⟩ := exists_decomp (F := F) (E := E) hσ
  have κone : κ 1 = 0 := by have := κmul 1 1; rw [mul_one] at this; linarith
  have κpow : ∀ y (k : ℕ), κ (y ^ k) = k * κ y := fun y k => by
    induction k with
    | zero => simp [κone]
    | succ k ih => rw [pow_succ, κmul, ih]; push_cast; ring
  have κinv : ∀ y, κ y⁻¹ = - κ y := fun y => by
    have := κmul y y⁻¹
    rw [mul_inv_cancel, κone] at this
    linarith
  obtain ⟨M, hM⟩ := hDc.exists_bound_of_continuousOn (f := fun d => G (t (ι d) * g0))
    ((G1.comp ((htc.comp ιcont).mul continuous_const)).continuousOn)
  have bound : ∀ y, ‖G (t (ι y) * g0)‖ ≤ ‖expChar F n s (Pi.single i (κ y))‖ * M := by
    intro y
    obtain ⟨γ, hγ⟩ := hdec y
    set d := incl γ * ((archUnit F E (κ y))⁻¹ * y) with hd
    have hy : y = archUnit F E (κ y) * (incl γ⁻¹ * d) := by
      rw [hd, map_inv]; group
    obtain ⟨u, hu⟩ := GlobalTheory.T.step_sum_surjective_initial_segment hS (Pi.single i (κ y))
      (fun k hk => Pi.single_eq_of_ne (show k ≠ i from fun e' => hk (e' ▸ hi)) _)
    obtain ⟨a, ha⟩ := exists_isSplitElt S hσ hJ hW u
    have el : (fun j => archUnit F E (stepSum S u j)) = ι (archUnit F E (κ y)) := funext fun j => by
      rw [hu]
      rcases eq_or_ne j i with rfl | hj
      · simp [ι]
      · simp [ι, Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, archUnit_zero]
    have hat : a = t (ι (archUnit F E (κ y))) := el ▸ splitT u a ha
    have e1 : G (t (ι y) * g0) = expChar F n s (Pi.single i (κ y)) * G (t (ι d) * g0) := by
      conv_lhs => rw [hy, ιmul, tmul, ιmul, tmul, ← hat, mul_assoc, mul_assoc, G3 u a ha, hu, G2]
    rw [e1, norm_mul]
    exact mul_le_mul_of_nonneg_left (hM _ hγ) (norm_nonneg _)
  have iter : ∀ (y : (AF F ⊗[F] E)ˣ) (μ : ℂ), (∀ x, G (t (ι y) * x) = μ * G x) → ∀ k : ℕ,
      G (t (ι (y ^ k)) * g0) = μ ^ k * G g0 := by
    intro y μ hy k
    induction k with
    | zero => simp [ι, t1]
    | succ k ih => rw [pow_succ', ιmul, tmul, mul_assoc, hy, ih]; ring
  have he : ∀ x, G (t (ι e) * x) = (c * δ) * G x := by rw [← hh']; exact Gh
  have hinv : t (ι e⁻¹) = h⁻¹ := by
    rw [hh']
    exact eq_inv_of_mul_eq_one_right (by rw [← tmul, ← ιmul, mul_inv_cancel]; simp [ι, t1])
  have heinv : ∀ x, G (t (ι e⁻¹) * x) = (c * δ)⁻¹ * G x := fun x => by
    rw [hinv]
    have := Gh (h⁻¹ * x)
    rw [mul_inv_cancel_left] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  set ρ := Real.exp (2 * Module.finrank ℚ F * κ e * ((s i).re - (negRho n r i).re)) with hρ
  have expk : ∀ c0 : ℝ, ‖expChar F n s (Pi.single i c0)‖ =
      Real.exp (2 * Module.finrank ℚ F * c0 * ((s i).re - (negRho n r i).re)) := fun c0 => GlobalTheory.T.norm_exp_character_single s i c0
  have h1 : ∀ k : ℕ, ‖c * (δ : ℂ)‖ ^ k * ‖G g0‖ ≤ ρ ^ k * M := by
    intro k
    have := bound (e ^ k)
    have eq : Real.exp (2 * Module.finrank ℚ F * (k * κ e) * ((s i).re - (negRho n r i).re)) = ρ ^ k := by
      rw [hρ, ← Real.exp_nat_mul]; ring_nf
    rw [iter e _ he k, norm_mul, norm_pow, expk, κpow, eq] at this
    exact this
  have h2 : ∀ k : ℕ, ‖c * (δ : ℂ)‖⁻¹ ^ k * ‖G g0‖ ≤ ρ⁻¹ ^ k * M := by
    intro k
    have := bound (e⁻¹ ^ k)
    have eq : Real.exp (2 * Module.finrank ℚ F * (k * κ e⁻¹) * ((s i).re - (negRho n r i).re)) = ρ⁻¹ ^ k := by
      rw [κinv, hρ, ← Real.exp_neg, ← Real.exp_nat_mul]; ring_nf
    rw [iter e⁻¹ _ heinv k, norm_mul, norm_pow, norm_inv, expk, κpow, eq] at this
    exact this
  have key : ‖c * (δ : ℂ)‖ = ρ :=
    eq_of_pow_bound (norm_pos_iff.2 hlam) (Real.exp_pos _) (norm_pos_iff.2 hg0) h1 h2
  have hA : (absE F E e : ℝ) = Real.exp (2 * Module.finrank ℚ F * κ e) := κabs e
  have hδ' : δ = Real.exp (2 * Module.finrank ℚ F * κ e * (((n : ℝ) - 1) / 2 - (i : ℝ))) := by
    rw [hδ, hA, ← Real.exp_mul]
  have hδpos : 0 < δ := by rw [hδ']; exact Real.exp_pos _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hδpos.le] at key
  have hc : ‖c‖ = ρ / δ := (eq_div_iff hδpos.ne').2 key
  have hx : (negRho n r i).re = (i : ℝ) - ((n : ℝ) - 1) / 2 := by simp [negRho]
  rw [hc, hA, ← Real.exp_mul, hρ, hδ', ← Real.exp_sub, hx]
  congr 1
  ring

end GlobalTheory.PositionPeel

end
