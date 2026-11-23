import Mathlib
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyPow.Test

theorem fn_point_ext (V : (Sp ℂ).Opens) (f g : Γ(Sp ℂ, V))
    (h : ⊤ ≤ V → valAt' (𝟙 (Sp ℂ)) V f = valAt' (𝟙 (Sp ℂ)) V g) : f = g := by
  by_cases hV : ⊤ ≤ V
  · exact (TorusAlg.valAt'_id_bijective V (top_unique hV)).1.1 (h hV)
  · have : V = ⊥ := eq_bot_iff.2 fun x hx => hV fun y _ => by
      rwa [show y = x from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
    subst this
    exact Subsingleton.elim _ _

theorem exists_isRig {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    ∃ rig : LB.Gen (L.pull (eSec A)), rig.IsGen ∧ u.IsRig rig := by
  classical
  have h0 : (u.ex 0).left = eSec A := by
    rw [(u.ker 0).2 u.Λ.zero_mem]
    change (toUnit _ ≫ η[A]).left = η[A].left
    rw [toUnit_unit, Category.id_comp]
  have hm : ∀ j : (L.pull (eSec A)).ι, ⊤ ≤ (L.pull (eSec A)).U j → ⊤ ≤ (u.ex 0).left ⁻¹ᵁ L.U (j PUnit.unit) :=
    fun j hj y hy => by rw [h0]; exact Set.mem_iInter.1 (hj hy) PUnit.unit
  let c : (L.pull (eSec A)).ι → ℂˣ := fun j =>
    if hj : ⊤ ≤ (L.pull (eSec A)).U j then Units.mk0 _ (u.fr_ne _ 0 (hm j hj)) else 1
  let k : ∀ U : (Sp ℂ).Opens, ℂ →+* Γ(Sp ℂ, U) := fun U =>
    ((𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ).appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hk : ∀ (j) (hj : ⊤ ≤ (L.pull (eSec A)).U j),
      valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U j) (k _ (c j)) = u.fr (j PUnit.unit) 0 := fun j hj => by
    refine (valAt'_constFn (𝟙 _) (𝟙 _) (Category.id_comp _) ((L.pull (eSec A)).U j) (c j) (fun y hy => hj hy)).trans ?_
    simp only [c, dif_pos hj, Units.val_mk0]
  refine ⟨⟨fun j => Units.map (k ((L.pull (eSec A)).U j)).toMonoidHom (c j)⟩, fun i j => Units.ext (fn_point_ext _ _ _ fun hV => ?_),
    fun j hj => (hk j hj).symm⟩
  have hi : ⊤ ≤ (L.pull (eSec A)).U i := hV.trans inf_le_left
  have hj : ⊤ ≤ (L.pull (eSec A)).U j := hV.trans inf_le_right
  rw [Units.val_mul, valAt'_mul]
  have hV' : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ ((L.pull (eSec A)).U i ⊓ (L.pull (eSec A)).U j) := fun y hy => hV hy
  refine ((valAt'_res (𝟙 _) inf_le_left _ hV').trans (hk i hi)).trans (Eq.trans ?_ (congrArg _
    ((valAt'_res (𝟙 _) inf_le_right _ hV').trans (hk j hj)).symm))
  rw [u.fr_compat _ (j PUnit.unit) 0 ((top_le_preimage_inf _ _ _).2 ⟨hm i hi, hm j hj⟩)]
  congr 1
  have gg : (L.pull (eSec A)).g i j = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => eSec A) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => eSec A) j PUnit.unit)))
      (pullU (eSec A) _ (L.g (i PUnit.unit) (j PUnit.unit))) :=
    (Fintype.prod_unique (fun k : PUnit => (res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => eSec A) i k))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => eSec A) j k)))
      (pullU (eSec A) _ (L.g (i k) (j k)))) ^ (1 : ℤ))).trans (zpow_one _)
  rw [gg]
  refine Eq.symm ((valAt'_map (𝟙 _) _ _ hV').trans ((valAt'_comp (𝟙 _) (eSec A) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
    (L.g (i PUnit.unit) (j PUnit.unit)).val).trans ?_))
  rw [h0]
  rfl

theorem isLieBasis_of_isDiff (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {c : ℂ} (hc : c ≠ 0)
    (v : Fin P.g → (epsR ℂ ⟶ P.A)) (ht : ∀ i, IsTangent (v i)) (hd : ∀ i, u.IsDiff (Pi.single i c) (v i)) :
    IsLieBasis v := by
  have := P.isAb.comm
  obtain ⟨e₁, e₂, -⟩ := LieComb.lieComb_algebra ℂ P.A P.g v ht
  have key : ∀ (d : Fin P.g → ℂ) w, IsLieComb d v w → u.IsDiff (c • d) w := fun d w h => by
    have := isDiff_sum_smul_of_isLieComb P.A P.isAb P.L _ _ u v (fun i => Pi.single i c) d w ht hd h
    convert this using 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  refine ⟨ht, fun w hw => ?_⟩
  obtain ⟨z, hz, hu⟩ := h₁ w hw
  obtain ⟨w', hw', -⟩ := e₁ (c⁻¹ • z)
  have e := key _ _ hw'
  rw [smul_inv_smul₀ hc] at e
  obtain rfl : w' = w := (h₂ z).unique ⟨e₂ _ _ hw', e⟩ ⟨hw, hz⟩
  refine ⟨_, hw', fun d h => ?_⟩
  rw [← hu _ (key d _ h), inv_smul_smul₀ hc]

theorem exists_classical (H : TorusAlgebraic) (g : ℕ) (hg : 1 ≤ g) (α β : ℂ) (hα : α = 0 ∨ α = 1 / 2)
    (hβ : β = 0 ∨ β = 1 / 2) :
    ∃ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), x.P.g = g ∧
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ (fun _ => α) (fun _ => β)) ∧
      ∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i) := by
  obtain ⟨hs, hp⟩ := TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero
  obtain ⟨P, u, th, e, hΛ, ⟨h₁, h₂⟩, hth, -⟩ := H g _ (fun _ => α) (fun _ => β) hs hp (fun _ => hα) (fun _ => hβ)
  subst e
  obtain ⟨rig, hr, hR⟩ := exists_isRig u
  choose v hv using fun i : Fin P.g => (h₂ (Pi.single i (2 * Real.pi * Complex.I)⁻¹)).exists
  have hb := isLieBasis_of_isDiff P u h₁ h₂ (inv_ne_zero Complex.two_pi_I_ne_zero) v (fun i => (hv i).1) fun i => (hv i).2
  obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level hs hp (fun _ => hα) (fun _ => hβ)).1
  obtain ⟨i, hi⟩ := exists_chart P.isLB ((u.ex z).left (default : PrimeSpectrum ℂ))
  have hi' := (top_le_preimage_iff_mem _ _).2 hi
  have hne : th.f i ≠ 0 := fun h => by
    have := hth i z hi'
    rw [h, valAt'_zero] at this
    exact mul_ne_zero hz (u.fr_ne i z hi') this.symm
  exact ⟨⟨P, hg, rig, hr, th, exists_mem_nonzeroLocus P th ⟨i, hne⟩, v, hb⟩, u, _, rfl, hs, hp, hΛ, hR, hth,
    fun i => (hv i).2⟩

theorem rule_values (H : TorusAlgebraic) (N : ℕ → ℕ) (κ : KeyIn ℂ → ℂˣ)
    (hH : ∀ (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv th' hth' v' hv') (a : ℂ)
      (M : Matrix (Fin P.g) (Fin P.g) ℂ), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ (8 * N P.g) * (κ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : ℂ) =
        M.det ^ (4 * N P.g) * κ ⟨P, hg, rig, hr, th, hth, v, hv⟩)
    (hK : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
      τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
      u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
      (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ x = 1)
    (g : ℕ) (hg : 1 ≤ g) (t : ℂ) (ht : t ≠ 0) : ∃ x : KeyIn ℂ, x.P.g = g ∧ (κ x : ℂ) = t ^ (g * (4 * N g)) := by
  obtain ⟨x, u, τ, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_classical H g hg 0 0 (Or.inl rfl) (Or.inl rfl)
  have e := hK x u τ _ _ h₁ h₂ (fun _ => Or.inl rfl) (fun _ => Or.inl rfl) h₃ h₄ h₅ h₆
  have := x.P.isAb.comm
  obtain ⟨e₁, -, -, -, e₅⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  let M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := t • 1
  have hM : M.det = t ^ x.P.g := by simp [M]
  choose v' hv' using fun i => (e₁ (M i)).exists
  have hb : IsLieBasis v' := (e₅ M v' x.basis hv').2 (by rw [hM]; exact (pow_ne_zero _ ht).isUnit)
  have f := hH x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne v' hb 1 M
    (fun i => by rw [constFn, map_one, map_one, _root_.one_mul]) hv'
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hb⟩, rfl, ?_⟩
  change _ = _ * (κ x : ℂ) at f
  rw [e, hM, _root_.one_pow, _root_.one_mul, Units.val_one, _root_.mul_one, ← pow_mul] at f
  exact f

theorem exists_archNorm_sq_mul_eq_two_pi_pow (H : TorusAlgebraic) (hU : ThetaUnifAV) (h : KeyFormulaPow) (g : ℕ) (hg : 1 ≤ g) :
    ∃ (x : KeyIn ℂ) (nth nη : ℝ), x.P.g = g ∧ IsArchNorm x nth nη ∧ nth ^ 2 * nη = (2 * Real.pi) ^ g := by
  obtain ⟨N, hN, κ, -, -, -, hK, hA⟩ := h
  obtain ⟨x, u, τ, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_classical H g hg (1 / 2) (1 / 2) (Or.inr rfl) (Or.inr rfl)
  have e := hK x u τ _ _ h₁ h₂ (fun _ => Or.inr rfl) (fun _ => Or.inr rfl) h₃ h₄ h₅ h₆
  obtain ⟨nth, nη, hn⟩ := exists_isArchNorm hU x
  refine ⟨x, nth, nη, rfl, hn, ?_⟩
  obtain ⟨u, Hm, W, χ, θ, Fd, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := hn
  have f := hA x u Hm W χ θ Fd _ _ a₁ a₂ a₃ a₄ a₅ a₆ a₇
  have p : 0 ≤ nη := a₇ ▸ by positivity
  have hn := hN x.P.g
  have := Real.pi_pos
  refine (pow_left_inj₀ (by positivity) (by positivity) (show 2 * N x.P.g ≠ 0 by omega)).1 ?_
  rw [e, Units.val_one, norm_one, _root_.one_mul] at f
  rw [mul_pow, ← pow_mul, ← pow_mul, show 2 * (2 * N x.P.g) = 4 * N x.P.g by ring, f]
  congr 1
  ring

open NumberField IsDedekindDomain in

theorem isLocalModel_of_integral {K : Type} [Field K] [NumberField K] (x₀ : KeyIn (𝓞 K)) (x : KeyIn K)
    (h : KeyPB x x₀ (algebraMap (𝓞 K) K)) (𝔭 : HeightOneSpectrum (𝓞 K)) : IsLocalModel x 𝔭 1 1 := by
  let f : 𝓞 K →+* (𝔭.valuation K).integer :=
    (algebraMap (𝓞 K) K).codRestrict _ fun r => 𝔭.valuation_le_one r
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ f
  have := x.P.isAb.comm
  refine ⟨_, _, inferInstance, inferInstance, _, inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K),
    y, x.th, x.th_ne, x.v, x.basis, fun r => r.2, fun i => by rw [constFn, map_one, map_one, _root_.one_mul],
    fun i => ?_, KeyCancel.keyPB_cancel _ _ _ x₀ y x f _ hy h⟩
  convert (LieComb.lieComb_algebra K x.P.A x.P.g x.v x.basis.1).2.2.2.1 i using 1
  funext k
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

open NumberField IsDedekindDomain in

theorem degree_of_integral (hU : ThetaUnifAV) (h : KeyDegreeSt) {K : Type} [Field K] [NumberField K]
    (x₀ : KeyIn (𝓞 K)) : ∃ (x : KeyIn K) (nth nη : (K →+* ℂ) → ℝ), KeyPB x x₀ (algebraMap (𝓞 K) K) ∧
      (∀ σ : K →+* ℂ, ∃ x' : KeyIn ℂ, KeyPB x' x σ ∧ IsArchNorm x' (nth σ) (nη σ)) ∧
      ∑ σ : K →+* ℂ, (4 * Real.log (nth σ) + 2 * Real.log (nη σ)) =
        2 * x.P.g * Module.finrank ℚ K * Real.log (2 * Real.pi) := by
  obtain ⟨x, hx⟩ := exists_keyPB_ring x₀ (algebraMap (𝓞 K) K)
  obtain ⟨nth, nη, hn⟩ := exists_archNorms hU x
  refine ⟨x, nth, nη, hx, hn, ?_⟩
  simpa using (h K x 0 0 nth nη (fun 𝔭 => ⟨1, 1, isLocalModel_of_integral x₀ x hx 𝔭, by simp, by simp⟩) hn).2.2

end GlobalTheory.KeyPow.Test
