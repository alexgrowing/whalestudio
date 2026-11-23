import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
import GroundTheory.AutomorphicForms.CompactModCentre
import GroundTheory.AutomorphicForms.Cartan

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Zero.LLC

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem val_det_sub_one_lt {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) :
    valuation k ((GeneralLinearGroup.det g : kˣ) - 1 : k) < 1 := by
  classical
  rw [GlobalTheory.StepData.mem_KOne] at hg
  unfold GlobalTheory.StepData.MaxM at hg
  have hint : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro i j
    have h1 := hg i j
    rw [Matrix.sub_apply] at h1
    have h2 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [Valuation.mem_integer_iff]
    calc valuation k ((g : Matrix (Fin n) (Fin n) k) i j)
        = valuation k (((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)
            + (1 : Matrix (Fin n) (Fin n) k) i j) := by rw [sub_add_cancel]
      _ ≤ max _ _ := Valuation.map_add _ _ _
      _ ≤ 1 := max_le h1.le h2
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g : Matrix (Fin n) (Fin n) k) i j, hint i j⟩
  have hdet : ((M.det : 𝒪[k]) : k) = ((GeneralLinearGroup.det g : kˣ) : k) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    have h3 := RingHom.map_det (𝒪[k].subtype) M
    rw [Subring.coe_subtype] at h3
    rw [h3]
    congr 1
  have hres : IsLocalRing.residue 𝒪[k] M.det = IsLocalRing.residue 𝒪[k] 1 := by
    rw [RingHom.map_det, map_one]
    have hM : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
      have h5 : IsLocalRing.residue 𝒪[k] (M i j)
          = IsLocalRing.residue 𝒪[k] (if i = j then 1 else 0) := by
        rw [GlobalTheory.StepData.residue_eq_iff_lt]
        have h6 := hg i j
        rw [Matrix.sub_apply, Matrix.one_apply] at h6
        split_ifs at h6 ⊢ <;> simpa [M] using h6
      rw [h5]
      split_ifs <;> simp
    rw [hM, Matrix.det_one]
  have h4 := (GlobalTheory.StepData.residue_eq_iff_lt _ _).mp hres
  rw [hdet] at h4
  simpa using h4

private theorem fixed_ne_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) {H : Subgroup G} {v : V}
    (hv : v ∈ fixed ρ H) (h0 : v ≠ 0) : fixed σ H ≠ ⊥ := by
  intro hbot
  have hm : e v ∈ fixed σ H := by
    rw [GlobalTheory.Parabolic.mem_fixed] at hv ⊢
    intro u hu
    have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap u v
    simp only [Representation.Equiv.coe_toIntertwiningMap] at this
    rw [← this, hv u hu]
  rw [hbot, Submodule.mem_bot] at hm
  exact h0 ((map_eq_zero_iff e (EquivLike.injective e)).mp hm)

private def dOf (i₀ : Fin n) (u : kˣ) : GL (Fin n) k :=
  ⟨diagonal (Function.update (fun _ => (1 : k)) i₀ u), diagonal (Function.update (fun _ => (1 : k)) i₀ (u⁻¹ : kˣ)),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h]⟩

private theorem det_dOf (i₀ : Fin n) (u : kˣ) : GeneralLinearGroup.det (dOf i₀ u) = u := by
  ext
  simp [dOf, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal, Finset.prod_update_of_mem]

private theorem dOf_mem {i₀ : Fin n} {u : kˣ} (hu : valuation k ((u : k) - 1) < 1) : dOf i₀ u ∈ KOne k (Fin n) := by
  rw [GlobalTheory.StepData.mem_KOne]
  unfold GlobalTheory.StepData.MaxM
  intro i j
  simp only [dOf, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : i = i₀
    · subst h
      simpa using hu
    · simp [Function.update_of_ne h]
  · simp [hij]

private theorem dOf_comm (i₀ : Fin n) (u : kˣ) (μ : Fin n → ℤ) :
    dOf i₀ u * GroundTheory.Automorphic.Cartan.diagPow k n μ = GroundTheory.Automorphic.Cartan.diagPow k n μ * dOf i₀ u := by
  apply Units.ext
  simp only [Units.val_mul, GroundTheory.Automorphic.Cartan.coe_diagPow, dOf, diagonal_mul_diagonal, mul_comm]

end SlopeTestRemainingChoices

private theorem tame_of_dz {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (y : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (h0 : 0 < y.1) (hy : DZ y) (ht : DZ (y.tw χ hχ)) : TameChar χ := by
  classical
  unfold DZ at hy ht
  unfold TameChar
  intro u hu
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hy
  have ht' : fixed (twist y.rep (detChar (Fin y.fst) χ)) (KOne k (Fin y.fst)) ≠ ⊥ := by
    obtain ⟨w', hw', hw0'⟩ := (Submodule.ne_bot_iff _).mp ht
    exact fixed_ne_bot (y.twEquiv χ hχ).symm hw' hw0'
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp ht'
  set σ := twist y.rep (detChar (Fin y.fst) χ) with hσ
  set K := KOne k (Fin y.fst) with hK
  let i₀ : Fin y.fst := ⟨0, h0⟩
  have hd : dOf i₀ u ∈ K := dOf_mem hu
  set c : ℂ := ((χ u : ℂˣ) : ℂ) with hc
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hc1 : c⁻¹ - 1 ≠ 0 := by
    intro h
    apply hne
    apply Units.ext
    rw [Units.val_one]
    exact inv_eq_one.mp (sub_eq_zero.mp h)
  have key : ∀ x ∈ fixed σ K, ∀ μ : Fin y.fst → ℤ,
      y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x ∈ twKer y.rep K 1 := by
    intro x hx μ
    rw [GlobalTheory.Parabolic.mem_fixed] at hx
    have hdx : c • y.rep (dOf i₀ u) x = x := by
      have h1 := hx (dOf i₀ u) hd
      rwa [hσ, twist_apply, detChar_apply, det_dOf] at h1
    have hdx' : y.rep (dOf i₀ u) x = c⁻¹ • x := by
      calc y.rep (dOf i₀ u) x = c⁻¹ • (c • y.rep (dOf i₀ u) x) := by
            rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • x := by rw [hdx]
    have hz : y.rep (dOf i₀ u) (y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x)
        = c⁻¹ • y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x := by
      rw [← Module.End.mul_apply, ← map_mul, dOf_comm, map_mul, Module.End.mul_apply, hdx', map_smul]
    have hgen : y.rep (dOf i₀ u) (y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x)
        - (((1 : ↥K →* ℂˣ) ⟨dOf i₀ u, hd⟩ : ℂˣ) : ℂ) • y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x
        ∈ twKer y.rep K 1 := by
      unfold twKer
      exact Submodule.subset_span ⟨⟨dOf i₀ u, hd⟩, _, rfl⟩
    rw [hz, MonoidHom.one_apply, Units.val_one, one_smul] at hgen
    rw [show ∀ z : y.snd.rep.V, c⁻¹ • z - z = (c⁻¹ - 1) • z from
      fun z => by rw [sub_smul, one_smul]] at hgen
    have h2 := Submodule.smul_mem _ (c⁻¹ - 1)⁻¹ hgen
    rwa [smul_smul, inv_mul_cancel₀ hc1, one_smul] at h2
  have hall : ∀ g, y.rep g w ∈ twKer y.rep K 1 := by
    intro g
    obtain ⟨μ, -, k1, hk1, k2, hk2, rfl⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagPow_mul k y.fst g
    rw [← GlobalTheory.CompanionTheory.SphSupp.KO_eq_integralGL] at hk1 hk2
    have hx := GlobalTheory.DepthZeroJac.apply_mem_fixed (π := σ) hw hk2
    have h3 := key _ hx μ
    rw [hσ, twist_apply, map_smul] at h3
    have h4 := Submodule.smul_mem _ (((detChar (Fin y.fst) χ) k2 : ℂˣ) : ℂ)⁻¹ h3
    rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h4
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact GlobalTheory.DepthZeroJac.apply_mem_twKer_of_normalizer (GlobalTheory.DepthZeroJac.mem_normalizer_KOne hk1) h4
  haveI : y.rep.IsIrreducible := y.snd.rep.irr
  have htop := GroundTheory.Automorphic.SchurOrthogonality.span_orbit_eq_top (π := y.rep) hw0
  have hvk : v ∈ twKer y.rep K 1 := by
    have h5 : v ∈ Submodule.span ℂ (Set.range fun g => y.rep g w) := by
      rw [htop]
      exact Submodule.mem_top
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hall g) h5
  exact hv0 (GlobalTheory.IwahoriInj.eq_zero_of_fixed y.snd.rep.smooth GlobalTheory.DepthZeroJac.isCompact_KOne hv hvk)

private theorem dz_of_tame {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (y : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hy : DZ y) (ht : TameChar χ) : DZ (y.tw χ hχ) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy
  refine fixed_ne_bot (y.twEquiv χ hχ) (v := v) (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_) hv0
  have h1 : χ (GeneralLinearGroup.det g) = 1 := ht _ (val_det_sub_one_lt (n := y.1) hg)
  rw [twist_apply, detChar_apply, h1]
  simpa using GlobalTheory.Parabolic.mem_fixed.1 hv g hg

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.twTame :
    UpperTheory.Zero.LLC.TwTame := by
  unfold TwTame
  intro k _ _ _ _ _ y χ hχ h0 hy
  exact ⟨fun ht => tame_of_dz y χ hχ h0 hy ht, fun ht => dz_of_tame y χ hχ hy ht⟩
