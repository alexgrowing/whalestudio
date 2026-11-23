import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical HeckeAlgebra
open scoped ValuativeRel Pointwise

namespace PositivityTheory.JacquetShalikaLocal

namespace MinusculeCentralEigen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem unipC_univ (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    unipC (F := F) Finset.univ c = 1 := by
  refine Units.ext ?_
  rw [coe_unipC, Units.val_one]
  have : cMat (F := F) (Finset.univ : Finset (Fin n)) c = 0 := by
    ext i j
    rw [cMat_apply_of_not c (fun h => h.2.1 (Finset.mem_univ _)), Matrix.zero_apply]
  rw [this, add_zero]

theorem lamS_univ : lamS (Finset.univ : Finset (Fin n)) = fun _ => 1 := by
  funext i
  simp [lamS]

theorem gMat_univ (c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F]) :
    gMat (F := F) Finset.univ c = torusPow F n (fun _ => 1) := by
  rw [gMat, unipC_univ, one_mul, lamS_univ]

theorem torusPow_one_mem : torusPow F n (fun _ => 1) ∈ minusculeSet F n n := by
  have c : Pairs (Finset.univ : Finset (Fin n)) → 𝓀[F] := fun p => absurd p.2.2.1 (by simp)
  have h := gMat_mem_minusculeSet (F := F) Finset.univ c
  rwa [gMat_univ, Finset.card_univ, Fintype.card_fin] at h

theorem mk_eq_of_mem {x : GL (Fin n) F} (hx : x ∈ minusculeSet F n n) :
    (QuotientGroup.mk x : GL (Fin n) F ⧸ integralGL F n) = QuotientGroup.mk (torusPow F n (fun _ => 1)) := by
  obtain ⟨S, hS, c, hc⟩ := exists_gMat hx
  have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS, Fintype.card_fin])
  subst hSu
  rw [← hc, gMat_univ]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rho_torusPow_one (ρ : Representation ℂ (GL (Fin n) F) V) (v : V) (z : Fin n → ℂˣ)
    (h : Heig ρ v z) : ρ (torusPow F n (fun _ => 1)) v = monomialChar (fun _ => 1) z • v := by
  have e := h.2 n le_rfl
  rw [Nat.sub_self, mul_zero, pow_zero, one_mul, evalAt_esymmL] at e
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [hp, Finset.sum_singleton, lamS_univ] at e
  rw [← e, finsum_eq_single _ (QuotientGroup.mk (torusPow F n (fun _ => 1)))]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (torusPow F n (fun _ => (1 : ℤ)))
    have hm : torusPow F n (fun _ => (1 : ℤ)) * (k : GL (Fin n) F) ∈ minusculeSet F n n := by
      have := mul_mem_minusculeSet (torusPow_one_mem (F := F) (n := n)) (integralGL F n).one_mem k.2
      rwa [one_mul] at this
    rw [hk, Set.indicator_of_mem hm, one_smul, map_mul, Module.End.mul_apply, h.1 _ k.2]
  · intro x hx
    have hm : x.out ∉ minusculeSet F n n := by
      intro hm
      apply hx
      rw [← mk_eq_of_mem hm, QuotientGroup.out_eq']
    rw [Set.indicator_of_notMem hm, zero_smul]

theorem rho_torusPow_neg_one (ρ : Representation ℂ (GL (Fin n) F) V) (v : V) (z : Fin n → ℂˣ)
    (h : Heig ρ v z) : ρ (torusPow F n (fun _ => -1)) v = monomialChar (fun _ => -1) z • v := by
  have hc : monomialChar (fun _ : Fin n => (1 : ℤ)) z * monomialChar (fun _ => -1) z = 1 := by
    rw [← monomialChar_add]
    have : ((fun _ : Fin n => (1 : ℤ)) + fun _ => -1) = 0 := by
      funext i
      simp
    rw [this, monomialChar_zero]
  have hneg : torusPow F n (fun _ => -1) = (torusPow F n (fun _ => 1))⁻¹ := by
    rw [← torusPow_neg]
    congr 1
  have e := rho_torusPow_one ρ v z h
  have e2 : ρ (torusPow F n (fun _ => 1)) (monomialChar (fun _ => -1) z • v) = v := by
    rw [map_smul, e, smul_smul, mul_comm, hc, one_smul]
  calc ρ (torusPow F n (fun _ => -1)) v
      = ρ (torusPow F n (fun _ => -1)) (ρ (torusPow F n (fun _ => 1)) (monomialChar (fun _ => -1) z • v)) := by
        rw [e2]
    _ = monomialChar (fun _ => -1) z • v := by
        rw [← Module.End.mul_apply, ← map_mul, hneg, inv_mul_cancel, map_one, Module.End.one_apply]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem eig_minuscule (ρ : Representation ℂ (GL (Fin n) F) V) (v : V) (z : Fin n → ℂˣ)
    (h : Heig ρ v z) (l : V →ₗ[ℂ] ℂ) {r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * l (ρ (g * x) v) ∂μ =
      evalAt z (satakeTransform μ (minusculeHecke μ r)) * l (ρ g v) := by
  set W : GL (Fin n) F → ℂ := fun y => l (ρ y v) with hW
  have hWK : ∀ y, ∀ k ∈ integralGL F n, W (y * k) = W y := by
    intro y k hk
    simp only [hW, map_mul, Module.End.mul_apply, h.1 k hk]
  set Φ : GL (Fin n) F → ℂ := fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * W (g * x) with hΦ
  have hcs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [hΦ, minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  have hK : ∀ x, ∀ k ∈ integralOpen F n, Φ (x * k) = Φ x := by
    intro x k hk
    simp only [hΦ]
    rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hWK _ k hk]
  change ∫ x, Φ x ∂μ = _
  rw [integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hcs hK,
    Complex.real_smul, evalAt_satakeTransform_minusculeHecke z hr]
  change _ * (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n, Φ x.out) = _
  set Ψ : GL (Fin n) F ⧸ integralGL F n → V :=
    fun c => (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) c.out • ρ c.out v with hΨ
  have hΦΨ : ∀ c : GL (Fin n) F ⧸ integralGL F n, Φ c.out = (l ∘ₗ ρ g) (Ψ c) := by
    intro c
    simp only [hΦ, hΨ, hW, minusculeHecke_apply, LinearMap.comp_apply, map_smul, smul_eq_mul, map_mul,
      Module.End.mul_apply]
  have hfin : (Function.support Ψ).Finite := by
    have hc : HasCompactSupport ((minusculeSet F n r).indicator (fun _ => (1 : ℂ))) :=
      (minusculeHecke μ r : HeckeAlgebra μ).mem.2
    have hfin' : (QuotientGroup.mk '' tsupport ((minusculeSet F n r).indicator (fun _ => (1 : ℂ))) :
        Set (GL (Fin n) F ⧸ integralGL F n)).Finite := finite_image_mk_tsupport (integralOpen F n) hc
    refine hfin'.subset fun c hc' => ?_
    refine ⟨c.out, subset_tsupport _ fun h0 => hc' ?_, QuotientGroup.out_eq' c⟩
    simp only [hΨ]
    rw [h0, zero_smul]
  simp only [hΦΨ]
  rw [← map_finsum _ hfin, hΨ, h.2 r hr, map_smul, smul_eq_mul]
  simp only [LinearMap.comp_apply]
  rw [show ((integralOpen F n : Set (GL (Fin n) F))) = (integralGL F n : Set (GL (Fin n) F)) from rfl]
  ring

theorem eig_central (ρ : Representation ℂ (GL (Fin n) F) V) (v : V) (z : Fin n → ℂˣ)
    (h : Heig ρ v z) (l : V →ₗ[ℂ] ℂ) (g : GL (Fin n) F) :
    ∫ x, (centralHecke μ : HeckeAlgebra μ) x * l (ρ (g * x) v) ∂μ =
      evalAt z (satakeTransform μ (centralHecke μ)) * l (ρ g v) := by
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * l (ρ (g * x) v)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) * l (ρ (g * (g₀ * y)) v)) =
      (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => l (ρ (g * g₀) v)) := by
    funext y
    rw [centralHecke_apply]
    by_cases hy : y ∈ integralGL F n
    · have hm : g₀ * y ∈ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ (integralGL F n : Set (GL (Fin n) F))
        from hy), one_mul, ← mul_assoc, map_mul, Module.End.mul_apply, h.1 y hy]
    · have hm : g₀ * y ∉ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ (integralGL F n :
        Set (GL (Fin n) F)) from hy), zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, map_mul, Module.End.mul_apply, rho_torusPow_neg_one ρ v z h, map_smul,
    map_smul, smul_eq_mul, satakeTransform_centralHecke, map_smul, monomial, evalAt_single, one_mul,
    smul_eq_mul]
  ring

end MinusculeCentralEigen

open MinusculeCentralEigen in
theorem minuscule_eigenvalue : L7 := by
  intro F _ _ _ _ ψ hψ n V _ _ ρ v z h l hl g
  borelize (GL (Fin n) F)
  have hWN : ∀ u ∈ unipotent F n, ∀ g, l (ρ (u * g) v) = Whittaker.psiN ψ u * l (ρ g v) := by
    intro u hu g
    rw [map_mul, Module.End.mul_apply, hl u hu]
  have hWK : ∀ g, ∀ k ∈ integralGL F n, l (ρ (g * k) v) = l (ρ g v) := by
    intro g k hk
    rw [map_mul, Module.End.mul_apply, h.1 k hk]
  have htop := eigenSubalgebra_eq_top (μ := (Measure.haar : Measure (GL (Fin n) F))) z (f := fun y => l (ρ y v)) hWK
    (fun r hr g => eig_minuscule ρ v z h l hr g) (fun g => eig_central ρ v z h l g)
  have heig : ∀ (k : SphericalHecke (Measure.haar : Measure (GL (Fin n) F)) (F := F) (n := n))
      (g : GL (Fin n) F), ∫ x, (k : HeckeAlgebra (Measure.haar : Measure (GL (Fin n) F))) x * l (ρ (g * x) v) ∂Measure.haar =
        evalAt z (satakeTransform _ k) * l (ρ g v) := by
    intro k
    have hmem : k ∈ eigenSubalgebra _ z (fun y => l (ρ y v)) hWK := by
      rw [htop]
      exact Algebra.mem_top
    exact hmem
  have := eq_smul_sphericalWhittaker hψ.1 hψ.2.1 z (W := fun y => l (ρ y v)) hWN hWK heig g
  simpa [map_one] using this

end PositivityTheory.JacquetShalikaLocal

end
