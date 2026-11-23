import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSApx

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

variable {F : Type} [Field F] [NumberField F] {Δ : F}

private abbrev MA (Δ : F) : Type := ∀ v : Pl F, Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v Δ))

private def RA (Δ : F) : Subring (MA Δ) where
  carrier := {m | ∀ v, m v ∈ Dm (cv v Δ) ∧ ∀ i j, IsIntegral (Ov v) (m v i j)}
  mul_mem' {a b} ha hb v := ⟨mul_mem (ha v).1 (hb v).1, fun i j => by
    rw [Pi.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    exact (((ha v).2 _ _).mul ((hb v).2 _ _)).add (((ha v).2 _ _).mul ((hb v).2 _ _))⟩
  one_mem' v := ⟨one_mem _, fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h, isIntegral_one, isIntegral_zero]⟩
  add_mem' {a b} ha hb v := ⟨add_mem (ha v).1 (hb v).1, fun i j => ((ha v).2 i j).add ((hb v).2 i j)⟩
  zero_mem' v := ⟨zero_mem _, fun _ _ => isIntegral_zero⟩
  neg_mem' {a} ha v := ⟨neg_mem (ha v).1, fun i j => ((ha v).2 i j).neg⟩

private def jA (Δ : F) : Dm Δ →+* MA Δ := RingHom.pi fun v => (lmap (cv v) Δ).mapMatrix.comp (Dm Δ).subtype

private def psiA (Δ : F) : DA Δ →* (MA Δ)ˣ :=
  MonoidHom.toHomUnits (MonoidHom.pi fun v : Pl F =>
    (Units.coeHom _).comp ((DX (cv v Δ)).subtype.comp ((rpg _ fun v : Pl F => KD (cv v Δ) (Ov v)).p v)))

private theorem psiA_apply (g : DA Δ) (v : Pl F) : (psiA Δ g : MA Δ) v = mt (g.1 v) := rfl

theorem Dm_unit [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (x : Dm Δ) (hx : x ≠ 0) :
    IsUnit (x : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_Dm x.2]
  refine IsUnit.map _ (Ne.isUnit fun h => hx ?_)
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  set σ := (IsTotallyReal.complexEmbedding_isReal φ).embedding
  have hs := congrArg σ h
  simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hs
  have hn := neg_pos.2 (hneg σ)
  have p1 := mul_nonneg hn.le (sq_nonneg (σ (x.1 0 0).im))
  have p2 := mul_nonneg hn.le (sq_nonneg (σ (x.1 0 1).im))
  have p3 := sq_nonneg (σ (x.1 0 0).re)
  have p4 := sq_nonneg (σ (x.1 0 1).re)
  have z : ∀ t : F, σ t ^ 2 = 0 → t = 0 := fun t ht => by simpa using ht
  have z' : ∀ t : F, -σ Δ * σ t ^ 2 = 0 → t = 0 := fun t ht => z t ((mul_eq_zero.1 ht).resolve_left hn.ne')
  have e0 : x.1 0 0 = 0 := QuadraticAlgebra.ext (z _ (by linarith)) (z' _ (by linarith))
  have e1 : x.1 0 1 = 0 := QuadraticAlgebra.ext (z _ (by linarith)) (z' _ (by linarith))
  refine Subtype.ext ?_
  ext i j : 1
  fin_cases i <;> fin_cases j
  · exact e0
  · exact e1
  · exact x.2.2.trans (by simp [e1])
  · exact x.2.1.trans (by simp [e0])

private theorem finite_lat (hΔ : Δ ≠ 0) : Module.Finite ℤ ((RA Δ).comap (jA Δ)) := by
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul Δ
  have hc : (2 * m * Δ : F) ≠ 0 := by simp [hΔ, hm0]
  have hi := fun (y : (RA Δ).comap (jA Δ)) i => coords_glob (a := y.1.1 0 i) (fun v => (y.2 v).2 0 i) hm
  let ψ : (RA Δ).comap (jA Δ) →+ (Fin 2 → 𝓞 F × 𝓞 F) :=
    { toFun := fun y i => (⟨_, (hi y i).1⟩, ⟨_, (hi y i).2⟩)
      map_zero' := funext fun i => Prod.ext (Subtype.ext (mul_zero _)) (Subtype.ext (mul_zero _))
      map_add' := fun x y => funext fun i => Prod.ext (Subtype.ext (mul_add _ _ _)) (Subtype.ext (mul_add _ _ _)) }
  refine Module.Finite.of_injective ψ.toIntLinearMap fun x y h => Subtype.ext (Subtype.ext ?_)
  have e : ∀ i, x.1.1 0 i = y.1.1 0 i := fun i => QuadraticAlgebra.ext
    (mul_left_cancel₀ hc (congrArg (fun p : 𝓞 F × 𝓞 F => (p.1 : F)) (congrFun h i)))
    (mul_left_cancel₀ hc (congrArg (fun p : 𝓞 F × 𝓞 F => (p.2 : F)) (congrFun h i)))
  ext i j : 1
  fin_cases i <;> fin_cases j
  · exact e 0
  · exact e 1
  · exact x.1.2.2.trans (e 1 ▸ y.1.2.2.symm)
  · exact x.1.2.1.trans (e 0 ▸ y.1.2.1.symm)

private theorem apx_alg {K K' O : Type} [Field K] [Field K'] [CommRing O] [Algebra O K'] (f : K →+* K') (Δ : K) (a : Lsq K' (f Δ))
    (n m : ℕ) (x1 x2 : K) (h : f ((n : K) * m) ≠ 0) (hm : IsIntegral O (f ((m : K) * Δ)))
    (h1 : IsIntegral O ((f ((n : K) * m))⁻¹ * a.re - f x1)) (h2 : IsIntegral O ((f ((n : K) * m))⁻¹ * a.im - f x2)) :
    ∃ r : Lsq K' (f Δ), IsIntegral O r ∧ a = lmap f Δ ⟨n * m * x1, n * m * x2⟩ + n * r := by
  simp only [map_mul, map_natCast] at h hm h1 h2
  refine ⟨_, isIntegral_of_coords (a := ⟨((n : K') * m)⁻¹ * a.re - f x1, ((n : K') * m)⁻¹ * a.im - f x2⟩)
    (isIntegral_natCast m) hm h1 h2, ?_⟩
  have hn := left_ne_zero_of_mul h
  have hm' := right_ne_zero_of_mul h
  ext <;> simp [lmap] <;> field_simp <;> ring

private theorem apx_den {K K' O : Type} [Field K] [Field K'] [CommRing O] [Algebra O K'] (f : K →+* K') (Δ : K) (a : Lsq K' (f Δ))
    (ha : IsIntegral O a) (m : ℕ) (c : K) (h : f c ≠ 0) (hm : IsIntegral O (f ((m : K) * Δ))) :
    IsIntegral O (f (2 * m * Δ * c) * ((f c)⁻¹ * a.re)) ∧ IsIntegral O (f (2 * m * Δ * c) * ((f c)⁻¹ * a.im)) := by
  simp only [map_mul, map_natCast, map_ofNat, mul_assoc _ (f c), mul_inv_cancel_left₀ h] at hm ⊢
  exact isIntegral_coords ha (isIntegral_natCast m) hm

theorem apx_L (hΔ : Δ ≠ 0) (a : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)) (ha : ∀ v, IsIntegral (Ov v) (a v)) (n : ℕ) (hn : n ≠ 0) :
    ∃ (x : Lsq F Δ) (r : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)), ∀ v, IsIntegral (Ov v) (r v) ∧ a v = lmap (cv v) Δ x + n * r v := by
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul Δ
  have hc : (2 * m * Δ * (n * m) : F) ≠ 0 := by simp [hΔ, hm0, hn]
  have hmv := isIntegral_glob.1 hm
  have hnm : ∀ v : Pl F, cv v ((n : F) * m) ≠ 0 := fun v => (_root_.map_ne_zero _).2 (by simp [hm0, hn])
  have hi := fun v => apx_den (cv v) Δ (a v) (ha v) m _ (hnm v) (hmv v)
  obtain ⟨x1, h1⟩ := apx _ hc _ fun v => isIntegral_Ov.1 (hi v).1
  obtain ⟨x2, h2⟩ := apx _ hc _ fun v => isIntegral_Ov.1 (hi v).2
  choose r hr using fun v => apx_alg (O := Ov v) (cv v) Δ (a v) n m x1 x2 (hnm v) (hmv v) (isIntegral_Ov.2 (h1 v))
    (isIntegral_Ov.2 (h2 v))
  exact ⟨_, r, hr⟩

private theorem dense_lat (hΔ : Δ ≠ 0) (r : MA Δ) (hr : r ∈ RA Δ) (n : ℕ) (hn : n ≠ 0) :
    ∃ x : Dm Δ, ∃ r' ∈ RA Δ, r = jA Δ x + n * r' := by
  choose x s h using fun i => apx_L hΔ (fun v => r v 0 i) (fun v => (hr v).2 0 i) n hn
  refine ⟨⟨!![x 0, x 1; -star (x 1), star (x 0)], rfl, rfl⟩, fun v => !![s 0 v, s 1 v; -star (s 1 v), star (s 0 v)],
    fun v => ⟨⟨rfl, rfl⟩, fun i j => ?_⟩, funext fun v => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact (h 0 v).1
    · exact (h 1 v).1
    · exact (isIntegral_star (h 1 v).1).neg
    · exact isIntegral_star (h 0 v).1
  · have e : ∀ y : Lsq F Δ, lmap (cv v) Δ (star y) = star (lmap (cv v) Δ y) := fun y => by ext <;> simp [lmap]
    rw [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, ← nsmul_eq_mul]
    ext i j : 1
    fin_cases i <;> fin_cases j
    · simpa [jA] using (h 0 v).2
    · simpa [jA] using (h 1 v).2
    · refine (hr v).1.2.trans ?_
      rw [(h 1 v).2]
      simp [jA, e, add_comm]
    · refine (hr v).1.1.trans ?_
      rw [(h 0 v).2]
      simp [jA, e]

theorem clsD [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ∃ Y : Finset (DA Δ), ∀ g, ∃ γ, ∃ y ∈ Y, ∃ k ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v)), g = ι γ * y * k := by
  have hΔ := ne_zero_of_neg hneg
  have := finite_lat hΔ
  have : CharZero (Dm Δ) := ⟨fun a b h => by
    have h1 := congrArg (fun x : Dm Δ => (x.1 0 0).re) h
    simpa [Matrix.natCast_apply] using h1⟩
  have : NoZeroDivisors (Dm Δ) := ⟨fun {a b} h => or_iff_not_imp_left.2 fun ha =>
    Subtype.ext ((Dm_unit hneg a ha).mul_right_eq_zero.1 (congrArg Subtype.val h))⟩
  have : IsDomain (Dm Δ) := NoZeroDivisors.to_isDomain _
  refine cls_abs_unit (jA Δ) (RA Δ) (psiA Δ) ι _ (fun k h1 h2 => Subgroup.mem_iInf.2 fun v => mem_KD.2 ⟨(h1 v).2, (h2 v).2⟩)
    (fun x hx => ?_) (fun g => ?_) (dense_lat hΔ)
  · refine ⟨⟨(Dm_unit hneg x hx).unit, mem_DX.2 x.2⟩, funext fun v => ?_⟩
    rw [psiA_apply, hι]
    rfl
  · obtain ⟨n, hn, h⟩ := den_DA g
    refine ⟨n, hn, fun v => ⟨mul_mem (natCast_mem _ n) (mt_mem _), fun i j => ?_⟩⟩
    rw [Pi.mul_apply, Pi.natCast_apply, ← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul]
    exact h v i j

end UpperTheory.V.Z.Sym.Glob
