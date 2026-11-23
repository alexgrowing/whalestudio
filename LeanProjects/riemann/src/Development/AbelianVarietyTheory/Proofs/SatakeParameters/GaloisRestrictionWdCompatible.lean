import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section
open IsNilpotent

namespace GlobalTheory.AboveL.ResWD

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem exists_tval_resI (h' : IsPlaceOver A v') (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]} {t' : Ine (F := L) A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') :
    ∃ c : Qbar l, c ≠ 0 ∧ ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ := by
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul L Ω A v' h' l hl' (t.comp ResEx.resI) t'
    (ht.1.comp ResEx.continuous_resI) ht'.1 ht'.2
  refine ⟨algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]), ?_, fun σ => ?_⟩
  swap
  · have := hc σ
    simp only [MonoidHom.comp_apply] at this
    simp [tval, this]
  intro h0
  rw [map_eq_zero, PadicInt.coe_eq_zero] at h0
  have hc0 : ∀ σ, (t (ResEx.resI (K := K) σ)).toAdd = 0 := fun σ => by
    have := hc σ
    simpa [h0] using this
  obtain ⟨σ, hσ⟩ := ht.2 (Multiplicative.ofAdd 1)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let f : ℕ → (L →ₐ[K] Ω) := fun n => (((σ : G K Ω) ^ n : G K Ω) : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω)
  have main : ∀ i j : ℕ, i < j → f i = f j → False := fun i j hij e => by
    set k := j - i with hk
    have hk0 : 0 < k := Nat.sub_pos_of_lt hij
    have hfix : ∀ x : L, ((σ : G K Ω) ^ k).toRingEquiv (algebraMap L Ω x) = algebraMap L Ω x := fun x => by
      have e1 := congrArg (fun g : L →ₐ[K] Ω => g x) e
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_algHom] at e1
      have e2 : (σ : G K Ω) ^ j = (σ : G K Ω) ^ i * (σ : G K Ω) ^ k := by
        rw [← pow_add, hk, Nat.add_sub_cancel' hij.le]
      rw [e2, AlgEquiv.mul_apply] at e1
      exact (((σ : G K Ω) ^ i).injective e1).symm
    let σ'' : G L Ω := AlgEquiv.ofRingEquiv (f := ((σ : G K Ω) ^ k).toRingEquiv) hfix
    have hres : AlgEquiv.restrictScalarsHom K σ'' = (σ : G K Ω) ^ k := AlgEquiv.ext fun _ => rfl
    have hmem : σ'' ∈ Ine (F := L) A := by
      show AlgEquiv.restrictScalarsHom K σ'' ∈ Ine (F := K) A
      rw [hres]
      exact pow_mem σ.2 k
    have e3 : ResEx.resI (K := K) ⟨σ'', hmem⟩ = σ ^ k := Subtype.ext (by rw [SubgroupClass.coe_pow, ← hres]; rfl)
    have := hc0 ⟨σ'', hmem⟩
    rw [e3, map_pow, hσ, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at this
    omega
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact main i j hlt e
  · exact main j i hlt e.symm

theorem isMonodromy_res {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    IsMonodromy t' (resTo L r) (c • N) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  refine ⟨h1.smul c, U.comap ResEx.resI, hU.preimage ResEx.continuous_resI, fun σ hσ => ?_⟩
  have := H _ hσ
  rw [smul_smul, mul_comm, ← hc]
  exact this

theorem exists_conj (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    ∃ β : Qbar l, ∀ g : Weil h', exp (β • N) * wdMat t' (deg_frob (h := h')) (resTo L r) (c • N) g =
      wdMat t (deg_frob (h := h)) r N (ResEx.resW h h' g) * exp (β • N) := by
  have hq0 : ((normV v : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV v).ne_bot
  have hf : deg (ResEx.resW h h' (frob h')) ≠ 0 := by
    intro h0
    have h1 : ((frob h' : Weil h') : G L Ω) ∈ Ine (F := L) A :=
      (deg_eq_zero_iff (σ := ResEx.resW h h' (frob h'))).1 h0
    have h2 := (deg_eq_zero_iff (σ := frob h')).2 h1
    rw [deg_frob] at h2
    exact one_ne_zero h2
  have hq1 : 1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    intro h1
    have h3 : (((normV v : ℕ) : ℚ) ^ deg (ResEx.resW h h' (frob h')) : ℚ) = 1 := by
      rw [← Rat.cast_inj (α := Qbar l)]; push_cast; exact h1
    exact hf ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _)
      (Nat.cast_ne_one.mpr (one_lt_normV v).ne')).mp h3)
  have key : ∀ m : ℤ,
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ m))⁻¹) := fun m => by
    have h1 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h'))
      (ResEx.resW h h' (frob h') ^ m)
    have h2 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)
      (ResEx.resW h h' (frob h'))
    rw [(Commute.self_zpow (ResEx.resW h h' (frob h')) m).eq] at h1
    linear_combination h2 - h1
  refine ⟨tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹), fun g => ?_⟩
  have hg : g = frob h' ^ deg g * ineIncl h' (inePart (deg_frob (h := h')) g) := by
    rw [ineIncl_inePart, mul_inv_cancel_left]
  have hRg : ResEx.resW h h' g =
      ResEx.resW h h' (frob h') ^ deg g * ineIncl h (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    conv_lhs => rw [hg]
    rw [map_mul, map_zpow, ResEx.resW_ineIncl]
  have hT : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' g)) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) +
        tval t (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    rw [hRg, ht.tval_inePart_mul hl, deg_ineIncl, zpow_zero, inv_one, one_mul, inePart_ineIncl]
  have hd : deg (ResEx.resW h h' g) = deg (ResEx.resW h h' (frob h') ^ deg g) := by
    rw [hRg, deg_mul, deg_ineIncl, add_zero]
  have hs := key (deg g)
  have hqd : ((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g) ≠ 0 := zpow_ne_zero _ hq0
  rw [wdMat, wdMat, hT]
  have e1 : (-tval t' (inePart (deg_frob (h := h')) g)) • (c • N) =
      (-tval t (ResEx.resI (inePart (deg_frob (h := h')) g))) • N := by
    rw [smul_smul, hc]
    congr 1
    ring
  have e2 : ((resTo L r g : Matrix (Fin a) (Fin a) (Qbar l))) = r (ResEx.resW h h' g) := rfl
  rw [e1, e2]
  set β := tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) with hβ
  have h2 := hN.mul_exp hl ht (ResEx.resW h h' g) ((((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g))⁻¹ * β)
  rw [mul_inv_cancel_left₀ hqd] at h2
  rw [← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have hsm : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) =
      β * (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ deg g))⁻¹) := by
    rw [hβ, div_mul_eq_mul_div, eq_div_iff hq1]
    linear_combination hs
  rw [hd]
  linear_combination hsm

end GlobalTheory.AboveL.ResWD

namespace GlobalTheory.AboveL

theorem wdOf_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)) (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal) (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal), Continuous r → Restricts (wdOf h hl ι r) (wdOf h' hl' ι (resTo L r)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι a r hl hl' hr
  have hr' : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp hr
  have ht := isTameChar_tameL h hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr'
  obtain ⟨c, hc0, hc⟩ := ResWD.exists_tval_resI h' hl' ht ht'
  have hN' := ResWD.isMonodromy_res hN hc
  obtain ⟨β, hβ⟩ := ResWD.exists_conj h h' hl ht hN hc
  obtain ⟨aK, haK⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  have ex : wdOf h hl ι r = WD.mk aK := IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, aK, hN, haK, rfl⟩
  have hb : IsFrobSS (fun g => toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)))
      (toEndC ι N) (ResEx.resRep h h' aK) := ⟨haK.1, fun g => haK.2 _⟩
  obtain ⟨aL2, haL2⟩ := hN'.exists_isFrobSS hl' ht' (deg_frob (h := h')) ι
  have hcomm : ∀ g, hN'.rep hl' ht' (deg_frob (h := h')) ι g * toEndC ι N =
      ((normV v' : ℕ) : ℂ) ^ deg g • (toEndC ι N * hN'.rep hl' ht' (deg_frob (h := h')) ι g) := fun g => by
    have := hN'.rep_comm hl' ht' (deg_frob (h := h')) ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at this
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) this
  obtain ⟨aL1, haL1⟩ := WeilDeligne.exists_isFrobSS (hN'.rep hl' ht' (deg_frob (h := h')) ι) (toEndC ι N)
    (hN'.isSmooth_rep hl' ht' _ ι) (hN.1.map _) hcomm
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul β)).map (toEndC ι (n := Fin a))
  have i1 : aL1.Iso (ResEx.resRep h h' aK) := haL1.iso hb (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι (wdMat (tameL h' hl') (deg_frob (h := h')) (resTo L r) (c • N) g)) w =
        (toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)) * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, hβ, map_mul])
    (fun w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι N) w = (toEndC ι N * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : aL1.Iso aL2 := haL1.iso_of_smul ((map_ne_zero ι).mpr hc0) (by
    have := haL2
    rw [toEndC_smul] at this
    exact this)
  have ex' : wdOf h' hl' ι (resTo L r) = WD.mk (ResEx.resRep h h' aK) :=
    (IsWDOf.wdOf_eq hl' ⟨_, ht', _, deg_frob, c • N, aL2, hN', haL2, rfl⟩).trans (WD.sound (i2.symm.trans i1))
  refine ⟨a, aK, ResEx.resRep h h' aK, ex.symm, ex'.symm, rfl, fun σ σ' hs => ?_⟩
  show aK.ρ (ResEx.resW h h' σ') = aK.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL

end
