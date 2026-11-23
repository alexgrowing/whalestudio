import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermCL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.GmapLeLocS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement

open NumberField PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Lin

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {M : ℕ}

theorem linOf_mul (b : Module.Basis (Fin M) E V) (u w : GL (Fin M) E) :
    linOf b (u * w) = linOf b u * linOf b w := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, LinearEquiv.mul_apply, equivFun_linOf, equivFun_linOf, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem linOf_one (b : Module.Basis (Fin M) E V) : linOf b (1 : GL (Fin M) E) = 1 := by
  apply LinearEquiv.ext
  intro v
  apply b.equivFun.injective
  rw [equivFun_linOf, Units.val_one, Matrix.one_mulVec]
  rfl

end Lin

theorem gmap_one {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (X : Submodule (𝓞 E) V) : gmap (1 : V ≃ₗ[E] V) X = X := by
  ext v
  simp [gmap, Submodule.mem_map]

theorem lattices_close_locally : LatClose := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  classical
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL0
  obtain ⟨u, hu, hu'⟩ := up_nat (crdOf b L0) ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat (crdOf b L0) ⟨c2, hc2, hlow⟩
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹
  obtain ⟨dg, hdg, hdgi⟩ := mat_den ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
  set Nn : ℕ := dg * dI * dJ * (u * k) with hNn
  have hNpos : 0 < Nn := by positivity
  refine ⟨(Nn : 𝓞 F), by exact_mod_cast hNpos.ne', fun D' hD' γ hγ S hS hcong => ?_⟩
  obtain ⟨c, rfl⟩ := hD'
  choose r hr y hy using hcong
  set R : 𝓞 E := ∏ q : Fin M × Fin M, r q.1 q.2 with hRd
  have hRS : R ∈ S := Submonoid.prod_mem _ fun q _ => hr q.1 q.2
  set cE : E := algebraMap F E ((c : 𝓞 F) : F) with hcE
  have hcEi : IsIntegral ℤ cE := c.isIntegral_coe.algebraMap
  have hz : ∀ i j, ∃ z : E, IsIntegral ℤ z ∧
      (R : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) = (Nn : E) * cE * z := by
    intro i j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun q : Fin M × Fin M => r q.1 q.2) (Finset.mem_univ (i, j))
    refine ⟨(q : E) * (y i j : E), q.isIntegral_coe.mul (y i j).isIntegral_coe, ?_⟩
    have e1 : (R : E) = (r i j : E) * (q : E) := by rw [hRd, hq]; push_cast; rfl
    rw [e1, mul_comm (r i j : E) (q : E), mul_assoc, hy i j]
    have e2 : algebraMap F E (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : E) * cE := by
      have e5 : (((Nn : 𝓞 F) * c : 𝓞 F) : F) = (Nn : F) * ((c : 𝓞 F) : F) := by push_cast; ring
      rw [e5, map_mul, map_natCast]
    rw [e2]; ring
  choose z hzi hze using hz
  set gi : Matrix (Fin M) (Fin M) E := ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hgi
  set K : GL (Fin M) E := g⁻¹ * γ with hKd
  set Km : Matrix (Fin M) (Fin M) E := (K : Matrix (Fin M) (Fin M) E) with hKm
  have hgig : gi * (g : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]

  set e0 : Fin M → Fin M → E := fun i j => -cE * ∑ l, ((dg : E) * gi i l) * z l j with he0d
  have he0i : ∀ i j, IsIntegral ℤ (e0 i j) := fun i j =>
    (hcEi.neg).mul (IsIntegral.sum _ fun l _ => (hdgi i l).mul (hzi l j))
  have hK1 : ∀ i j, (algebraMap (𝓞 E) E R) * (Km - 1) i j = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * e0 i j) := by
    intro i j
    have eK : Km - 1 = gi * ((γ : Matrix (Fin M) (Fin M) E) - (g : Matrix (Fin M) (Fin M) E)) := by
      rw [hKm, hKd, Units.val_mul, Matrix.mul_sub, hgig]
    rw [eK, Matrix.mul_apply, Finset.mul_sum, he0d]
    simp only [Matrix.sub_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := hze l j
    change (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) = _
    have e3 : (R : E) * (gi i l * ((γ : Matrix (Fin M) (Fin M) E) l j - (g : Matrix (Fin M) (Fin M) E) l j)) =
        -(gi i l * ((R : E) * ((g : Matrix (Fin M) (Fin M) E) l j - (γ : Matrix (Fin M) (Fin M) E) l j))) := by ring
    rw [e3, this, hNn]
    push_cast
    ring

  have hKu : K ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J := (PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).mul_mem ((PI.UnitaryApproxDefs.UJ (σ : E →+* E) J).inv_mem hg) hγ
  have hKu' : PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km = J := hKu
  have hJJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  set KImage : Matrix (Fin M) (Fin M) E := ((K⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) with hKim
  have hKK : Km * KImage = 1 := by rw [hKm, hKim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKinv : KImage = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by
    calc KImage = J⁻¹ * J * KImage := by rw [hJJ, Matrix.one_mul]
      _ = J⁻¹ * (PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * Km) * KImage := by rw [hKu']
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J * (Km * KImage) := by simp only [Matrix.mul_assoc]
      _ = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) Km * J := by rw [hKK, Matrix.mul_one]
  have hcs : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) = PI.UnitaryApproxDefs.cT (σ : E →+* E) Km - 1 := by
    have h1 := PI.UnitaryApproxDefs.cT_one (n := Fin M) (σ : E →+* E)
    unfold PI.UnitaryApproxDefs.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hKi1 : KImage - 1 = J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) * J := by
    rw [hKinv, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]
  have hR0 : σ (algebraMap (𝓞 E) E R) = algebraMap (𝓞 E) E R := hS R hRS
  have hK2 : ∀ i j, (algebraMap (𝓞 E) E R) * (KImage - 1) i j = ((u * k : ℕ) : E) *
      (∑ a, ∑ b', ((dI : E) * J⁻¹ i a) * σ (e0 b' a) * ((dJ : E) * J b' j)) := by
    intro i j
    rw [hKi1]
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b' _ => ?_
    have hσK : (algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a) = ((u * k : ℕ) : E) * (((dI * dJ : ℕ) : E) * σ (e0 b' a)) := by
      rw [← hR0, ← map_mul, hK1 b' a, map_mul, map_mul, map_natCast, map_natCast]
    have hX : PI.UnitaryApproxDefs.cT (σ : E →+* E) (Km - 1) a b' = σ ((Km - 1) b' a) := rfl
    rw [hX]
    calc (algebraMap (𝓞 E) E R) * (J⁻¹ i a * σ ((Km - 1) b' a) * J b' j)
        = J⁻¹ i a * ((algebraMap (𝓞 E) E R) * σ ((Km - 1) b' a)) * J b' j := by ring
      _ = _ := by rw [hσK]; push_cast; ring

  have h1 : gmap (linOf b K) L0 ≤ locS S L0 := gmap_le_locS b L0 S K fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' Km R _ (fun i j => (isIntegral_natCast _).mul (he0i i j)) hK1 hx⟩
  have h2 : gmap (linOf b K⁻¹) L0 ≤ locS S L0 := gmap_le_locS b L0 S K⁻¹ fun x hx =>
    ⟨R, hRS, glob_stab (F := F) b L0 hu' hk' KImage R _ (fun i j => IsIntegral.sum _ fun a _ =>
      IsIntegral.sum _ fun b' _ => ((hdIi i a).mul (int_sigma (σ : E →+* E) (he0i b' a))).mul (hdJi b' j)) hK2 hx⟩
  have h3 : L0 ≤ locS S (gmap (linOf b K) L0) := by
    have e4 : gmap (linOf b K) (gmap (linOf b K⁻¹) L0) = L0 := by
      rw [← gmap_comp, ← linOf_mul, mul_inv_cancel, linOf_one, gmap_one]
    calc L0 = gmap (linOf b K) (gmap (linOf b K⁻¹) L0) := e4.symm
      _ ≤ gmap (linOf b K) (locS S L0) := Submodule.map_mono h2
      _ = locS S (gmap (linOf b K) L0) := gmap_locS _ S L0
  have hKeq : locS S (gmap (linOf b K) L0) = locS S L0 := locS_eq_of S h1 h3
  have hγK : γ = g * K := by rw [hKd, mul_inv_cancel_left]
  rw [hγK, linOf_mul, gmap_comp, ← gmap_locS, hKeq, gmap_locS]

end PI.UnitaryGroupMassFormula.UJClassMass
