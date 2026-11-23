import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin r) R × GL (Fin s) R) :
    GeneralLinearGroup.map p (lev R r s g) = lev S r s (GeneralLinearGroup.map p g.1, GeneralLinearGroup.map p g.2) := by
  ext i j
  change p ((lev R r s g : Matrix _ _ R) i j) = (lev S r s _ : Matrix _ _ S) i j
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp [Matrix.fromBlocks] <;> rfl

theorem lev_infGL (y₁ : GL (Fin r) (Cinf E)) (y₂ : GL (Fin s) (Cinf E)) :
    lev (Ad E) r s (infGL E r y₁, infGL E s y₂) = infGL E (r + s) (lev (Cinf E) r s (y₁, y₂)) := by
  refine ga_ext ?_ ?_
  · rw [map_lev, pInf_infGL, pInf_infGL, pInf_infGL]
  · rw [map_lev, pFin_infGL, pFin_infGL, pFin_infGL]
    exact map_one _

theorem lev_finGL (k₁ : GL (Fin r) (Af E)) (k₂ : GL (Fin s) (Af E)) :
    lev (Ad E) r s (finGL E r k₁, finGL E s k₂) = finGL E (r + s) (lev (Af E) r s (k₁, k₂)) := by
  refine ga_ext ?_ ?_
  · rw [map_lev, pInf_finGL, pInf_finGL, pInf_finGL]
    exact map_one _
  · rw [map_lev, pFin_finGL, pFin_finGL, pFin_finGL]

theorem star_val_lev (k : Kinf E r) :
    star ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) =
      ((lev (Cinf E) r s (Unitary.toUnits (star k), 1) : GL _ _) : Matrix _ _ _) := by
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    Matrix.fromBlocks_conjTranspose]
  simp
  rfl

theorem lev_mem_unitary (k : Kinf E r) :
    ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) ∈
      Matrix.unitaryGroup (Fin (r + s)) (Cinf E) := by
  rw [Matrix.mem_unitaryGroup_iff, star_val_lev, ← Units.val_mul, ← map_mul, Prod.mk_mul_mk, ← map_mul,
    Unitary.mul_star_self, map_one, one_mul, Prod.mk_one_one, map_one, Units.val_one]

variable (E r s) in

def levK : Kinf E r →* Kinf E (r + s) where
  toFun k := ⟨_, lev_mem_unitary (s := s) k⟩
  map_one' := Subtype.ext (by
    change Units.val (lev (Cinf E) r s (Unitary.toUnits 1, 1)) = 1
    rw [map_one, Prod.mk_one_one, map_one, Units.val_one])
  map_mul' k k' := Subtype.ext (by
    change Units.val (lev (Cinf E) r s (Unitary.toUnits (k * k'), 1)) =
      Units.val (lev (Cinf E) r s (Unitary.toUnits k, 1)) * Units.val (lev (Cinf E) r s (Unitary.toUnits k', 1))
    rw [← Units.val_mul, ← map_mul, Prod.mk_mul_mk, map_mul, one_mul])

theorem toUnits_levK (k : Kinf E r) :
    Unitary.toUnits (levK E r s k) = lev (Cinf E) r s (Unitary.toUnits k, 1) := Units.ext rfl

theorem infGL_levK (k : Kinf E r) :
    infGL E (r + s) (Unitary.toUnits (levK E r s k)) = lev (Ad E) r s (infGL E r (Unitary.toUnits k), 1) := by
  rw [toUnits_levK, ← lev_infGL, map_one]

theorem continuous_levK : Continuous (levK E r s) := by
  refine Continuous.subtype_mk ?_ _
  have e : (fun k : Kinf E r => ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))) =
      fun k : Kinf E r => Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
        (Matrix.fromBlocks k.1 0 0 1) := by
    funext k
    rw [GlobalTheory.SmGL.val_emb₂]
    rfl
  change Continuous (fun k : Kinf E r => ((lev (Cinf E) r s (Unitary.toUnits k, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)))
  rw [e]
  exact (continuous_subtype_val.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _

variable (s) in

def levelOne (L : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) : Subgroup (GL (Fin r) (Af E)) :=
  L.comap ((MulAut.conj t⁻¹).toMonoidHom.comp ((lev (Af E) r s).comp (MonoidHom.inl _ _)))

theorem mem_levelOne {L : Subgroup (GL (Fin (r + s)) (Af E))} {t : GL (Fin (r + s)) (Af E)} {k : GL (Fin r) (Af E)} :
    k ∈ levelOne s L t ↔ t⁻¹ * lev (Af E) r s (k, 1) * t ∈ L := by
  simp [levelOne, MulAut.conj_apply]

theorem continuous_lev (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] : Continuous (lev R r s) :=
  (GlobalTheory.SmGL.continuous_leviEmb R _).comp (GlobalTheory.SmGL.continuous_leviTwo R)

theorem isOpen_levelOne {L : Subgroup (GL (Fin (r + s)) (Af E))} (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E))))
    (t : GL (Fin (r + s)) (Af E)) : IsOpen (levelOne s L t : Set (GL (Fin r) (Af E))) := by
  have hc : Continuous fun k : GL (Fin r) (Af E) => t⁻¹ * lev (Af E) r s (k, 1) * t :=
    (continuous_const.mul ((continuous_lev (Af E)).comp (continuous_id.prodMk continuous_const))).mul continuous_const
  convert hL.preimage hc using 1
  ext k
  exact mem_levelOne

end GlobalTheory.CompanionTheory.CTFin.Slice1
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem lev_mul_one (m₁ x : GA E r) (m₂ : GA E s) :
    lev (Ad E) r s (m₁ * x, m₂) = lev (Ad E) r s (m₁, m₂) * lev (Ad E) r s (x, 1) := by
  rw [← map_mul, Prod.mk_mul_mk, mul_one]

theorem lev_infGL_right (g : GA E r) (y : GL (Fin r) (Cinf E)) (m₂ : GA E s) (t : GL (Fin (r + s)) (Af E))
    (c : GL (Fin (r + s)) (Cinf E)) :
    lev (Ad E) r s (g * infGL E r y, m₂) * finGL E (r + s) t * infGL E (r + s) c =
      lev (Ad E) r s (g, m₂) * finGL E (r + s) t * infGL E (r + s) (lev (Cinf E) r s (y, 1) * c) := by
  have e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1)) := by
    rw [← lev_infGL, map_one]
  rw [lev_mul_one, e1, map_mul (infGL E (r + s)), mul_assoc (lev (Ad E) r s (g, m₂)) (infGL E (r + s) _),
    infGL_comm]
  simp only [mul_assoc]

theorem lev_finGL_right (m : GA E r) (k : GL (Fin r) (Af E)) (m₂ : GA E s) (t : GL (Fin (r + s)) (Af E))
    (c : GL (Fin (r + s)) (Cinf E)) :
    lev (Ad E) r s (m * finGL E r k, m₂) * finGL E (r + s) t * infGL E (r + s) c =
      lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) c *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t) := by
  have e1 : lev (Ad E) r s (finGL E r k, 1) = finGL E (r + s) (lev (Af E) r s (k, 1)) := by
    rw [← lev_finGL, map_one]
  have hY : finGL E (r + s) (lev (Af E) r s (k, 1)) * finGL E (r + s) t =
      finGL E (r + s) t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [lev_mul_one, e1, mul_assoc (lev (Ad E) r s (m, m₂)), hY, mul_assoc _ (infGL E (r + s) c), infGL_comm]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem commute_rt_of_mem_Zalg {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (h : GA E a) :
    Commute z (rt E a h) := by
  have hc : ∀ τ u, Commute (cap (a := a) τ u) (rt E a h) := fun τ u => by
    rw [← infGL_mul_finGL h, map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _).mul_right (commute_cap_finRep τ u _)
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact hc τ u
  | algebraMap c => exact Algebra.commute_algebraMap_left c _
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

theorem zfin_of_cofin {J : Set (Module.End ℂ (Sm E a))} (hJ : Cofin J) {φ : Sm E a} (h : ∀ z ∈ J, z φ = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  obtain ⟨-, V, hV, hz⟩ := hJ
  let ev : Module.End ℂ (Sm E a) →ₗ[ℂ] Sm E a := LinearMap.applyₗ φ
  have hev : ∀ z, ev z = z φ := fun _ => rfl
  have hw0 : ∀ w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, ev w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, -, j, hj, rfl⟩ := hy
        rw [hev, Module.End.mul_apply, h j hj, map_zero]
      | zero => exact map_zero ev
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hle : Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ≤ V.map ev := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz', rfl⟩
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.1 (hz z hz')
    refine ⟨v, hv, ?_⟩
    change ev v = ev z
    rw [← hvw, map_add, hw0 w hw, add_zero]
  haveI := hV
  exact Submodule.finiteDimensional_of_le hle

theorem fd_span_of_forall_mem {K X : Type} (C : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ C] (f : K → X → ℂ)
    (hf : ∀ x, (fun k => f k x) ∈ C) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := by
  let b := Module.finBasis ℂ C
  let A : Fin (Module.finrank ℂ C) → X → ℂ := fun i x => b.repr ⟨_, hf x⟩ i
  have hA : ∀ k, f k = ∑ i, (b i : K → ℂ) k • A i := by
    intro k
    funext x
    have e := congrArg (fun c : C => (c : K → ℂ) k) (b.sum_repr ⟨_, hf x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, A]
    rw [← e]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hle : Submodule.span ℂ (Set.range f) ≤ Submodule.span ℂ (Set.range A) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [hA k]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range A)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range A)
  exact Submodule.finiteDimensional_of_le hle

theorem kfin_of_coeff {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (φ : Sm E a) (h : ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := by
  haveI := GlobalTheory.CompanionTheory.CTFin.UniSol.finiteDimensional_coeffSpan ρ
  haveI := fd_span_of_forall_mem _ (fun k => (cptRep E a k φ).1) h
  let S := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  have e : S.map (Sm E a).subtype = Submodule.span ℂ (Set.range fun k => (cptRep E a k φ).1) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  haveI : FiniteDimensional ℂ (S.map (Sm E a).subtype) := by rw [e]; infer_instance
  exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) S).symm.finiteDimensional

theorem coeff_comp {K K' W : Type} [Group K] [Group K'] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K' W)
    (f : K →* K') (κ : K') {c : K' → ℂ} (hc : c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (fun k => c (f k * κ)) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp f) := by
  let T : (K' → ℂ) →ₗ[ℂ] (K → ℂ) := LinearMap.funLeft ℂ ℂ (fun k => f k * κ)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp f)).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ κ w, funext fun k => ?_⟩
    simp [T, LinearMap.funLeft, map_mul, Module.End.mul_apply]
  exact hle hc

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
