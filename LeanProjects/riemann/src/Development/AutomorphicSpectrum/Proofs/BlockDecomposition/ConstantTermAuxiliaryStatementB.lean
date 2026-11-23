import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CTFin.Slice2

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin r) R × GL (Fin s) R) :
    Matrix.GeneralLinearGroup.map f (lev R r s g) =
      lev S r s (Matrix.GeneralLinearGroup.map f g.1, Matrix.GeneralLinearGroup.map f g.2) := by
  apply Units.ext
  change (lev R r s g).val.map f = (lev S r s _).val
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp <;> rfl

theorem lev_infGL (a : GL (Fin r) (Cinf E)) (b : GL (Fin s) (Cinf E)) :
    lev (Ad E) r s (infGL E r a, infGL E s b) = infGL E (r + s) (lev (Cinf E) r s (a, b)) := by
  refine ga_ext ?_ ?_
  · rw [map_lev, pInf_infGL, pInf_infGL, pInf_infGL]
  · rw [map_lev, pFin_infGL, pFin_infGL, pFin_infGL]
    exact map_one _

theorem lev_finGL (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) :
    lev (Ad E) r s (finGL E r a, finGL E s b) = finGL E (r + s) (lev (Af E) r s (a, b)) := by
  refine ga_ext ?_ ?_
  · rw [map_lev, pInf_finGL, pInf_finGL, pInf_finGL]
    exact map_one _
  · rw [map_lev, pFin_finGL, pFin_finGL, pFin_finGL]

theorem lev_split (R : Type) [CommRing R] (a : GL (Fin r) R) (b : GL (Fin s) R) :
    lev R r s (a, b) = lev R r s (1, b) * lev R r s (a, 1) := by
  rw [← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem lev_mul_right (R : Type) [CommRing R] (a : GL (Fin r) R) (b c : GL (Fin s) R) :
    lev R r s (a, b * c) = lev R r s (a, b) * lev R r s (1, c) := by
  rw [← map_mul, Prod.mk_mul_mk, mul_one]

theorem star_lev (k : Kinf E s) :
    star (lev (Cinf E) r s (1, Unitary.toUnits k)).val = (lev (Cinf E) r s (1, (Unitary.toUnits k)⁻¹)).val := by
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  have e : ((Unitary.toUnits k)⁻¹).val = star (Unitary.toUnits k).val := rfl
  ext i j
  simp only [Matrix.star_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp [e, Matrix.one_apply, eq_comm] <;> split_ifs <;> simp

variable (E r s) in

def levK : Kinf E s →* Kinf E (r + s) where
  toFun k := ⟨(lev (Cinf E) r s (1, Unitary.toUnits k)).val, by
    refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [star_lev, ← Units.val_mul, ← map_mul, Prod.mk_mul_mk]
    simp
    exact map_one (lev (Cinf E) r s)⟩
  map_one' := Subtype.ext (by simp; exact map_one (lev (Cinf E) r s))
  map_mul' k l := Subtype.ext (by
    change (lev (Cinf E) r s (1, Unitary.toUnits (k * l))).val = (lev (Cinf E) r s (1, Unitary.toUnits k)).val * (lev (Cinf E) r s (1, Unitary.toUnits l)).val
    rw [← Units.val_mul, ← map_mul, Prod.mk_mul_mk, map_mul, one_mul])

theorem toUnits_levK (k : Kinf E s) : Unitary.toUnits (levK E r s k) = lev (Cinf E) r s (1, Unitary.toUnits k) :=
  Units.ext rfl

theorem continuous_levK : Continuous (levK E r s) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [GlobalTheory.SmGL.val_emb₂, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · change Continuous fun k : Kinf E s => k.val a b
    exact (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)

def lev2 (R : Type) [CommRing R] (r s : ℕ) : GL (Fin s) R →* GL (Fin (r + s)) R :=
  (lev R r s).comp (MonoidHom.inr _ _)

theorem continuous_lev2 : Continuous (lev2 (Af E) r s) := by
  exact ((GlobalTheory.SmGL.continuous_leviEmb (Af E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))).comp
    (GlobalTheory.SmGL.continuous_leviTwo (Af E))).comp (continuous_const.prodMk continuous_id)

theorem lev_infGL_one (y : GL (Fin s) (Cinf E)) :
    lev (Ad E) r s (1, infGL E s y) = infGL E (r + s) (lev (Cinf E) r s (1, y)) := by
  rw [← lev_infGL, map_one]

theorem lev_finGL_one (k : GL (Fin s) (Af E)) :
    lev (Ad E) r s (1, finGL E s k) = finGL E (r + s) (lev (Af E) r s (1, k)) := by
  rw [← lev_finGL, map_one]

def blkL (x : Lie E s) : Lie E (r + s) :=
  toL (Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (Matrix.fromBlocks 1 0 0 (Matrix.of x)))

theorem contDiff_blkL : ContDiff ℝ ∞ (blkL (E := E) (r := r) (s := s)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [blkL, Matrix.reindex_apply, Matrix.submatrix_apply]
  change ContDiff ℝ ∞ fun x : Lie E s => Matrix.fromBlocks 1 0 0 (Matrix.of x)
    ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j)
  rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const
  · exact (contDiff_apply ℝ _ b).comp (contDiff_apply ℝ _ a)

theorem blkL_val (y : GL (Fin s) (Cinf E)) : blkL (r := r) (toL y.val) = toL (lev (Cinf E) r s (1, y)).val := by
  simp only [blkL]
  rw [GlobalTheory.SmGL.val_emb₂]
  rfl

theorem res_mem_Sm (F : Sm E (r + s)) : (fun m : GA E s => F.1 (lev (Ad E) r s (1, m))) ∈ Sm E s := by
  intro g
  refine ((F.2 (lev (Ad E) r s (1, g))).comp contDiff_blkL.contDiffOn ?_).congr ?_
  · intro x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    rw [blkL_val]
    exact val_mem_invSet _
  · intro x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    rw [chart_val, Function.comp_apply, blkL_val, chart_val, lev_mul_right, ← lev_infGL_one]

theorem Zalg_comm_rt {a : ℕ} (h : GA E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) : Commute z (rt E a h) := by
  have hle : Zalg E a ≤ Subalgebra.centralizer ℂ {rt E a h} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro y hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    rw [← infGL_mul_finGL h, map_mul]
    exact ((GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _).mul_right (commute_cap_finRep τ u _)).symm.eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hle hz) _ rfl |>.symm

theorem exists_interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (S : Finset K) (lam : K → S → ℂ), ∀ c ∈ A, ∀ k, c k = ∑ κ : S, lam k κ * c κ.1 := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.CTFin.UniSol.exists_finset_separating A
  let ev : A →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun κ => (LinearMap.proj κ.1 : (K → ℂ) →ₗ[ℂ] ℂ) ∘ₗ A.subtype
  have hinj : LinearMap.ker ev = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun c hc => Subtype.ext (hS c.1 c.2 fun κ hκ => ?_)
    exact congrFun hc ⟨κ, hκ⟩
  obtain ⟨P, hP⟩ := ev.exists_leftInverse_of_injective hinj
  refine ⟨S, fun k κ => (P (Pi.single κ 1)).1 k, fun c hc k => ?_⟩
  have h1 : P (ev ⟨c, hc⟩) = ⟨c, hc⟩ := LinearMap.congr_fun hP _
  have h2 : ev ⟨c, hc⟩ = ∑ κ : S, c κ.1 • (Pi.single κ 1 : S → ℂ) := by
    funext κ'
    simp [Finset.sum_apply, Pi.single_apply, ev]
  have h3 := congrArg (fun x : A => x.1 k) h1
  simp only [h2, map_sum, map_smul] at h3
  rw [← h3]
  simp [mul_comm]

theorem kfin_of_coeff {a : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (φ : Sm E a)
    (h : ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := by
  classical
  haveI := GlobalTheory.CompanionTheory.CTFin.UniSol.finiteDimensional_coeffSpan ρ
  obtain ⟨S, lam, key⟩ := exists_interp (GlobalTheory.Published.AutFin.coeffSpan ρ)
  have hle : Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ≤
      Submodule.span ℂ ((fun κ : Kinf E a => cptRep E a κ φ) '' (S : Set (Kinf E a))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    have e : cptRep E a k φ = ∑ κ : S, lam k κ • cptRep E a κ.1 φ := by
      refine Subtype.ext (funext fun g => ?_)
      have h1 := key _ (h g) k
      rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      exact h1
    beta_reduce
    rw [e]
    exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ.1, κ.2, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ((fun κ : Kinf E a => cptRep E a κ φ) '' (S : Set (Kinf E a)))) :=
    FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image _)
  exact Submodule.finiteDimensional_of_le hle

theorem zfin_of_cofin {a : ℕ} {J : Set (Module.End ℂ (Sm E a))} (hJ : Cofin J) (φ : Sm E a) (h : ∀ z ∈ J, z φ = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  obtain ⟨-, V, hV, hz⟩ := hJ
  let ev : Module.End ℂ (Sm E a) →ₗ[ℂ] Sm E a := LinearMap.applyₗ φ
  have hker : Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j} ≤ LinearMap.ker ev := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, -, j, hj, rfl⟩
    change x (j φ) = 0
    rw [h j hj, map_zero]
  refine Submodule.finiteDimensional_of_le (S₂ := V.map ev) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hzZ, rfl⟩
  obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.1 (hz z hzZ)
  refine ⟨v, hv, ?_⟩
  have : y φ = 0 := hker hy
  change v φ = v φ + y φ
  rw [this, add_zero]

theorem norm_toL_lev (y : GL (Fin s) (Cinf E)) :
    ‖toL (lev (Cinf E) r s (1, y)).val‖ ≤ 1 + ‖toL y.val‖ := by
  have n0 := norm_nonneg (toL y.val)
  have h1 : ‖(1 : Cinf E)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(lev (Cinf E) r s (1, y)).val i j‖ ≤ _
  rw [GlobalTheory.SmGL.val_emb₂]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b
  · simp only [Matrix.fromBlocks_apply₁₁, Units.val_one, Matrix.one_apply]
    split_ifs
    · linarith
    · simp only [norm_zero]; linarith
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]; linarith
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]; linarith
  · simp only [Matrix.fromBlocks_apply₂₂]
    have := (norm_le_pi_norm (toL y.val a) b).trans (norm_le_pi_norm (toL y.val) a)
    refine le_trans this ?_
    linarith

theorem height_lev_le (y : GL (Fin s) (Cinf E)) : height (lev (Cinf E) r s (1, y)) ≤ 3 * height y := by
  have e : (lev (Cinf E) r s (1, y))⁻¹ = lev (Cinf E) r s (1, y⁻¹) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_toL_lev (r := r) y
  have h2 := norm_toL_lev (r := r) y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

def bnd {a : ℕ} (c : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖

theorem height_mul_le {a : ℕ} (c y : GL (Fin a) (Cinf E)) : height (y * c) ≤ bnd c * height y := by
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height bnd
  rw [h1, h2]
  nlinarith

theorem coeff_comp {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W)
    (κ : Kinf E (r + s)) {c : Kinf E (r + s) → ℂ} (hc : c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    (fun k => c (levK E r s k * κ)) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s)) := by
  let T : (Kinf E (r + s) → ℂ) →ₗ[ℂ] (Kinf E s → ℂ) := LinearMap.funLeft ℂ ℂ (fun k => levK E r s k * κ)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s))).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    refine Submodule.subset_span ⟨ℓ, ρ κ w, funext fun k => ?_⟩
    change ℓ (ρ (levK E r s k * κ) w) = ℓ (ρ (levK E r s k) (ρ κ w))
    rw [map_mul, Module.End.mul_apply]
  exact hle hc

def hh (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) : GA E (r + s) :=
  lev (Ad E) r s (m₁, 1) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)

def sl (F : Sm E (r + s)) (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) : Sm E s :=
  ⟨fun m => (rt E (r + s) (hh m₁ t κ) F).1 (lev (Ad E) r s (1, m)), res_mem_Sm _⟩

theorem sl_apply (F : Sm E (r + s)) (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (m : GA E s) :
    (sl F m₁ t κ).1 m = F.1 (lev (Ad E) r s (m₁, m) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  change F.1 (lev (Ad E) r s (1, m) * hh m₁ t κ) = _
  rw [lev_split (Ad E) m₁ m, hh]
  simp only [mul_assoc]

theorem sl_inf (F : Sm E (r + s)) (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (g : GA E s)
    (y : GL (Fin s) (Cinf E)) :
    (sl F m₁ t κ).1 (g * infGL E s y) = F.1 (lev (Ad E) r s (m₁, g) * finGL E (r + s) t *
      infGL E (r + s) (lev (Cinf E) r s (1, y) * Unitary.toUnits κ)) := by
  rw [sl_apply, lev_mul_right, lev_infGL_one, map_mul, mul_assoc (lev (Ad E) r s (m₁, g)), infGL_comm]
  simp only [mul_assoc]

theorem sl_left (F : Sm E (r + s))
    (a2 : ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)),
      F.1 (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g) = F.1 g)
    (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (γ : GL (Fin s) E) (g : GA E s) :
    (sl F m₁ t κ).1 (ratGL E s γ * g) = (sl F m₁ t κ).1 g := by
  rw [sl_apply, sl_apply]
  have e : lev (Ad E) r s (m₁, ratGL E s γ * g) =
      lev (Ad E) r s (ratGL E r 1, ratGL E s γ) * lev (Ad E) r s (m₁, g) := by
    rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul]
  rw [e]
  simp only [mul_assoc]
  exact a2 (1, γ) _

variable (r) in

def L₂ (L : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) : Subgroup (GL (Fin s) (Af E)) :=
  L.comap ((MulAut.conj t⁻¹).toMonoidHom.comp (lev2 (Af E) r s))

theorem isOpen_L₂ {L : Subgroup (GL (Fin (r + s)) (Af E))} (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E))))
    (t : GL (Fin (r + s)) (Af E)) : IsOpen (L₂ r L t : Set (GL (Fin s) (Af E))) := by
  have hc : Continuous fun k : GL (Fin s) (Af E) => t⁻¹ * lev2 (Af E) r s k * t⁻¹⁻¹ :=
    (continuous_const.mul continuous_lev2).mul continuous_const
  exact hL.preimage hc

theorem sl_level (F : Sm E (r + s)) {L : Subgroup (GL (Fin (r + s)) (Af E))}
    (a3 : ∀ k ∈ L, finRep E (r + s) k F = F) (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s))
    (k : GL (Fin s) (Af E)) (hk : k ∈ L₂ r L t) : finRep E s k (sl F m₁ t κ) = sl F m₁ t κ := by
  refine Subtype.ext (funext fun g => ?_)
  change (sl F m₁ t κ).1 (g * finGL E s k) = _
  rw [sl_apply, sl_apply]
  set ℓ := t⁻¹ * lev2 (Af E) r s k * t with hℓ
  have hmem : ℓ ∈ L := by
    have : t⁻¹ * lev2 (Af E) r s k * t⁻¹⁻¹ ∈ L := hk
    rwa [inv_inv] at this
  have h := congrFun (congrArg Subtype.val (a3 ℓ hmem))
    (lev (Ad E) r s (m₁, g) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))
  change F.1 (_ * finGL E (r + s) ℓ) = _ at h
  have e0 : t * ℓ = lev (Af E) r s (1, k) * t := by
    rw [hℓ]
    change t * (t⁻¹ * lev (Af E) r s (1, k) * t) = _
    group
  have e1 : finGL E (r + s) t * finGL E (r + s) ℓ = finGL E (r + s) (lev (Af E) r s (1, k)) * finGL E (r + s) t := by
    rw [← map_mul, ← map_mul, e0]
  have e2 : lev (Ad E) r s (m₁, g) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) * finGL E (r + s) ℓ =
      lev (Ad E) r s (m₁, g) * (finGL E (r + s) t * finGL E (r + s) ℓ) * infGL E (r + s) (Unitary.toUnits κ) := by
    rw [mul_assoc _ (infGL E (r + s) _), infGL_comm]
    simp only [mul_assoc]
  rw [← h, e2, e1, lev_mul_right, lev_finGL_one]
  simp only [mul_assoc]

theorem sl_coeff {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W) (F : Sm E (r + s))
    (a4 : ∀ g : GA E (r + s), (fun k : Kinf E (r + s) => (cptRep E (r + s) k F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ)
    (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (g : GA E s) :
    (fun k : Kinf E s => (cptRep E s k (sl F m₁ t κ)).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s)) := by
  convert coeff_comp ρ κ (a4 (lev (Ad E) r s (m₁, g) * finGL E (r + s) t)) using 1
  funext k
  change (sl F m₁ t κ).1 (g * infGL E s (Unitary.toUnits k)) =
    F.1 (lev (Ad E) r s (m₁, g) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits (levK E r s k * κ)))
  have e : Unitary.toUnits (levK E r s k * κ) = lev (Cinf E) r s (1, Unitary.toUnits k) * Unitary.toUnits κ := by
    rw [map_mul, toUnits_levK]
  rw [sl_inf, e]

theorem sl_growth (F : Sm E (r + s))
    (a5 : ∀ g : GA E (r + s), ∃ (C : ℝ) (N : ℕ), ∀ y, ‖F.1 (g * infGL E (r + s) y)‖ ≤ C * height y ^ N)
    (m₁ : GA E r) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (g : GA E s) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(sl F m₁ t κ).1 (g * infGL E s y)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, h⟩ := a5 (lev (Ad E) r s (m₁, g) * finGL E (r + s) t)
  set c := bnd (Unitary.toUnits κ) with hc
  have c0 : 0 ≤ c := by
    rw [hc, bnd]; positivity
  refine ⟨|C| * (c * 3) ^ N, N, fun y => ?_⟩
  rw [sl_inf]
  have hy0 : 0 ≤ height y := zero_le_one.trans (one_le_height y)
  have h0 : 0 ≤ height (lev (Cinf E) r s (1, y) * Unitary.toUnits κ) := zero_le_one.trans (one_le_height _)
  have h1 : height (lev (Cinf E) r s (1, y) * Unitary.toUnits κ) ≤ c * 3 * height y := by
    refine (height_mul_le _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (height_lev_le y) c0
  refine (h _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)).trans ?_)
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 N) (abs_nonneg C)

theorem slice2 : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ)
    (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J →
    ∀ J₂ : Set (Module.End ℂ (Sm E s)), Cofin J₂ →
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      (∀ z ∈ J, z F = 0) → ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) →
    ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)),
    ∃ (L₂ : Subgroup (GL (Fin s) (Af E))) (ρ₂ : Representation ℂ (Kinf E s) W),
      IsOpen (L₂ : Set (GL (Fin s) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₂ ∧
      ∀ F ∈ goodCT L ρ J, ∀ m₁ : GA E r, ∃ G ∈ genSpace L₂ ρ₂ J₂, ∀ m₂ : GA E s,
        G.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  intro E _ _ _ r s L hL W _ _ _ ρ hρ J hJ J₂ hJ₂ H t κ
  refine ⟨L₂ r L t, ρ.comp (levK E r s), isOpen_L₂ hL t, fun ℓ w => (hρ ℓ w).comp continuous_levK, ?_⟩
  rintro F ⟨a1, a2, a3, a4, a5, a6⟩ m₁
  have hlev := sl_level F a3 m₁ t κ
  have hco := sl_coeff ρ F a4 m₁ t κ
  have hkill : ∀ z ∈ J₂, z (sl F m₁ t κ) = 0 := by
    refine H (rt E (r + s) (hh m₁ t κ) F) (fun x g => ?_) (fun z hz => ?_) _ (fun m => rfl)
    · simp only [rt_apply, mul_assoc]
      exact a1 x _
    · have h := LinearMap.congr_fun (Zalg_comm_rt (hh m₁ t κ) (hJ.1 hz)).eq F
      rw [Module.End.mul_apply, Module.End.mul_apply, a6 z hz, map_zero] at h
      exact h
  refine ⟨sl F m₁ t κ, ⟨⟨fun γ g => sl_left F a2 m₁ t κ γ g, ?_, kfin_of_coeff _ _ hco,
    zfin_of_cofin hJ₂ _ hkill, sl_growth F a5 m₁ t κ⟩, hlev, hco, hkill⟩, sl_apply F m₁ t κ⟩
  exact isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((isOpen_L₂ hL t).mem_nhds (one_mem _)) hlev)

end GlobalTheory.CompanionTheory.CTFin.Slice2

end
