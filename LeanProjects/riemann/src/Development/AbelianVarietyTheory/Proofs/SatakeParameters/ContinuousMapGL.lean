import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.ContraPair
open GlobalTheory.ThetaPull (cFin pInf_conjAd pFin_conjAd conjAd_conjAd continuous_conjAd)
open scoped ContDiff

namespace GlobalTheory.BarPull

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

theorem map_map_comm (p : R →+* S) (c : R →+* R) (c' : S →+* S) (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) := by
  ext i j
  exact h _

theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R) (h : Continuous c) :
    Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))

theorem map_unip {r : ℕ} (c : R →+* R) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) := by
  ext i j
  change c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) R) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

omit [IsCMField E] in

def barL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => star (X i j)
      map_add' := fun X Y => by funext i j; simp
      map_smul' := fun t X => by funext i j; simp }

variable (E a) in

def barA : GA E a →* GA E a := GeneralLinearGroup.map (conjAd E)

theorem barA_barA (g : GA E a) : barA E a (barA E a g) = g := by
  ext i j : 2
  exact conjAd_conjAd _

theorem barA_infGL (y : GL (Fin a) (Cinf E)) :
    barA E a (infGL E a y) = infGL E a (GeneralLinearGroup.map (starRingEnd (Cinf E)) y) :=
  ga_ext (by rw [barA, map_map_comm _ _ _ pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [barA, map_map_comm _ _ _ pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

theorem barA_finGL (k : GL (Fin a) (Af E)) : barA E a (finGL E a k) = finGL E a (GeneralLinearGroup.map (cFin E) k) :=
  ga_ext (by rw [barA, map_map_comm _ _ _ pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [barA, map_map_comm _ _ _ pFin_conjAd, pFin_finGL, pFin_finGL])

theorem barA_ratGL (γ : GL (Fin a) E) :
    barA E a (ratGL E a γ) =
      ratGL E a (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom γ) :=
  (map_map_comm _ _ _ (fun x => (conjAd_algebraMap x).symm) γ).symm

theorem chart_bar (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (barA E a g)) g x = chart φ (barA E a g) (barL x) ∧ barL x ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [show barL (toL u.val) = toL (GeneralLinearGroup.map (starRingEnd (Cinf E)) u).val from rfl,
    chart_val, chart_val, map_mul, barA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem bar_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun g => φ (barA E a g)) ∈ Sm E a := fun g =>
  ((hφ (barA E a g)).comp (barL (E := E) (a := a)).contDiff.contDiffOn
    fun _ hx => (chart_bar φ g hx).2).congr fun _ hx => (chart_bar φ g hx).1

variable (E a) in

def pull : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun g => φ.1 (barA E a g), bar_mem_Sm φ.2⟩
  invFun φ := ⟨fun g => φ.1 (barA E a g), bar_mem_Sm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (barA_barA g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (barA_barA g)

theorem pull_apply (φ : Sm E a) (g : GA E a) : (pull E a φ).1 g = φ.1 (barA E a g) := rfl

theorem pull_pull (φ : Sm E a) : pull E a (pull E a φ) = φ := (pull E a).left_inv φ

theorem rt_pull (h : GA E a) (φ : Sm E a) : rt E a h (pull E a φ) = pull E a (rt E a (barA E a h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (barA E a) g h)

theorem lie_pull (X : Lie E a) (φ : Sm E a) : lie E a X (pull E a φ) = pull E a (lie E a (barL X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (pull E a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (barA E a g) ∘ barL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_bar φ.1 g hx).1
  have h1 : barL (oneL E a) = oneL E a := by
    funext i j
    change star ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have h2 := HasFDerivAt.comp (oneL E a) (f := barL)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (barA E a g)).hasFDerivAt) barL.hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, h2.fderiv]
  rfl

theorem act_pull (o : Op E a) (φ : Sm E a) : act o (pull E a φ) = pull E a (act (conjOp o) φ) := by
  cases o with
  | fin k => exact (rt_pull _ φ).trans (by rw [barA_finGL]; rfl)
  | cpt k =>
    have e : GeneralLinearGroup.map (starRingEnd (Cinf E)) (Unitary.toUnits k) = Unitary.toUnits (barK k) :=
      Units.ext rfl
    exact (rt_pull (infGL E a (Unitary.toUnits k)) φ).trans (by rw [barA_infGL, e]; rfl)
  | lie X => exact lie_pull X φ

theorem pull_act (o : Op E a) (φ : Sm E a) : pull E a (act o φ) = act (conjOp o) (pull E a φ) := by
  conv_lhs => rw [← pull_pull φ, act_pull, pull_pull]

theorem Eop_pull (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (pull E a φ) = pull E a (Eop (ComplexEmbedding.conjugate τ) i j φ) := by
  have h2 : ∀ z, lieS E a i j (atEmb τ z) (pull E a φ) =
      pull E a (lieS E a i j (atEmb (ComplexEmbedding.conjugate τ) z) φ) := fun z => by
    have e : star (atEmb τ z) = atEmb (ComplexEmbedding.conjugate τ) z := by
      classical
      rw [atEmb_conj]
      unfold atEmb
      rw [Pi.star_single]
      split_ifs <;> rfl
    have e' : barL (toL (Matrix.single i j (atEmb τ z))) = toL (Matrix.single i j (star (atEmb τ z))) := by
      funext k l
      change star (Matrix.single i j (atEmb τ z) k l) = Matrix.single i j (star (atEmb τ z)) k l
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [lieS_apply, lie_pull, e', e, lieS_apply]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, map_smul, map_sub]

theorem cap_pull (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (pull E a φ) = pull E a (cap (ComplexEmbedding.conjugate τ) u φ) := by
  have h := map_qdet ((pull E a).conjAlgEquiv ℂ).toAlgHom
    (Eop (ComplexEmbedding.conjugate τ)) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i j => ((pull E a).conjAlgEquiv ℂ).toAlgHom (Eop (ComplexEmbedding.conjugate τ) i j)) = Eop τ := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pull E a).surjective ψ
    rw [Eop_pull]
    change pull E a (Eop (ComplexEmbedding.conjugate τ) i j ((pull E a).symm (pull E a ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e] at h
  rw [cap, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) (ComplexEmbedding.conjugate τ)) (u + ((a : ℂ) - 1) / 2) = z
  change pull E a (z ((pull E a).symm (pull E a φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (pull E a φ) = pull E a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

omit [IsCMField E] in

theorem height_bar (y : GL (Fin a) (Cinf E)) :
    height (GeneralLinearGroup.map (starRingEnd (Cinf E)) y) = height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (GeneralLinearGroup.map (starRingEnd (Cinf E)) y).val‖ = ‖toL y.val‖ :=
    fun y => norm_star (toL y.val)
  unfold height
  rw [← map_inv, h1, h1]

theorem isAutForm_pull {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (pull E a φ) where
  left γ g := by rw [pull_apply, map_mul, barA_ratGL, h.left, pull_apply]
  level := by
    convert h.level.preimage (continuous_mapGL (cFin E) (continuous_conjFin _)) using 1
    ext k
    exact (Eq.congr_left (act_pull (.fin k) φ)).trans (pull E a).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (pull E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (pull E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (barA E a g)
    refine ⟨C, N, fun y => ?_⟩
    rw [pull_apply, map_mul, barA_infGL, ← height_bar]
    exact h1 _

theorem bar_mem_ratN {r : ℕ} {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) :
    (fun p => conjAd E (x p)) ∈ ratN E a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => IsCMField.complexConj E (y p), funext fun p => (conjAd_algebraMap (y p)).symm⟩

open MeasureTheory in

theorem isCuspidal_pull {φ : GA E a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (barA E a g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := fun x p => conjAd E (x p)
      invFun := fun x p => conjAd E (x p)
      left_inv := fun x => funext fun p => conjAd_conjAd _
      right_inv := fun x => funext fun p => conjAd_conjAd _
      map_add' := fun x y => funext fun p => map_add (conjAd E) _ _
      continuous_toFun := continuous_pi fun p => continuous_conjAd.comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => continuous_conjAd.comp (continuous_apply p) }
  let e : ratN E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, bar_mem_ratN y.2⟩
      invFun := fun x => ⟨β x, bar_mem_ratN x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (barA E a g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, barA, map_unip]
  rfl

def barSub (π : CuspSub E a) : CuspSub E a where
  V := π.V.map (pull E a).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨isAutForm_pull (π.cusp φ hφ).1, isCuspidal_pull (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_pull o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pull E a)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (pull E a).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (pull E a).injective h2]) fun o φ hφ => by
      change pull E a (act o φ) ∈ W
      rw [pull_act]
      exact hs _ _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := (pull E a).toLinearMap) (pull E a).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

end GlobalTheory.BarPull

end
