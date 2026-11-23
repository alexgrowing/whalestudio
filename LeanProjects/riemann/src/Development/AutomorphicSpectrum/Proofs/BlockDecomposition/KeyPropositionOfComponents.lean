import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep

noncomputable section

open Finset MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.KeyAsm

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Abstract

theorem starProjection_comm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (U U' : H →L[ℂ] H) (hU : ∀ v, ‖U v‖ = ‖v‖)
    (hUU' : ∀ v, U (U' v) = v) (hS : ∀ v ∈ S, U v ∈ S) (hS' : ∀ v ∈ S, U' v ∈ S) (x : H) :
    S.starProjection (U x) = U (S.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hS _ (Submodule.starProjection_apply_mem S x)) fun w hw => ?_
  let I : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, hU⟩
  have e : inner ℂ (U x - U (S.starProjection x)) (U (U' w)) =
      inner ℂ (x - S.starProjection x) (U' w) := by
    rw [← map_sub]
    exact I.inner_map_map _ _
  rw [hUU'] at e
  rw [e]
  exact Submodule.starProjection_inner_eq_zero _ _ (hS' w hw)

theorem exists_surjective {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    {A : ℕ → Type*} [∀ m, AddCommGroup (A m)] [∀ m, Module ℂ (A m)] (f : ∀ m, A m →ₗ[ℂ] S)
    (hall : ∀ y, ∃ (m : ℕ) (a : A m), f m a = y)
    (hmono : ∀ m m', m ≤ m' → ∀ a : A m, ∃ a' : A m', f m' a' = f m a) :
    ∃ m, Function.Surjective (f m) := by
  let b := Module.finBasis ℂ S
  choose M a ha using fun i => hall (b i)
  refine ⟨Finset.univ.sup M, ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨a', h⟩ := hmono _ _ (Finset.le_sup (Finset.mem_univ i)) (a i)
  exact ⟨a', h.trans (ha i)⟩

end Abstract

section Hol

theorem continuous_lead (i : ℕ) : Continuous (lead i : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [dif_pos h]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · simp only [dif_neg h]
    exact continuous_const

theorem isOpen_OmegaSet (n : ℕ) : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_lead _) continuous_const

theorem differentiableAt_of_mem_OmF {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : DifferentiableAt ℂ F z :=
  (hF.1.differentiableOn (by simp)).differentiableAt ((isOpen_OmegaSet n).mem_nhds hz)

theorem lop_add (Y : Matrix (Fin n) (Fin n) ℂ) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n)
    (hG : G ∈ OmF n) : lop Y (F + G) = lop Y F + lop Y G := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, if_pos hz, Pi.add_apply]
    have e : fderiv ℂ (F + G) z = fderiv ℂ F z + fderiv ℂ G z :=
      ((differentiableAt_of_mem_OmF hF hz).hasFDerivAt.add
        (differentiableAt_of_mem_OmF hG hz).hasFDerivAt).fderiv
    rw [e]
    simp only [ContinuousLinearMap.add_apply]
    ring
  · simp [lop, if_neg hz]

theorem lop_smul (Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : F ∈ OmF n) :
    lop Y (c • F) = c • lop Y F := by
  funext z
  by_cases hz : z ∈ OmegaSet n
  · simp only [lop, if_pos hz, Pi.smul_apply]
    have e : fderiv ℂ (c • F) z = c • fderiv ℂ F z :=
      ((differentiableAt_of_mem_OmF hF hz).hasFDerivAt.const_smul c).fderiv
    rw [e]
    simp
  · simp [lop, if_neg hz]

def lopL (h1 : ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ), F ∈ OmF n → lop Y F ∈ OmF n)
    (Y : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (OmF n) where
  toFun F := ⟨lop Y F, h1 Y F F.2⟩
  map_add' F G := Subtype.ext (lop_add Y F.2 G.2)
  map_smul' c F := Subtype.ext (lop_smul Y c F.2)

theorem lword_coe (h1 : ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ), F ∈ OmF n → lop Y F ∈ OmF n)
    (Φ : OmF n) : ∀ w : List (Fin n × Fin n),
      ((lword (fun a b => lopL h1 (Matrix.single a b 1)) w Φ : OmF n) : Matrix (Fin n) (Fin n) ℂ → ℂ) =
        lw w (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ)
  | [] => rfl
  | p :: w => by
      show lop (Matrix.single p.1 p.2 1) _ = lop (Matrix.single p.1 p.2 1) _
      rw [lword_coe h1 Φ w]

theorem lowAlg_model (hL : LowAlg) (hH : HolFacts) (μ : Fin n → ℤ) (η : Fin n → ℝ)
    {B : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hB : B ∈ Submodule.span ℂ (Set.range fun w : List (Fin n × Fin n) => lw w (PhiO μ)))
    (hw : ∀ c, lop (Matrix.single c c 1) B = (η c : ℂ) • B) (h0 : B ≠ 0) :
    InCone (fun a => ((μ a : ℤ) : ℝ)) η ∧ (η = (fun a => ((μ a : ℤ) : ℝ)) → ∃ c : ℂ, B = c • PhiO μ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH n μ
  let L : Fin n → Fin n → Module.End ℂ (OmF n) := fun a b => lopL h1 (Matrix.single a b 1)
  let Φ : OmF n := ⟨PhiO μ, h3⟩
  have hmap : Submodule.span ℂ (Set.range fun w : List (Fin n × Fin n) => lw w (PhiO μ)) =
      (Submodule.span ℂ (Set.range fun w : List (Fin n × Fin n) => lword L w Φ)).map (OmF n).subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext w
    exact (lword_coe h1 Φ w).symm
  rw [hmap] at hB
  obtain ⟨x, hx, rfl⟩ := hB
  have hGl : IsGlRep L := by
    intro a b c d
    refine LinearMap.ext fun F => Subtype.ext ?_
    have h := h2 F a b c d F.2
    by_cases hbc : b = c <;> by_cases hda : d = a
    · simp only [if_pos hbc, if_pos hda] at h ⊢
      exact h
    · simp only [if_pos hbc, if_neg hda] at h ⊢
      exact h
    · simp only [if_neg hbc, if_pos hda] at h ⊢
      exact h
    · simp only [if_neg hbc, if_neg hda] at h ⊢
      exact h
  have hd : ∀ a, L a a Φ = (((μ a : ℤ) : ℝ) : ℂ) • Φ := by
    intro a
    refine Subtype.ext ?_
    have := h4 a
    simpa [L, Φ, lopL] using this
  have hl : ∀ a b, b < a → L a b Φ = 0 := fun a b hab => Subtype.ext (h5 a b hab)
  have hx0 : x ≠ 0 := fun h => h0 (by simp [h])
  have hwx : ∀ c, L c c x = (η c : ℂ) • x := fun c => Subtype.ext (hw c)
  obtain ⟨r1, r2⟩ := hL n (OmF n) L (fun a => ((μ a : ℤ) : ℝ)) η Φ x hGl hd hl hx hwx hx0
  refine ⟨r1, fun he => ?_⟩
  obtain ⟨c, hc⟩ := r2 he
  exact ⟨c, congrArg Subtype.val hc⟩

end Hol

section Act

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem actF_add_smul (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a a' : AS T m) (c : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    actF T Ψ (a + c • a') g = actF T Ψ a g + c * actF T Ψ a' g := by
  simp only [actF, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : (fun g => inner ℂ T.w (Ψ g ((a + c • a') x))) =
      fun g => jfun Ψ T.w (a x) g + c * jfun Ψ T.w (a' x) g := by
    funext g
    simp [jfun, inner_add_right, inner_smul_right]
  rw [e]
  exact icx_eword_add_smul (datumFunction_isSmoothL2 hP T.w (a x)).1 (datumFunction_isSmoothL2 hP T.w (a' x)).1 c _ g hg

theorem actF_zero {m : ℕ} : actF T Ψ (0 : AS T m) = 0 := by
  funext g
  simp only [actF, Finset.sum_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  have e : (fun g => inner ℂ T.w (Ψ g ((0 : AS T m) x))) = fun _ => (0 : ℂ) := by
    funext g
    simp
  rw [e, icx_eword_zero]

theorem actF_memLp (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) :
    MemLp (fun g : Formalism.REAL.UJ ε => actF T Ψ a (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  simp only [actF, Finset.sum_apply]
  exact memLp_finsetSum _ fun x _ => (datumFunction_isSmoothL2 hP T.w (a x)).2 (ofW x)

def actLin (hP : IsPsiFor ε lam T Ψ) (m : ℕ) : AS T m →ₗ[ℂ] L2 ε where
  toFun := actL T Ψ
  map_add' a a' := by
    have e : toL2 ε (actF T Ψ (a + a')) = toL2 ε (actF T Ψ a + actF T Ψ a') :=
      toL2_congr_of_forall_inUJ_eq fun g hg => by
        have h := actF_add_smul hP a a' 1 hg
        simpa using h
    exact e.trans (toL2_add_smooth ε (actF_memLp hP a) (actF_memLp hP a'))
  map_smul' c a := by
    have e : toL2 ε (actF T Ψ (c • a)) = toL2 ε (c • actF T Ψ a) :=
      toL2_congr_of_forall_inUJ_eq fun g hg => by
        have h := actF_add_smul hP 0 a c hg
        simpa [actF_zero] using h
    exact e.trans (toL2_smul_smooth ε c _)

def betaLin {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (m : ℕ) :
    AS T m →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  toFun := betaF T μ
  map_add' a a' := by
    simp only [betaF, Pi.add_apply, inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp [betaF, inner_smul_right, Finset.smul_sum, mul_smul]

end Act

section Sub

variable {ε : Fin n → Bool}

theorem toMK_mem (k : KG ε) : toMK k ∈ UJset ε := k.1.2

theorem continuous_toMK : Continuous (fun k : KG ε => toMK k) :=
  (continuous_toM ε).comp continuous_subtype_val

theorem rreg_toMK_mul (k k' : KG ε) :
    rreg ε (toMK (k * k')) = (rreg ε (toMK k)).comp (rreg ε (toMK k')) :=
  (rreg_isURepOn ε).1.2 _ (toMK_mem k) _ (toMK_mem k')

theorem rreg_toMK_one : rreg ε (toMK (1 : KG ε)) = 1 := (rreg_isURepOn ε).1.1

theorem rreg_toMK_inv (k : KG ε) (v : L2 ε) : rreg ε (toMK k) (rreg ε (toMK k⁻¹) v) = v := by
  have h := rreg_toMK_mul k k⁻¹
  rw [mul_inv_cancel, rreg_toMK_one] at h
  exact (DFunLike.congr_fun h v).symm

def sigS (S : Submodule ℂ (L2 ε)) (hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S) (k : KG ε) : S →L[ℂ] S :=
  ((rreg ε (toMK k)).comp S.subtypeL).codRestrict S fun x => hK _ k.2 x x.2

variable {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem exists_section (hSec : EquivSection) (hRho : RhoRep) (hAct : ActEquiv) (hEx : Exhaust)
    (hP : IsPsiFor ε lam T Ψ) (S : Submodule ℂ (L2 ε)) [FiniteDimensional ℂ S] [S.HasOrthogonalProjection]
    (hle : S ≤ Hlam ε Ψ T.w) (hK : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S) :
    ∃ (m : ℕ) (s : S →ₗ[ℂ] AS T m), (∀ y, S.orthogonalProjectionOnto (actL T Ψ (s y)) = y) ∧
      ∀ k y, s (sigS S hK k y) = rhoA T m k (s y) := by
  let f : ∀ m, AS T m →ₗ[ℂ] S := fun m => S.orthogonalProjectionOnto.toLinearMap ∘ₗ actLin hP m
  obtain ⟨h1, h2, -⟩ := hEx n ε lam T Ψ hP
  have hall : ∀ y : S, ∃ (m : ℕ) (a : AS T m), f m a = y := by
    intro y
    have hy : (y : L2 ε) ∈ Hlam ε Ψ T.w := hle y.2
    let Gs : Submodule ℂ (L2 ε) :=
      (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)).map (smD ε (rreg ε)).subtype
    let R : Submodule ℂ S := Gs.map S.orthogonalProjectionOnto.toLinearMap
    have hRc : IsClosed (R : Set S) := Submodule.closed_of_finiteDimensional R
    have hy' : (y : L2 ε) ∈ closure (Gs : Set (L2 ε)) := hy
    have hm : S.orthogonalProjectionOnto (y : L2 ε) ∈ closure (R : Set S) :=
      map_mem_closure S.orthogonalProjectionOnto.continuous hy' fun x hx => ⟨x, hx, rfl⟩
    rw [hRc.closure_eq, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at hm
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hm
    obtain ⟨m, a, ha⟩ := h1 x hx
    refine ⟨m, a, ?_⟩
    rw [← hxy]
    exact congrArg S.orthogonalProjectionOnto ha.symm
  have hmono : ∀ m m', m ≤ m' → ∀ a : AS T m, ∃ a' : AS T m', f m' a' = f m a := by
    intro m m' hm a
    obtain ⟨a', h⟩ := h2 m m' hm a
    exact ⟨a', congrArg S.orthogonalProjectionOnto h⟩
  obtain ⟨m, hm⟩ := exists_surjective f hall hmono
  have := compactSpace_KG ε
  obtain ⟨r1, r2, r3, r4, r5⟩ := hRho n ε (lowK ε lam) T m
  let ρl : KG ε → (AS T m →ₗ[ℂ] AS T m) := fun k =>
    { toFun := rhoA T m k, map_add' := r3 k, map_smul' := r4 k }
  let ρ : KG ε → (AS T m →L[ℂ] AS T m) := fun k => LinearMap.toContinuousLinearMap (ρl k)
  have hρ1 : ρ 1 = 1 := ContinuousLinearMap.ext r1
  have hρ2 : ∀ g h, ρ (g * h) = ρ g ∘L ρ h := fun g h => ContinuousLinearMap.ext (r2 g h)
  have hρ3 : Continuous ρ := continuous_clm_apply.2 r5
  have hσ1 : sigS S hK 1 = 1 := by
    refine ContinuousLinearMap.ext fun y => Subtype.ext ?_
    show rreg ε (toMK (1 : KG ε)) y = y
    rw [rreg_toMK_one]
    rfl
  have hσ2 : ∀ g h, sigS S hK (g * h) = sigS S hK g ∘L sigS S hK h := by
    intro g h
    refine ContinuousLinearMap.ext fun y => Subtype.ext ?_
    show rreg ε (toMK (g * h)) y = rreg ε (toMK g) (rreg ε (toMK h) y)
    rw [rreg_toMK_mul]
    rfl
  have hσ3 : ∀ y, Continuous fun g => sigS S hK g y := by
    intro y
    refine Continuous.subtype_mk ?_ _
    exact ((rreg_isURepOn ε).2.2 (y : L2 ε)).comp_continuous continuous_toMK toMK_mem
  have heq : ∀ g a, f m (ρ g a) = sigS S hK g (f m a) := by
    intro k a
    refine Subtype.ext ?_
    show (S.starProjection (actL T Ψ (rhoA T m k a))) =
      rreg ε (toMK k) (S.starProjection (actL T Ψ a))
    rw [← hAct n ε lam T Ψ m hP k a]
    exact starProjection_comm S _ (rreg ε (toMK k⁻¹)) ((rreg_isURepOn ε).2.1 _ (toMK_mem k))
      (rreg_toMK_inv k) (hK _ k.2) (hK _ (k⁻¹).2) _
  obtain ⟨s, hs1, hs2⟩ := hSec (KG ε) (AS T m) S ρ (sigS S hK) hρ1 hρ2 hρ3 hσ1 hσ2 hσ3 (f m) hm heq
  exact ⟨m, s, hs1, hs2⟩

end Sub

theorem toL2_zero_eq_zero (ε : Fin n → Bool) : toL2 ε (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) = 0 := by
  simpa using toL2_smul_smooth ε 0 (0 : Matrix (Fin n) (Fin n) ℂ → ℂ)

theorem key_of_steps : LowAlg → HolFacts → EquivSection → RhoRep → ActEquiv → RhoTorus → TorW → Transfer →
    Exhaust → BetaWeight → PositivityTheory.RgDs.Key := by
  intro hLow hHol hSec hRho hAct _ _ hTr hEx hBeta n ε lam T μ hHC hMu hP S hfd hle hK
  haveI := hfd
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  obtain ⟨m, s, hs1, hs2⟩ := exists_section hSec hRho hAct hEx hP S hle hK
  have hwt : ∀ (η : Fin n → ℝ) (x : S),
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) η (x : L2 ε) →
      betaF T μ (s x) ∈ Submodule.span ℂ (Set.range fun w : List (Fin n × Fin n) => lw w (PhiO μ)) ∧
      ∀ c, lop (Matrix.single c c 1) (betaF T μ (s x)) =
        ((((μ c : ℤ) : ℝ) + η c - lowK ε lam c : ℝ) : ℂ) • betaF T μ (s x) := by
    intro η x hx
    refine hBeta n ε (lowK ε lam) T μ m η (s x) fun θ k hk => ?_
    have hσ : sigS S hK k x = Complex.exp (((∑ c, η c * θ c : ℝ) : ℂ) * Complex.I) • x := by
      refine Subtype.ext ?_
      show rreg ε (toMK k) x = _
      have hm : toMK k ∈ Formalism.REAL.Kset ε := k.2
      rw [hk] at hm ⊢
      exact hx θ hm
    rw [← hs2, hσ, map_smul]
  refine ⟨Matrix (Fin n) (Fin n) ℂ → ℂ, inferInstance, inferInstance, betaLin T μ m ∘ₗ s, PhiO μ, ?_, ?_, ?_⟩
  · intro S' hS' hK' hne
    by_contra hcon
    push_neg at hcon
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    apply hv0
    let x : S := ⟨v, hS' hv⟩
    have hz : ∀ k, betaF T μ (rhoA T m k (s x)) = 0 := fun k => by
      rw [← hs2 k x]
      exact hcon (sigS S hK k x) (hK' _ k.2 v hv)
    have hF : ∀ g, inUJ ε g → actF T (PsiM T μ) (s x) g = (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) g := by
      intro g₀ hg₀
      obtain ⟨W, hW, k₀, h⟩ := hTr n ε lam T μ m hHC hMu (s x) g₀ hg₀
      rw [h g₀ (mem_of_mem_nhds hW) hg₀]
      simp [hz]
    have hL : actL T (PsiM T μ) (s x) = 0 := (toL2_congr_of_forall_inUJ_eq hF).trans (toL2_zero_eq_zero ε)
    have h := hs1 x
    rw [hL, map_zero] at h
    exact congrArg Subtype.val h.symm
  · intro η x hx hne
    obtain ⟨hb, hl⟩ := hwt η x hx
    obtain ⟨c, hc1, hc2⟩ := (lowAlg_model hLow hHol μ (fun c => ((μ c : ℤ) : ℝ) + η c - lowK ε lam c)
      hb hl hne).1
    refine ⟨c, hc1, ?_⟩
    funext a
    have h := congrFun hc2 a
    simp only [Pi.add_apply] at h ⊢
    linarith
  · intro x hx
    by_cases h0 : betaF T μ (s x) = 0
    · exact ⟨0, by rw [zero_smul]; exact h0⟩
    · obtain ⟨hb, hl⟩ := hwt _ x hx
      exact (lowAlg_model hLow hHol μ (fun c => ((μ c : ℤ) : ℝ) + lowK ε lam c - lowK ε lam c)
        hb hl h0).2 (by funext a; simp)

end GlobalTheory.CompanionTheory.KeyAsm
