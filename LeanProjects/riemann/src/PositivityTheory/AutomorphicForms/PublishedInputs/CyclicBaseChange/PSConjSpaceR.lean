import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain Topology Matrix
open scoped ContDiff RestrictedProduct

namespace UpperTheory.CBC.SConjSpaceRAux

open UpperTheory.V.TR
open GlobalTheory.CuspRep (Ad Af GA pFin sFin finGL ratGL cornerGL map_cornerGL_of_zero IsCuspidal ratN unip BlockIx pFin_finGL)
open GlobalTheory.BarPull (map_map_comm continuous_mapGL map_unip)

theorem exists_eval {ι : Type} [Finite ι] (f : (ι → ℝ) →+* ℝ) : ∃ j, ∀ x, f x = x j := by
  classical
  have := Fintype.ofFinite ι
  have hsum : ∑ j, f (Pi.single j 1) = 1 := by
    rw [← map_sum]
    have e : ∑ j, (Pi.single j (1 : ℝ) : ι → ℝ) = 1 := Finset.univ_sum_single (1 : ι → ℝ)
    rw [e, map_one]
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ one_ne_zero : ∑ j, f (Pi.single j 1) ≠ 0)
  have hidem : f (Pi.single j 1) * f (Pi.single j 1) = f (Pi.single j 1) := by
    rw [← map_mul]
    congr 1
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have h1 : f (Pi.single j 1) = 1 := mul_left_cancel₀ hj (hidem.trans (mul_one _).symm)
  have hid : f.comp (Pi.constRingHom ι ℝ) = RingHom.id ℝ := Subsingleton.elim _ _
  refine ⟨j, fun x => ?_⟩
  have e : x * Pi.single j 1 = Pi.constRingHom ι ℝ (x j) * Pi.single j 1 := by
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  calc f x = f x * f (Pi.single j 1) := by rw [h1, mul_one]
    _ = f (x * Pi.single j 1) := (map_mul f _ _).symm
    _ = f (Pi.constRingHom ι ℝ (x j)) * f (Pi.single j 1) := by rw [e, map_mul]
    _ = x j := by rw [h1, mul_one, ← RingHom.comp_apply, hid, RingHom.id_apply]

theorem exists_perm {ι : Type} [Finite ι] (t : (ι → ℝ) →+* (ι → ℝ)) (ht : Function.Surjective t) :
    ∃ p : ι ≃ ι, ∀ x i, t x i = x (p i) := by
  classical
  choose p hp using fun i => exists_eval ((Pi.evalRingHom (fun _ : ι => ℝ) i).comp t)
  have hinj : Function.Injective p := by
    intro i i' h
    by_contra hne
    obtain ⟨x, hx⟩ := ht (Pi.single i 1)
    have a1 : t x i = x (p i) := hp i x
    have a2 : t x i' = x (p i') := hp i' x
    rw [hx] at a1 a2
    rw [h, ← a2] at a1
    simp [Ne.symm hne] at a1
  exact ⟨Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj), fun x i => hp i x⟩

section Top

variable {M : Type} [Field M] [NumberField M]

instance finiteAdeleRing_t2Space : T2Space (FiniteAdeleRing (𝓞 M) M) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 M),
    [v.adicCompletion M, v.adicCompletionIntegers M]))

instance sigmaCompact_infAd : SigmaCompactSpace (InfiniteAdeleRing M) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

instance sigmaCompact_ad : SigmaCompactSpace (AdeleRing (𝓞 M) M) :=
  inferInstanceAs (SigmaCompactSpace (InfiniteAdeleRing M × FiniteAdeleRing (𝓞 M) M))

instance adeleRing_t2Space : T2Space (AdeleRing (𝓞 M) M) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing M × FiniteAdeleRing (𝓞 M) M))

theorem continuous_symm (s : Ad M ≃+* Ad M) (hs : Continuous s) : Continuous s.symm := by
  have ho : IsOpenMap s :=
    AddMonoidHom.isOpenMap_of_sigmaCompact (s.toRingHom.toAddMonoidHom) s.surjective hs
  exact (s.toEquiv.toHomeomorphOfContinuousOpen hs ho).symm.continuous

end Top

section Places

variable {M : Type} [Field M] [NumberField M] [IsTotallyReal M]

def permR (p : InfinitePlace M ≃ InfinitePlace M) : Rinf M ≃+* Rinf M where
  toFun x w := x (p w)
  invFun x w := x (p.symm w)
  left_inv x := funext fun w => by simp
  right_inv x := funext fun w => by simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem pInf_sFin (y : Af M) : pInf M (sFin M y) = 0 := map_zero (infEq M).symm

theorem pInf_sInf (x : Rinf M) : pInf M (sInf M x) = x := (infEq M).symm_apply_apply x

theorem pFin_sInf (x : Rinf M) : pFin M (sInf M x) = 0 := rfl

theorem pFin_sFin (y : Af M) : pFin M (sFin M y) = y := rfl

theorem decomp (x : Ad M) : sInf M (pInf M x) + sFin M (pFin M x) = x :=
  ad_ext (by rw [map_add, pInf_sInf, pInf_sFin, add_zero]) (by rw [map_add, pFin_sInf, pFin_sFin, zero_add])

theorem continuous_pInf : Continuous (pInf M) := by
  have h : Continuous fun x : InfiniteAdeleRing M => (infEq M).symm x :=
    continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_sFin : Continuous (sFin M) :=
  (continuous_const.prodMk continuous_id : Continuous fun y : Af M => ((0, y) : InfiniteAdeleRing M × Af M))

variable {σ : M ≃+* M} {s : Ad M ≃+* Ad M}

theorem pInf_s_sFin_one (hs : IsGalAd σ s) : pInf M (s (sFin M 1)) = 0 := by
  funext w
  have key : pInf M (s (sFin M 1)) * pInf M (s (sFin M 1)) = pInf M (s (sFin M 1)) := by
    rw [← map_mul (pInf M), ← map_mul s, ← map_mul (sFin M), mul_one]
  have hw : pInf M (s (sFin M 1)) w * (pInf M (s (sFin M 1)) w - 1) = 0 := by
    have := congrFun key w
    rw [Pi.mul_apply] at this
    rw [mul_sub, this, mul_one, sub_self]
  rcases mul_eq_zero.1 hw with h | h
  · exact h
  exfalso
  have h1 : pInf M (s (sFin M 1)) w = 1 := sub_eq_zero.1 h
  let ψ : Af M →+* ℝ :=
    { toFun := fun y => pInf M (s (sFin M y)) w
      map_one' := h1
      map_mul' := fun x y => by simp only [map_mul, Pi.mul_apply]
      map_zero' := by simp only [map_zero, Pi.zero_apply]
      map_add' := fun x y => by simp only [map_add, Pi.add_apply] }
  have hc : Continuous ψ := (continuous_apply w).comp (continuous_pInf.comp (hs.1.comp continuous_sFin))
  have hK := (GroundTheory.Global.isCompact_integralFiniteAdeles M).image hc
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hmem : ((⌊C⌋₊ + 1 : ℕ) : Af M) ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 M) M : Set (Af M)) := natCast_mem _ _
  have hn := hC _ (Set.mem_image_of_mem ψ hmem)
  rw [map_natCast, Real.norm_natCast] at hn
  have := Nat.lt_floor_add_one C
  push_cast at hn
  linarith

theorem pInf_s_sFin (hs : IsGalAd σ s) (y : Af M) : pInf M (s (sFin M y)) = 0 := by
  rw [show sFin M y = sFin M y * sFin M 1 by rw [← map_mul, mul_one], map_mul, map_mul, pInf_s_sFin_one hs, mul_zero]

theorem pFin_s_sInf (hs : IsGalAd σ s) (z : Rinf M) : pFin M (s (sInf M z)) = 0 := by
  change (s (sInf M z)).2 = 0
  rw [hs.2.2]
  exact map_zero _

theorem pInf_s (hs : IsGalAd σ s) (x : Ad M) : pInf M (s x) = pInf M (s (sInf M (pInf M x))) := by
  conv_lhs => rw [← decomp x]
  rw [map_add, map_add, pInf_s_sFin hs, add_zero]

theorem free_etale_sheaf_zmod_exists_hom_sending_generator (hs : IsGalAd σ s) :
    ∃ t : Rinf M →+* Rinf M, Function.Surjective t ∧ ∀ x, pInf M (s x) = t (pInf M x) := by
  have h1 : pInf M (s (sInf M 1)) = 1 := by
    have := pInf_s hs 1
    simp only [map_one] at this
    exact this.symm
  let t : Rinf M →+* Rinf M :=
    { toFun := fun x => pInf M (s (sInf M x))
      map_one' := h1
      map_mul' := fun x y => by simp only [map_mul]
      map_zero' := by simp only [map_zero]
      map_add' := fun x y => by simp only [map_add] }
  refine ⟨t, fun z => ⟨pInf M (s.symm (sInf M z)), ?_⟩, fun x => pInf_s hs x⟩
  change pInf M (s (sInf M (pInf M (s.symm (sInf M z))))) = z
  rw [← pInf_s hs, RingEquiv.apply_symm_apply, pInf_sInf]

theorem exists_perm_alt (hs : IsGalAd σ s) :
    ∃ p : InfinitePlace M ≃ InfinitePlace M, ∀ x, pInf M (s x) = permR p (pInf M x) := by
  obtain ⟨t, ht, h⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hs
  obtain ⟨p, hp⟩ := exists_perm t ht
  exact ⟨p, fun x => by rw [h]; funext w; exact hp _ w⟩

structure Good (S : Ad M ≃+* Ad M) (p : InfinitePlace M ≃ InfinitePlace M) : Prop where
  inf : ∀ x, pInf M (S x) = permR p (pInf M x)
  fin0 : ∀ z, pFin M (S (sInf M z)) = 0

theorem good_alt {p : InfinitePlace M ≃ InfinitePlace M} (hs : IsGalAd σ s)
    (hp : ∀ x, pInf M (s x) = permR p (pInf M x)) : Good s p := ⟨hp, pFin_s_sInf hs⟩

theorem good_symm {p : InfinitePlace M ≃ InfinitePlace M} (hs : IsGalAd σ s)
    (hp : ∀ x, pInf M (s x) = permR p (pInf M x)) : Good s.symm p.symm := by
  have e : ∀ z, s.symm (sInf M z) = sInf M ((permR p).symm z) := fun z => by
    rw [RingEquiv.symm_apply_eq]
    refine ad_ext ?_ ?_
    · rw [hp, pInf_sInf, pInf_sInf, RingEquiv.apply_symm_apply]
    · rw [pFin_s_sInf hs, pFin_sInf]
  refine ⟨fun x => ?_, fun z => by rw [e, pFin_sInf]⟩
  have := hp (s.symm x)
  rw [RingEquiv.apply_symm_apply] at this
  rw [this]
  funext w
  change _ = pInf M (s.symm x) (p (p.symm w))
  rw [Equiv.apply_symm_apply]

end Places

section Pull

variable {M : Type} [Field M] [NumberField M] [IsTotallyReal M] {a : ℕ}

theorem map_map' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) (x : GL (Fin a) R) :
    GeneralLinearGroup.map g (GeneralLinearGroup.map f x) = GeneralLinearGroup.map (g.comp f) x := by
  ext i j; rfl

variable (M a) in

def sA (S : Ad M ≃+* Ad M) : GA M a →* GA M a := GeneralLinearGroup.map S.toRingHom

theorem sA_sA_symm (S : Ad M ≃+* Ad M) (g : GA M a) : sA M a S (sA M a S.symm g) = g :=
  Units.ext <| Matrix.ext fun i j => S.apply_symm_apply (g.val i j)

theorem sA_symm_sA (S : Ad M ≃+* Ad M) (g : GA M a) : sA M a S.symm (sA M a S g) = g :=
  Units.ext <| Matrix.ext fun i j => S.symm_apply_apply (g.val i j)

variable {S : Ad M ≃+* Ad M} {p : InfinitePlace M ≃ InfinitePlace M}

theorem sA_infGL (hS : Good S p) (y : GL (Fin a) (Rinf M)) :
    sA M a S (infGL M a y) = infGL M a (GeneralLinearGroup.map (permR p).toRingHom y) :=
  ga_ext (by rw [sA, map_map_comm (pInf M) S.toRingHom (permR p).toRingHom hS.inf, pInf_infGL, pInf_infGL])
    (by
      rw [pFin_infGL, sA, map_map']
      exact map_cornerGL_of_zero (sInf M) ((pFin M).comp S.toRingHom) hS.fin0 y)

variable (S) in

def finPart (k : GL (Fin a) (Af M)) : GL (Fin a) (Af M) := GeneralLinearGroup.map (pFin M) (sA M a S (finGL M a k))

theorem sA_finGL (hS : Good S p) (k : GL (Fin a) (Af M)) : sA M a S (finGL M a k) = finGL M a (finPart S k) :=
  ga_ext (by rw [pInf_finGL, sA, map_map_comm (pInf M) S.toRingHom (permR p).toRingHom hS.inf, pInf_finGL, map_one])
    (by rw [pFin_finGL]; rfl)

variable (p) in

def permL : Lie M a →L[ℝ] Lie M a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => permR p (X i j)
      map_add' := fun X Y => rfl
      map_smul' := fun t X => rfl }

theorem permL_toL (u : GL (Fin a) (Rinf M)) :
    permL p (toL u.val) = toL (GeneralLinearGroup.map (permR p).toRingHom u).val := rfl

theorem permL_oneL : permL p (oneL M a) = oneL M a := by
  rw [show oneL M a = toL (1 : GL (Fin a) (Rinf M)).val from rfl, permL_toL, map_one]

theorem permL_symm_permL (X : Lie M a) : permL p.symm (permL p X) = X := by
  funext i j w
  change X i j (p (p.symm w)) = X i j w
  rw [Equiv.apply_symm_apply]

theorem norm_permL_le (q : InfinitePlace M ≃ InfinitePlace M) (X : Lie M a) : ‖permL q X‖ ≤ ‖X‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg X)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg X)).2 fun j =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg X)).2 fun w => ?_
  show ‖X i j (q w)‖ ≤ ‖X‖
  exact ((norm_le_pi_norm (X i j) (q w)).trans (norm_le_pi_norm (X i) j)).trans (norm_le_pi_norm X i)

theorem norm_permL (q : InfinitePlace M ≃ InfinitePlace M) (X : Lie M a) : ‖permL q X‖ = ‖X‖ :=
  le_antisymm (norm_permL_le q X) (by
    calc ‖X‖ = ‖permL q.symm (permL q X)‖ := by rw [permL_symm_permL]
      _ ≤ ‖permL q X‖ := norm_permL_le q.symm _)

theorem height_perm (y : GL (Fin a) (Rinf M)) : height (GeneralLinearGroup.map (permR p).toRingHom y) = height y := by
  have h1 : ∀ z : GL (Fin a) (Rinf M), ‖toL (GeneralLinearGroup.map (permR p).toRingHom z).val‖ = ‖toL z.val‖ :=
    fun z => norm_permL p (toL z.val)
  unfold height
  rw [← map_inv, h1, h1]

variable (p) in

def permK (k : Kinf M a) : Kinf M a :=
  ⟨(k : Matrix (Fin a) (Fin a) (Rinf M)).map (permR p).toRingHom, by
    have hk := k.2
    rw [Matrix.mem_unitaryGroup_iff] at hk ⊢
    have e : star ((k : Matrix (Fin a) (Fin a) (Rinf M)).map (permR p).toRingHom) =
        (star (k : Matrix (Fin a) (Fin a) (Rinf M))).map (permR p).toRingHom := by
      ext i j; rfl
    rw [e, ← Matrix.map_mul, hk, Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem map_toUnits (k : Kinf M a) :
    GeneralLinearGroup.map (permR p).toRingHom (Unitary.toUnits k) = Unitary.toUnits (permK p k) := Units.ext rfl

theorem chart_pull (hS : Good S p) (φ : GA M a → ℂ) (g : GA M a) {x : Lie M a} (hx : x ∈ invSet M a) :
    chart (fun g => φ (sA M a S g)) g x = chart φ (sA M a S g) (permL p x) ∧ permL p x ∈ invSet M a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [permL_toL, chart_val, chart_val, map_mul, sA_infGL hS]
  exact ⟨rfl, val_mem_invSet _⟩

theorem pull_mem_Sm (hS : Good S p) {φ : GA M a → ℂ} (hφ : φ ∈ Sm M a) : (fun g => φ (sA M a S g)) ∈ Sm M a := fun g =>
  ((hφ (sA M a S g)).comp (permL (a := a) p).contDiff.contDiffOn
    fun _ hx => (chart_pull hS φ g hx).2).congr fun _ hx => (chart_pull hS φ g hx).1

def pullL (hS : Good S p) : Sm M a →ₗ[ℂ] Sm M a where
  toFun φ := ⟨fun g => φ.1 (sA M a S g), pull_mem_Sm hS φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rt_pull (hS : Good S p) (h : GA M a) (φ : Sm M a) :
    rt M a h (pullL hS φ) = pullL hS (rt M a (sA M a S h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (sA M a S) g h)

theorem lie_pull (hS : Good S p) (X : Lie M a) (φ : Sm M a) :
    lie M a X (pullL hS φ) = pullL hS (lie M a (permL p X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (pullL hS φ).1 g =ᶠ[𝓝 (oneL M a)] chart φ.1 (sA M a S g) ∘ permL p :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_pull hS φ.1 g hx).1
  have h2 := HasFDerivAt.comp (oneL M a) (f := permL p)
    (by rw [permL_oneL]; exact (differentiableAt_chart φ.2 (sA M a S g)).hasFDerivAt) (permL p).hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, h2.fderiv]
  rfl

variable (S p) in

def opS : Op M a → Op M a
  | .fin k => .fin (finPart S k)
  | .cpt k => .cpt (permK p k)
  | .lie X => .lie (permL p X)

theorem act_pull (hS : Good S p) (o : Op M a) (φ : Sm M a) : act o (pullL hS φ) = pullL hS (act (opS S p o) φ) := by
  cases o with
  | fin k => exact (rt_pull hS (finGL M a k) φ).trans (by rw [sA_finGL hS]; rfl)
  | cpt k => exact (rt_pull hS (infGL M a (Unitary.toUnits k)) φ).trans (by rw [sA_infGL hS, map_toUnits]; rfl)
  | lie X => exact lie_pull hS X φ

open Classical in
theorem Eop_pull (hS : Good S p) (v : InfinitePlace M) (i j : Fin a) (φ : Sm M a) :
    Eop v i j (pullL hS φ) = pullL hS (Eop (p.symm v) i j φ) := by
  have e : permL p (toL (Matrix.single i j (Pi.single v (1 : ℝ)))) =
      toL (Matrix.single i j (Pi.single (p.symm v) (1 : ℝ))) := by
    funext k l w
    change (Matrix.single i j (Pi.single v (1 : ℝ) : Rinf M) k l) (p w) =
      (Matrix.single i j (Pi.single (p.symm v) (1 : ℝ) : Rinf M) k l) w
    rw [Matrix.single_apply, Matrix.single_apply]
    split_ifs
    · simp only [Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]
    · rfl
  simp only [Eop]
  rw [lie_pull hS, e]

end Pull

section Conj

variable {M : Type} [Field M] [NumberField M] [IsTotallyReal M] {a : ℕ}
variable {σ : M ≃+* M} {s : Ad M ≃+* Ad M} {p : InfinitePlace M ≃ InfinitePlace M}

variable (a) in

def pullE (hs : IsGalAd σ s) (hp : ∀ x, pInf M (s x) = permR p (pInf M x)) : Sm M a ≃ₗ[ℂ] Sm M a where
  toFun := pullL (good_alt hs hp)
  invFun := pullL (good_symm hs hp)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (sA_sA_symm s g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (sA_symm_sA s g)

variable (hs : IsGalAd σ s) (hp : ∀ x, pInf M (s x) = permR p (pInf M x))

theorem pullE_apply (φ : Sm M a) (g : GA M a) : (pullE a hs hp φ).1 g = φ.1 (sA M a s g) := rfl

theorem act_pullE (o : Op M a) (φ : Sm M a) : act o (pullE a hs hp φ) = pullE a hs hp (act (opS s p o) φ) :=
  act_pull (good_alt hs hp) o φ

theorem pull_act (o : Op M a) (φ : Sm M a) :
    pullE a hs hp (act o φ) = act (opS s.symm p.symm o) (pullE a hs hp φ) := by
  have := act_pull (good_symm hs hp) o (pullE a hs hp φ)
  rw [show pullL (good_symm hs hp) (pullE a hs hp φ) = φ from (pullE a hs hp).symm_apply_apply φ] at this
  rw [this]
  exact (pullE a hs hp).apply_symm_apply _

open Classical in
theorem Eop_pullE (v : InfinitePlace M) (i j : Fin a) (φ : Sm M a) :
    Eop v i j (pullE a hs hp φ) = pullE a hs hp (Eop (p.symm v) i j φ) :=
  Eop_pull (good_alt hs hp) v i j φ

theorem cap_pull (v : InfinitePlace M) (u : ℂ) (φ : Sm M a) :
    cap v u (pullE a hs hp φ) = pullE a hs hp (cap (p.symm v) u φ) := by
  have h := GlobalTheory.CuspRep.map_qdet ((pullE a hs hp).conjAlgEquiv ℂ).toAlgHom (Eop (p.symm v)) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i j => ((pullE a hs hp).conjAlgEquiv ℂ).toAlgHom (Eop (p.symm v) i j)) = Eop v := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pullE a hs hp).surjective ψ
    rw [Eop_pullE]
    change pullE a hs hp (Eop (p.symm v) i j ((pullE a hs hp).symm (pullE a hs hp ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e] at h
  rw [cap, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) (p.symm v)) (u + ((a : ℂ) - 1) / 2) = z
  change pullE a hs hp (z ((pullE a hs hp).symm (pullE a hs hp φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem Zalg_pull {z : Module.End ℂ (Sm M a)} (hz : z ∈ Zalg M a) :
    ∃ z' ∈ Zalg M a, ∀ φ, z (pullE a hs hp φ) = pullE a hs hp (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull hs hp v u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

include hs in
theorem sA_ratGL (γ : GL (Fin a) M) :
    sA M a s (ratGL M a γ) = ratGL M a (GeneralLinearGroup.map σ.toRingHom γ) :=
  (map_map_comm (algebraMap M (Ad M)) σ.toRingHom s.toRingHom (fun x => (hs.2.1 x).symm) γ).symm

include hs in
theorem continuous_c : Continuous (GlobalTheory.CuspRep.conjFin σ) := by
  have e : ⇑(GlobalTheory.CuspRep.conjFin σ) = fun y => pFin M (s (sFin M y)) := funext fun y => (hs.2.2 (sFin M y)).symm
  rw [e]
  exact continuous_snd.comp (hs.1.comp continuous_sFin)

include hs in
theorem finPart_eq (k : GL (Fin a) (Af M)) : finPart s k = GeneralLinearGroup.map (GlobalTheory.CuspRep.conjFin σ) k := by
  rw [finPart, sA, map_map_comm (pFin M) s.toRingHom (GlobalTheory.CuspRep.conjFin σ) hs.2.2, pFin_finGL]

theorem isAutForm_pull {φ : Sm M a} (h : IsAutForm φ) : IsAutForm (pullE a hs hp φ) where
  left γ g := by rw [pullE_apply, map_mul, sA_ratGL hs, h.left, pullE_apply]
  level := by
    have hc : Continuous fun k : GL (Fin a) (Af M) => finPart s k := by
      have e : (fun k : GL (Fin a) (Af M) => finPart s k) =
          fun k => GeneralLinearGroup.map (n := Fin a) (GlobalTheory.CuspRep.conjFin σ) k :=
        funext fun k => finPart_eq hs k
      rw [e]
      exact continuous_mapGL (a := a) _ (continuous_c hs)
    convert h.level.preimage hc using 1
    ext k
    exact (Eq.congr_left (act_pullE hs hp (.fin k) φ)).trans (pullE a hs hp).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep M a k φ)).map
      (pullE a hs hp).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pullE hs hp (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm M a) => z φ) ''
      Zalg M a)).map (pullE a hs hp).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull hs hp hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (sA M a s g)
    refine ⟨C, N, fun y => ?_⟩
    rw [pullE_apply, map_mul, sA_infGL (good_alt hs hp), ← height_perm (p := p)]
    exact h1 _

include hs in
theorem mem_ratN {r : ℕ} {x : BlockIx a r → Ad M} (hx : x ∈ ratN M a r) : (fun q => s (x q)) ∈ ratN M a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun q => σ (y q), funext fun q => (hs.2.1 (y q)).symm⟩

include hs in
theorem symm_mem_ratN {r : ℕ} {x : BlockIx a r → Ad M} (hx : x ∈ ratN M a r) :
    (fun q => s.symm (x q)) ∈ ratN M a r := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨fun q => σ.symm (y q), funext fun q => ?_⟩
  change algebraMap M (Ad M) (σ.symm (y q)) = s.symm (algebraMap M (Ad M) (y q))
  rw [RingEquiv.eq_symm_apply, hs.2.1, RingEquiv.apply_symm_apply]

include hs in
open MeasureTheory in

theorem isCuspidal_pull {φ : GA M a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (sA M a s g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  have hsc : Continuous s.symm := continuous_symm s hs.1
  let β : (BlockIx a r → Ad M) ≃ₜ+ (BlockIx a r → Ad M) :=
    { toFun := fun x q => s (x q)
      invFun := fun x q => s.symm (x q)
      left_inv := fun x => funext fun q => s.symm_apply_apply _
      right_inv := fun x => funext fun q => s.apply_symm_apply _
      map_add' := fun x y => funext fun q => map_add s _ _
      continuous_toFun := continuous_pi fun q => hs.1.comp (continuous_apply q)
      continuous_invFun := continuous_pi fun q => hsc.comp (continuous_apply q) }
  let e : ratN M a r ≃ ratN M a r :=
    { toFun := fun y => ⟨β.symm y, symm_mem_ratN hs y.2⟩
      invFun := fun x => ⟨β x, mem_ratN hs x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (sA M a s g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, sA, map_unip]
  rfl

def conjSub (π : CuspSub M a) : CuspSub M a where
  V := π.V.map (pullE a hs hp).toLinearMap
  cusp := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨isAutForm_pull hs hp (π.cusp φ hφ).1, isCuspidal_pull hs (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_pullE hs hp o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pullE a hs hp)).1 h)
  irred W hW hst := by
    have h := π.irred (W.comap (pullE a hs hp).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (pullE a hs hp).injective h2]) fun o φ hφ => by
      change pullE a hs hp (act o φ) ∈ W
      rw [pull_act]
      exact hst _ _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := (pullE a hs hp).toLinearMap) (pullE a hs hp).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

end Conj

end UpperTheory.CBC.SConjSpaceRAux

open UpperTheory.CBC.SConjSpaceRAux in
theorem UpperTheory.CBC.SConjSpaceR_holds : UpperTheory.CBC.SConjSpaceR := by
  intro M _ _ _ σ s hs n P
  obtain ⟨p, hp⟩ := exists_perm_alt hs
  refine ⟨conjSub hs hp P, ?_⟩
  ext f
  constructor
  · rintro ⟨ψ, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨φ.1, ⟨φ, hφ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩

end
