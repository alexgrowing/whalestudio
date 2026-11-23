import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwineAlt

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_aeval_intertwine {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z) (h : ∀ y, ψ (A y) = B (ψ y)) (p : ℂ[X])
    (y : Y) : ψ (aeval A p y) = aeval B p (ψ y) := by
  first | exact UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine .. | (apply UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> first | assumption | infer_instance)

theorem dc_tensSub_fd {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M}
    (hS : FiniteDimensional ℂ S) : FiniteDimensional ℂ (tensSub (n := n) S) := by
  let F : (Fin n → S) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun c => S.subtype ∘ₗ LinearMap.proj c
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range F) fun f hf => ?_
  refine ⟨fun c => ⟨f c, dc_mem_tensSub.mp hf c⟩, ?_⟩
  funext c
  simp [F]

theorem dc_tensSub_mono {M : Type*} [AddCommGroup M] [Module ℂ M] {S T : Submodule ℂ M} (h : S ≤ T) :
    tensSub (n := n) S ≤ tensSub T :=
  fun f hf => dc_mem_tensSub.mpr fun c => h (dc_mem_tensSub.mp hf c)

theorem dc_tens_kStable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (dual : Bool) {S : Submodule ℂ M} (hS : IsKStableSub ε E S) (a b : Fin n) (hab : ε a = ε b) :
    ∀ f ∈ tensSub S, tensF dual E a b f ∈ tensSub S := by
  intro f hf
  rw [dc_mem_tensSub] at hf ⊢
  intro c
  cases dual
  · simp only [tensF, cond_false, tensV_coord]
    refine S.add_mem (hS a b hab _ (hf c)) ?_
    split_ifs
    · exact hf b
    · exact S.zero_mem
  · simp only [tensF, cond_true, tensVd_coord]
    refine S.sub_mem (hS a b hab _ (hf c)) ?_
    split_ifs
    · exact hf a
    · exact S.zero_mem

theorem dc_genSub_stable' {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (a b : Fin n) {v : M} (hv : v ∈ genSub E V) : E a b v ∈ genSub E V := by
  rw [genSub, Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem dc_eeF_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) : ∀ f ∈ tensSub (genSub E V), eeF dual E f ∈ tensSub (genSub E V) := by
  intro f hf
  rw [dc_mem_tensSub] at hf ⊢
  intro c
  cases dual
  · simp only [eeF, cond_false, eeV_coord]
    exact Submodule.sum_mem _ fun r _ => dc_genSub_stable' _ _ (hf r)
  · simp only [eeF, cond_true, eeVd_coord]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun r _ => dc_genSub_stable' _ _ (hf r))

theorem dc_eeF_comm {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (dual : Bool) (a b : Fin n) (y : Fin n → M) :
    tensF dual E a b (eeF dual E y) = eeF dual E (tensF dual E a b y) := by
  cases dual
  · simpa [tensF, eeF, Module.End.mul_apply] using LinearMap.congr_fun (eeV_comm hE a b) y
  · simpa [tensF, eeF, Module.End.mul_apply] using LinearMap.congr_fun (eeVd_comm hE a b) y

theorem dc_eeF_pow_comm {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (dual : Bool) (a b : Fin n) (j : ℕ) (y : Fin n → M) :
    tensF dual E a b ((eeF dual E ^ j) y) = (eeF dual E ^ j) (tensF dual E a b y) := by
  induction j generalizing y with
  | zero => simp
  | succ j ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, dc_eeF_comm hE]

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_core {Xs Ys : Type*} [NormedAddCommGroup Xs] [InnerProductSpace ℂ Xs] [AddCommGroup Ys] [Module ℂ Ys]
    {A : Fin n → Fin n → Module.End ℂ Xs} {B : Fin n → Fin n → Module.End ℂ Ys}
    (hA : IsGlRep A) (hU : IsKUnitary ε A)
    {LX : Submodule ℂ Xs} (hLfd : FiniteDimensional ℂ LX) (hLk : IsKStableSub ε A LX)
    {S0 : Submodule ℂ Ys} (hS0fd : FiniteDimensional ℂ S0) (hS0k : IsKStableSub ε B S0)
    (ψ0 : Ys →ₗ[ℂ] Xs) (hψ0 : ∀ a b, ε a = ε b → ∀ y, ψ0 (B a b y) = A a b (ψ0 y))
    (p : Fin n → ℂ[X]) (hp : ∀ c, ∀ y ∈ S0, aeval (B c c) (p c) y = 0)
    (hgood : ∀ y ∈ S0, ∀ z ∈ LX, ψ0 y - z ∈ LXᗮ → ψ0 y - z ≠ 0 → ∀ μ : Fin n → ℝ,
      (∀ c, (p c).eval (μ c : ℂ) = 0) → IsKHWVec ε A μ (ψ0 y - z) → False) :
    ∀ y ∈ S0, ψ0 y ∈ LX := by
  classical
  haveI : CompleteSpace LX := FiniteDimensional.complete ℂ LX
  have hcomm := fun a b (hab : ε a = ε b) x => starProjection_comm (S := LX) hU hLk hab x
  let ψ : Ys →ₗ[ℂ] Xs := ψ0 - (LX.starProjection : Xs →ₗ[ℂ] Xs) ∘ₗ ψ0
  have hψ : ∀ y, ψ y = ψ0 y - LX.starProjection (ψ0 y) := fun y => rfl
  have hψi : ∀ a b, ε a = ε b → ∀ y, ψ (B a b y) = A a b (ψ y) := by
    intro a b hab y
    rw [hψ, hψ, hψ0 a b hab, hcomm a b hab, map_sub]
  have hRfd : FiniteDimensional ℂ (S0.map ψ) := inferInstance
  have hRk : IsKStableSub ε A (S0.map ψ) := by
    intro a b hab x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨_, hS0k a b hab y hy, hψi a b hab y⟩
  have hR : S0.map ψ = ⊥ := by
    by_contra hne
    obtain ⟨w, hwR, hw0, μ, hμ⟩ := exists_khw hA hU hRfd hRk hne
    obtain ⟨y, hy, rfl⟩ := hwR
    refine hgood y hy _ (Submodule.starProjection_apply_mem _ _)
      (Submodule.sub_starProjection_mem_orthogonal _) hw0 μ (fun c => ?_) hμ
    have h1 := dc_aeval_intertwine ψ (B c c) (A c c) (hψi c c rfl) (p c) y
    rw [hp c y hy, map_zero, dc_aeval_eigen (hμ.1 c)] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hw0
  intro y hy
  have h0 : ψ y = 0 := by
    have : ψ y ∈ S0.map ψ := ⟨y, hy, rfl⟩
    rw [hR] at this
    exact this
  rw [hψ, sub_eq_zero] at h0
  rw [h0]
  exact Submodule.starProjection_apply_mem _ _

theorem dc_layer_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} (dual : Bool) (hE : IsGlRep E) (hKU : IsKUnitary ε E)
    (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) (L : Submodule ℂ D) (hLfd : FiniteDimensional ℂ L)
    (hLk : IsKStableSub ε E L) (hLM : L ≤ genSub E V) (p : Fin n → ℂ[X])
    (hp : ∀ c, ∀ y ∈ tensSub V, aeval (tensF dual E c c) (p c) y = 0)
    (hL : ∀ μ : Fin n → ℝ, (∀ c, (p c).eval (μ c : ℂ) = 0) → ∀ c, ∀ w ∈ genSub E V,
      IsKHWVec ε E (dc_wsh dual μ c) w → w ∈ L)
    (T : Module.End ℂ (Fin n → D)) (hT : ∀ a b, ε a = ε b → ∀ y, T (tensF dual E a b y) = tensF dual E a b (T y))
    (hTM : ∀ y ∈ tensSub V, T y ∈ tensSub (genSub E V)) :
    ∀ y ∈ tensSub V, T y ∈ tensSub L := by
  classical
  have h4 : IsKStableSub ε (dc_tensX dual E) ((tensSub (n := n) L).map ((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D)) := by
    intro a b hab x hx
    obtain ⟨f, hf, rfl⟩ := hx
    exact ⟨tensF dual E a b f, dc_tens_kStable dual hLk a b hab f hf, by simp [dc_tensX_apply]⟩
  have h5 : ∀ a b, ε a = ε b → ∀ y, (((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D) ∘ₗ T) (tensF dual E a b y) = dc_tensX dual E a b ((((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D) ∘ₗ T) y) := by
      intro a b hab y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [dc_tensX_apply, LinearEquiv.apply_symm_apply, hT a b hab]
  have h3 : FiniteDimensional ℂ ((tensSub (n := n) L).map ((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D)) := by
    haveI := dc_tensSub_fd (n := n) hLfd; infer_instance
  have key := dc_core (Xs := dc_TX n ↥D) (Ys := Fin n → ↥D) (A := dc_tensX dual E) (B := tensF dual E)
    (dc_tensX_isGlRep hE) (dc_tensX_isKUnitary hKU) h3 h4 (dc_tensSub_fd hVfd) (dc_tens_kStable dual hVk) _ h5 p hp
  intro y hy
  obtain ⟨z, hz, hze⟩ := key (by
    intro y hy x hx horth hx0 μ hμ hhw
    obtain ⟨zf, hzf, rfl⟩ := hx
    set f : Fin n → D := dc_eqv (((dc_eqv (n := n) (D := ↥D)).symm (T y)) - (dc_eqv (n := n) (D := ↥D)).symm zf) with hfdef
    have hfe : f = T y - zf := by
      rw [hfdef, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hfM : f ∈ tensSub (genSub E V) := by
      rw [hfe]
      exact Submodule.sub_mem _ (hTM y hy) (dc_tensSub_mono hLM hzf)
    have hf0 : f ≠ 0 := by
      intro h
      apply hx0
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← (dc_eqv (n := n) (D := ↥D)).map_eq_zero_iff]
      exact h
    have hfhw : IsKHWVec ε (tensF dual E) μ f := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hhw
      refine ⟨fun a => ?_, fun a b hab he => ?_⟩
      · rw [hfdef, ← dc_eqv_tensX, hhw.1 a, map_smul]
      · rw [hfdef, ← dc_eqv_tensX, hhw.2 a b hab he, map_zero]
    obtain ⟨c, hc0, hchw⟩ := dc_top_coord hfhw hf0
    have hcL : f c ∈ L := hL μ hμ c _ (dc_mem_tensSub.mp hfM c) hchw
    have hsing : ((dc_eqv (n := n) (D := ↥D)).symm (Pi.single c (f c)) : dc_TX n D) ∈
        (tensSub (n := n) L).map ((dc_eqv (n := n) (D := ↥D)).symm : (Fin n → D) →ₗ[ℂ] dc_TX n D) := by
      refine ⟨Pi.single c (f c), dc_mem_tensSub.mpr fun i => ?_, rfl⟩
      rw [Pi.single_apply]
      split_ifs with h
      · subst h; exact hcL
      · exact L.zero_mem
    have h0 := Submodule.inner_right_of_mem_orthogonal hsing horth
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h0
    have h0' : inner ℂ (f c) (f c) = 0 := by
      rw [PiLp.inner_apply, Finset.sum_eq_single c (fun i _ hi => by simp [dc_eqv_symm_apply, hi]) (by simp)] at h0
      simpa [hfdef, dc_eqv_symm_apply, dc_eqv_apply] using h0
    exact hc0 (inner_self_eq_zero.mp h0')) y hy
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hze
  have : z = T y := (dc_eqv (n := n) (D := ↥D)).symm.injective hze
  rw [← this]
  exact hz

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_ee_fin_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} {lam : Fin n → ℝ} (dual : Bool)
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap : StdGap ε lam) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ tensSub V ≤ W ∧
      W ≤ tensSub (genSub E V) ∧ ∀ f ∈ W, eeF dual E f ∈ W := by
  classical
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  set EE := eeF dual E with hEE
  set S0 : Submodule ℂ (Fin n → D) := tensSub V with hS0
  have hS0fd : FiniteDimensional ℂ S0 := dc_tensSub_fd hV.1
  have hS0k := dc_tens_kStable dual hV.2.1
  have hS0c : ∀ c, ∀ f ∈ S0, tensF dual E c c f ∈ S0 := fun c => hS0k c c rfl
  let p : Fin n → ℂ[X] := fun c => minpoly ℂ ((tensF dual E c c).restrict (hS0c c))
  have hp0 : ∀ c, p c ≠ 0 := fun c => minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  have hpS : ∀ c, ∀ f ∈ S0, aeval (tensF dual E c c) (p c) f = 0 := by
    intro c f hf
    have h := dc_aeval_intertwine S0.subtype ((tensF dual E c c).restrict (hS0c c)) (tensF dual E c c)
      (fun y => rfl) (p c) ⟨f, hf⟩
    rw [minpoly.aeval] at h
    simpa using h.symm
  set Λs : Set (Fin n → ℝ) := {μ | ∀ c, (p c).eval (μ c : ℂ) = 0} with hΛs
  have hΛ : Λs.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | (p c).eval (r : ℂ) = 0}) fun c => ?_).subset ?_
    · refine ((p c).roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset ?_
      intro r hr
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (hp0 c)).mpr hr
    · intro μ hμ c _
      exact hμ c
  choose kf hkf using fun μ => khw_mem_layer hE hU hV hc hgap μ
  let g : (Fin n → ℝ) → ℕ := fun μ => univ.sup fun c => kf (dc_wsh dual μ c)
  obtain ⟨K0, hK0⟩ := (hΛ.image g).bddAbove
  have hKb : ∀ μ ∈ Λs, ∀ c, kf (dc_wsh dual μ c) ≤ K0 := fun μ hμ c =>
    (Finset.le_sup (f := fun c => kf (dc_wsh dual μ c)) (mem_univ c)).trans (hK0 ⟨μ, hμ, rfl⟩)
  set L := layer ε E V K0 with hL
  have hLfd : FiniteDimensional ℂ L := finiteDimensional_layer hV.1 K0
  have hLk : IsKStableSub ε E L := layer_kStable hE hV.2.1 K0
  have hLM : tensSub (n := n) L ≤ tensSub (genSub E V) := dc_tensSub_mono (layer_le_genSub K0)
  have hpowM : ∀ j, ∀ f ∈ tensSub (genSub E V), (EE ^ j) f ∈ tensSub (genSub E V) := by
    intro j
    induction j with
    | zero => intro f hf; simpa using hf
    | succ j ih => intro f hf; rw [pow_succ', Module.End.mul_apply]; exact dc_eeF_mem dual _ (ih f hf)
  haveI hLfd' : FiniteDimensional ℂ (tensSub (n := n) L) := dc_tensSub_fd hLfd
  have hVg : V ≤ genSub E V := by unfold genSub; exact le_sInf fun T hT => hT.1
  have key : ∀ j, S0.map (EE ^ j) ≤ tensSub L := by
    intro j x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact dc_layer_map dual hE hKU hV.1 hV.2.1 L hLfd hLk (layer_le_genSub K0) p hpS
      (fun μ hμ c w hw hhw => layer_mono (hKb μ hμ c) (hkf _ w hw hhw))
      (EE ^ j) (fun a b _ y => (dc_eeF_pow_comm hE dual a b j y).symm)
      (fun y hy => hpowM j y (dc_tensSub_mono hVg hy)) y hy
  let W : Submodule ℂ (Fin n → D) := ⨆ j, S0.map (EE ^ j)
  have hWL : W ≤ tensSub L := iSup_le key
  refine ⟨W, Submodule.finiteDimensional_of_le hWL, ?_, hWL.trans hLM, ?_⟩
  · have : S0.map (EE ^ 0) ≤ W := le_iSup (fun j => S0.map (EE ^ j)) 0
    simpa [pow_zero, Module.End.one_eq_id, Submodule.map_id] using this
  · intro f hf
    induction hf using Submodule.iSup_induction' with
    | mem j x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine le_iSup (fun j => S0.map (EE ^ j)) (j + 1) ⟨y, hy, ?_⟩
      rw [pow_succ', Module.End.mul_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_adjSign_mul_swap (a b : Fin n) : adjSign ε a b * adjSign ε b a = 1 := by
  unfold adjSign
  by_cases h : ε a = ε b
  · simp [h]
  · have h' : ¬ ε b = ε a := fun e => h e.symm
    simp [h, h']

theorem dc_tens_genSub_stable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) (a b : Fin n) :
    ∀ f ∈ tensSub (genSub E V), tensF dual E a b f ∈ tensSub (genSub E V) :=
  dc_tens_kStable (ε := fun _ => true) dual (fun a b _ v hv => dc_genSub_stable' a b hv) a b rfl

theorem dc_casimir_tensF_apply {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (dual : Bool) {c0 : ℂ} {S : Submodule ℂ M} (hc : ∀ v ∈ S, casimir E v = c0 • v) :
    ∀ f ∈ tensSub S, casimir (tensF dual E) f = (c0 + n) • f + (2 : ℂ) • eeF dual E f := by
  intro f hf
  have hd : diagOp (n := n) (casimir E) f = c0 • f := by
    funext c
    rw [diagOp_coord, hc _ (dc_mem_tensSub.mp hf c), Pi.smul_apply]
  cases dual
  · have h := LinearMap.congr_fun (casimir_tensV (n := n) hE) f
    simp only [tensF, eeF, cond_false, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h ⊢
    rw [h, hd, add_smul]
  · have h := LinearMap.congr_fun (casimir_tensVd (n := n) hE) f
    simp only [tensF, eeF, cond_true, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h ⊢
    rw [h, hd, add_smul]

theorem dc_eeF_Qsymm {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (hE : IsGlRep E) (dual : Bool) {c0 : ℝ}
    (hc : ∀ v ∈ genSub E V, casimir E v = (c0 : ℂ) • v) {Q : (Fin n → M) →ₗ⋆[ℂ] (Fin n → M) →ₗ[ℂ] ℂ}
    (hadj : ∀ a b, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q (tensF dual E a b f) g = adjSign ε a b * Q f (tensF dual E b a g)) :
    ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q (eeF dual E f) g = Q f (eeF dual E g) := by
  intro f hf g hg
  have hΩ : Q (casimir (tensF dual E) f) g = Q f (casimir (tensF dual E) g) := by
    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hadj a b _ (dc_tens_genSub_stable dual b a f hf) g hg,
      hadj b a f hf _ (dc_tens_genSub_stable dual b a g hg), ← mul_assoc, dc_adjSign_mul_swap, one_mul]
  have e : ∀ x ∈ tensSub (genSub E V), eeF dual E x =
      (1 / 2 : ℂ) • (casimir (tensF dual E) x - (((c0 : ℝ) : ℂ) + n) • x) := by
    intro x hx
    rw [dc_casimir_tensF_apply hE dual hc x hx, add_sub_cancel_left, smul_smul]
    norm_num
  rw [e f hf, e g hg]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, map_smul, hΩ,
    smul_eq_mul]
  simp [Complex.conj_ofReal, map_ofNat]

end ReciprocityTheory.ChartRestriction.DS.G2

end
