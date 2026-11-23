import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf

noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.LowestDataIso

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (lowK)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (LocFin IsMin Cyc mem_cyc cyc_stab hMultAlg)

variable {n : ℕ} {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

def fstL (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] : WithLp 2 (V × V') →ₗ[ℂ] V :=
  LinearMap.fst ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

def sndL (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] : WithLp 2 (V × V') →ₗ[ℂ] V' :=
  LinearMap.snd ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

def pair (x : V) (y : V') : WithLp 2 (V × V') := WithLp.toLp 2 (x, y)

@[simp] theorem fstL_pair (x : V) (y : V') : fstL V V' (pair x y) = x := rfl

@[simp] theorem sndL_pair (x : V) (y : V') : sndL V V' (pair x y) = y := rfl

theorem ext2 {x y : WithLp 2 (V × V')} (h₁ : fstL V V' x = fstL V V' y) (h₂ : sndL V V' x = sndL V V' y) : x = y :=
  WithLp.ofLp_injective _ (Prod.ext h₁ h₂)

theorem inner_eq (x y : WithLp 2 (V × V')) :
    ⟪x, y⟫_ℂ = ⟪fstL V V' x, fstL V V' y⟫_ℂ + ⟪sndL V V' x, sndL V V' y⟫_ℂ :=
  WithLp.prod_inner_apply x y

def sumE (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n) :
    Module.End ℂ (WithLp 2 (V × V')) :=
  (WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ (E a b).prodMap (E' a b) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

variable {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}

@[simp] theorem fstL_sumE (a b : Fin n) (x : WithLp 2 (V × V')) :
    fstL V V' (sumE E E' a b x) = E a b (fstL V V' x) := rfl

@[simp] theorem sndL_sumE (a b : Fin n) (x : WithLp 2 (V × V')) :
    sndL V V' (sumE E E' a b x) = E' a b (sndL V V' x) := rfl

theorem glRel_sumE (hE : GlRel E) (hE' : GlRel E') : GlRel (sumE E E') := by
  intro a b c d
  refine LinearMap.ext fun x => ?_
  have h₁ := LinearMap.congr_fun (hE a b c d) (fstL V V' x)
  have h₂ := LinearMap.congr_fun (hE' a b c d) (sndL V V' x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h₁ h₂
  refine ext2 ?_ ?_
  · by_cases p : b = c <;> by_cases q : d = a <;> simp_all
  · by_cases p : b = c <;> by_cases q : d = a <;> simp_all

theorem kUnit_sumE {ε : Fin n → Bool} (hU : KUnit ε E) (hU' : KUnit ε E') : KUnit ε (sumE E E') := by
  intro a b hab x y
  rw [inner_eq, inner_eq, fstL_sumE, sndL_sumE, fstL_sumE, sndL_sumE, hU a b hab, hU' a b hab]

theorem locFin_sumE {ε : Fin n → Bool} (hF : LocFin ε E) (hF' : LocFin ε E') : LocFin ε (sumE E E') := by
  intro x
  obtain ⟨S, hS, hk, hx⟩ := hF (fstL V V' x)
  obtain ⟨S', hS', hk', hx'⟩ := hF' (sndL V V' x)
  have hfg : (S.prod S').FG :=
    Submodule.FG.prod (Module.Finite.iff_fg.1 hS) (Module.Finite.iff_fg.1 hS')
  refine ⟨(S.prod S').map (WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap,
    Module.Finite.iff_fg.2 (hfg.map _), ?_, ?_⟩
  · rintro a b hab _ ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    exact ⟨(E a b y.1, E' a b y.2), ⟨hk a b hab _ hy₁, hk' a b hab _ hy₂⟩, rfl⟩
  · exact ⟨(fstL V V' x, sndL V V' x), ⟨hx, hx'⟩, rfl⟩

theorem kHighest_fst {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : WithLp 2 (V × V')}
    (h : KHighest ε (sumE E E') μ x) : KHighest ε E μ (fstL V V' x) :=
  ⟨fun a => by rw [← fstL_sumE (E' := E'), h.1 a, map_smul],
    fun a b hab he => by rw [← fstL_sumE (E' := E'), h.2 a b hab he, map_zero]⟩

theorem kHighest_snd {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : WithLp 2 (V × V')}
    (h : KHighest ε (sumE E E') μ x) : KHighest ε E' μ (sndL V V' x) :=
  ⟨fun a => by rw [← sndL_sumE (E := E), h.1 a, map_smul],
    fun a b hab he => by rw [← sndL_sumE (E := E), h.2 a b hab he, map_zero]⟩

theorem kHighest_pair {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : V} {y : V'} (h : KHighest ε E μ x)
    (h' : KHighest ε E' μ y) : KHighest ε (sumE E E') μ (pair x y) :=
  ⟨fun a => ext2 (by simpa using h.1 a) (by simpa using h'.1 a),
    fun c d hcd he => ext2 (by simpa using h.2 c d hcd he) (by simpa using h'.2 c d hcd he)⟩

theorem isMin_sumE {ε : Fin n → Bool} {lam : Fin n → ℝ} (hM : IsMin ε E lam) (hM' : IsMin ε E' lam) :
    IsMin ε (sumE E E') lam := by
  intro μ x hx h
  by_cases h₁ : fstL V V' x = 0
  · refine hM' μ _ (fun h₂ => hx ?_) (kHighest_snd h)
    exact ext2 (by simpa using h₁) (by simpa using h₂)
  · exact hM μ _ h₁ (kHighest_fst h)

theorem exists_iso_of_highest {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) (hE : GlRel E)
    (hE' : GlRel E') (hU : KUnit ε E) (hU' : KUnit ε E') (hF : LocFin ε E) (hF' : LocFin ε E')
    (hM : IsMin ε E lam) (hM' : IsMin ε E' lam)
    (hS : ∀ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hS' : ∀ S : Submodule ℂ V', (∀ a b, ∀ x ∈ S, E' a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    {v₁ : V} {v₂ : V'} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (k₁ : KHighest ε E (lowK ε lam) v₁)
    (k₂ : KHighest ε E' (lowK ε lam) v₂) :
    ∃ e : V ≃ₗ[ℂ] V', ∀ a b x, e (E a b x) = E' a b (e x) := by
  set v : WithLp 2 (V × V') := pair v₁ v₂ with hv
  have hv0 : v ≠ 0 := fun h => h₁ (show fstL V V' v = 0 by rw [h, map_zero])
  have hvk : KHighest ε (sumE E E') (lowK ε lam) v := kHighest_pair k₁ k₂
  have hone : ∀ w ∈ Cyc (sumE E E') v, KHighest ε (sumE E E') (lowK ε lam) w → ∃ c : ℂ, w = c • v :=
    fun w hw hh => hMultAlg n ε lam _ (sumE E E') hlam (glRel_sumE hE hE') (kUnit_sumE hU hU')
      (locFin_sumE hF hF') (isMin_sumE hM hM') v w hv0 hvk hh hw
  set C := Cyc (sumE E E') v with hC
  have hvC : v ∈ C := mem_cyc.2 ⟨1, by simp⟩
  have hst : ∀ a b, ∀ w ∈ C, sumE E E' a b w ∈ C := fun a b w hw => cyc_stab a b hw

  have hp₁ : C.map (fstL V V') = ⊤ := by
    refine (hS _ ?_).resolve_left fun h => h₁ ?_
    · rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨_, hst a b w hw, rfl⟩
    · have : v₁ ∈ C.map (fstL V V') := ⟨v, hvC, rfl⟩
      rwa [h, Submodule.mem_bot] at this
  have hp₂ : C.map (sndL V V') = ⊤ := by
    refine (hS' _ ?_).resolve_left fun h => h₂ ?_
    · rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨_, hst a b w hw, rfl⟩
    · have : v₂ ∈ C.map (sndL V V') := ⟨v, hvC, rfl⟩
      rwa [h, Submodule.mem_bot] at this

  have hno₁ : pair v₁ (0 : V') ∉ C := by
    intro h
    obtain ⟨c, hc⟩ := hone _ h (kHighest_pair k₁ ⟨fun a => by simp, fun a b _ _ => by simp⟩)
    have e₁ : v₁ = c • v₁ := by simpa [hv] using congrArg (fstL V V') hc
    have e₂ : (0 : V') = c • v₂ := by simpa [hv] using congrArg (sndL V V') hc
    rcases smul_eq_zero.1 e₂.symm with rfl | h
    · exact h₁ (by simpa using e₁)
    · exact h₂ h
  have hno₂ : pair (0 : V) v₂ ∉ C := by
    intro h
    obtain ⟨c, hc⟩ := hone _ h (kHighest_pair ⟨fun a => by simp, fun a b _ _ => by simp⟩ k₂)
    have e₁ : (0 : V) = c • v₁ := by simpa [hv] using congrArg (fstL V V') hc
    have e₂ : v₂ = c • v₂ := by simpa [hv] using congrArg (sndL V V') hc
    rcases smul_eq_zero.1 e₁.symm with rfl | h
    · exact h₂ (by simpa using e₂)
    · exact h₁ h
  have hsplit : pair v₁ (0 : V') + pair (0 : V) v₂ = v := ext2 (by simp [hv]) (by simp [hv])

  let K₁ : Submodule ℂ V :=
    C.comap ((WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ LinearMap.inl ℂ V V')
  let K₂ : Submodule ℂ V' :=
    C.comap ((WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ LinearMap.inr ℂ V V')
  have mem₁ : ∀ x, x ∈ K₁ ↔ pair x (0 : V') ∈ C := fun x => Iff.rfl
  have mem₂ : ∀ y, y ∈ K₂ ↔ pair (0 : V) y ∈ C := fun y => Iff.rfl
  have hK₁ : K₁ = ⊥ := by
    refine (hS K₁ fun a b x hx => ?_).resolve_right fun h => hno₂ ?_
    · rw [mem₁] at hx ⊢
      have := hst a b _ hx
      have e : sumE E E' a b (pair x (0 : V')) = pair (E a b x) (0 : V') := ext2 (by simp) (by simp)
      rwa [e] at this
    · have : pair v₁ (0 : V') ∈ C := (mem₁ _).1 (h ▸ Submodule.mem_top)
      have h' := C.sub_mem hvC this
      rwa [← hsplit, add_sub_cancel_left] at h'
  have hK₂ : K₂ = ⊥ := by
    refine (hS' K₂ fun a b x hx => ?_).resolve_right fun h => hno₁ ?_
    · rw [mem₂] at hx ⊢
      have := hst a b _ hx
      have e : sumE E E' a b (pair (0 : V) x) = pair (0 : V) (E' a b x) := ext2 (by simp) (by simp)
      rwa [e] at this
    · have : pair (0 : V) v₂ ∈ C := (mem₂ _).1 (h ▸ Submodule.mem_top)
      have h' := C.sub_mem hvC this
      rwa [← hsplit, add_sub_cancel_right] at h'

  let q₁ : C →ₗ[ℂ] V := (fstL V V').comp C.subtype
  let q₂ : C →ₗ[ℂ] V' := (sndL V V').comp C.subtype
  have b₁ : Function.Bijective q₁ := by
    refine ⟨(injective_iff_map_eq_zero q₁).2 fun w hw => ?_, fun x => ?_⟩
    · have hw' : fstL V V' (w : WithLp 2 (V × V')) = 0 := hw
      have e : (w : WithLp 2 (V × V')) = pair (0 : V) (sndL V V' w) := ext2 (by simpa using hw') (by simp)
      have : sndL V V' w ∈ K₂ := (mem₂ _).2 (e ▸ w.2)
      rw [hK₂, Submodule.mem_bot] at this
      exact Subtype.ext (by rw [e, this]; exact ext2 (by simp) (by simp))
    · obtain ⟨w, hw, rfl⟩ : x ∈ C.map (fstL V V') := hp₁ ▸ Submodule.mem_top
      exact ⟨⟨w, hw⟩, rfl⟩
  have b₂ : Function.Bijective q₂ := by
    refine ⟨(injective_iff_map_eq_zero q₂).2 fun w hw => ?_, fun x => ?_⟩
    · have hw' : sndL V V' (w : WithLp 2 (V × V')) = 0 := hw
      have e : (w : WithLp 2 (V × V')) = pair (fstL V V' w) (0 : V') := ext2 (by simp) (by simpa using hw')
      have : fstL V V' w ∈ K₁ := (mem₁ _).2 (e ▸ w.2)
      rw [hK₁, Submodule.mem_bot] at this
      exact Subtype.ext (by rw [e, this]; exact ext2 (by simp) (by simp))
    · obtain ⟨w, hw, rfl⟩ : x ∈ C.map (sndL V V') := hp₂ ▸ Submodule.mem_top
      exact ⟨⟨w, hw⟩, rfl⟩
  let f₁ : C ≃ₗ[ℂ] V := LinearEquiv.ofBijective q₁ b₁
  let f₂ : C ≃ₗ[ℂ] V' := LinearEquiv.ofBijective q₂ b₂
  refine ⟨f₁.symm.trans f₂, fun a b x => ?_⟩
  obtain ⟨w, rfl⟩ := f₁.surjective x
  have e : E a b (f₁ w) = f₁ ⟨sumE E E' a b w, hst a b w w.2⟩ := rfl
  rw [e]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem algUniq : CompanionTheory.RgExh.Fin.AlgUniq := by
  intro n ε V V' _ _ _ _ E E' hE hE' s mu hU hU' hF hF' hS hS' hD hD'
  obtain ⟨hP, -, hM, v₁, h₁, k₁⟩ := hD
  obtain ⟨-, -, hM', v₂, h₂, k₂⟩ := hD'
  have gl : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W}, GlRel F →
      GlRel fun a b => F (s a) (s b) := by
    intro W _ _ F hF a b c d
    simpa only [s.injective.eq_iff] using hF (s a) (s b) (s c) (s d)
  have un : ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {F : Fin n → Fin n → Module.End ℂ W},
      IsUnitary ε F → KUnit (ε ∘ s) fun a b => F (s a) (s b) := by
    intro W _ _ F hF a b hab x y
    have hab' : ε (s a) = ε (s b) := hab
    rw [hF (s a) (s b) x y]
    simp [Formalism.REAL.sgn, hab']
  have lf : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W}, LocFin ε F →
      LocFin (ε ∘ s) fun a b => F (s a) (s b) := by
    intro W _ _ F hF x
    obtain ⟨S, hS, hk, hx⟩ := hF x
    exact ⟨S, hS, fun a b hab y hy => hk (s a) (s b) hab y hy, hx⟩
  have si : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W},
      (∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, F a b x ∈ S) → S = ⊥ ∨ S = ⊤) →
      ∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, F (s a) (s b) x ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro W _ _ F hF S hst
    refine hF S fun a b x hx => ?_
    simpa using hst (s.symm a) (s.symm b) x hx
  obtain ⟨e, he⟩ := exists_iso_of_highest (ε := ε ∘ s) (lam := mu) (E := fun a b => E (s a) (s b))
    (E' := fun a b => E' (s a) (s b)) hP.1 (gl hE) (gl hE') (un hU) (un hU') (lf hF) (lf hF') hM hM'
    (si hS.2) (si hS'.2) h₁ h₂ k₁ k₂
  refine ⟨e, fun a b x => ?_⟩
  simpa using he (s.symm a) (s.symm b) x

end GlobalTheory.CompanionTheory.LowestDataIso
