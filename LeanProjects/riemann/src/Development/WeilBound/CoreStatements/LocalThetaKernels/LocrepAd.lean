import Development.WeilBound.CoreStatements.LocalThetaKernels.LocrepSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility

noncomputable section

namespace PositivityTheory.ThKH.Locrep

open scoped Matrix
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right)

variable {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F)

variable (κ) in

def evA : (κ → AF F) →+ (κ → Fv F v) where
  toFun x i := evFin F v (x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

variable (κ) in

def inA : (κ → Fv F v) →+ (κ → AF F) where
  toFun y i := atPlace v (y i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

variable (κ) in

def evF : (κ → Af F) →+ (κ → Fv F v) where
  toFun x i := evalV F v (x i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

variable (κ) in

def inF : (κ → Fv F v) →+ (κ → Af F) where
  toFun y i := singleFin v (y i)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

theorem evA_inA (y : κ → Fv F v) : evA κ v (inA κ v y) = y := funext fun i => evFin_atPlace v (y i)

theorem evF_inF (y : κ → Fv F v) : evF κ v (inF κ v y) = y := funext fun i => evalV_singleFin_self v (y i)

theorem continuous_evF : Continuous (evF (F := F) κ v) :=
  continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)

theorem continuous_inF : Continuous (inF (F := F) κ v) :=
  continuous_pi fun i => (continuous_singleFin v).comp (continuous_apply i)

abbrev putA (x : κ → AF F) (y : κ → Fv F v) : κ → AF F := put (evA κ v) (inA κ v) x y

abbrev PA (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) : Module.End ℂ ((κ → AF F) → ℂ) := Pm (evA κ v) (inA κ v) φ y

theorem putA_fst (x : κ → AF F) (y : κ → Fv F v) (i : κ) : (putA v x y i).1 = (x i).1 := by
  change (x i).1 - 0 + 0 = _
  simp

theorem putA_snd (x : κ → AF F) (y : κ → Fv F v) :
    (fun i => (putA v x y i).2) = put (evF κ v) (inF κ v) (fun i => (x i).2) y := rfl

theorem PA_pureA (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → Af F) → ℂ) : PA v φ y (pureA F f g) = pureA F f (Pm (evF κ v) (inF κ v) φ y g) := by
  funext x
  simp only [Pm_apply, pureA, putA_fst, putA_snd]
  exact mul_left_comm _ _ _

theorem at_inA (y : κ → Fv F v) : At (evFin F v) (inA κ v y) :=
  GlobalTheory.VacAny.at_pi fun i => GlobalTheory.VacAny.at_atPlace (y i)

theorem inA_evA {z : κ → AF F} (hz : At (evFin F v) z) : inA κ v (evA κ v z) = z :=
  funext fun i => (GlobalTheory.SchrLoc.eq_atPlace_of_at (fun u hu => congrFun (hz u hu) i)).symm

theorem putA_add {z : κ → AF F} (hz : At (evFin F v) z) (x : κ → AF F) (y : κ → Fv F v) :
    putA v (x + z) y = putA v x y := by
  rw [putA, put, map_add, map_add, inA_evA v hz, putA, put]; abel

theorem inv_putA {r : (κ → AF F) → ℂ} (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (x : κ → AF F)
    (y : κ → Fv F v) : r (putA v x y) = r x := by
  rw [putA, put, hr _ _ (at_inA v y), sub_eq_add_neg, ← map_neg, hr _ _ (at_inA v _)]

theorem PA_tens {r : (κ → AF F) → ℂ} (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (φ φ₁ : (κ → Fv F v) → ℂ)
    (y : κ → Fv F v) : PA v φ y (tens (evFin F v) φ₁ r) = φ₁ y • tens (evFin F v) φ r := by
  funext x
  change φ (evA κ v x) * (φ₁ (evA κ v (putA v x y)) * r (putA v x y)) = φ₁ y * (φ (evA κ v x) * r x)
  rw [ev_put (evA_inA v), inv_putA v hr, mul_left_comm]

def pureL (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : ((κ → Af F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun := pureA F f
  map_add' g g' := by funext x; simp [pureA, mul_add]
  map_smul' c g := by funext x; simp [pureA, mul_left_comm]

variable [Fintype κ]

theorem pureA_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

omit [Fintype κ] in
theorem PF_mem {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (y : κ → Fv F v) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) :
    Pm (evF κ v) (inF κ v) φ y g ∈ SB _ :=
  Pm_mem_SB (evF_inF v) (continuous_evF v) (continuous_inF v) hφ y hg

theorem PA_mem {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (y : κ → Fv F v) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    PA v φ y Φ ∈ schA F κ := by
  refine (Submodule.span_le (p := (schA F κ).comap (PA v φ y))).2 ?_ hΦ
  rintro _ ⟨f, g, hg, rfl⟩
  change PA v φ y _ ∈ schA F κ
  rw [PA_pureA]
  exact pureA_mem f (PF_mem v hφ y hg)

theorem PA_adm {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (y : κ → Fv F v) {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (hl : l ∈ (adeleClass F).adm κ) : l ∘ₗ PA v φ y ∈ (adeleClass F).adm κ := fun g hg => by
  obtain ⟨T, hT⟩ := hl _ (PF_mem v hφ y hg)
  exact ⟨T, fun f => by rw [LinearMap.comp_apply, PA_pureA, hT]⟩

theorem schA_le (N : Submodule ℂ ((κ → AF F) → ℂ))
    (h : ∀ φ ∈ SB (κ → Fv F v), ∀ y, ∀ Ψ ∈ schA F κ, PA v φ y Ψ ∈ N) : schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  refine (Submodule.span_le (p := N.comap (pureL f))).2 ?_
    (mem_span_Pm (evF_inF v) (continuous_evF v) (continuous_inF v) hg)
  rintro _ ⟨φ, hφ, y, rfl⟩
  have := h φ hφ y _ (pureA_mem f hg)
  rwa [PA_pureA] at this

theorem admissible_of_integral_conj_le (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ φ ∈ SB (κ → Fv F v), ∀ y, l ∘ₗ PA v φ y ∈ (adeleClass F).adm κ) : l ∈ (adeleClass F).adm κ := by
  intro g hg
  have hs := mem_span_Pm (evF_inF v) (continuous_evF v) (continuous_inF v) hg
  refine Submodule.span_induction (p := fun g' _ => ∃ T : SInf F κ →L[ℂ] ℂ, ∀ f : SInf F κ, l (pureA F f g') = T f)
    ?_ ⟨0, fun f => ?_⟩ ?_ ?_ hs
  · rintro _ ⟨φ, hφ, y, rfl⟩
    obtain ⟨T, hT⟩ := h φ hφ y g hg
    exact ⟨T, fun f => by rw [← hT, LinearMap.comp_apply, PA_pureA]⟩
  · exact map_zero (l ∘ₗ pureL f)
  · rintro a b - - ⟨T, hT⟩ ⟨T', hT'⟩
    exact ⟨T + T', fun f => (map_add (l ∘ₗ pureL f) a b).trans (congrArg₂ (· + ·) (hT f) (hT' f))⟩
  · rintro c a - ⟨T, hT⟩
    exact ⟨c • T, fun f => (map_smul (l ∘ₗ pureL f) c a).trans (congrArg (c • ·) (hT f))⟩

def res (x₀ : κ → AF F) : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ where
  toFun Φ y := Φ (putA v x₀ y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_mem (x₀ : κ → AF F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : res v x₀ Φ ∈ SB _ := by
  refine schA_le v ((SB _).comap (res v x₀)) (fun φ hφ y Ψ _ => ?_) hΦ
  have : res v x₀ (PA v φ y Ψ) = Ψ (putA v x₀ y) • φ := by
    funext z
    change φ (evA κ v (putA v x₀ z)) * Ψ (putA v (putA v x₀ z) y) = _
    rw [ev_put (evA_inA v), putA, putA, put_put (evA_inA v), mul_comm]; rfl
  rw [Submodule.mem_comap, this]
  exact Submodule.smul_mem _ _ hφ

open Classical in
theorem res_adm (x₀ : κ → AF F) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : l ∘ₗ res v x₀ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨l (fun y => g (put (evF κ v) (inF κ v) (fun i => (x₀ i).2) y)) •
    (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  have : res v x₀ (pureA F f g) = f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x₀ i).1) •
      fun y => g (put (evF κ v) (inF κ v) (fun i => (x₀ i).2) y) := by
    funext y
    change pureA F f g (putA v x₀ y) = _
    simp only [pureA, putA_fst, putA_snd]
    rfl
  rw [LinearMap.comp_apply, this, map_smul, smul_eq_mul, mul_comm]
  rfl

def tensL (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun φ := tens (evFin F v) φ r
  map_add' g g' := by funext x; simp [tens, add_mul]
  map_smul' c g := by funext x; simp [tens, mul_assoc]

variable (κ) in
theorem exists_base : ∃ (r₀ : (κ → AF F) → ℂ) (x₀ : κ → AF F), (∀ φ ∈ SB _, Rest (evFin F v) φ r₀) ∧ r₀ x₀ = 1 := by
  obtain ⟨Φ, hΦ, hne⟩ := (GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ).2.2
  obtain ⟨x₀, hx⟩ : ∃ x₀, Φ x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by simp [thetaSum, h])
  refine ⟨fun x => ((Φ x₀)⁻¹ • Φ) (putA v x (evA κ v x₀)), x₀, fun φ hφ => ⟨fun x z hz => ?_, ?_⟩, ?_⟩
  · simp only [putA_add v hz]
  · exact PA_mem v hφ (evA κ v x₀) (Submodule.smul_mem _ _ hΦ)
  · simp only [putA, put_self, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hx

theorem eq_of_acts {r₀ : (κ → AF F) → ℂ} {x₀ : κ → AF F} (h₁ : r₀ x₀ = 1)
    {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ : (κ → Fv F v) → ℂ} (h₀ : Rest (evFin F v) φ r₀)
    (h : Acts (evFin F v) T φ φ₁) : φ₁ = res v x₀ (T (tens (evFin F v) φ r₀)) := by
  funext y
  rw [h r₀ h₀]
  change _ = φ₁ (evA κ v (putA v x₀ y)) * r₀ (putA v x₀ y)
  rw [ev_put (evA_inA v), inv_putA v h₀.1, h₁, mul_one]

def Sop (T : Module.End ℂ ((κ → AF F) → ℂ)) (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) :
    Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ x := T (PA v φ (evA κ v x) Φ) (putA v x y)
  map_add' a b := by funext x; rw [map_add, map_add]; rfl
  map_smul' c a := by funext x; rw [map_smul, map_smul]; rfl

omit [Fintype κ] in
theorem Sop_PA (T : Module.End ℂ ((κ → AF F) → ℂ)) (φ φ₁ : (κ → Fv F v) → ℂ) (y y₁ : κ → Fv F v)
    (Ψ : (κ → AF F) → ℂ) : Sop v T φ y (PA v φ₁ y₁ Ψ) = PA v φ₁ y (T (PA v φ y₁ Ψ)) := by
  funext x
  change T (PA v φ (evA κ v x) (PA v φ₁ y₁ Ψ)) (putA v x y) = _
  rw [Pm_Pm (evA_inA v), map_smul]
  rfl

omit [Fintype κ] in
theorem putA_apply (x : κ → AF F) (y : κ → Fv F v) (i : κ) :
    putA v x y i = x i - atPlace v 1 * x i + atPlace v (y i) := by
  rw [atPlace_mul_right, one_mul]; rfl

theorem idem_at (t : Fv F v) : atPlace v 1 * atPlace v t = atPlace v t := by
  rw [atPlace_mul_right, evFin_atPlace, one_mul]

theorem dot₁ (z w : κ → AF F) (a : κ → Fv F v) : putA v z a ⬝ᵥ w = z ⬝ᵥ putA v w 0 + inA κ v a ⬝ᵥ w := by
  simp only [dotProduct, ← Finset.sum_add_distrib, putA_apply, Pi.zero_apply, map_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = _ + atPlace v (a i) * w i
  ring

theorem dot₂ (x w : κ → AF F) (y : κ → Fv F v) :
    inA κ v (evA κ v x) ⬝ᵥ w + putA v x y ⬝ᵥ putA v w 0 = x ⬝ᵥ w := by
  simp only [dotProduct, ← Finset.sum_add_distrib, putA_apply, Pi.zero_apply, map_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : inA κ v (evA κ v x) i = atPlace v 1 * x i := by rw [atPlace_mul_right, one_mul]; rfl
  rw [e]
  linear_combination (x i * w i) * idem_at v 1 - w i * idem_at v (y i)

theorem PA_schr (ψ : AddChar (AF F) ℂ) (φ : (κ → Fv F v) → ℂ) (a : κ → Fv F v) (w : (κ → AF F) × (κ → AF F))
    (Φ : (κ → AF F) → ℂ) : PA v φ a (schr ψ w Φ) =
      ψ (inA κ v a ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2 - putA v w.1 0 ⬝ᵥ putA v w.2 0)) •
        schr ψ (putA v w.1 0, putA v w.2 0) (PA v φ (a + evA κ v w.1) Φ) := by
  funext z
  have e1 : evA κ v (z + putA v w.1 0) = evA κ v z := by rw [map_add, ev_put (evA_inA v), add_zero]
  have e2 : putA v (z + putA v w.1 0) (a + evA κ v w.1) = putA v z a + w.1 := by
    rw [putA, put, e1, putA, putA, put, put, map_add, map_zero]; abel
  change φ (evA κ v z) * (ψ (putA v z a ⬝ᵥ w.2 + _) * Φ (putA v z a + w.1)) =
    ψ _ * (ψ (z ⬝ᵥ putA v w.2 0 + ⅟(2 : AF F) * (putA v w.1 0 ⬝ᵥ putA v w.2 0)) *
      (φ (evA κ v (z + putA v w.1 0)) * Φ (putA v (z + putA v w.1 0) (a + evA κ v w.1))))
  rw [e1, e2, ← mul_assoc (ψ _), ← AddChar.map_add_eq_mul, mul_left_comm, dot₁]
  congr 2
  ring

section Main

variable {ψ : AddChar (AF F) ℂ} {T : Module.End ℂ ((κ → AF F) → ℂ)}

theorem Sop_schr (hc : ∀ w : (κ → AF F) × (κ → AF F), evA κ v w.1 = 0 → evA κ v w.2 = 0 →
      ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ w (T Φ)) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (y : κ → Fv F v)
    (w : (κ → AF F) × (κ → AF F)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Sop v T φ y (schr ψ w Φ) = schr ψ w (Sop v T φ y Φ) := by
  funext x
  have e2 : putA v (x + w.1) y = putA v x y + putA v w.1 0 := by
    simp only [putA, put, map_add, map_zero]; abel
  change T (PA v φ (evA κ v x) (schr ψ w Φ)) (putA v x y) =
    ψ (x ⬝ᵥ w.2 + _) * T (PA v φ (evA κ v (x + w.1)) Φ) (putA v (x + w.1) y)
  rw [PA_schr, map_smul, hc _ (ev_put (evA_inA v) _ _) (ev_put (evA_inA v) _ _) _ (PA_mem v hφ _ hΦ), e2,
    map_add (evA κ v) x]
  change ψ _ * (ψ (putA v x y ⬝ᵥ putA v w.2 0 + ⅟(2 : AF F) * (putA v w.1 0 ⬝ᵥ putA v w.2 0)) * _) = _
  rw [← mul_assoc (ψ _), ← AddChar.map_add_eq_mul, ← dot₂ v x w.2 y]
  congr 2
  ring

theorem acts_res (h1 : Continuous ψ) (h2 : ψ ≠ 1) (h3 : ∀ a : F, ψ (algebraMap F (AF F) a) = 1)
    (hp : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (ha : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (hc : ∀ w : (κ → AF F) × (κ → AF F), evA κ v w.1 = 0 → evA κ v w.2 = 0 →
      ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ w (T Φ))
    {r₀ : (κ → AF F) → ℂ} {x₀ : κ → AF F} (h₁ : r₀ x₀ = 1) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _)
    (h₀ : Rest (evFin F v) φ r₀) : Acts (evFin F v) T φ (res v x₀ (T (tens (evFin F v) φ r₀))) := by
  by_cases h0 : φ = 0
  · intro r _
    have e : ∀ r, tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 := fun r => map_zero (tensL v r)
    simp only [h0, e, map_zero]
  obtain ⟨b, hb⟩ := Function.ne_iff.1 h0
  have key : ∀ y, ∃ a : ℂ, ∀ r, Rest (evFin F v) φ r → ∀ x, T (tens (evFin F v) φ r) (putA v x y) = a * r x := by
    intro y
    obtain ⟨a, hA⟩ := GlobalTheory.CompanionTheory.AdelicSchur.schur F κ ψ h1 h2 h3 (Sop v T φ y)
      (fun Φ hΦ => schA_le v ((schA F κ).comap (Sop v T φ y)) (fun φ₁ hφ₁ y₁ Ψ hΨ => by
        rw [Submodule.mem_comap, Sop_PA]
        exact PA_mem v hφ₁ _ (hp _ (PA_mem v hφ _ hΨ))) hΦ)
      (fun l hl => admissible_of_integral_conj_le v _ fun φ₁ hφ₁ y₁ => by
        rw [show (l ∘ₗ Sop v T φ y) ∘ₗ PA v φ₁ y₁ = ((l ∘ₗ PA v φ₁ y) ∘ₗ T) ∘ₗ PA v φ y₁ from
          LinearMap.ext fun Ψ => congrArg l (Sop_PA v T φ φ₁ y y₁ Ψ)]
        exact PA_adm v hφ _ (ha _ (PA_adm v hφ₁ _ hl)))
      (fun w Φ hΦ => Sop_schr v hc hφ y w hΦ)
    refine ⟨a, fun r hr x => ?_⟩
    have := congrFun (hA _ hr.2) (putA v x b)
    change T (PA v φ (evA κ v (putA v x b)) (tens (evFin F v) φ r)) (putA v (putA v x b) y) =
      a * (φ (evA κ v (putA v x b)) * r (putA v x b)) at this
    rw [ev_put (evA_inA v), PA_tens v hr.1, map_smul, inv_putA v hr.1, putA, putA, put_put (evA_inA v),
      mul_left_comm] at this
    exact mul_left_cancel₀ hb this
  intro r hr
  funext x
  obtain ⟨a, hA⟩ := key (evA κ v x)
  change _ = T (tens (evFin F v) φ r₀) (putA v x₀ (evA κ v x)) * r x
  rw [hA r₀ h₀, h₁, mul_one, ← hA r hr, putA, put_self]

end Main

end PositivityTheory.ThKH.Locrep
