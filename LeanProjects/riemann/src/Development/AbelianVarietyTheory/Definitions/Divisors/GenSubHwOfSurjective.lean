import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjoint

noncomputable section

namespace GlobalTheory.ThK.RealK

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.OneParam GlobalTheory.ThK.DescB

section Alg

variable {R S : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def isoPart (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (Λ : Ix R S → ℚ) : Submodule ℂ V :=
  sInf {N | hwSub act Λ ≤ N ∧ KStable act N}

theorem mem_wtSub {act : Mat R S →ₗ[ℂ] Module.End ℂ V} {μ : Ix R S → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = (μ a : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem mem_hwSub {act : Mat R S →ₗ[ℂ] Module.End ℂ V} {μ : Ix R S → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = (μ a : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, mem_wtSub, Submodule.mem_iInf]

theorem hwSub_le_isoPart (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (Λ : Ix R S → ℚ) : hwSub act Λ ≤ isoPart act Λ :=
  le_sInf fun _ h => h.1

theorem subset_genSub (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (T : Set V) : T ⊆ genSub act T :=
  fun _ hv => Submodule.mem_sInf.2 fun _ hN => hN.1 hv

theorem act_mem_genSub (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (T : Set V) (Z : Mat R S) {v : V} (hv : v ∈ genSub act T) :
    act Z v ∈ genSub act T :=
  Submodule.mem_sInf.2 fun N hN => hN.2 Z _ (Submodule.mem_sInf.1 hv N hN)

theorem genSub_le {act : Mat R S →ₗ[ℂ] Module.End ℂ V} {T : Set V} {N : Submodule ℂ V} (hT : T ⊆ N)
    (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act T ≤ N := sInf_le ⟨hT, hN⟩

theorem genSub_isoPart (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (Λ : Ix R S → ℚ) :
    genSub act (isoPart act Λ) = genSub act (hwSub act Λ) :=
  le_antisymm (genSub_le (sInf_le (a := genSub act (hwSub act Λ))
      ⟨subset_genSub act _, fun X _ _ h => act_mem_genSub act _ X h⟩) fun Z _ h => act_mem_genSub act _ Z h)
    (genSub_le (fun _ h => subset_genSub act _ (hwSub_le_isoPart act Λ h)) fun Z _ h => act_mem_genSub act _ Z h)

variable {a : Mat R S →ₗ[ℂ] Module.End ℂ V} {b : Mat R S →ₗ[ℂ] Module.End ℂ W} {π : V →ₗ[ℂ] W}

theorem map_mem_wtSub (h : ∀ X v, b X (π v) = π (a X v)) {μ : Ix R S → ℚ} {v : V} (hv : v ∈ wtSub a μ) :
    π v ∈ wtSub b μ := mem_wtSub.2 fun c => by rw [h, mem_wtSub.1 hv c, map_smul]

theorem map_mem_hwSub (h : ∀ X v, b X (π v) = π (a X v)) {μ : Ix R S → ℚ} {v : V} (hv : v ∈ hwSub a μ) :
    π v ∈ hwSub b μ :=
  mem_hwSub.2 ⟨fun c => by rw [h, (mem_hwSub.1 hv).1 c, map_smul],
    fun c d hcd => by rw [h, (mem_hwSub.1 hv).2 c d hcd, map_zero]⟩

theorem genSub_hw_of_surjective (hπ : Function.Surjective π) (h : ∀ X v, b X (π v) = π (a X v)) {Λ : Ix R S → ℚ}
    (hg : genSub a (hwSub a Λ) = ⊤) : genSub b (hwSub b Λ) = ⊤ := by
  have : genSub a (hwSub a Λ) ≤ (genSub b (hwSub b Λ)).comap π :=
    genSub_le (fun v hv => subset_genSub b _ (map_mem_hwSub h hv)) fun Z y hy => by
      rw [Submodule.mem_comap, ← h]; exact act_mem_genSub b _ Z hy
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨v, rfl⟩ := hπ y
  exact this (hg ▸ Submodule.mem_top)

theorem exists_upq_add (Z : Mat R S) : ∃ X ∈ upq R S, ∃ Y ∈ upq R S, Z = X + Complex.I • Y := by
  open GlobalTheory.RealPar.DerivedAdjoint in
  refine ⟨(1 / 2 : ℂ) • (Z - adjZ Z), mem_upq_of_adjZ ?_, (-Complex.I / 2) • (Z + adjZ Z), mem_upq_of_adjZ ?_, ?_⟩
  · rw [adjZ_smul, adjZ_sub, adjZ_adjZ, show star (1 / 2 : ℂ) = 1 / 2 by simp]
    module
  · rw [adjZ_smul, adjZ_add, adjZ_adjZ, show star (-Complex.I / 2) = Complex.I / 2 by simp]
    module
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
    module

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n R S : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

def rT (h : UA σ J) : (UA σ J → ℂ) →ₗ[ℂ] (UA σ J → ℂ) := LinearMap.funLeft ℂ ℂ (· * h)

@[simp] theorem rT_apply (h : UA σ J) (f : UA σ J → ℂ) (g : UA σ J) : rT h f g = f (g * h) := rfl

def cmp {w : InfinitePlace F} (τ : EmbOver E w) (g : UA σ J) : Matrix (Fin n) (Fin n) ℂ := (mat g).map (piInf τ)

theorem cmp_mul {w : InfinitePlace F} (τ : EmbOver E w) (g h : UA σ J) : cmp τ (g * h) = cmp τ g * cmp τ h :=
  Matrix.map_mul

theorem cmp_one {w : InfinitePlace F} (τ : EmbOver E w) : cmp τ (1 : UA σ J) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def herm (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (τ : EmbOver E w) : Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • J.map τ.1

theorem incM_map {m k : Type} (A : Matrix m k E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F A).map (piInf τ) = A.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

variable (τ : ∀ w : InfinitePlace F, EmbOver E w) (w : InfinitePlace F)

variable (σ J) in

def GAt : Set (UA σ J) := {g | At (evI F) (mat g - 1) ∧ ∀ w', w' ≠ w → cmp (τ w') g = 1}

variable (σ J) in

def LinesAt : Set (Multiplicative ℝ →* UA σ J) := {γ | Continuous γ ∧ ∀ t, γ t ∈ GAt σ J τ w}

def HasRDer (γ : Multiplicative ℝ →* UA σ J) (f f' : UA σ J → ℂ) : Prop :=
  ∀ g, HasDerivAt (fun t : ℝ => f (g * γ (Multiplicative.ofAdd t))) (f' g) 0

variable (σ J) in

def SmoothAt (f : UA σ J → ℂ) : Prop :=
  ∃ T : Submodule ℂ (UA σ J → ℂ), f ∈ T ∧ ∀ φ ∈ T, ∀ γ ∈ LinesAt σ J τ w, ∃ φ' ∈ T, HasRDer γ φ φ'

variable {w} in

def IsGenAt (τ : EmbOver E w) (C : Matrix (Fin n) (Ix R S) ℂ) (γ : Multiplicative ℝ →* UA σ J) (X : Mat R S) : Prop :=
  ∀ t : ℝ, cmp τ (γ (Multiplicative.ofAdd t)) * C = C * NormedSpace.exp (t • X)

variable (σ) in

def KAt (Y : Spc F E n) : Set (UA σ Y.J) := {k | k ∈ GAt σ Y.J τ w ∧ Commute (cmp (τ w) k) (Y.θ w)}

def TAt (C : Matrix (Fin n) (Ix R S) ℂ) : Set (UA σ J) :=
  {k | k ∈ GAt σ J τ w ∧ ∃ d : Ix R S → ℂ, cmp (τ w) k * C = C * Matrix.diagonal d}

def IsAdapted (Y : Spc F E n) (C : Matrix (Fin n) (Ix R S) ℂ) : Prop :=
  IsFrame (herm Y.J (τ w)) C ∧ Y.θ w * C = C * Jm R S

def IsRightAct (C : Matrix (Fin n) (Ix R S) ℂ) (T : Submodule ℂ (UA σ J → ℂ)) (act : Mat R S →ₗ[ℂ] Module.End ℂ T) : Prop :=
  ∀ γ ∈ LinesAt σ J τ w, ∀ X, IsGenAt (τ w) C γ X → ∀ f : T, HasRDer γ (f : UA σ J → ℂ) (act X f : T)

structure IsGKAt (C : Matrix (Fin n) (Ix R S) ℂ) (T : Submodule ℂ (UA σ J → ℂ)) (act : Mat R S →ₗ[ℂ] Module.End ℂ T) :
    Prop where
  frame : IsFrame (herm J (τ w)) C
  der : IsRightAct τ w C T act
  lie : IsLieAct act
  kfin : ∀ v, ∃ W : Submodule ℂ T, FiniteDimensional ℂ W ∧ v ∈ W ∧ KStable act W
  wts : ∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub act μ

def Stable (Y : Spc F E n) (C : Matrix (Fin n) (Ix R S) ℂ) (T : Submodule ℂ (UA σ Y.J → ℂ)) : Prop :=
  IsAdapted τ w Y C ∧ (∀ h ∈ finK σ Y τ, ∀ f ∈ T, rT h f ∈ T) ∧ ∃ act, IsGKAt τ w C T act

def GenBy (C : Matrix (Fin n) (Ix R S) ℂ) (T : Submodule ℂ (UA σ J → ℂ)) (Λ : Ix R S → ℚ) : Prop :=
  ∃ act, IsGKAt τ w C T act ∧ genSub act (isoPart act Λ) = ⊤

variable (σ) in

def IsKFinAt (Y : Spc F E n) (f : UA σ Y.J → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {φ | ∃ k ∈ KAt σ τ w Y, φ = rT k f})

def isoK (Y : Spc F E n) {T : Submodule ℂ (UA σ Y.J → ℂ)} (act : Mat R S →ₗ[ℂ] Module.End ℂ T) (Λ : Ix R S → ℚ) :
    Submodule ℂ (UA σ Y.J → ℂ) :=
  Submodule.span ℂ {φ | ∃ k ∈ KAt σ τ w Y, ∃ v ∈ hwSub act Λ, φ = rT k (v : UA σ Y.J → ℂ)}

variable {τ w} {C : Matrix (Fin n) (Ix R S) ℂ} {T : Submodule ℂ (UA σ J → ℂ)}

def IsGKAt.toGKMod {act : Mat R S →ₗ[ℂ] Module.End ℂ T} (h : IsGKAt τ w C T act) : GKMod R S where
  V := T
  act := act
  lie := h.lie
  kfin := h.kfin
  wts := h.wts

theorem genBy_iff_hw {Λ : Ix R S → ℚ} :
    GenBy τ w C T Λ ↔ ∃ act, IsGKAt τ w C T act ∧ genSub act (hwSub act Λ) = ⊤ := by
  simp only [GenBy, genSub_isoPart]

theorem HasRDer.unique {γ : Multiplicative ℝ →* UA σ J} {f f₁ f₂ : UA σ J → ℂ} (h₁ : HasRDer γ f f₁) (h₂ : HasRDer γ f f₂) :
    f₁ = f₂ := funext fun g => (h₁ g).unique (h₂ g)

open Classical in

def liftAt [IsTotallyReal F] (τ : ∀ w : InfinitePlace F, EmbOver E w) (w : InfinitePlace F) (ξ : E)
    (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (AE F E) := 1 + liftM τ ξ (Pi.single w (G - 1))

open Classical in

theorem liftAt_map [IsTotallyReal F] {ξ : E} (hξ : ∀ w, ((τ w).1 ξ).im ≠ 0) (G : Matrix (Fin n) (Fin n) ℂ)
    (w' : InfinitePlace F) : (liftAt τ w ξ G).map (piInf (τ w')) = if w' = w then G else 1 := by
  rw [liftAt, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ]
  split_ifs with e
  · subst e; rw [Pi.single_eq_same, add_sub_cancel]
  · rw [Pi.single_eq_of_ne e, add_zero]

theorem at_liftAt [IsTotallyReal F] (ξ : E) (G : Matrix (Fin n) (Fin n) ℂ) : At (evI F) (liftAt τ w ξ G - 1) := by
  rw [liftAt, add_sub_cancel_left]
  exact at_liftM τ ξ _

theorem map_cA_map (hCM : IsCMExt F E σ) (τ : EmbOver E w) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    (A.map (cA σ)).map (piInf τ) = (A.map (piInf τ)).map star := by
  rw [Matrix.map_map, Matrix.map_map]
  congr 1
  funext z
  exact piInf_cA hCM τ z

theorem exists_lift (hCM : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (w : InfinitePlace F)
    (J : Matrix (Fin n) (Fin n) E) : ∃ L : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) (AE F E), Continuous L ∧ L 1 = 1 ∧
      (∀ G H, L (G * H) = L G * L H) ∧ (∀ G, At (evI F) (L G - 1)) ∧ (∀ G, (L G).map (piInf (τ w)) = G) ∧
      (∀ G w', w' ≠ w → (L G).map (piInf (τ w')) = 1) ∧
      ∀ G, Gᵀ * herm J (τ w) * G.map star = herm J (τ w) → (L G)ᵀ * incM F J * (L G).map (cA σ) = incM F J := by
  classical
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine ⟨liftAt τ w ξ, continuous_const.add ((continuous_liftM τ ξ).comp ((continuous_single w).comp
    (continuous_id.sub continuous_const))), ?_, fun G H => ?_, at_liftAt ξ, fun G => by rw [liftAt_map hξ', if_pos rfl],
    fun G w' e => by rw [liftAt_map hξ', if_neg e], fun G hG => ?_⟩
  · refine eq_of_at hCM τ (at_liftAt ξ 1) fun w' => ?_
    rw [liftAt_map hξ', ite_self, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine (eq_of_at hCM τ ?_ fun w' => ?_).symm
    · have e : liftAt τ w ξ G * liftAt τ w ξ H - liftAt τ w ξ (G * H) =
          (liftAt τ w ξ G - 1) * liftAt τ w ξ H + (liftAt τ w ξ H - 1) - (liftAt τ w ξ (G * H) - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (at_liftAt ξ G) _) (at_liftAt ξ H)) (at_liftAt ξ _)
    · rw [Matrix.map_mul, liftAt_map hξ', liftAt_map hξ', liftAt_map hξ']
      split_ifs <;> simp
  · set f := liftAt τ w ξ G with hf
    have hfat : At (evI F) (f - 1) := at_liftAt ξ G
    refine eq_of_at hCM τ ?_ fun w' => ?_
    · have e : fᵀ * incM F J * f.map (cA σ) - incM F J = (f - 1)ᵀ * incM F J * f.map (cA σ) + incM F J * (f - 1).map (cA σ) := by
        have e1 : (f - 1).map (cA σ) = f.map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose hfat) _) _) (at_mul_left (at_map_cA σ hfat) _)
    · rw [Matrix.map_mul, Matrix.map_mul, map_cA_map hCM, Matrix.transpose_map, hf, liftAt_map hξ', incM_map]
      split_ifs with e
      · subst e
        rw [herm, Matrix.mul_smul, Matrix.smul_mul] at hG
        exact smul_right_injective _ Complex.I_ne_zero hG
      · rw [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (by simp) (by simp), Matrix.mul_one]

theorem exists_lineAt (hCM : IsCMExt F E σ) (hC : IsFrame (herm J (τ w)) C) {X : Mat R S} (hX : X ∈ upq R S) :
    ∃ γ ∈ LinesAt σ J τ w, IsGenAt (τ w) C γ X := by
  obtain ⟨L, hc, h1, hm, hat, hw, hw', hu⟩ := exists_lift hCM τ w J
  obtain ⟨hF, C', hC'⟩ := hC
  have hL : C' * C = 1 := frame_inv hF hC'
  set f : ℝ → Matrix (Fin n) (Fin n) (AE F E) := fun t => L (C * NormedSpace.exp (t • X) * C') with hf
  have hfadd : ∀ s t, f (s + t) = f s * f t := fun s t => by simp only [hf]; rw [conj_add hL, hm]
  have hf0 : f 0 = 1 := by simp only [hf]; rw [conj_zero hC', h1]
  have hfc : Continuous f := hc.comp ((continuous_const.matrix_mul (continuous_exp_smul X)).matrix_mul continuous_const)
  let g : ℝ → UA σ J := fun t => ⟨⟨f t, f (-t), by rw [← hfadd, add_neg_cancel, hf0],
    by rw [← hfadd, neg_add_cancel, hf0]⟩, hu _ (conj_unitary hF hC' hX t)⟩
  let γ : Multiplicative ℝ →* UA σ J :=
    { toFun := fun t => g (Multiplicative.toAdd t)
      map_one' := Subtype.ext (Units.ext hf0)
      map_mul' := fun x y => Subtype.ext (Units.ext (hfadd _ _)) }
  refine ⟨γ, ⟨?_, fun t => ⟨hat _, hw' _⟩⟩, fun t => ?_⟩
  · have hu : Continuous fun t : Multiplicative ℝ => ((g (Multiplicative.toAdd t)).1 : GL (Fin n) (AE F E)) :=
      Units.continuous_iff.2 ⟨hfc.comp continuous_toAdd, (hfc.comp continuous_neg).comp continuous_toAdd⟩
    exact hu.subtype_mk _
  · change (f t).map (piInf (τ w)) * C = _
    rw [hf, hw, Matrix.mul_assoc, hL, Matrix.mul_one]

theorem IsRightAct.unique (hCM : IsCMExt F E σ) (hC : IsFrame (herm J (τ w)) C) {a b : Mat R S →ₗ[ℂ] Module.End ℂ T}
    (ha : IsRightAct τ w C T a) (hb : IsRightAct τ w C T b) : a = b := by
  have key : ∀ X ∈ upq R S, a X = b X := fun X hX => by
    obtain ⟨γ, hγ, h⟩ := exists_lineAt hCM hC hX
    exact LinearMap.ext fun f => Subtype.ext ((ha γ hγ X h f).unique (hb γ hγ X h f))
  refine LinearMap.ext fun Z => ?_
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_upq_add Z
  rw [map_add, map_add, map_smul, map_smul, key X hX, key Y hY]

theorem exists_isGKAt_range (hCM : IsCMExt F E σ) (hC : IsFrame (herm J (τ w)) C) (M : GKMod R S)
    (φ : M.V →ₗ[ℂ] (UA σ J → ℂ))
    (hφ : ∀ γ ∈ LinesAt σ J τ w, ∀ X, IsGenAt (τ w) C γ X → ∀ v, HasRDer γ (φ v) (φ (M.act X v))) :
    ∃ act, IsGKAt τ w C (LinearMap.range φ) act ∧ ∀ X v, act X (φ.rangeRestrict v) = φ.rangeRestrict (M.act X v) := by
  have hker : ∀ Z v, φ v = 0 → φ (M.act Z v) = 0 := fun Z v hv => by
    have key : ∀ X ∈ upq R S, φ (M.act X v) = 0 := fun X hX => by
      obtain ⟨γ, hγ, h⟩ := exists_lineAt hCM hC hX
      refine (hφ γ hγ X h v).unique fun g => ?_
      rw [hv]; exact hasDerivAt_const _ _
    obtain ⟨X, hX, Y, hY, rfl⟩ := exists_upq_add Z
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, key X hX, key Y hY, smul_zero,
      add_zero]
  have hs := φ.surjective_rangeRestrict
  obtain ⟨s, hs'⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective φ.range_rangeRestrict
  let act : Mat R S →ₗ[ℂ] Module.End ℂ (LinearMap.range φ) :=
    { toFun := fun X => φ.rangeRestrict ∘ₗ M.act X ∘ₗ s
      map_add' := fun X Y => by rw [map_add, LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun c X => by rw [map_smul, LinearMap.smul_comp, LinearMap.comp_smul]; rfl }
  have heq : ∀ X v, act X (φ.rangeRestrict v) = φ.rangeRestrict (M.act X v) := fun X v => by
    have h0 : φ (s (φ.rangeRestrict v) - v) = 0 := by
      rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val (LinearMap.congr_fun hs' (φ.rangeRestrict v))
    have h1 := hker X _ h0
    rw [map_sub, map_sub, sub_eq_zero] at h1
    exact Subtype.ext h1
  refine ⟨act, ⟨hC, fun γ hγ X hX f => ?_, fun X Y => LinearMap.ext fun f => ?_, fun f => ?_, fun f => ?_⟩, heq⟩
  all_goals obtain ⟨v, rfl⟩ := hs f
  · rw [heq]; exact hφ γ hγ X hX v
  · rw [heq, M.lie X Y]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, heq, map_sub]
  · obtain ⟨W, hW, hv, hK⟩ := M.kfin v
    refine ⟨W.map φ.rangeRestrict, inferInstance, Submodule.mem_map_of_mem hv, ?_⟩
    rintro X hX _ ⟨y, hy, rfl⟩
    rw [heq]; exact Submodule.mem_map_of_mem (hK X hX y hy)
  · have : (⨆ μ, wtSub M.act μ) ≤ (⨆ μ, wtSub act μ).comap φ.rangeRestrict :=
      iSup_le fun μ y hy => Submodule.mem_iSup_of_mem μ (map_mem_wtSub heq hy)
    exact this (M.wts v)

theorem genBy_range (hCM : IsCMExt F E σ) (hC : IsFrame (herm J (τ w)) C) (M : GKMod R S) (φ : M.V →ₗ[ℂ] (UA σ J → ℂ))
    (hφ : ∀ γ ∈ LinesAt σ J τ w, ∀ X, IsGenAt (τ w) C γ X → ∀ v, HasRDer γ (φ v) (φ (M.act X v))) {Λ : Ix R S → ℚ}
    (hΛ : genSub M.act (hwSub M.act Λ) = ⊤) : GenBy τ w C (LinearMap.range φ) Λ := by
  obtain ⟨act, h, e⟩ := exists_isGKAt_range hCM hC M φ hφ
  exact genBy_iff_hw.2 ⟨act, h, genSub_hw_of_surjective φ.surjective_rangeRestrict e hΛ⟩

def c₁ (a a' p q : ℕ) : ℚ := ((a : ℚ) + a' - 2 * (p + q)) / 2

def c₂ (a p : ℕ) : ℚ := ((a : ℚ) - 2 * p) / 2

def x₁ (a a' p q : ℕ) (κ : ℤ) : ℚ := (κ : ℚ) / 2 - c₁ a a' p q + c₂ a p

def x₂ (a p : ℕ) : ℚ := c₂ a p

def y₁ (a a' p q : ℕ) (κ : ℤ) : ℚ := (κ : ℚ) / 2 + c₁ a a' p q - c₂ a p

def y₂ (a p : ℕ) : ℚ := -c₂ a p

abbrev laC (R S a p i : ℕ) (κ : ℤ) : Ix R S → ℚ := lam (a - p - i) (p - i) R S κ

def laAt (B : Base F E) (w : InfinitePlace F) (R S a p i : ℕ) : Ix R S → ℚ :=
  fun c => laC R S a p i (B.mα w - B.mβ w) c + (B.mβ w : ℚ) / 2

section Entries

variable {a a' p q i j : ℕ} (κ : ℤ)

theorem cPair_eq_c₁ (hR : R + (p + q) + (i + j) = a + a') (hS : S + (i + j) = p + q) : cPair R S = c₁ a a' p q := by
  have h1 := congrArg (Nat.cast : ℕ → ℚ) hR
  have h2 := congrArg (Nat.cast : ℕ → ℚ) hS
  push_cast at h1 h2
  rw [cPair, c₁]; linear_combination (h1 - h2) / 2

theorem cPair_eq_c₂ (hi : i ≤ p) (ha : p + i ≤ a) : cPair (a - p - i) (p - i) = c₂ a p := by
  rw [cPair, c₂, Nat.sub_sub, Nat.cast_sub ha, Nat.cast_sub hi]; push_cast; ring

theorem x₂_lt_x₁ (hκ : ((a + a' : ℕ) : ℤ) < κ) (hy : 2 * (p + q) ≤ a + a') :
    x₂ a p < x₁ a a' p q κ ∧ y₂ a p < y₁ a a' p q κ := by
  have h1 : ((a : ℚ) + a') < κ := by exact_mod_cast hκ
  have h2 : 2 * ((p : ℚ) + q) ≤ a + a' := by exact_mod_cast hy
  have h3 : (0 : ℚ) ≤ p + q := by positivity
  constructor <;> simp only [x₁, y₁, x₂, y₂, c₁] <;> linarith

end Entries

example : (List.ofFn fun k : Fin 5 => laC 5 1 4 1 0 8 (.inl k)) = [3, 3, 3, 1, 1] ∧ laC 5 1 4 1 0 8 (.inr 0) = 5 := by
  simp [lam, cPair, List.ofFn_succ]; norm_num

def stdWt (c : Ix R S) : Ix R S → ℚ := fun d => if d = c then 1 else 0

theorem single_mem_wtSub (c : Ix R S) :
    Pi.single c (1 : ℂ) ∈ wtSub (Matrix.toLin' : Mat R S ≃ₗ[ℂ] _).toLinearMap (stdWt c) := mem_wtSub.2 fun d => by
  ext e
  by_cases h : d = c <;> simp [Eab, stdWt, h, Matrix.single_apply, Pi.single_apply, eq_comm]

variable (R S) in

abbrev stdMod : GKMod R S where
  V := Ix R S → ℂ
  act := (Matrix.toLin' : Mat R S ≃ₗ[ℂ] _).toLinearMap
  lie := fun X Y => by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]
  kfin := fun _ => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩
  wts := fun v => by
    rw [pi_eq_sum_univ' v]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem _ (single_mem_wtSub c))

theorem stdMod_gen : genSub (stdMod (R + 1) S).act (hwSub (stdMod (R + 1) S).act (stdWt (.inl 0))) = ⊤ := by
  have h0 : Pi.single (.inl 0) (1 : ℂ) ∈ hwSub (stdMod (R + 1) S).act (stdWt (.inl 0)) :=
    mem_hwSub.2 ⟨mem_wtSub.1 (single_mem_wtSub _), fun b c hbc => by
      have : c ≠ .inl 0 := by
        rintro rfl
        cases b <;> simp [posC] at hbc
      ext e
      simp [Eab, Matrix.single_apply, this]⟩
  refine eq_top_iff.2 fun v _ => ?_
  rw [pi_eq_sum_univ' v]
  refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
  have := act_mem_genSub _ _ (Eab c (.inl 0)) (subset_genSub (stdMod (R + 1) S).act _ h0)
  convert this using 1
  ext e
  simp [Eab, Matrix.single_apply, Pi.single_apply, eq_comm]

def coef (τ : EmbOver E w) (C : Matrix (Fin n) (Ix R S) ℂ) (i : Fin n) : (Ix R S → ℂ) →ₗ[ℂ] (UA σ J → ℂ) :=
  LinearMap.pi fun g => LinearMap.proj i ∘ₗ Matrix.toLin' (cmp τ g * C)

theorem coef_apply (τ : EmbOver E w) (i : Fin n) (v : Ix R S → ℂ) (g : UA σ J) :
    coef τ C i v g = ((cmp τ g * C) *ᵥ v) i := rfl

theorem hasRDer_coef (τ : EmbOver E w) (i : Fin n) {γ : Multiplicative ℝ →* UA σ J} {X : Mat R S} (hX : IsGenAt τ C γ X)
    (v : Ix R S → ℂ) : HasRDer γ (coef τ C i v) (coef τ C i (X *ᵥ v)) := fun g => by
  letI : NormedRing (Mat R S) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat R S) := Matrix.linftyOpNormedAlgebra
  let l : Mat R S →ₗ[ℝ] ℂ :=
    { toFun := fun A => ((cmp τ g * C) *ᵥ (A *ᵥ v)) i
      map_add' := fun A B => by simp [Matrix.add_mulVec, Matrix.mulVec_add]
      map_smul' := fun c A => by simp [Matrix.smul_mulVec, Matrix.mulVec_smul] }
  have h := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const X (0 : ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change ((cmp τ (g * _) * C) *ᵥ v) i = ((cmp τ g * C) *ᵥ (NormedSpace.exp (t • X) *ᵥ v)) i
  rw [cmp_mul, Matrix.mul_assoc, hX t, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem stable_genBy_coef (hCM : IsCMExt F E σ) {Y : Spc F E n} {C : Matrix (Fin n) (Ix (R + 1) S) ℂ}
    (hC : IsAdapted τ w Y C) (i : Fin n) : Stable τ w Y C (LinearMap.range (coef (σ := σ) (τ w) C i)) ∧
      GenBy τ w C (LinearMap.range (coef (σ := σ) (J := Y.J) (τ w) C i)) (stdWt (.inl 0)) := by
  have h := genBy_range (J := Y.J) hCM hC.1 (stdMod _ _) (coef (τ w) C i) (fun γ _ X hX v => hasRDer_coef _ i hX v) stdMod_gen
  refine ⟨⟨hC, ?_, h.imp fun _ h => h.1⟩, h⟩
  rintro k - _ ⟨v, rfl⟩
  obtain ⟨C', hC'⟩ := hC.1.2
  refine ⟨(C' * cmp (τ w) k * C) *ᵥ v, funext fun g => ?_⟩
  rw [rT_apply, coef_apply, coef_apply, cmp_mul, Matrix.mulVec_mulVec]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc C C', hC', Matrix.one_mul]

variable (F E) in

def hypPlane : Spc F E 2 := ⟨!![0, 1; -1, 0], ⊤, fun _ => !![0, -2 * Complex.I; Complex.I / 2, 0], fun _ => 1⟩

def hypFrame : Matrix (Fin 2) (Ix 1 1) ℂ :=
  Matrix.of fun r => Sum.elim (fun _ => ![1, Complex.I / 2] r) fun _ => ![1, -Complex.I / 2] r

theorem isAdapted_hyp : IsAdapted τ w (hypPlane F E) hypFrame := by
  refine ⟨⟨?_, Matrix.of (Sum.elim (fun _ => ![1 / 2, -Complex.I]) fun _ => ![1 / 2, Complex.I]), ?_⟩, ?_⟩
  · ext (b | b) (c | c) <;> rw [Subsingleton.elim b 0, Subsingleton.elim c 0] <;>
      simp [herm, hypPlane, hypFrame, Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat, Complex.ext_iff] <;> norm_num
  · ext r s
    fin_cases r <;> fin_cases s <;> simp [hypFrame, Matrix.mul_apply, Complex.ext_iff] <;> norm_num
  · ext r (c | c) <;> rw [Subsingleton.elim c 0] <;> fin_cases r <;>
      simp [hypPlane, hypFrame, Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

theorem exists_stable_hyp (hCM : IsCMExt F E σ) : ∃ T : Submodule ℂ (UA σ (hypPlane F E).J → ℂ),
    Stable τ w (hypPlane F E) hypFrame T ∧ GenBy τ w hypFrame T (stdWt (.inl 0)) ∧
      ∀ act, IsRightAct τ w hypFrame T act → act (Eab (.inr 0) (.inl 0)) ≠ 0 := by
  have h := stable_genBy_coef (R := 0) (τ := τ) (w := w) hCM isAdapted_hyp 0
  refine ⟨_, h.1, h.2, fun act ha h0 => ?_⟩
  obtain ⟨b, hb, e⟩ := exists_isGKAt_range (J := (hypPlane F E).J) hCM (isAdapted_hyp (τ := τ) (w := w)).1 (stdMod 1 1)
    (coef (τ w) hypFrame 0) fun γ _ X hX v => hasRDer_coef _ 0 hX v
  have e1 := e (Eab (.inr 0) (.inl 0)) (Pi.single (.inl 0) 1)
  rw [← IsRightAct.unique hCM hb.frame ha hb.der, h0] at e1
  have e2 : (0 : ℂ) = ((cmp (τ w) (1 : UA σ (hypPlane F E).J) * hypFrame) *ᵥ
      (Eab (.inr 0) (.inl 0) *ᵥ Pi.single (.inl 0) 1)) 0 := congrFun (congrArg Subtype.val e1) 1
  rw [cmp_one, Matrix.one_mul] at e2
  simp [Eab, hypFrame, Matrix.mulVec, dotProduct, Matrix.single_apply] at e2

example : ∃ (F E : Type) (_ : Field F) (_ : NumberField F) (_ : Field E) (_ : NumberField E) (_ : Algebra F E)
    (σ : E →ₐ[F] E) (τ : ∀ w : InfinitePlace F, EmbOver E w) (w : InfinitePlace F)
    (T : Submodule ℂ (UA σ (hypPlane F E).J → ℂ)), IsCMExt F E σ ∧ Stable τ w (hypPlane F E) hypFrame T ∧
      GenBy τ w hypFrame T (stdWt (.inl 0)) ∧ ∀ act, IsRightAct τ w hypFrame T act → act (Eab (.inr 0) (.inl 0)) ≠ 0 := by
  haveI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  haveI : IsCMField (CyclotomicField 3 ℚ) := IsCyclotomicExtension.Rat.isCMField _ (S := {3}) ⟨3, rfl, by norm_num⟩
  have hCM : IsCMExt (maximalRealSubfield (CyclotomicField 3 ℚ)) (CyclotomicField 3 ℚ)
      (IsCMField.complexConj (CyclotomicField 3 ℚ)).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj _ τ x⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield (CyclotomicField 3 ℚ))) := inferInstance
  obtain ⟨T, hT⟩ := exists_stable_hyp (τ := fun _ => Classical.arbitrary _) (w := w) hCM
  exact ⟨_, _, _, _, _, _, _, _, _, w, T, hCM, hT⟩

end GlobalTheory.ThK.RealK

end
