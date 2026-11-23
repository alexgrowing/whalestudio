import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousSmulSemi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCharacterSeminormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyFiniteDimSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSchwartzFiniteValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCharacterMinusOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticTraceBasisExistsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XTermDecay

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def coeL : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefFun (β : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ) : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun Φ y := β fun z => Φ fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (z i)
  map_add' Φ Φ' := funext fun _ => β.map_add _ _
  map_smul' a Φ := funext fun _ => β.map_smul a _

omit [Fintype κ] in
theorem slice_pureA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    (fun z : κ → Af F => pureA F f g fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (z i)) = f y • g := by
  funext z
  simp only [pureA, HeisSchA.mk, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]

theorem coefFun_pureA (β : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    coefFun β (pureA F f g) = coeL (β g • f) := by
  funext y
  change β _ = β g * f y
  rw [slice_pureA, map_smul, smul_eq_mul, mul_comm]

theorem coefFun_mem (β : ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ) : ∀ Φ ∈ schA F κ, coefFun β Φ ∈ LinearMap.range (coeL (F := F) (κ := κ)) := by
  have : schA F κ ≤ (LinearMap.range (coeL (F := F) (κ := κ))).comap (coefFun β) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, -, rfl⟩
    exact ⟨_, (coefFun_pureA β f g).symm⟩
  exact this

theorem slice_mem_SB (y : κ → mixedEmbedding.mixedSpace F) : ∀ Φ ∈ schA F κ,
    (fun z : κ → Af F => Φ fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (z i)) ∈ SB (κ → Af F) := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [slice_pureA]
    exact Submodule.smul_mem _ _ hg
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem exists_decomp {T : Type} (Ψ : T → (κ → AF F) → ℂ) (hΨ : ∀ t, Ψ t ∈ schA F κ)
    (hb : ∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) :
    ∃ (m : ℕ) (g : Fin m → (κ → Af F) → ℂ) (f : Fin m → T → SInf F κ), (∀ j, g j ∈ SB _) ∧
      (∀ t, Ψ t = ∑ j, pureA F (f j t) (g j)) ∧
      ∀ j (p : Seminorm ℂ (SInf F κ)), Continuous p → ∃ C : ℝ, ∀ t, p (f j t) ≤ C := by
  obtain ⟨W, hW, hsl⟩ := GlobalTheory.T.schwartz_family_finite_dim_span F κ T Ψ hΨ hb
  let W' : Submodule ℂ ((κ → Af F) → ℂ) := W ⊓ SB _
  haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_left
  let b := Module.finBasis ℂ W'
  choose β hβ using fun j => LinearMap.exists_extend (b.coord j)
  obtain ⟨r, hr⟩ := (coeL (F := F) (κ := κ)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
  have hr' : ∀ f, r (coeL f) = f := fun f => LinearMap.congr_fun hr f
  refine ⟨_, fun j => b j, fun j t => r (coefFun (β j) (Ψ t)), fun j => (b j).2.2, fun t => ?_, fun j p hp => ?_⟩
  · funext x
    let y : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
    let s : W' := ⟨_, hsl t _, slice_mem_SB y _ (hΨ t)⟩
    have h1 := congrFun (congrArg Subtype.val (b.sum_repr s)) fun i => (x i).2
    have h2 : ∀ j, r (coefFun (β j) (Ψ t)) y = b.repr s j := fun j => by
      obtain ⟨f, hf⟩ := coefFun_mem (β j) _ (hΨ t)
      rw [← hf, hr']
      exact (congrFun hf y).trans (LinearMap.congr_fun (hβ j) s)
    have h3 : (s : (κ → Af F) → ℂ) (fun i => (x i).2) = Ψ t x := by
      simp only [s, y, RingEquiv.symm_apply_apply]
      rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [Finset.sum_apply]
    refine (h1.trans h3).symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← h2 j]
    rfl
  · refine bounded_of_weak _ (fun l => hb (l.toLinearMap ∘ₗ r ∘ₗ coefFun (β j)) fun g _ => ⟨β j g • l, fun f => ?_⟩) p hp
    simp only [LinearMap.comp_apply, coefFun_pureA, hr', map_smul]
    rfl

def qA : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1

def archW (w : (κ → AF F) × (κ → AF F)) : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => qA (w.1 i), fun i => qA (w.2 i))

def archOp (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) : SInf F κ →ₗ[ℂ] SInf F κ :=
  (heisOp (-trL w.2) (-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA (⅟(2 : AF F)) * (w.1 ⬝ᵥ w.2)))) w.1).toLinearMap

def finOp (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) (w : (κ → AF F) × (κ → AF F)) : (κ → Af F) → ℂ :=
  finS ψ g (fun i => p2 (w.2 i)) (fun i => p2 (w.1 i)) (p2 (⅟(2 : AF F)) * ((fun i => p2 (w.1 i)) ⬝ᵥ fun i => p2 (w.2 i)))

theorem schr_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    schr ψ w (pureA F f g) = pureA F (archOp (archW w) f) (finOp ψ g w) := by
  let h : AF F := ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)
  let c : κ → mixedEmbedding.mixedSpace F := fun i => qA (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => qA (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA h)
  let d : κ → Af F := fun i => p2 (w.2 i)
  let s : κ → Af F := fun i => p2 (w.1 i)
  have ea : archOp (archW w) f = archS f c t k := by
    simp only [k, h, map_mul, RingHom.map_dotProduct]
    rfl
  have ef : finOp ψ g w = finS ψ g d s (p2 h) := by
    simp only [h, map_mul, RingHom.map_dotProduct]
    rfl
  rw [ea, ef]
  funext x
  let y : κ → mixedEmbedding.mixedSpace F := fun i => qA (x i)
  let z : κ → Af F := fun i => p2 (x i)
  have h1 : (fun i => qA ((x + w.1) i)) = y + t := funext fun i => map_add qA (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + qA h := by
        change qA (x ⬝ᵥ w.2 + h) = _
        rw [map_add, RingHom.map_dotProduct]
        rfl
      rw [e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add, RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => qA ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem exists_trL_bound : ∃ c : ℝ, 0 ≤ c ∧ ∀ y : κ → mixedEmbedding.mixedSpace F, ‖trL y‖ ≤ c * ‖y‖ := by
  let T : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
    { toFun := trL
      map_add' := fun a b => ContinuousLinearMap.ext fun y => by
        simp only [ContinuousLinearMap.add_apply, trL_apply, dotProduct_add, map_add]
      map_smul' := fun r a => ContinuousLinearMap.ext fun y => by
        simp only [ContinuousLinearMap.smul_apply, trL_apply, dotProduct_smul, map_smul, RingHom.id_apply] }
  exact ⟨‖LinearMap.toContinuousLinearMap T‖, norm_nonneg _, fun y => (LinearMap.toContinuousLinearMap T).le_opNorm y⟩

theorem tame_archOp : Tame (archOp (F := F) (κ := κ)) := by
  obtain ⟨c, hc, hb⟩ := exists_trL_bound (F := F) (κ := κ)
  set η := ‖qA (⅟(2 : AF F))‖
  have hη : 0 ≤ η := norm_nonneg _
  refine tame_heisOp (GlobalTheory.T.schwartz_translation_seminorm_bound _) (GlobalTheory.T.schwartz_character_seminorm_bound _) _ _ _ (1 + c + c * η) (by nlinarith) (fun w => ?_) (fun w => ?_)
    fun w => norm_fst_le w
  · rw [norm_neg]
    have := norm_snd_le w
    refine (hb _).trans ?_
    gcongr
    nlinarith
  · rw [abs_neg, ← smul_eq_mul, ← smul_dotProduct, ← trL_apply, ← Real.norm_eq_abs]
    have h1 := norm_fst_le w
    have h2 := norm_snd_le w
    calc _ ≤ ‖trL w.2‖ * ‖qA (⅟(2 : AF F)) • w.1‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (c * ‖w‖) * (η * ‖w‖) := by
        gcongr
        · exact (hb _).trans (by gcongr)
        · exact (norm_smul_le _ _).trans (by gcongr)
      _ = c * η * ‖w‖ ^ 2 := by ring
      _ ≤ _ := by gcongr; linarith

def schrL (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun := schr ψ w
  map_add' := fun φ φ' => funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' := fun a φ => funext fun x => by
    simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schr_comm (ψ : AddChar (AF F) ℂ) (s u : (κ → AF F) × (κ → AF F)) (Φ : (κ → AF F) → ℂ) :
    schr ψ s (schr ψ u Φ) = ψ (s.1 ⬝ᵥ u.2 - u.1 ⬝ᵥ s.2) • schr ψ u (schr ψ s Φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct]
  congr 2
  · ring
  · abel

theorem norm_qA_le (a : AF F) : ‖qA a‖ ≤ ∑ v, ‖a.1 v‖ := by
  change ‖InfiniteAdeleRing.ringEquiv_mixedSpace F a.1‖ ≤ _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  have hS : 0 ≤ ∑ v, ‖a.1 v‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine max_le ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_) ((pi_norm_le_iff_of_nonneg hS).2 fun v => ?_)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖a.1 w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v.1).norm_map_of_map_zero (map_zero _)]
    exact Finset.single_le_sum (f := fun w => ‖a.1 w‖) (fun w _ => norm_nonneg _) (Finset.mem_univ v.1)

omit [Fintype κ] in
theorem archW_smul (a : AF F) (w : (κ → AF F) × (κ → AF F)) : archW (a • w) = qA a • archW w :=
  Prod.ext (funext fun i => map_mul qA a (w.1 i)) (funext fun i => map_mul qA a (w.2 i))

omit [Fintype κ] in
theorem archW_sum {ι : Type} [Fintype ι] (w : ι → (κ → AF F) × (κ → AF F)) : archW (∑ i, w i) = ∑ i, archW (w i) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp only [archW, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, map_sum]

theorem finOp_arch (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) (a : Ainf F) (w : (κ → AF F) × (κ → AF F)) :
    finOp ψ g (mk a 0 • w) = g := by
  have h : ∀ b : AF F, p2 (mk a 0 * b) = 0 := fun b => by rw [map_mul]; exact zero_mul _
  funext z
  simp only [finOp, finS, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, h, dotProduct, mul_zero,
    Finset.sum_const_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  congr 1
  funext i
  exact add_zero _

omit [Fintype κ] in
theorem pureA_add (f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    pureA F (f + f') g = pureA F f g + pureA F f' g := funext fun _ => add_mul _ _ _

theorem slice_decay {κ₁ ι T : Type} [Fintype κ₁] [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → mixedEmbedding.mixedSpace F) → ℂ)
    (hsl : ∀ g ∈ SB (κ → Af F), ∃ L : SInf F κ →L[ℂ] SInf F κ₁, ∀ f, ⇑(L f) = e (pureA F f g))
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, e (schr ψ (a • U i) Φ) = e Φ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (f : T → SInf F κ)
    (hf : ∀ p : Seminorm ℂ (SInf F κ), Continuous p → ∃ C : ℝ, ∀ t, p (f t) ≤ C)
    {Ω : Set (ι → Af F)} (hΩ : IsCompact Ω) (p : Seminorm ℂ (SInf F κ₁)) (hp : Continuous p) (N : ℕ) :
    ∃ C : ℝ, ∀ t (x : ι → AF F), (fun i => (x i).2) ∈ Ω → ∃ f₁ : SInf F κ₁, ⇑f₁ = e (schr ψ (∑ i, x i • S i) (pureA F (f t) g)) ∧
      p f₁ ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.heisenberg_character_minus_one F ψ hψ ι
  have key : ∀ g' : (κ → Af F) → ℂ, ∃ C : ℝ, ∀ t (x : ι → AF F), finOp ψ g (∑ i, x i • S i) = g' →
      ∃ f₁ : SInf F κ₁, ⇑f₁ = e (schr ψ (∑ i, x i • S i) (pureA F (f t) g)) ∧
        p f₁ ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
    intro g'
    by_cases hg' : g' ∈ SB (κ → Af F)
    swap
    · exact ⟨0, fun t x hx => (hg' (hx ▸ finS_mem ψ hψ.1 hg _ _ _)).elim⟩
    obtain ⟨L, hL⟩ := hsl g' hg'
    obtain ⟨q, hq, hdec⟩ := (tame_archOp (F := F) (κ := κ)).decay (p.comp L.toLinearMap) (hp.comp L.continuous)
      (∑ i, ‖archW (S i)‖) (C₀ * ∑ i, ‖archW (U i)‖) N
    obtain ⟨C, hC⟩ := hf q hq
    refine ⟨C, fun t x hx => ?_⟩
    set s := ∑ i, x i • S i with hs
    set r := ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ with hr
    have hr0 : 0 ≤ r := by positivity
    have hLs : ∀ h : SInf F κ, ⇑(L (archOp (archW s) h)) = e (schr ψ s (pureA F h g)) := fun h => by
      rw [hL, schr_pureA ψ hψ, hx]
    refine ⟨_, hLs (f t), (hdec (archW s) r hr0 ?_ (fun hr1 => ?_) (f t)).trans ?_⟩
    · rw [hs, archW_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [archW_smul, mul_comm]
      refine (norm_smul_le _ _).trans ?_
      gcongr
      exact (norm_qA_le _).trans (Finset.single_le_sum (f := fun i => ∑ v : InfinitePlace F, ‖(x i).1 v‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
    · obtain ⟨i, a, ha, ha'⟩ := hC₀ x hr1
      refine ⟨archW (mk a 0 • U i), ?_, fun h => ?_⟩
      · rw [archW_smul]
        have h1 : ‖archW (U i)‖ ≤ ∑ i, ‖archW (U i)‖ :=
          Finset.single_le_sum (f := fun i => ‖archW (U i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
        calc _ ≤ ‖qA (mk a 0)‖ * ‖archW (U i)‖ * r := by gcongr; exact norm_smul_le _ _
          _ = (‖qA (mk a 0)‖ * r) * ‖archW (U i)‖ := by ring
          _ ≤ _ := mul_le_mul ha' h1 (norm_nonneg _) (le_trans (by positivity) ha')
      · have hz : L (archOp (archW s) (archOp (archW (mk a 0 • U i)) h + h)) = 0 := by
          refine DFunLike.coe_injective ?_
          have hΦ : pureA F h g ∈ schA F κ := Submodule.subset_span ⟨h, g, hg, rfl⟩
          have hω : s.1 ⬝ᵥ (mk a 0 • U i).2 - (mk a 0 • U i).1 ⬝ᵥ s.2 = x i * mk a 0 := by
            have : ∀ j, (x j • S j).1 ⬝ᵥ (mk a 0 • U i).2 - (mk a 0 • U i).1 ⬝ᵥ (x j • S j).2 =
                if i = j then x j * mk a 0 else 0 := fun j => by
              simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
              have := hSU i j
              split_ifs at this ⊢
              · linear_combination (x j * mk a 0) * this
              · linear_combination (x j * mk a 0) * this
            rw [hs, Prod.fst_sum, Prod.snd_sum, sum_dotProduct, dotProduct_sum, ← Finset.sum_sub_distrib]
            simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          have h1 : pureA F (archOp (archW (mk a 0 • U i)) h + h : SInf F κ) g =
              schr ψ (mk a 0 • U i) (pureA F h g) + pureA F h g := by
            rw [schr_pureA ψ hψ, finOp_arch]
            exact pureA_add _ _ _
          rw [hLs, h1]
          change e (schrL ψ s _) = 0
          rw [map_add, map_add]
          change e (schr ψ s _) + e (schr ψ s _) = 0
          rw [schr_comm, map_smul, hinv _ _ _ (schr_mem_schA ψ hψ s _ hΦ), hω, ha, neg_one_smul, neg_add_cancel]
        rw [Seminorm.comp_apply]
        change p (L _) = 0
        rw [hz, map_zero]
    · have := Real.rpow_nonneg (show 0 ≤ 1 + r by linarith) (-(N : ℝ))
      gcongr
      exact hC t
  choose C hC using key
  let d : (ι → Af F) → κ → Af F := fun y a => ∑ i, y i * p2 ((S i).2 a)
  let s : (ι → Af F) → κ → Af F := fun y a => ∑ i, y i * p2 ((S i).1 a)
  have hd : Continuous d := continuous_pi fun a => continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  have hs : Continuous s := continuous_pi fun a => continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  let m : (ι → Af F) → (κ → Af F) × (κ → Af F) × Af F := fun y => (d y, s y, p2 (⅟(2 : AF F)) * (s y ⬝ᵥ d y))
  have hm : Continuous m := hd.prodMk (hs.prodMk (continuous_const.mul (hs.dotProduct hd)))
  have hfin := GlobalTheory.T.heisenberg_schwartz_finite_values F κ ψ hψ.1 g hg _ (hΩ.image hm)
  refine ⟨∑ g' ∈ hfin.toFinset, |C g'|, fun t x hx => ?_⟩
  have hmem : finOp ψ g (∑ i, x i • S i) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨_, ⟨_, hx, rfl⟩, ?_⟩
    simp only [finOp, m, d, s, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, map_sum, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  obtain ⟨f₁, h1, h2⟩ := hC _ t x rfl
  refine ⟨f₁, h1, h2.trans ?_⟩
  have := Real.rpow_nonneg (show 0 ≤ 1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ by positivity) (-(N : ℝ))
  gcongr
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun g' => |C g'|) (fun _ _ => abs_nonneg _) hmem)

def sliceL (c : κ → Af F) : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → mixedEmbedding.mixedSpace F) → ℂ where
  toFun Φ y := Φ fun q => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q)) (c q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_slice_clm {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (hM : M.IsGood B.ψ)
    (hE : IsEv B M M₁ ι ι' I e) (c₀ : Fin n₁ × Fin d₁ → Af F) : ∀ g ∈ SB (Fin n × Fin d → Af F),
    ∃ L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), ∀ f, ⇑(L f) = (sliceL c₀ ∘ₗ e) (pureA F f g) := by
  intro g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := GlobalTheory.EvAdm.exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  refine ⟨(∑ k, c k * ∏ᶠ v, ev v (φ k v) fun i => evalV F v (c₀ i)) • ei, fun f => ?_⟩
  have h1 : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  have h2 : ∀ k, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k)) = pureA F (ei f : (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) → ℂ)
      (fun y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) := fun k =>
    hloc f (φ k) (hφSB k) (hφvac k)
  rw [LinearMap.comp_apply, h1, map_sum, map_sum]
  funext y
  rw [Finset.sum_apply]
  change (∑ k, c k * ∏ᶠ v, ev v (φ k v) fun i => evalV F v (c₀ i)) * ei f y = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, h2, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm _ (ei f y)]
  congr 1
  simp only [sliceL, pureA, LinearMap.coe_mk, AddHom.coe_mk, HeisSchA.mk, RingEquiv.apply_symm_apply]

theorem form_swap (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (x y : Fin n → E) : form σ J y x = -σ (form σ J x y) := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem arch_decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∀ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U → ∀ (c : Fin b × Fin (b + a') → Af F) (N : ℕ) (s : Finset (ℕ × ℕ)),
      ∃ C : ℝ, ∀ k ∈ K, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
        ∃ f : SInf F (Fin b × Fin (b + a')), (∀ y, f y = e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c q))) ∧
          (s.sup (schwartzSeminormFamily ℂ _ ℂ)) f ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ h U hU c N s
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hX.lat)) hsub
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  have hΦA : Φ ∈ schA F _ := by
    refine Submodule.span_le.mpr ?_ hΦ
    rintro _ ⟨f, -, φ, hφ, hvac, rfl⟩
    exact GlobalTheory.BigNZ.Fam.mem hT.geo.hM ⟨hφ, hvac⟩ f
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun k : K => om (k.1, h) Φ)
    (fun k => hw.isUSplitting.pres (k.1, h) Φ hΦA) fun l hl => by
      have hc := (hw.2.2 l hl Φ hΦA).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V.J => (g, h))
      obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨C, fun k => hC k.1 k.2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by
    rw [form_swap hT.base.cm hT.geo.hW.skew, hC.hH'.xy, map_one])
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U' := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x))
  have hp : Continuous ⇑(Finset.sup s (schwartzSeminormFamily ℂ (Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F) ℂ)) :=
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  choose C hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) (hg j) (f j) (hf j) hU _ hp N
  refine ⟨∑ j, C j, fun k hk l hl => ?_⟩
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ (GlobalTheory.XTermMaj.crd F E (l : AE F E)) hl
  have hS : G.M.co.e (shiftA H H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    rw [shiftA]
    congr 1
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  refine ⟨∑ j, f₁ j, fun y => ?_, ?_⟩
  · have h1 := hdec ⟨k, hk⟩
    simp only at h1
    rw [h1, Darboux.rho, hS]
    change coeL (∑ j, f₁ j) y = (sliceL c ∘ₗ e) (schrL B.ψ _ _) y
    rw [map_sum, map_sum, map_sum]
    exact congrFun (Finset.sum_congr rfl fun j _ => hf₁ j) y
  · rw [Finset.sum_mul]
    exact (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans (Finset.sum_le_sum fun j _ => hb₁ j)

end GlobalTheory.XTermDecay

end
