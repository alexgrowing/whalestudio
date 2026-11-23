import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCharacterMinusOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticTraceBasisExists

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeArchDecay

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def evAt {Y : Type} (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (Y → ℂ)) (g : (κ → Af F) → ℂ) (y : Y) : SInf F κ →ₗ[ℂ] ℂ where
  toFun h := e (pureA F h g) y
  map_add' h h' := by
    have : pureA F (h + h' : SInf F κ) g = pureA F h g + pureA F h' g := GlobalTheory.XTermDecay.pureA_add _ _ _
    rw [this, map_add, Pi.add_apply]
  map_smul' c h := by
    have : pureA F (c • h : SInf F κ) g = c • pureA F h g := funext fun _ => mul_assoc _ _ _
    rw [this, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem exists_sup_seminorm {V Y : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    (l : Y → V →ₗ[ℂ] ℂ) (q : Seminorm ℂ V) (hq : Continuous q) (hb : ∀ y h, ‖l y h‖ ≤ q h) :
    ∃ p : Seminorm ℂ V, Continuous p ∧ (∀ y h, ‖l y h‖ ≤ p h) ∧ ∀ h, (∀ y, l y h = 0) → p h = 0 := by
  let P : Y → Seminorm ℂ V := fun y => (normSeminorm ℂ ℂ).comp (l y)
  have hB : BddAbove (Set.range P) := ⟨q, by rintro _ ⟨y, rfl⟩; exact hb y⟩
  have hap : ∀ h, (⨆ y, P y) h = ⨆ y, ‖l y h‖ := fun h => Seminorm.iSup_apply hB
  have hle : (⨆ y, P y) ≤ q := fun h => by
    rw [hap]
    exact Real.iSup_le (fun y => hb y h) (apply_nonneg q h)
  refine ⟨⨆ y, P y, Seminorm.continuous_of_le hq hle, fun y h => ?_, fun h hh => ?_⟩
  · exact le_ciSup hB y h
  · rw [hap]
    simp [hh]

theorem core_decay {Y ι : Type} [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (Y → ℂ))
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, e (schr ψ (a • U i) Φ) = e Φ)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (q₀ : Seminorm ℂ (SInf F κ)) (hq₀ : Continuous q₀)
    (hb : ∀ y (h : SInf F κ), ‖e (pureA F h g) y‖ ≤ q₀ h) (N : ℕ) :
    ∃ q : Seminorm ℂ (SInf F κ), Continuous q ∧ ∀ (f : SInf F κ) (x : ι → AF F),
      (mk 1 0 : AF F) • ∑ i, x i • S i = ∑ i, x i • S i → ∀ y,
        ‖e (schr ψ (∑ i, x i • S i) (pureA F f g)) y‖ ≤
          q f * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.ArchHalfTurn.halfturn F ψ hψ ι
  obtain ⟨p, hp, hpl, hp0⟩ := exists_sup_seminorm (evAt e g) q₀ hq₀ hb
  obtain ⟨q, hq, hdec⟩ := (tame_archOp (F := F) (κ := κ)).decay p hp
    (∑ i, ‖archW (S i)‖) (C₀ * ∑ i, ‖archW (U i)‖) N
  refine ⟨q, hq, fun f x hx y => ?_⟩
  set s := ∑ i, x i • S i with hs
  set r := ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hfin : finOp ψ g s = g := by rw [← hx, finOp_arch]
  have hLs : ∀ (h : SInf F κ) y, evAt e g y (archOp (archW s) h) = e (schr ψ s (pureA F h g)) y := fun h y => by
    rw [schr_pureA ψ hψ, hfin]; rfl
  rw [← hLs]
  refine (hpl y _).trans (hdec (archW s) r hr0 ?_ (fun hr1 => ?_) f)
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
    · refine hp0 _ fun y => ?_
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
        exact GlobalTheory.XTermDecay.pureA_add _ _ _
      have h2 : e (schr ψ s (pureA F (archOp (archW (mk a 0 • U i)) h + h : SInf F κ) g)) = 0 := by
        rw [h1]
        change e (schrL ψ s _) = 0
        rw [map_add, map_add]
        change e (schr ψ s _) + e (schr ψ s _) = 0
        rw [schr_comm, map_smul, hinv _ _ _ (schr_mem_schA ψ hψ s _ hΦ), hω, ha, neg_one_smul, neg_add_cancel]
      rw [hLs, h2, Pi.zero_apply]

theorem exists_bound_of_exp {κ' : Type} [Fintype κ'] {e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g : (κ → Af F) → ℂ} (he : GlobalTheory.EvTame.HasTameExp e g) :
    ∃ q₀ : Seminorm ℂ (SInf F κ), Continuous q₀ ∧ ∀ y (h : SInf F κ), ‖e (pureA F h g) y‖ ≤ q₀ h := by
  obtain ⟨ι, _, P, k, hk, hP⟩ := he
  have hkb : ∀ j, ∃ C : ℝ, ∀ z, ‖k j z‖ ≤ C := fun j =>
    (hk j).1.continuous.bounded_above_of_compact_support (hk j).2
  choose C hC using hkb
  have hc : ∀ j, Continuous ((SchwartzMap.seminorm ℂ 0 0).comp (P j).toLinearMap : Seminorm ℂ (SInf F κ)) := fun j =>
    ((schwartz_withSeminorms ℂ (κ' → mixedEmbedding.mixedSpace F) ℂ).continuous_seminorm (0, 0)).comp (P j).continuous
  choose q hq hqe using fun j => continuous_smul_semi (C j) _ (hc j)
  have hsum : ∀ h, (∑ j, q j) h = ∑ j, q j h := fun h => by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Seminorm.add_apply, ih]
  refine ⟨∑ j, q j, ?_, fun y h => ?_⟩
  · rw [show (⇑(∑ j, q j) : SInf F κ → ℝ) = fun h => ∑ j, q j h from funext hsum]
    exact continuous_finset_sum _ fun j _ => hq j
  · rw [hsum, hP, Finset.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [hqe, pureA, norm_mul, mul_comm]
    exact mul_le_mul ((hC j _).trans (le_abs_self _)) (SchwartzMap.norm_le_seminorm ℂ (P j h) _) (norm_nonneg _)
      (abs_nonneg _)

theorem norm_ev_shift_arch_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ g ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → FiniteAdeleRing (𝓞 F) F), ∀ S : Set (SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsCompact S → ∀ N : ℕ, ∃ C : ℝ,
      ∀ f ∈ S, ∀ t : AE F E, (pairA F 1 0 : AF F) • t = t → ∀ y : Fin b × Fin (b + a') → AF F,
        ‖e (G.M.co.rho B.ψ (t • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (pureA F f g)) y‖ ≤
          C * ((1 + GlobalTheory.IdeleDecay.size F E t) ^ N)⁻¹ := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ g hg K hK N
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨q₀, hq₀, hb₀⟩ := exists_bound_of_exp (e := e) (g := g)
    (GlobalTheory.EvTame.isTame_of_isEv F E σ B _ _ _ _ _ _ _ _ G.M G₁.M H.ι H'.ι _ e hT.geo.hM hT₁.geo.hM he g hg)
  obtain ⟨τ, hτ⟩ := GlobalTheory.ArchDualPair.dualPair F E σ _ _ G.V.J G.W.J H.x H.y H'.x H'.y hC.hH.xy (by
    rw [form_swap hT.base.cm hT.geo.hW.skew, hC.hH'.xy, map_one])
  let S := fun j => G.M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  let U := fun i => G.M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (τ i) • incV F H.y) (incV F H'.x))
  obtain ⟨q, hq, hdec⟩ := core_decay B.ψ hT.base.std S U (fun i j => by rw [← G.M.co.form]; convert hτ i j)
    e (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (τ i) • incV F H.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact this) hg q₀ hq₀ hb₀ N
  obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hq.continuousOn
  refine ⟨C, fun f hf t ht y => ?_⟩
  have hS : G.M.co.e (t • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) = ∑ i, GlobalTheory.IdeleDecay.coord F E t i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun t).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hx : (mk 1 0 : AF F) • ∑ i, GlobalTheory.IdeleDecay.coord F E t i • S i = ∑ i, GlobalTheory.IdeleDecay.coord F E t i • S i := by
    rw [← hS, ← map_smul, ← smul_assoc]
    congr 2
  rw [Darboux.rho, hS]
  refine (hdec f _ hx y).trans ?_
  have hsz : GlobalTheory.IdeleDecay.size F E t ≤ ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.IdeleDecay.coord F E t i).1 v‖ :=
    Finset.sum_le_sum fun i _ => norm_qA_le _
  have h0 := GlobalTheory.IdeleDecay.size_nonneg (F := F) (E := E) t
  have hqC : q f ≤ C := (le_abs_self _).trans (hCb f hf)
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
  refine mul_le_mul hqC ?_ (by positivity) ((apply_nonneg q f).trans hqC)
  gcongr

end GlobalTheory.ConeArchDecay

end
