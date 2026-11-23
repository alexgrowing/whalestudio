import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SmallHeisFix

variable {F : Type} [Field F] [NumberField F]

theorem one_mem_intA : (1 : FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchADecomp.intA F := by
  intro v
  have h := map_one (evalV F v)
  rw [GlobalTheory.SchADecomp.evalV_eq] at h
  rw [h]
  exact one_mem _

theorem exists_natCast_mem (V : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) (hV : IsOpen (V : Set (FiniteAdeleRing (𝓞 F) F))) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : FiniteAdeleRing (𝓞 F) F) ∈ V := by
  haveI : CompactSpace (GlobalTheory.SchADecomp.intA F) :=
    isCompact_iff_compactSpace.1 GlobalTheory.SchADecomp.isCompact_intA
  have ho : IsOpen ((V.addSubgroupOf (GlobalTheory.SchADecomp.intA F)) : Set (GlobalTheory.SchADecomp.intA F)) :=
    hV.preimage continuous_subtype_val
  haveI : Finite (GlobalTheory.SchADecomp.intA F ⧸ V.addSubgroupOf (GlobalTheory.SchADecomp.intA F)) :=
    AddSubgroup.quotient_finite_of_isOpen _ ho
  refine ⟨(V.addSubgroupOf (GlobalTheory.SchADecomp.intA F)).index, AddSubgroup.index_ne_zero_of_finite, ?_⟩
  have := AddSubgroup.nsmul_index_mem (V.addSubgroupOf (GlobalTheory.SchADecomp.intA F))
    (⟨1, one_mem_intA⟩ : GlobalTheory.SchADecomp.intA F)
  rw [AddSubgroup.mem_addSubgroupOf] at this
  simpa using this

variable {κ : Type} [Fintype κ]

def wFin (y z : κ → Af F) (a : Af F) : (κ → AF F) × (κ → AF F) :=
  (fun i => pairA F 0 (a * y i), fun i => pairA F 0 (a * z i))

theorem schr_add (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (Φ₁ Φ₂ : (κ → AF F) → ℂ) :
    schr ψ w (Φ₁ + Φ₂) = schr ψ w Φ₁ + schr ψ w Φ₂ := by
  funext x
  simp only [schr, Pi.add_apply, mul_add]

theorem schr_smul (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    schr ψ w (c • Φ) = c • schr ψ w Φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem schr_zero (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) :
    schr ψ w (0 : (κ → AF F) → ℂ) = 0 := by
  funext x
  simp only [schr, Pi.zero_apply, mul_zero]

def phase (y z : κ → Af F) (p : Af F × (κ → Af F)) : Af F :=
  p.2 ⬝ᵥ (fun i => p.1 * z i) +
    GlobalTheory.HeisSchA.p2 (⅟(2 : AF F)) * ((fun i => p.1 * y i) ⬝ᵥ (fun i => p.1 * z i))

theorem continuous_phase (y z : κ → Af F) : Continuous (phase y z) := by
  have h1 : Continuous fun p : Af F × (κ → Af F) => p.2 ⬝ᵥ (fun i => p.1 * z i) := by
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_snd).mul (continuous_fst.mul continuous_const)
  have h2 : Continuous fun p : Af F × (κ → Af F) => (fun i => p.1 * y i) ⬝ᵥ (fun i => p.1 * z i) := by
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ => (continuous_fst.mul continuous_const).mul (continuous_fst.mul continuous_const)
  exact h1.add (continuous_const.mul h2)

theorem phase_zero (y z : κ → Af F) (u : κ → Af F) : phase y z (0, u) = 0 := by
  simp [phase]

theorem schr_wFin_pureA (ψ : AddChar (AF F) ℂ) (y z : κ → Af F) (a : Af F)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (x : κ → AF F) :
    schr ψ (wFin y z a) (pureA F f g) x =
      GlobalTheory.HeisSchA.finChar ψ (phase y z (a, fun i => (x i).2)) *
        (f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g ((fun i => (x i).2) + a • y)) := by
  simp only [schr, pureA]
  rw [GlobalTheory.HeisSchA.map_eq_mul ψ]
  have h1 : GlobalTheory.HeisSchA.p1 (x ⬝ᵥ (wFin y z a).2 + ⅟(2 : AF F) * ((wFin y z a).1 ⬝ᵥ (wFin y z a).2)) = 0 := by
    simp only [map_add, map_mul, RingHom.map_dotProduct]
    have : (⇑GlobalTheory.HeisSchA.p1 ∘ (wFin y z a).2 : κ → InfiniteAdeleRing F) = 0 := by funext i; rfl
    simp [this]
  have h2 : GlobalTheory.HeisSchA.p2 (x ⬝ᵥ (wFin y z a).2 + ⅟(2 : AF F) * ((wFin y z a).1 ⬝ᵥ (wFin y z a).2)) =
      phase y z (a, fun i => (x i).2) := by
    simp only [map_add, map_mul, RingHom.map_dotProduct]
    rfl
  rw [h1, h2]
  have h0 : ψ (GlobalTheory.HeisSchA.mk 0 0) = 1 := AddChar.map_zero_eq_one ψ
  rw [h0, one_mul]
  have ha : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (wFin y z a).1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    exact congrArg _ (add_zero (x i).1)
  have hf : (fun i => ((x + (wFin y z a).1) i).2) = (fun i => (x i).2) + a • y := rfl
  rw [ha, hf]

theorem pure_fix (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (y z : κ → Af F)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (hg : g ∈ SB (κ → Af F)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ M : ℕ, schr ψ (wFin y z ((N : Af F) * (M : Af F))) (pureA F f g) = pureA F f g := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → Af F) := GlobalTheory.HeisSchA.nonarch_pi
  obtain ⟨M', hM'o, hM'⟩ := GlobalTheory.SchADecomp.exists_open_invariant g hg
  have hKo : IsOpen {b : Af F | GlobalTheory.HeisSchA.finChar ψ b = 1} :=
    (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).isOpen_fiber 1
  obtain ⟨U, W', hUo, -, h0U, hW', hUW⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : Af F))) hg.2
    (hKo.preimage (continuous_phase y z)) (by
      rintro ⟨a, u⟩ ⟨ha, -⟩
      simp only [Set.mem_singleton_iff] at ha
      subst ha
      show GlobalTheory.HeisSchA.finChar ψ (phase y z (0, u)) = 1
      rw [phase_zero]
      exact AddChar.map_zero_eq_one _)
  have hT : IsOpen {a : Af F | a • y ∈ M'} := hM'o.preimage (continuous_id.smul continuous_const)
  have hnhds : U ∩ {a : Af F | a • y ∈ M'} ∈ 𝓝 (0 : Af F) :=
    Filter.inter_mem (hUo.mem_nhds (h0U rfl)) (hT.mem_nhds (by simp [M'.zero_mem]))
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hnhds
  obtain ⟨N, hN, hNV⟩ := exists_natCast_mem (V : AddSubgroup (Af F)) V.isOpen
  refine ⟨N, hN, fun M => ?_⟩
  have haV : (N : Af F) * (M : Af F) ∈ (V : AddSubgroup (Af F)) := by
    rw [mul_comm, ← nsmul_eq_mul]
    exact (V : AddSubgroup (Af F)).nsmul_mem hNV M
  obtain ⟨haU, haT⟩ := hV haV
  have haT' : ((N : Af F) * (M : Af F)) • y ∈ M' := haT
  funext x
  rw [schr_wFin_pureA, hM' _ haT']
  by_cases hgx : g (fun i => (x i).2) = 0
  · simp [pureA, hgx]
  · have hmem : (((N : Af F) * (M : Af F)), fun i => (x i).2) ∈ U ×ˢ W' :=
      ⟨haU, hW' (subset_tsupport _ hgx)⟩
    have h1 : GlobalTheory.HeisSchA.finChar ψ (phase y z (((N : Af F) * (M : Af F)), fun i => (x i).2)) = 1 := hUW hmem
    rw [h1, one_mul]
    rfl

end GlobalTheory.SmallHeisFix

theorem GlobalTheory.SmallHeisFix.main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Ψ ∈ schA F κ, ∀ (m : ℕ) (y z : Fin m → κ → Af F), ∃ N : ℕ, N ≠ 0 ∧ ∀ j,
      schr ψ (fun i => pairA F 0 ((N : Af F) * y j i), fun i => pairA F 0 ((N : Af F) * z j i)) Ψ = Ψ := by
  intro F _ _ κ _ ψ hψ Ψ hΨ m y z
  have key : ∀ j, ∃ N : ℕ, N ≠ 0 ∧ ∀ M : ℕ,
      schr ψ (GlobalTheory.SmallHeisFix.wFin (y j) (z j) ((N : Af F) * (M : Af F))) Ψ = Ψ := by
    intro j
    induction hΨ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      exact GlobalTheory.SmallHeisFix.pure_fix ψ hψ (y j) (z j) (⇑f) g hg
    | zero => exact ⟨1, one_ne_zero, fun M => GlobalTheory.SmallHeisFix.schr_zero ψ _⟩
    | add Φ₁ Φ₂ _ _ h1 h2 =>
      obtain ⟨N₁, hN₁, e1⟩ := h1
      obtain ⟨N₂, hN₂, e2⟩ := h2
      refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, fun M => ?_⟩
      have c1 : ((N₁ * N₂ : ℕ) : Af F) * (M : Af F) = (N₁ : Af F) * ((N₂ * M : ℕ) : Af F) := by
        push_cast; ring
      have c2 : ((N₁ * N₂ : ℕ) : Af F) * (M : Af F) = (N₂ : Af F) * ((N₁ * M : ℕ) : Af F) := by
        push_cast; ring
      rw [GlobalTheory.SmallHeisFix.schr_add]
      congr 1
      · rw [c1]; exact e1 _
      · rw [c2]; exact e2 _
    | smul c Φ _ h =>
      obtain ⟨N, hN, e⟩ := h
      exact ⟨N, hN, fun M => by rw [GlobalTheory.SmallHeisFix.schr_smul, e]⟩
  choose N hN hNe using key
  refine ⟨∏ j, N j, Finset.prod_ne_zero_iff.2 fun j _ => hN j, fun j => ?_⟩
  have h := hNe j (∏ j' ∈ Finset.univ.erase j, N j')
  rw [← Nat.cast_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ j)] at h
  exact h
