import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeUnif

theorem exists_open_addSubgroup (F : Type) [Field F] [NumberField F] {I : Type} [Fintype I]
    (V : Set (I → FiniteAdeleRing (𝓞 F) F)) (hV : V ∈ 𝓝 (0 : I → FiniteAdeleRing (𝓞 F) F)) :
    ∃ U : AddSubgroup (I → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (I → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ η ∈ U, η ∈ V := by
  let e := Fintype.equivFin I
  have hc : Continuous fun (u : Fin (Fintype.card I) → FiniteAdeleRing (𝓞 F) F) (i : I) => u (e i) :=
    continuous_pi fun i => continuous_apply _
  have hV' : (fun (u : Fin (Fintype.card I) → FiniteAdeleRing (𝓞 F) F) (i : I) => u (e i)) ⁻¹' V ∈
      𝓝 (0 : Fin (Fintype.card I) → FiniteAdeleRing (𝓞 F) F) :=
    hc.continuousAt.preimage_mem_nhds hV
  obtain ⟨L, hLo, -, hL⟩ := GlobalTheory.SWQ.FinAnnih.basis_nhds (F := F) _ hV'
  refine ⟨AddSubgroup.pi Set.univ (fun _ => L), ?_, fun η hη => ?_⟩
  · exact isOpen_set_pi Set.finite_univ fun _ _ => hLo
  · have := hL (fun l => η (e.symm l)) fun l => hη _ (Set.mem_univ _)
    simpa using this

theorem ef_mul (F : Type) [Field F] [NumberField F] (c : AF F) : pairA F 0 1 * c = pairA F 0 c.2 := by
  show ((0 * c.1, 1 * c.2) : _ × _) = (0, c.2)
  simp

theorem coords_small_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (K : Set (UA σ X.J)), IsCompact K →
    ∀ N ∈ 𝓝 (0 : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) × (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F)),
      ∃ U : AddSubgroup (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ k ∈ K, ∀ η ∈ U, ∃ p ∈ N, M.co.e (mat k⁻¹ * (incM F ι * M₁.co.e.symm (0, fun i => pairA F 0 (η i)) * (incM F ι')ᵀ)) =
          (fun i => pairA F 0 (p.1 i), fun i => pairA F 0 (p.2 i)) := by
  intro F E _ _ _ _ _ σ n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' K hK N hN
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI hMt : ∀ a b : ℕ, IsModuleTopology (AF F) (Matrix (Fin a) (Fin b) (AE F E)) := fun a b =>
    inferInstanceAs (IsModuleTopology (AF F) (Fin a → Fin b → AE F E))
  have hc1 : Continuous M.co.e := by
    have := IsModuleTopology.continuous_of_linearMap (R := AF F) M.co.e.toLinearMap
    exact this
  have hc2 : Continuous M₁.co.e.symm := by
    have := IsModuleTopology.continuous_of_linearMap (R := AF F) M₁.co.e.symm.toLinearMap
    exact this
  have hsn : Continuous (fun a : AF F => a.2) := continuous_snd
  have hpa : Continuous (fun y : FiniteAdeleRing (𝓞 F) F => pairA F 0 y) := continuous_const.prodMk continuous_id
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ X.J => mat g⁻¹ := hm.comp continuous_inv
  let z : (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → Matrix (Fin n₁) (Fin d₁) (AE F E) :=
    fun η => M₁.co.e.symm (0, fun i => pairA F 0 (η i))
  have hz : Continuous z := hc2.comp
    (continuous_const.prodMk (continuous_pi fun i => hpa.comp (continuous_apply i)))
  have hz0 : z 0 = 0 := by
    show M₁.co.e.symm (0, fun i => pairA F 0 0) = 0
    exact map_zero M₁.co.e.symm
  have hzf : ∀ η, pairA F 0 1 • z η = z η := by
    intro η
    show pairA F 0 1 • M₁.co.e.symm (0, fun i => pairA F 0 (η i)) = M₁.co.e.symm (0, fun i => pairA F 0 (η i))
    rw [← map_smul]
    congr 1
    refine Prod.ext (smul_zero _) (funext fun i => ?_)
    exact ef_mul F _
  let out : (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) × UA σ X.J →
      (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    fun q => M.co.e (mat q.2⁻¹ * (incM F ι * z q.1 * (incM F ι')ᵀ))
  have hout : Continuous out := hc1.comp ((hmi.comp continuous_snd).matrix_mul
    ((continuous_const.matrix_mul (hz.comp continuous_fst)).matrix_mul continuous_const))
  have houtf : ∀ q, pairA F 0 1 • out q = out q := by
    intro q
    show pairA F 0 1 • M.co.e (mat q.2⁻¹ * (incM F ι * z q.1 * (incM F ι')ᵀ)) =
      M.co.e (mat q.2⁻¹ * (incM F ι * z q.1 * (incM F ι')ᵀ))
    rw [← map_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, hzf]
  let p : (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) × UA σ X.J →
      (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) × (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) :=
    fun q => (fun i => ((out q).1 i).2, fun i => ((out q).2 i).2)
  have hp : Continuous p :=
    (continuous_pi fun i => hsn.comp ((continuous_apply i).comp (continuous_fst.comp hout))).prodMk
      (continuous_pi fun i => hsn.comp ((continuous_apply i).comp (continuous_snd.comp hout)))
  have hp0 : ∀ k, p (0, k) = 0 := by
    intro k
    have h0 : out (0, k) = 0 := by
      show M.co.e (mat k⁻¹ * (incM F ι * z 0 * (incM F ι')ᵀ)) = 0
      rw [hz0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, map_zero]
    show ((fun i => ((out (0, k)).1 i).2, fun i => ((out (0, k)).2 i).2) : _ × _) = 0
    rw [h0]
    rfl
  have hev : ∀ᶠ η in 𝓝 (0 : Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F), ∀ k ∈ K, p (η, k) ∈ N := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    refine hp.continuousAt.preimage_mem_nhds ?_
    rw [hp0]; exact hN
  obtain ⟨U, hUo, hU⟩ := exists_open_addSubgroup F _ hev
  refine ⟨U, hUo, fun k hk η hη => ⟨p (η, k), hU η hη k hk, ?_⟩⟩
  show out (η, k) = _
  rw [← houtf]
  exact Prod.ext (funext fun i => ef_mul F _) (funext fun i => ef_mul F _)

end GlobalTheory.ConeUnif
