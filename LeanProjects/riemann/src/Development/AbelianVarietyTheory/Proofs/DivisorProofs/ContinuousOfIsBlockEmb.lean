import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockLevel

open Matrix
open scoped TensorProduct
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAFE : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAFE : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_ad (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add, LinearMap.map_add, ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem infTens_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    GlobalTheory.LFun.infTens F E (sigR (AF F) σ z) = sigR (Ainf F) σ (GlobalTheory.LFun.infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem continuous_finGL (d : ℕ) : Continuous (GlobalTheory.CuspRep.finGL E d) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (GlobalTheory.CuspRep.sFin E : GlobalTheory.CuspRep.Af E → GlobalTheory.CuspRep.Ad E) :=
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GlobalTheory.CuspRep.Af E => ((0, x) : InfiniteAdeleRing E × GlobalTheory.CuspRep.Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E) => 1 - GlobalTheory.CuspRep.matN d (GlobalTheory.CuspRep.sFin E) 1 + x.map (GlobalTheory.CuspRep.sFin E))

variable [IsTotallyComplex E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
  {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ} {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem continuous_of_isBlockEmb (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) : Continuous ι := by
  obtain ⟨Φ, j, -, hΦs, -, -, hf⟩ := hι
  have hval : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := by
    simp only [hf, cT]
    have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g.1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := Units.continuous_val
    have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((g⁻¹).1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) :=
      Units.continuous_val.comp continuous_inv
    have h3 := h1.matrix_map hΦs
    have h4 := ((h2.matrix_map hΦs).matrix_map (continuous_sigR_ad σ)).matrix_transpose
    exact (continuous_const.add ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h4.sub continuous_const)).matrix_mul continuous_const)
  have hU : Continuous fun g : GlobalTheory.CuspRep.GA E d => matHom (AF F) σ J (ι g) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1) =
        (fun g => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) ∘ fun g => g⁻¹ := by
      funext g; simp [map_inv]
    rw [this]
    exact hval.comp continuous_inv
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 hU

theorem infTens_symm_finGL (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E)
    (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
    (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) :
    GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = (1 : Matrix (Fin d) (Fin d) (Ainf F ⊗[F] E)) a b := by
  have e1 : GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = j.symm (((GlobalTheory.CuspRep.finGL E d k).1 a b).1) := by
    have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
      have e := congrArg Prod.fst (hΦ (Φ.symm x))
      rw [RingEquiv.apply_symm_apply] at e
      rw [e, RingEquiv.symm_apply_apply]
    exact key _
  rw [e1]
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b - GlobalTheory.CuspRep.sFin E ((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E)) a b) + GlobalTheory.CuspRep.sFin E (k.1 a b)).1) = _
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b).1 - 0 + 0) = _
  rw [sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem finGL_mem_finPts (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) :
    ι (GlobalTheory.CuspRep.finGL E d k) ∈ finPts σ J := by
  obtain ⟨Φ, j, -, -, -, hΦ, hf⟩ := hι
  have hA : ∀ k : GL (Fin d) (GlobalTheory.CuspRep.Af E),
      (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm) = 1 := by
    intro k
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact infTens_symm_finGL Φ j hΦ k a b
  have hB : (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E))
      (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm)) = 1 := by
    rw [← map_inv]
    ext a b
    have e := congrArg (fun M => M b a) (hA k⁻¹)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cT, Matrix.transpose_apply, infTens_sigR, e]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
  simp only [finPts, MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply Units.ext
  change (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) (matHom (AF F) σ J (ι (GlobalTheory.CuspRep.finGL E d k))).1 = 1
  have hA' : ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hA, map_one, sub_self]
  have hB' : (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm) - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hB, map_one, sub_self]
  rw [hf]
  simp only [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_mul, hA', hB', Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem isOpen_rightInv_finGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        IsOpen {k : GL (Fin d) (GlobalTheory.CuspRep.Af E) | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)} := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι hι _ _ _ _ ψ hψ g₀ _
  obtain ⟨U, hUo, hU⟩ := hψ.1.level
  let H : Subgroup (GL (Fin d) (GlobalTheory.CuspRep.Af E)) :=
    { carrier := {k | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)}
      one_mem' := fun g => by simp
      mul_mem' := fun {a b} ha hb g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d (a * b)) * g₀) = _
        rw [(GlobalTheory.CuspRep.finGL E d).map_mul a b, ← mul_assoc, hb (g * GlobalTheory.CuspRep.finGL E d a), ha g]
      inv_mem' := fun {a} ha g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d a⁻¹) * g₀) = _
        have e : g * GlobalTheory.CuspRep.finGL E d a⁻¹ * GlobalTheory.CuspRep.finGL E d a = g := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
        rw [← ha (g * GlobalTheory.CuspRep.finGL E d a⁻¹), e] }
  let m : GL (Fin d) (GlobalTheory.CuspRep.Af E) → GAd σ J := fun k => g₀⁻¹ * ι (GlobalTheory.CuspRep.finGL E d k) * g₀
  have hm : Continuous m :=
    (continuous_const.mul ((continuous_of_isBlockEmb hι).comp (continuous_finGL d))).mul continuous_const
  have hN : (finPts σ J).Normal := MonoidHom.normal_ker _
  have hsub : m ⁻¹' (U : Set (GAd σ J)) ⊆ (H : Set (GL (Fin d) (GlobalTheory.CuspRep.Af E))) := by
    intro k hk g
    have hfin : m k ∈ finPts σ J := by
      have := hN.conj_mem _ (finGL_mem_finPts hι k) g₀⁻¹
      simpa [m] using this
    have e := hU (m k) hk hfin (ι g * g₀)
    rw [← e]
    simp only [m, map_mul, mul_assoc, mul_inv_cancel_left]
  have h1 : m ⁻¹' (U : Set (GAd σ J)) ∈ nhds (1 : GL (Fin d) (GlobalTheory.CuspRep.Af E)) := by
    refine hm.continuousAt.preimage_mem_nhds ?_
    have : m 1 = 1 := by simp [m]
    rw [this]
    exact hUo.mem_nhds U.one_mem
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset h1 hsub)

end GlobalTheory.BlockLevel
