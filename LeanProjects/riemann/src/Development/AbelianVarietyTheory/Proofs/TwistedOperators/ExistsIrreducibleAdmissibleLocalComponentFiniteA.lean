import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LocCompFin

open GlobalTheory.CuspRep.LocEx GlobalTheory.AutMult

section Groups

variable {D : D7} (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  GlobalTheory.AdelicU.proj_emb_self _ _ u x

theorem commute_locFin (x : Gv V u) {g : GfC V} (hg : finLoc V u g = 1) : Commute (locFin V u x) g :=
  Subtype.ext (GlobalTheory.AdelicU.commute_emb _ _ x hg).eq

theorem continuous_locFin : Continuous (locFin V u) :=
  (GlobalTheory.AdelicU.continuous_emb _ _ u).subtype_mk _

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (GlobalTheory.AdelicU.continuous_proj _ _ u).comp continuous_subtype_val

theorem finLoc_inv_mul (g : GfC V) : finLoc V u ((locFin V u (finLoc V u g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, finLoc_locFin, inv_mul_cancel]

end Groups

theorem exists_locComp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N),
      π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  intro D V u W _ _ σ hirr hadm
  obtain ⟨hnt, hinv⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr
  obtain ⟨x, hx0⟩ := exists_ne (0 : W)
  have hsplit : ∀ g (y : W), σ g y = σ (locFin V u (finLoc V u g)) (σ ((locFin V u (finLoc V u g))⁻¹ * g) y) :=
    fun g y => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hcomm : ∀ g : GfC V, finLoc V u g = 1 → ∀ h (y : W),
      σ g (σ (locFin V u h) y) = σ (locFin V u h) (σ g y) := by
    intro g hg h y
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin V u h hg).eq, map_mul, Module.End.mul_apply]
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun v => (hadm.1 v).preimage (continuous_locFin V u)
  let K₀ : Subgroup (GfC V) := stab σ x
  have hK₀ : IsOpen (K₀ : Set (GfC V)) := hadm.1 x
  let Kc : Subgroup (Gv V u) := K₀.comap (locFin V u) ⊓ Kv V u
  have hKco : IsOpen (Kc : Set (Gv V u)) :=
    (hK₀.preimage (continuous_locFin V u)).inter (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ u)
  have hKcc : IsCompact (Kc : Set (Gv V u)) :=
    (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ u).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKco) fun k hk => hk.2
  have hKcK₀ : ∀ k ∈ Kc, locFin V u k ∈ K₀ := fun k hk => hk.1
  have hxKc : x ∈ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc := mem_fix.2 fun k hk => hKcK₀ k hk
  have hnull : nullPart (σ.comp (locFin V u)) Kc = ⊥ := by
    rcases hinv (nullPart (σ.comp (locFin V u)) Kc) (fun g y hy => by
      rw [hsplit g y]
      exact nullPart_act _ Kc (finLoc V u g) (nullPart_comm _ Kc (σ _)
        (fun h z => hcomm _ (finLoc_inv_mul V u g) h z) hy)) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_nullPart hρ hKcc hxKc (h ▸ Submodule.mem_top)) hx0
  have h2 : ∀ Y : Submodule ℂ W, (∀ g, ∀ v ∈ Y, σ.comp (locFin V u) g v ∈ Y) →
      Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc = ⊥ → Y = ⊥ :=
    fun Y hY h => le_bot_iff.1 (hnull ▸ le_nullPart hρ hKcc Y hY h)
  let L' : Subgroup (GfC V) := K₀ ⊓ (finLoc V u).ker
  let U : Submodule ℂ W := GlobalTheory.PRep.fixed σ L'
  have hU : ∀ g, ∀ v ∈ U, σ.comp (locFin V u) g v ∈ U := fun g v hv => mem_fix.2 fun k hk => by
    change σ k (σ (locFin V u g) v) = σ (locFin V u g) v
    rw [hcomm k hk.2 g v, mem_fix.1 hv k hk]
  have hU0 : U ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hk.1, hx0⟩
  obtain ⟨C, hCo, hCc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfin : ∀ K' : Subgroup (Gv V u), IsOpen (K' : Set (Gv V u)) →
      FiniteDimensional ℂ ↥(U ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) K') := by
    intro K' hK'
    let M : Subgroup (GfC V) := (K₀ ⊓ (Kc ⊓ K').comap (finLoc V u)) ⊓ C
    have hMo : IsOpen (M : Set (GfC V)) :=
      (hK₀.inter ((hKco.inter hK').preimage (continuous_finLoc V u))).inter hCo
    have hMc : IsCompact (M : Set (GfC V)) :=
      hCc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hMo) fun k hk => hk.2
    have := hadm.2 M hMo hMc
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.PRep.fixed σ M) fun v hv => mem_fix.2 fun k hk => ?_
    have hk1 : (locFin V u (finLoc V u k))⁻¹ * k ∈ L' :=
      ⟨K₀.mul_mem (K₀.inv_mem (hKcK₀ _ hk.1.2.1)) hk.1.1, finLoc_inv_mul V u k⟩
    rw [hsplit k v, mem_fix.1 hv.1 _ hk1]
    exact mem_fix.1 hv.2 _ hk.1.2.2
  obtain ⟨π, ⟨f, hf0, hf⟩, hπ⟩ := exists_irred hρ hKco h2 U hU hU0 hfin
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.irred, hπ, ?_⟩
  let F : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }
  have hI : ∀ g, ∀ y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)), σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)) := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u))) hy ?_ ?_ ?_
    · rintro T _ ⟨z, rfl⟩
      let T' : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
        { toLinearMap := σ ((locFin V u (finLoc V u g))⁻¹ * g) ∘ₗ T.toLinearMap
          isIntertwining' := fun h => LinearMap.ext fun w => by
            change σ _ (T (π.ρ h w)) = σ (locFin V u h) (σ _ (T w))
            rw [T.isIntertwining]
            exact hcomm _ (finLoc_inv_mul V u g) h _ }
      refine Submodule.mem_iSup_of_mem T' ⟨π.ρ (finLoc V u g) z, ?_⟩
      change T' (π.ρ (finLoc V u g) z) = σ g (T z)
      rw [T'.isIntertwining, hsplit g (T z)]
      rfl
    · simp only [map_zero]; exact zero_mem _
    · intro a b ha hb; simp only [map_add]; exact add_mem ha hb
  rcases hinv _ hI with h | h
  · refine absurd ?_ hf0
    have hr : LinearMap.range F.toLinearMap ≤ ⊥ :=
      h ▸ le_iSup (fun T : π.ρ.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range T.toLinearMap) F
    exact LinearMap.range_eq_bot.1 (le_bot_iff.1 hr)
  · exact h

end GlobalTheory.LocCompFin
