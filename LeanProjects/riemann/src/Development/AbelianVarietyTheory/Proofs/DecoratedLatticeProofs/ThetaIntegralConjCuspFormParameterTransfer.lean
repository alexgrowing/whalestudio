import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvariStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isParamVec_of_injective_equivariant {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : GlobalTheory.LFun.IsParamVec σ J L h ρ' (f x) B) : GlobalTheory.LFun.IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, GlobalTheory.LFun.IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, GlobalTheory.LFun.IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

theorem thetaKO_om_apply {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g a : GA D S)
    (x a' : GA D T) (u : WO S T → ℂ) : thetaKO om g x (om (a, a') u) = thetaKO om (g * a) (x * a') u := by
  simp only [thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem thetaKO_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {u : WO S T → ℂ}
    (hu : IsThetaFunO ψ S T u) (γ : GA D S) (hγ : γ ∈ GQ S) (g : GA D S) (x : GA D T) :
    thetaKO om (γ * g) x u = thetaKO om g x u := by
  have e : ((γ * g, x) : GA D S × GA D T) = (γ, 1) * (g, x) := by simp
  simp only [thetaKO, e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hu)

theorem thetaIntegral_param : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, TransferOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (f : WO S T → ℂ), VacFin ψ S T v f → ∀ (y : GA D S → ℂ) (B : Multiset ℂˣ), IsAutFunSm θ S y → IsCuspFun S y → IsParamVec D.sp.cm.sig S.gram (frameLat S) h ((rightReg ℂ (GA D S) ℂ).comp (embV S v)) (fun g => conj (y g)) B → (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) ≠ 0 → IsParamVec D.sp.cm.sig T.gram (frameLat T) h ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) (stepPar χS χT t (fun _ => B) w) := by
  intro hP D hT ψ θ S T χS χT om hθ hW t ht ν 𝓕 hν h𝓕 v hunr w h f hf y B hy hc hB hne
  let U : Submodule ℂ (WO S T → ℂ) := GlobalTheory.FinWeilO.thetaSub ψ S T
  have hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U := fun a a' u hu => hW.om_pres _ u hu
  let ρ0 : Representation ℂ (Gv S v) (GA D S → ℂ) := (rightReg ℂ (GA D S) ℂ).comp (embV S v)
  have hρ0 : ∀ a (z : GA D S → ℂ) g, ρ0 a z g = z (g * embV S v a) := fun _ _ _ => rfl
  let cy : GA D S → ℂ := fun g => conj (y g)
  let X : Submodule ℂ (GA D S → ℂ) := Submodule.span ℂ (Set.range fun a : Gv S v => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (Gv S v) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u, IsThetaFunO ψ S T u → ∀ x, IntegrableOn (fun g => thetaKO om g x u * z g) 𝓕 ν) ∧
      (∀ γ ∈ GQ S, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u hu x => GlobalTheory.T.thetaKernel_mul_conj_cuspForm_integrableOn hP D ψ S T χS χT om hW θ hθ ν 𝓕 hν h𝓕 u y hu hy hc (embV S v a) x,
        fun γ hγ g => ?_⟩
      show conj (y (γ * g * embV S v a)) = conj (y (g * embV S v a))
      rw [mul_assoc, hy.left γ hγ]
    | zero => exact ⟨fun u _ x => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (z + z') g) = fun g => thetaKO om g x u * z g + thetaKO om g x u * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u hu x).add (h2.1 u hu x)
    | smul c z _ h1 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (c • z) g) = fun g => c * (thetaKO om g x u * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u hu x).const_mul c
  let bf : U → X → GA D T → ℂ := fun u z x => ∫ g in 𝓕, thetaKO om g x (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
  let b : U →ₗ[ℂ] X →ₗ[ℂ] (GA D T → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u u' z => by
      funext x
      show _ = bf u z x + bf u' z x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z z.2).1 u' u'.2 x)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u z z' => by
      funext x
      show _ = bf u z x + bf u z' x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z' z'.2).1 u u.2 x)]
      congr 1; funext g
      simp [mul_add])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ a a' (u : U) (z : X), b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a z) =
      (rightReg ℂ (GA D T) ℂ).comp (embV T v) a' (b u z) := by
    intro a a' u z
    funext x
    show ∫ g in 𝓕, thetaKO om g x (om (embV S v a, embV T v a') u) * (z : GA D S → ℂ) (g * embV S v a) ∂ν =
      ∫ g in 𝓕, thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
    simp_rw [thetaKO_om_apply]
    exact GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D S ν 𝓕 hν h𝓕 (fun g => thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hW u.2 γ hγ, (hXp z z.2).2 γ hγ]) (embV S v a)
  have hx : GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ ⟨cy, hcy⟩ B :=
    isParamVec_of_injective_equivariant X.subtype (fun _ _ => rfl) Subtype.val_injective hB
  exact hT ψ S T χS χT om hW t ht v trivial hunr w h U hU ⟨f, hf.1⟩ hf X ρ ⟨cy, hcy⟩ B hx (GA D T → ℂ)
    ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) b hb hne

end GlobalTheory.ChainOnto

end
