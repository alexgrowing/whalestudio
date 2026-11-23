import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreB
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreC
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreD
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDiscreteUOfIsDiscrete

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

namespace Core

def locFn {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) (F : Sm E N) (y : GA E N) : GL (Fin N) (w.adicCompletion E) → ℂ :=
  fun g => F.1 (y * finGL E N (locGL E N w g))

def locRepU {m : ℕ} (w : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (Sm E m))
    (hst : ∀ g : GL (Fin m) (Af E), ∀ ψ ∈ U, finRep E m g ψ ∈ U) :
    Representation ℂ (GL (Fin m) (w.adicCompletion E)) U :=
  GlobalTheory.PRep.sub ((finRep E m).comp (locGL E m w)) U fun g ψ hψ => hst _ ψ hψ

theorem evT_piTensor_locRepU {c : ℕ} {n : Fin c → ℕ} (w : HeightOneSpectrum (𝓞 E)) (U : ∀ i, Submodule ℂ (Sm E (n i)))
    (hst : ∀ i (g : GL (Fin (n i)) (Af E)), ∀ ψ ∈ U i, finRep E (n i) g ψ ∈ U i) (x : ∀ i, GA E (n i))
    (μ : ∀ i, GL (Fin (n i)) (w.adicCompletion E)) (v : ⨂[ℂ] i, U i) :
    evT (fun i => evAt (U i) (x i)) (piTensor (fun i => locRepU w (U i) (hst i)) μ v) =
      evT (fun i => evAt (U i) (x i * finGL E (n i) (locGL E (n i) w (μ i)))) v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r ψ =>
    rw [map_smul, map_smul, map_smul, piTensor_tprod, evT_tprod, evT_tprod]
    rfl
  | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

end Core

open PositivityTheory.Rg.Rs.SatakeVectors.Core in

theorem isSatVecGL_of_ind {c N : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) {w : HeightOneSpectrum (𝓞 E)}
    (U : ∀ i, Submodule ℂ (Sm E (n i)))
    (hst : ∀ i (g : GL (Fin (n i)) (Af E)), ∀ ψ ∈ U i, finRep E (n i) g ψ ∈ U i)
    (hsm : ∀ i, ∀ ψ ∈ U i, IsOpen {g : GL (Fin (n i)) (w.adicCompletion E) | finRep E (n i) (locGL E (n i) w g) ψ = ψ})
    (S : Fin c → Multiset ℂˣ) (hS : ∀ i, SatLike (U i) w (S i))
    {F : Sm E N} (h0 : F ≠ 0) (hK : ∀ k ∈ GlobalTheory.LFun.KGL w N, finRep E N (locGL E N w k) F = F)
    (hu : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, F.1 (u * g) = F.1 g)
    (ht : ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => F.1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈
        GlobalTheory.BCWords.tensorSp U) :
    GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) F
      (∑ i, (S i).map (· * qU w ((modExp (fun i => Fin (n i)) i : ℂ) / 2))) := by
  classical
  set Bt := ∑ i, (S i).map (· * qU w ((modExp (fun i => Fin (n i)) i : ℂ) / 2)) with hBt

  have key : ∀ y₀ : GA E N,
      Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) y₀) = 1 →
      locFn w F y₀ = 0 ∨ GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.PRep.rightReg ℂ _ ℂ) (locFn w F y₀) Bt := by
    intro y₀ hy₀
    by_cases hG0 : locFn w F y₀ = 0
    · exact Or.inl hG0
    right
    obtain ⟨u, hu₀, m, k, hy⟩ := iwasawa_inf n h y₀
    set g₀ := Matrix.GeneralLinearGroup.map (pFin E) y₀ with hg₀
    obtain ⟨v, hv⟩ := exists_tensor U (ht k g₀)
    have hs : ∀ i, GlobalTheory.PRep.IsSmooth (locRepU w (U i) (hst i)) := fun i ψ => by
      have e : {g : GL (Fin (n i)) (w.adicCompletion E) | locRepU w (U i) (hst i) g ψ = ψ} =
          {g | finRep E (n i) (locGL E (n i) w g) ψ.1 = ψ.1} := by
        ext g; exact Subtype.ext_iff
      rw [e]; exact hsm i ψ.1 ψ.2
    have hS' : ∀ i, ∀ x ∈ GlobalTheory.PRep.fixed (locRepU w (U i) (hst i)) (GlobalTheory.LFun.KGL w (n i)), x ≠ 0 →
        GlobalTheory.LFun.IsSatVecGL w (locRepU w (U i) (hst i)) x (S i) := fun i x hx hx0 =>
      GlobalTheory.LFun.IsSatVecGL.of_map (U i).subtype (fun _ _ => rfl) Subtype.val_injective
        (hS i x.1 x.2 (fun k' hk' => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k' hk'))
          fun e => hx0 (Subtype.ext e))

    have hcomm : ∀ x : GL (Fin N) (w.adicCompletion E),
        (infGL E N (Unitary.toUnits k) * finGL E N g₀) * finGL E N (locGL E N w x) =
          finGL E N (locGL E N w x) * (infGL E N (Unitary.toUnits k) * finGL E N g₀) := fun x => by
      rw [mul_assoc, ← map_mul, LocSph.comm_locGL w g₀ hy₀ x, map_mul, ← mul_assoc, ← mul_assoc, infGL_comm]
    refine isSatVecGL_of_levi h (X := fun i => U i) (π := fun i => locRepU w (U i) (hst i)) hs S hS'
      (fun i => qU w ((modExp (fun i => Fin (n i)) i : ℂ) / 2)) (fun i => rfl)
      (fun i => evAt (U i) (infGL E (n i) (m i))) (locFn w F y₀) (fun g k' hk' => ?_) (fun u' hu' g => ?_) v
      (fun μ => ?_) hG0
    · show F.1 (y₀ * finGL E N (locGL E N w (g * k'))) = F.1 (y₀ * finGL E N (locGL E N w g))
      rw [map_mul, map_mul, ← mul_assoc]
      exact congrArg (fun φ : Sm E N => φ.1 (y₀ * finGL E N (locGL E N w g))) (hK k' hk')
    · show F.1 (y₀ * finGL E N (locGL E N w (u' * g))) = F.1 (y₀ * finGL E N (locGL E N w g))
      rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hy₀, mul_assoc]
      exact hu _ (finGL_locGL_mem_unipRad n h w hu') _
    · rw [evT_piTensor_locRepU, ← hv]
      show F.1 (y₀ * finGL E N (locGL E N w (leviEmb (w.adicCompletion E) (stdBlocks n h) μ))) = _
      rw [hy, mul_assoc (u * _), hcomm, finGL_locGL_leviEmb, ← mul_assoc, mul_assoc u, ← map_mul, mul_assoc, hu _ hu₀]
      rfl
  have hL : ∀ (y₀ : GA E N) (g₁ : GL (Fin N) (w.adicCompletion E)),
      locFn w F (y₀ * finGL E N (locGL E N w g₁)) = fun g => locFn w F y₀ (g₁ * g) := fun y₀ g₁ => funext fun g => by
    show F.1 (y₀ * finGL E N (locGL E N w g₁) * finGL E N (locGL E N w g)) =
      F.1 (y₀ * finGL E N (locGL E N w (g₁ * g)))
    rw [map_mul, map_mul, mul_assoc]
  let large₂ : GL (Fin N) (w.adicCompletion E) →
      ((GL (Fin N) (w.adicCompletion E) → ℂ) →ₗ[ℂ] (GL (Fin N) (w.adicCompletion E) → ℂ)) :=
    fun g₁ => LinearMap.funLeft ℂ ℂ (g₁ * ·)
  have hLe : ∀ g₁ x (φ : GL (Fin N) (w.adicCompletion E) → ℂ),
      large₂ g₁ (GlobalTheory.PRep.rightReg ℂ _ ℂ x φ) = GlobalTheory.PRep.rightReg ℂ _ ℂ x (large₂ g₁ φ) := fun g₁ x φ => funext fun g => by
    show φ (g₁ * g * x) = φ (g₁ * (g * x))
    rw [mul_assoc]
  obtain ⟨y, hy⟩ : ∃ y, F.1 y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Subtype.ext (funext hc))
  obtain ⟨y₀, g₁, hy₀, rfl⟩ := exists_split_at w y
  have hne : locFn w F y₀ ≠ 0 := fun e => hy (congrFun e g₁)
  have hsat := (key y₀ hy₀).resolve_left hne
  refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k' hk' => hK k' hk', hsat.2.2.1, fun ϖ hϖ j hj => ?_⟩
  refine Subtype.ext (funext fun y' => ?_)
  obtain ⟨y₁, g₂, hy₁, rfl⟩ := exists_split_at w y'
  rw [heckeVec_apply w (GlobalTheory.LFun.Tj_mem_hecke hϖ j)]
  change GlobalTheory.LFun.heckeVec _ _ _ (locFn w F (y₁ * finGL E N (locGL E N w g₂))) 1 =
    GlobalTheory.LFun.satEig (Formalism.UG.qV E w) N Bt j * F.1 (y₁ * finGL E N (locGL E N w g₂))
  rw [hL, show (fun g => locFn w F y₁ (g₂ * g)) = large₂ g₂ (locFn w F y₁) from rfl,
    ← GlobalTheory.LFun.map_heckeVec (Formalism.UG.Final.GLintComm E w N) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (large₂ g₂) (hLe g₂)]
  show GlobalTheory.LFun.heckeVec _ _ _ (locFn w F y₁) (g₂ * 1) = _
  rcases key y₁ hy₁ with h1 | h1
  · have e0 : F.1 (y₁ * finGL E N (locGL E N w g₂)) = 0 := congrFun h1 g₂
    rw [h1, e0, mul_zero]
    have := (GlobalTheory.LFun.SatCompare.heckeLin (Formalism.UG.Final.GLintComm E w N) (GlobalTheory.LFun.Tj_mem_hecke hϖ j)
      (GlobalTheory.PRep.rightReg ℂ (GL (Fin N) (w.adicCompletion E)) ℂ)).map_zero
    exact congrFun this _
  · rw [h1.2.2.2 ϖ hϖ j hj, mul_one]
    rfl

end PositivityTheory.Rg.Rs.SatakeVectors

end
