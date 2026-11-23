import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix Filter Topology

noncomputable section

namespace GlobalTheory.CuspRep.TailFix

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem entry_int {w : HeightOneSpectrum (𝓞 E)} {g : GL (Fin a) (w.adicCompletion E)} (hg : g ∈ KGL w a)
    (i j : Fin a) : g i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨h, rfl⟩ := hg
  exact (h i j).2

theorem tendsto_of_loc {α : Type} {l : Filter α} {f : α → Af E} {x : Af E}
    (hx : ∀ v, pLoc E v x ∈ v.adicCompletionIntegers E) (hf : ∀ b v, pLoc E v (f b) ∈ v.adicCompletionIntegers E)
    (h : ∀ v, ∀ᶠ b in l, pLoc E v (f b) = pLoc E v x) : Tendsto f l (𝓝 x) := by
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : ∀ y : Af E, (∀ v, pLoc E v y ∈ v.adicCompletionIntegers E) →
      ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletionIntegers E : Set (v.adicCompletion E)) :=
    fun y hy v => ⟨pLoc E v y, hy v⟩
  have hl : ∀ y hy, s (lift y hy) = y := fun y hy => FiniteAdeleRing.ext _ fun v => rfl
  have h1 : Tendsto (fun b => lift (f b) (hf b)) l (𝓝 (lift x hx)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| (h v).mono fun b hb => Subtype.ext hb.symm
  have h2 := (hs.tendsto _).comp h1
  rw [hl] at h2
  exact h2.congr fun b => hl _ _

theorem exists_tail {U : Set (GL (Fin a) (Af E))} (hU : U ∈ 𝓝 (1 : GL (Fin a) (Af E))) :
    ∃ F : Finset (HeightOneSpectrum (𝓞 E)), ∀ r : GL (Fin a) (Af E),
      (∀ v, GeneralLinearGroup.map (pLoc E v) r ∈ KGL v a) →
      (∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) r = 1) → r ∈ U := by
  classical
  by_contra hn
  push_neg at hn
  choose r hr1 hr2 hrU using hn
  have ent : ∀ q : Finset (HeightOneSpectrum (𝓞 E)) → GL (Fin a) (Af E),
      (∀ F v, GeneralLinearGroup.map (pLoc E v) (q F) ∈ KGL v a) →
      (∀ F, ∀ v ∈ F, GeneralLinearGroup.map (pLoc E v) (q F) = 1) →
      Tendsto (fun F => (q F).val) atTop (𝓝 1) := fun q hq1 hq2 =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (fun v => by rw [Matrix.one_apply]; split_ifs <;> simp)
        (fun F v => entry_int (hq1 F v) i j) fun v => by
        filter_upwards [eventually_ge_atTop {v}] with F hF
        have e := hq2 F v (hF (Finset.mem_singleton_self v))
        rw [← map_one (GeneralLinearGroup.map (pLoc E v))] at e
        exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) e
  have ht : Tendsto r atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent r hr1 hr2).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
      (ent (fun F => (r F)⁻¹) (fun F v => by rw [map_inv]; exact inv_mem (hr1 F v))
        (fun F v hv => by rw [map_inv, hr2 F v hv, inv_one])))
  obtain ⟨F, hF⟩ := (ht.eventually hU).exists
  exact hrU F hF

end GlobalTheory.CuspRep.TailFix

open GlobalTheory.CuspRep.TailFix in

theorem GlobalTheory.CuspRep.fixed_of_locFixed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)),
    (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E),
    (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a) →
    (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  classical
  intro E _ _ _ a φ hφ S hS k hk1 hk2
  have hU : {x : GL (Fin a) (Af E) | finRep E a x φ = φ} ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
    hφ.level.mem_nhds (by simp)
  obtain ⟨F, hF⟩ := exists_tail hU
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w a) →
      (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∀ w ∈ F, w ∉ T → GeneralLinearGroup.map (pLoc E w) k = 1) → finRep E a k φ = φ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k h1 h2 h3
      refine hF k (fun v => ?_) (fun v hv => h3 v hv (by simp))
      by_cases hv : v ∈ S
      · rw [h2 v hv]; exact one_mem _
      · exact h1 v hv
    | insert w T hw ih =>
      intro k h1 h2 h3
      obtain ⟨g, hg⟩ : ∃ g, g = locGL E a w (GeneralLinearGroup.map (pLoc E w) k) := ⟨_, rfl⟩
      have hgH : finRep E a g φ = φ := by
        by_cases hwS : w ∈ S
        · rw [hg, h2 w hwS, map_one, map_one]; rfl
        · rw [hg]; exact hS w hwS _ (h1 w hwS)
      have e : ∀ v, GeneralLinearGroup.map (pLoc E v) (g⁻¹ * k) =
          if v = w then 1 else GeneralLinearGroup.map (pLoc E v) k := fun v => by
        rw [map_mul, map_inv]
        split_ifs with hv
        · subst hv; rw [hg, pLoc_locGL, inv_mul_cancel]
        · rw [hg, pLoc_locGL_of_ne hv, inv_one, one_mul]
      have hk' : finRep E a (g⁻¹ * k) φ = φ := by
        refine ih _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv hvT => ?_)
        · rw [e]; split_ifs
          · exact one_mem _
          · exact h1 v hv
        · rw [e]; split_ifs
          · rfl
          · exact h2 v hv
        · rw [e]; split_ifs with h
          · rfl
          · exact h3 v hv (by simp [h, hvT])
      calc finRep E a k φ = finRep E a (g * (g⁻¹ * k)) φ := by rw [mul_inv_cancel_left]
        _ = φ := by rw [map_mul, Module.End.mul_apply, hk', hgH]
  exact key F k hk1 hk2 (fun w hw hwF => absurd hw hwF)
