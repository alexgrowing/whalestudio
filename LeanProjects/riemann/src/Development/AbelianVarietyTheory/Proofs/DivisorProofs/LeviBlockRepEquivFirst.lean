import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DiagCell

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : Type}
    [Fintype t] [DecidableEq t]
    (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL t R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : Type} [Fintype t] [DecidableEq t] (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) {g : GL t R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

end GlobalTheory.DiagCell

namespace GlobalTheory.DiagCell

theorem cellFunctor_diag_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : Type} [Fintype m] [DecidableEq m] (b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m)),
    b.1 false true = 0 → b.1 true false = 0 →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k (Two (Fin 1) m)) W), IsSmooth ρ →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j),
      Nonempty ((cellFunctor f g ρ).Equiv ρ) := by
  intro k _ _ _ _ m _ _ b h01 h10 W _ _ ρ hsm
  have hrz : ∀ i j, j ≠ i → b.1 i j = 0 := by
    intro i j hj
    cases i <;> cases j <;> simp_all
  have hcz : ∀ j i, i ≠ j → b.1 i j = 0 := fun j i hi => hrz i j (Ne.symm hi)
  have hcard : ∀ i, Fintype.card (Fin (b.1 i i)) = Fintype.card (Two (Fin 1) m i) := by
    intro i
    have r := b.2.1 i
    rw [Fintype.sum_bool] at r
    cases i <;> simp_all
  let E : ∀ i, Fin (b.1 i i) ≃ Two (Fin 1) m i := fun i => Fintype.equivOfCardEq (hcard i)
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i := fun i =>
    (OneBlockCell.valEquiv (n := fun j => b.1 i j) i rfl (fun j hj => hrz i j hj)).trans (E i)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j := fun j =>
    (OneBlockCell.valEquiv (n := fun i => b.1 i j) j rfl (fun i hi => hcz j i hi)).trans (E j)
  refine ⟨f, g, ?_⟩
  have hbot : twKer ρ (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (Two (Fin 1) m)) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) i (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      OneBlockCell.deltaHalf_eq_one_of_single i (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      OneBlockCell.deltaHalf_eq_one_of_single j (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) j (fun i hi => hcz j i hi) (x j)
  have hfg : ∀ i (t : Fin (b.1 i i)), f i ⟨i, t⟩ = g i ⟨i, t⟩ := fun i t => rfl
  have hγ : ∀ (p : relParab k g),
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) =
        (p : Levi k (Two (Fin 1) m)) := by
    intro p
    funext i
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f i).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f i).surjective y
    have ha : a = i := by
      by_contra hne
      have h1 := hrz i a hne
      have h2 := t.2
      omega
    have ha' : a' = i := by
      by_contra hne
      have h1 := hrz i a' hne
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same, hfg, hfg]
    rfl
  let Ψ : W ≃ₗ[ℂ] Jacquet ρ (relUnip k f) := (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk u := fun u => rfl
  let τ := (twist ((relJac f ρ).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ (ρ p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ, hγ p]
    simp only [inv_one, Units.val_one, one_smul]
  let F : ρ.IntertwiningMap (cellFunctor f g ρ) :=
    { toFun := fun u => ⟨⟨fun x => Ψ (ρ x u), fun p x => by
          show Ψ (ρ (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : ρ x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ (ρ (y * x) u) = Ψ (ρ y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (ρ x (ρ h u)) = Ψ (ρ (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ (ρ 1 u) = Ψ (ρ 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ (ρ x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.DiagCell
