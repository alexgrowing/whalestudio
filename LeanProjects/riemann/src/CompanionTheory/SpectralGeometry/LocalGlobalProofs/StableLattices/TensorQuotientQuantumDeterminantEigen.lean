import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphismStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernelStatement

noncomputable section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

namespace GlobalTheory.CompanionTheory.RgTransport.Raise

theorem exists_capelliPoly_eq_sum {m : ℕ} (χ : Fin m → ℂ) :
    ∃ a : ℕ → ℂ, ∀ Y : ℂ, Formalism.QuantumDeterminants.capP χ Y = ∑ j ∈ Finset.range (m + 1), Y ^ j * a j := by
  let p : Polynomial ℂ := ∏ s : Fin m, (Polynomial.X + Polynomial.C (χ s))
  have hd : p.natDegree ≤ m := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ _s : Fin m, 1 := Finset.sum_le_sum fun s _ => (Polynomial.natDegree_X_add_C _).le
      _ = m := by simp
  refine ⟨p.coeff, fun Y => ?_⟩
  have e : Formalism.QuantumDeterminants.capP χ Y = p.eval Y := by
    simp [p, Formalism.QuantumDeterminants.capP, Polynomial.eval_prod]
  rw [e, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_raised : StepChar → TensDecomp → ∀ {m : ℕ} (M : GMod m) (χ : Fin m → ℂ), HasChar M χ →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin m → Fin m → Module.End ℂ V), GlRel E →
    ∀ Φ : (Fin m → M.V) →ₗ[ℂ] V, (∀ a b u, Φ (tensE M a b u) = E a b (Φ u)) → Φ ≠ 0 →
    ∃ r, ∃ w ∈ LinearMap.range Φ, w ≠ 0 ∧ ∀ Y : ℂ,
      qdet E (Y + ((m : ℂ) - 1) / 2) w = Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • w := by
  intro hS hT m M χ hM V _ _ E hE Φ hΦ hne
  have hsup := hT m M χ hM
  obtain ⟨r, hr⟩ : ∃ r, ¬ stepSub M (χ r) ≤ LinearMap.ker Φ := by
    by_contra h
    push Not at h
    have h' : (⊤ : Submodule ℂ (Fin m → M.V)) ≤ LinearMap.ker Φ := hsup ▸ iSup_le h
    exact hne (LinearMap.ker_eq_top.1 (top_le_iff.1 h'))
  obtain ⟨N, hN⟩ := hS m M χ r hM
  let f : (step M (χ r)).V →ₗ[ℂ] V := Φ ∘ₗ (stepSub M (χ r)).subtype
  have hf : ∀ a b x, f ((step M (χ r)).E a b x) = E a b (f x) := fun a b x => hΦ a b x.1
  let D : ℂ → Module.End ℂ V := fun Y =>
    qdet E (Y + ((m : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • (1 : Module.End ℂ V)
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h0
    refine hr fun x hx => ?_
    have : f ⟨x, hx⟩ ∈ LinearMap.range f := ⟨_, rfl⟩
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hsh : ∀ Y x, f ((qdet (step M (χ r)).E (Y + ((m : ℂ) - 1) / 2) -
      Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • (1 : Module.End ℂ (step M (χ r)).V)) x) = D Y (f x) := fun Y x =>
    shift_lin f _ _ (fun y => qdet_lin f (step M (χ r)).E E hf _ y) _ x
  have hcomm : ∀ Y Y', Commute (D Y) (D Y') := by
    intro Y Y'
    have h0 : Commute (qdet E (Y + ((m : ℂ) - 1) / 2)) (qdet E (Y' + ((m : ℂ) - 1) / 2)) :=
      GlobalTheory.CentreFin.commute_qdet (fun a b => qDetCentral _ m E hE _ a b) _
    refine Commute.sub_left (Commute.sub_right h0 ((Commute.one_right _).smul_right _)) ?_
    exact ((Commute.one_left _).smul_left _).sub_right ((Commute.one_left _).smul_left _ |>.smul_right _)
  have hst : ∀ Y, ∀ x ∈ LinearMap.range f, D Y x ∈ LinearMap.range f := by
    rintro Y _ ⟨x, rfl⟩
    exact ⟨_, hsh Y x⟩
  have hnil : ∀ Y, ∀ x ∈ LinearMap.range f, ∃ k : ℕ, (D Y ^ k) x = 0 := by
    rintro Y _ ⟨x, rfl⟩
    refine ⟨N, ?_⟩
    have e := pow_lin f _ (D Y) (hsh Y) N x
    rw [hN Y] at e
    simpa using e.symm
  obtain ⟨c, -, -, hc, -⟩ := GlobalTheory.CentreFin.exists_coef E (-(((m : ℂ) - 1) / 2)) (B := ⊤) (fun _ => trivial)
  obtain ⟨a, ha⟩ := exists_capelliPoly_eq_sum (χ + Pi.single r 1)
  have hD : ∀ Y, D Y = ∑ j ∈ Finset.range (m + 1), Y ^ j • (c j - a j • (1 : Module.End ℂ V)) := by
    intro Y
    have h1 := hc Y
    rw [sub_neg_eq_add] at h1
    simp only [D, h1, ha Y, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, mul_smul]
  obtain ⟨w, hw, hw0, hwD⟩ := GlobalTheory.T.commuting_locally_nilpotent_common_kernel _ hI D hcomm hst hnil (m + 1) _ hD
  obtain ⟨x, rfl⟩ := hw
  refine ⟨r, f x, ⟨_, rfl⟩, hw0, fun Y => ?_⟩
  have h2 := hwD Y
  simpa [D, sub_eq_zero] using h2

end GlobalTheory.CompanionTheory.RgTransport.Raise
