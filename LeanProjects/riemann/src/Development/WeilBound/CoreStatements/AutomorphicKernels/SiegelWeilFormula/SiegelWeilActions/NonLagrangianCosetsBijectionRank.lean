import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DiscFubiniVolume

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem non_lagrangian_cosets_bijection_rank (h : Hyp L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : Cs L.sd, Cr L) ≃ {q : Cs d // ¬ LagrangianCondition L (rep q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      rep (e x).1 = p * (w₁ * (cM x.2.1 * L.j (rep x.1))) := by
  have hg : ∀ x : (Σ _ : Cs L.sd, Cr L), w₁ * (cM x.2.1 * L.j (rep x.1)) ∈ rat2 σ d.Y := fun x =>
    (rat2 σ d.Y).mul_mem h.wr ((rat2 σ d.Y).mul_mem (cM_rat' h x.2.2.1 x.2.2.2) (j_rat L (rep_mem L.sd x.1)))
  have hfix : ∀ x : (Σ _ : Cs L.sd, Cr L), Fix L (cM x.2.1 * L.j (rep x.1)) := fun x => fix_mul (fix_cM' h _) (fix_j _)
  let Fm : (Σ _ : Cs L.sd, Cr L) → {q : Cs d // ¬ LagrangianCondition L (rep q)} := fun x =>
    ⟨Quotient.mk _ ⟨_, hg x⟩, by
      obtain ⟨p, hp, -, e⟩ := out_mk d ⟨_, hg x⟩
      rw [e, lagrangian_condition_parabolic_iff hp]
      exact not_lagrangian_w1_mul h (hfix x)⟩
  have hinj : Function.Injective Fm := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ hE
    have hE' : (Quotient.mk _ ⟨_, hg ⟨q₁, c₁⟩⟩ : Cs d) = Quotient.mk _ ⟨_, hg ⟨q₂, c₂⟩⟩ := congrArg Subtype.val hE
    rw [mk_eq_mk] at hE'
    set g₁ := w₁ * (cM c₁.1 * L.j (rep q₁))
    set g₂ := w₁ * (cM c₂.1 * L.j (rep q₂))
    have e : (g₂ * g₁⁻¹) * (w₁ * (cM c₁.1 * L.j (rep q₁))) = w₁ * (cM c₂.1 * L.j (rep q₂)) := by
      simp only [g₁, g₂]; group
    have hpr : g₂ * g₁⁻¹ ∈ rat2 σ d.Y := (rat2 σ d.Y).mul_mem (hg ⟨q₂, c₂⟩) ((rat2 σ d.Y).inv_mem (hg ⟨q₁, c₁⟩))
    obtain ⟨hP, hc⟩ := inj_core h hE' hpr (rep_mem L.sd q₁) (rep_mem L.sd q₂) e
    have hq : q₁ = q₂ := by
      rw [← mk_rep L.sd q₁, ← mk_rep L.sd q₂, mk_eq_mk]
      exact hP
    subst hq
    rw [hc rfl]
  have hsurj : Function.Surjective Fm := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hp, hpr, hfx⟩ := normalize h (rep_mem d q) hq
    have hr : w₁⁻¹ * (p * rep q) ∈ rat2 σ d.Y :=
      (rat2 σ d.Y).mul_mem ((rat2 σ d.Y).inv_mem h.wr) ((rat2 σ d.Y).mul_mem hpr (rep_mem d q))
    obtain ⟨s, c, γ', hsr, hW, hγ', -, hx⟩ := stab_dec h hr hfx
    obtain ⟨p', hp', hp'r, he'⟩ := out_mk L.sd ⟨γ', hγ'⟩
    obtain ⟨p₂, hp₂, hp₂r, c₂, hc₂⟩ := conj_par h ((par2 σ L.Y).inv_mem hp') ((rat2 σ L.Y).inv_mem hp'r) c
    refine ⟨⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩, Subtype.ext ?_⟩
    show (Quotient.mk _ ⟨_, hg ⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩⟩ : Cs d) = q
    conv_rhs => rw [← mk_rep d q]
    rw [mk_eq_mk]
    have hγ'' : γ' = p'⁻¹ * rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd) := by rw [he']; group
    have key : p * rep q = (w₁ * s * w₁⁻¹) * p₂ * (w₁ * (cM c₂.1 * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd)))) := by
      have h1 : p * rep q = w₁ * (s * (cM c.1 * L.j γ')) := by rw [← hx]; group
      rw [h1]
      conv_lhs => rw [hγ'', map_mul]
      have h2 : w₁ * (s * (cM c.1 * (L.j p'⁻¹ * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd))))) =
          (w₁ * s * w₁⁻¹) * ((w₁ * (cM c.1 * L.j p'⁻¹)) * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd))) := by group
      rw [h2, hc₂]
      group
    have : rep q * (w₁ * (cM c₂.1 * L.j (rep (Quotient.mk _ ⟨γ', hγ'⟩ : Cs L.sd))))⁻¹ = p⁻¹ * ((w₁ * s * w₁⁻¹) * p₂) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, key]; group
    rw [this]
    exact (par2 σ d.Y).mul_mem ((par2 σ d.Y).inv_mem hp) ((par2 σ d.Y).mul_mem hW hp₂)
  refine ⟨Equiv.ofBijective Fm ⟨hinj, hsurj⟩, fun x => ?_⟩
  obtain ⟨p, hp, hpr, e⟩ := out_mk d ⟨_, hg x⟩
  exact ⟨p, hp, hpr, e⟩

end PositivityTheory.SiegelWeilFormula.Act.C6

end
