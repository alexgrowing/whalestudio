import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 (K2)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Generic

variable {G H : Type} [Group G] [Group H] [Subsingleton H]

private theorem hint_prod (K : Subgroup G) (K₂ : Subgroup H) (u : G × H → ℂ)
    (hu : ∀ k ∈ K.prod K₂, ∀ x, u (x * k) = u x) : hint (K.prod K₂) u = hint K fun g => u (g, 1) := by
  have hv : ∀ k ∈ K, ∀ x, (fun g => u (g, 1)) (x * k) = (fun g => u (g, 1)) x := by
    intro k hk x
    have := hu (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩) (x, 1)
    simpa using this
  rw [UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.hintSph (G × H) (K.prod K₂) u hu, UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.hintSph G K _ hv]
  have hout : ∀ y : G × H, u ((y : (G × H) ⧸ K.prod K₂).out) = u y := by
    intro y
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.prod K₂) y
    rw [hh]
    exact hu h h.2 y
  symm
  refine finsum_eq_of_bijective (fun q : G ⧸ K => (((q.out, 1) : G × H) : (G × H) ⧸ K.prod K₂)) ⟨?_, ?_⟩ ?_
  · intro p q h
    have h' := QuotientGroup.eq.1 h
    have h1 : p.out⁻¹ * q.out ∈ K := by simpa using (Subgroup.mem_prod.1 h').1
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 h1
  · intro q'
    obtain ⟨⟨x, h⟩, rfl⟩ := QuotientGroup.mk_surjective q'
    refine ⟨(x : G ⧸ K), QuotientGroup.eq.2 ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    refine Subgroup.mem_prod.2 ⟨?_, ?_⟩
    · simp [hk]
    · rw [Subsingleton.elim (((((x : G ⧸ K).out, 1) : G × H)⁻¹ * (x, h)).2) 1]
      exact K₂.one_mem
  · intro q
    exact (hout _).symm

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tj_zero (w : Pl E) (j : ℕ) (y : GLw 0 w) : Tj ℂ 0 (Ov E w) (unif w) j y = 1 := by
  unfold Tj
  refine Set.indicator_of_mem ?_ _
  exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, Subsingleton.elim _ _⟩

private def toFirst (n : ℕ) (p : Fin (n + 1) × Fin (0 + 1)) : Ex (Fin (n + 1)) := .gen p.1

private theorem fn2_zero_apply_one_eq_fn1_bind (w : Pl E) (e : Ex (Fin (n + 1) × Fin (0 + 1))) (g : GLw n w) :
    fn2 n 0 w e (g, 1) = fn1 n w (e.bind (toFirst n)) g := by
  induction e generalizing g with
  | one =>
    show (K2 n 0 w : Set (GLw n w × GLw 0 w)).indicator (1 : GLw n w × GLw 0 w → ℂ) (g, 1) =
      (KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) g
    by_cases h : g ∈ KGL w n
    · rw [Set.indicator_of_mem (show (g, (1 : GLw 0 w)) ∈ (K2 n 0 w : Set _) from
        Subgroup.mem_prod.2 ⟨h, Subgroup.one_mem _⟩), Set.indicator_of_mem (show g ∈ (KGL w n : Set _) from h)]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h (Subgroup.mem_prod.1 h').1),
        Set.indicator_of_notMem (show g ∉ (KGL w n : Set _) from h)]
  | gen p =>
    show Tj ℂ n (Ov E w) (unif w) p.1 g * Tj ℂ 0 (Ov E w) (unif w) p.2 1 = Tj ℂ n (Ov E w) (unif w) p.1 g
    rw [tj_zero, mul_one]
  | smul c a ih =>
    show c * fn2 n 0 w a (g, 1) = c * fn1 n w (a.bind (toFirst n)) g
    rw [ih]
  | add a b iha ihb =>
    show fn2 n 0 w a (g, 1) + fn2 n 0 w b (g, 1) = fn1 n w (a.bind (toFirst n)) g + fn1 n w (b.bind (toFirst n)) g
    rw [iha, ihb]
  | mul a b iha ihb =>
    show hint (K2 n 0 w) (fun z => fn2 n 0 w a z * fn2 n 0 w b (z⁻¹ * (g, 1))) =
      hint (KGL w n) fun z => fn1 n w (a.bind (toFirst n)) z * fn1 n w (b.bind (toFirst n)) (z⁻¹ * g)
    have hA := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E n 0 w a
    have hB := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E n 0 w b
    rw [hint_prod (KGL w n) (KGL w 0) _ fun c hc z => ?_]
    · congr 1
      funext z
      rw [iha, ← ihb]
      congr 2
      simp
    · show fn2 n 0 w a (z * c) * fn2 n 0 w b ((z * c)⁻¹ * (g, 1)) = fn2 n 0 w a z * fn2 n 0 w b (z⁻¹ * (g, 1))
      rw [(hA.2 c hc z).2, _root_.mul_inv_rev, mul_assoc, (hB.2 c⁻¹ ((K2 n 0 w).inv_mem hc) _).1]

private theorem ev_bind (w : Pl E) (B : Multiset ℂˣ) (e : Ex (Fin (n + 1) × Fin (0 + 1))) :
    ev2 n 0 w e B 0 = ev1 n w (e.bind (toFirst n)) B := by
  have h0 : ∀ p : Fin (n + 1) × Fin (0 + 1), satEig (qV E w) 0 0 p.2 = 1 := by
    intro p
    have h : ((p.2 : Fin (0 + 1)) : ℕ) = 0 := by
      have := p.2.2
      omega
    rw [h]
    exact GlobalTheory.LFun.ConjPlace.satEig_zero _ _ _
  induction e with
  | one => rfl
  | gen p =>
    show satEig (qV E w) n B p.1 * satEig (qV E w) 0 0 p.2 = satEig (qV E w) n B p.1
    rw [h0, mul_one]
  | smul c a ih =>
    show c * ev2 n 0 w a B 0 = c * ev1 n w (a.bind (toFirst n)) B
    rw [ih]
  | add a b iha ihb =>
    show ev2 n 0 w a B 0 + ev2 n 0 w b B 0 = ev1 n w (a.bind (toFirst n)) B + ev1 n w (b.bind (toFirst n)) B
    rw [iha, ihb]
  | mul a b iha ihb =>
    show ev2 n 0 w a B 0 * ev2 n 0 w b B 0 = ev1 n w (a.bind (toFirst n)) B * ev1 n w (b.bind (toFirst n)) B
    rw [iha, ihb]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.ex2Act_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.ExAct → Ex2Act := by
  intro hEx E _ _ _ n w e
  have hf : (fun g => fn2 n 0 w e (g, 1)) = fn1 n w (e.bind (toFirst n)) := funext fun g => fn2_zero_apply_one_eq_fn1_bind w e g
  obtain ⟨h1, h2⟩ := hEx E n w (e.bind (toFirst n))
  rw [hf]
  refine ⟨h1, fun V _ _ ρ x B hx => ?_⟩
  rw [ev_bind]
  exact h2 V ρ x B hx
