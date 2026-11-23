import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistenceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergCombStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem comb_of_scalar {X A M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s) (cA : A →₀ ℂ) :
    ∃ C : X →₀ ℂ, ∀ s, vac s → (cA.sum fun p z => z • a p s) = C.sum fun x z => z • r x s := by
  choose ca hca using ha
  refine ⟨Finsupp.linearCombination ℂ ca cA, fun s hs => ?_⟩
  have h : Finsupp.linearCombination ℂ (fun x => r x s) (Finsupp.linearCombination ℂ ca cA) =
      Finsupp.linearCombination ℂ (fun p => a p s) cA := by
    rw [LinearMap.map_finsupp_linearCombination]
    congr 2
    funext p
    simp only [Function.comp, hca p s hs, Finsupp.linearCombination_apply]
  calc (cA.sum fun p z => z • a p s) = Finsupp.linearCombination ℂ (fun p => a p s) cA :=
        (Finsupp.linearCombination_apply ℂ cA).symm
    _ = _ := h.symm
    _ = _ := Finsupp.linearCombination_apply ℂ _

theorem comb_transfer {X A B M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (b : B → Module.End ℂ M)
    (hmodel : ∀ c : X →₀ ℂ, ∀ s, s ≠ 0 → vac s → (c.sum fun x z => z • r x s) = 0 →
      ∀ s', vac s' → (c.sum fun x z => z • r x s') = 0)
    (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s)
    (hb : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → b p s = c.sum fun x z => z • r x s)
    (cA : A →₀ ℂ) (cB : B →₀ ℂ) (s0 : M) (h0 : s0 ≠ 0) (hv : vac s0)
    (heq : (cA.sum fun p z => z • a p s0) = cB.sum fun p z => z • b p s0) :
    ∀ s, vac s → (cA.sum fun p z => z • a p s) = cB.sum fun p z => z • b p s := by
  obtain ⟨CA, hA⟩ := comb_of_scalar vac r a ha cA
  obtain ⟨CB, hB⟩ := comb_of_scalar vac r b hb cB
  have hsub : ∀ s, ((CA - CB).sum fun x z => z • r x s) =
      (CA.sum fun x z => z • r x s) - CB.sum fun x z => z • r x s := by
    intro s
    have e : ∀ C : X →₀ ℂ, (C.sum fun x z => z • r x s) = Finsupp.linearCombination ℂ (fun x => r x s) C :=
      fun C => (Finsupp.linearCombination_apply ℂ C).symm
    rw [e, e, e, map_sub]
  have h0' : ((CA - CB).sum fun x z => z • r x s0) = 0 := by
    rw [hsub, ← hA _ hv, ← hB _ hv, heq, sub_self]
  intro s hs
  have h := hmodel (CA - CB) s0 h0 hv h0' s hs
  rw [hsub, sub_eq_zero, ← hA s hs, ← hB s hs] at h
  exact h

theorem howe_on_span (hH : HoweUnram) {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ}
    {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}
    (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (s0 : M) (h0 : s0 ≠ 0) (hv : LocVac ρ s0) :
    (∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L),
        (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (g, 1) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun h => ω (1, h) s0)) ∧
    ∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun g => ω (g, 1) s0) := by
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  set M0 := Submodule.span ℂ (Set.range fun x => ρ x s0) with hM0
  have hs0 : s0 ∈ M0 := by
    refine Submodule.subset_span ⟨0, ?_⟩
    simp [hp.rho_zero]
  have hρ : ∀ x, ∀ m ∈ M0, ρ x m ∈ M0 := by
    intro x m hm
    have hle : M0 ≤ M0.comap (ρ x) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ρ x (ρ y s0) = (ρ x * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.rho_mul x y]
      exact M0.smul_mem _ (Submodule.subset_span ⟨x + y, rfl⟩)
    exact hle hm
  have hω : ∀ p, ∀ m ∈ M0, ω p m ∈ M0 := by
    rintro ⟨g, h⟩ m hm
    have hle : M0 ≤ M0.comap (ω (g, h)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ω (g, h) (ρ y s0) = (ω (g, h) * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.norm g h y]
      refine hρ _ _ ?_
      obtain ⟨c, hc⟩ := scal (g, h)
      rw [hc s0 hv]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨c, rfl⟩
    exact hle hm
  let ρ0 : Matrix (Fin n') (Fin n) L → Module.End ℂ M0 := fun x => (ρ x).restrict (hρ x)
  let ω0 : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M0 :=
    { toFun := fun p => (ω p).restrict (hω p)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro p p'
        ext m
        simp }
  have ρ0_val : ∀ x (m : M0), ((ρ0 x m : M0) : M) = ρ x m := fun _ _ => rfl
  have ω0_val : ∀ p (m : M0), ((ω0 p m : M0) : M) = ω p m := fun _ _ => rfl
  let t0 : M0 := ⟨s0, hs0⟩
  have hv0 : LocVac ρ0 t0 := fun u hu => Subtype.ext (hv u hu)
  have ht0 : t0 ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hspan : Submodule.span ℂ (Set.range fun x => ρ0 x t0) = ⊤ := by
    have e : (Set.range fun x => ρ0 x t0) = (Subtype.val ⁻¹' (Set.range fun x => ρ x s0) : Set M0) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hp0 : LocPair ϖ σ q δ JS JT ψ ρ0 ω0 :=
    { unr := hp.unr
      odd := hp.odd
      intS := hp.intS
      intT := hp.intT
      hermS := hp.hermS
      hermT := hp.hermT
      delta := hp.delta
      psi_int := hp.psi_int
      psi_ne := hp.psi_ne
      rho_zero := by
        ext m
        simp [ρ0, hp.rho_zero]
      rho_mul := by
        intro x y
        ext m
        have h := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.rho_mul x y)
        exact h
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, t0, hv0, rfl⟩
      norm := by
        intro g h x
        ext m
        have e := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.norm g h x)
        exact e
      fix := by
        intro g h hg hh s hs
        exact Subtype.ext (hp.fix g h hg hh s (fun u hu => congrArg Subtype.val (hs u hu))) }
  obtain ⟨h1, h2⟩ := hH L ϖ σ q δ n n' JS JT ψ M0 ρ0 ω0 hp0 t0 ht0 hv0 hspan
  constructor
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h1 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h2 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h

theorem howe_all_vacua : HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → (∀ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (k : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, k) (cT.sum fun b z => z • ω (1, b) s) = cT.sum fun b z => z • ω (1, b) s) → ∃ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, ∀ s, LocVac ρ s → (cT.sum fun b z => z • ω (1, b) s) = cS.sum fun a z => z • ω (a, 1) s) ∧ ∀ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (k, 1) (cS.sum fun a z => z • ω (a, 1) s) = cS.sum fun a z => z • ω (a, 1) s) → ∃ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, ∀ s, LocVac ρ s → (cS.sum fun a z => z • ω (a, 1) s) = cT.sum fun b z => z • ω (1, b) s := by
  intro hH L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  have model := GlobalTheory.T.locPair_vacuum_relation_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  by_cases hz : ∃ s0 : M, s0 ≠ 0 ∧ LocVac ρ s0
  · obtain ⟨s0, h0, hv⟩ := hz
    obtain ⟨hA, hB⟩ := howe_on_span hH hp s0 h0 hv
    refine ⟨fun cT hT => ?_, fun cS hS => ?_⟩
    · have hw : (cT.sum fun b z => z • ω (1, b) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun b => ω (1, b)) (fun b => scal (1, b)) cT
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cS, hcS⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hB _ hw (hT s0 hv))
      exact ⟨cS, comb_transfer (LocVac ρ) ρ (fun b => ω (1, b)) (fun a => ω (a, 1)) model
        (fun b => scal (1, b)) (fun a => scal (a, 1)) cT cS s0 h0 hv hcS.symm⟩
    · have hw : (cS.sum fun a z => z • ω (a, 1) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun a => ω (a, 1)) (fun a => scal (a, 1)) cS
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cT, hcT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hA _ hw (hS s0 hv))
      exact ⟨cT, comb_transfer (LocVac ρ) ρ (fun a => ω (a, 1)) (fun b => ω (1, b)) model
        (fun a => scal (a, 1)) (fun b => scal (1, b)) cS cT s0 h0 hv hcT.symm⟩
  · have hz' : ∀ s, LocVac ρ s → s = 0 := by
      intro s hs
      by_contra hne
      exact hz ⟨s, hne, hs⟩
    refine ⟨fun cT _ => ⟨0, fun s hs => ?_⟩, fun cS _ => ⟨0, fun s hs => ?_⟩⟩
    · simp [hz' s hs, Finsupp.sum]
    · simp [hz' s hs, Finsupp.sum]

end GlobalTheory.Hk3

end
