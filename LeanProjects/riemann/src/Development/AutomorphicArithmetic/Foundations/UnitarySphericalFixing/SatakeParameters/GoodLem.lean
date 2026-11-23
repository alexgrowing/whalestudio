import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr

noncomputable section

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands UpperTheory.Zero.LLC

namespace UpperTheory.One.M

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsQg (k : Type) [Field k] [TopologicalSpace k] : Prop := ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i

theorem good_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩

theorem good_of_toral {x : IrrGL k} (h : Toral x) : Good x :=
  let ⟨s, hs, h1⟩ := h
  ⟨s, hs, fun y hy => Or.inl (h1 y hy)⟩

variable [CharZero k]

theorem good_of_one (x : IrrGL k) (h : x.1 = 1) : Good x := by
  obtain ⟨χ, hχ, rfl⟩ := ((clBasic k x).2.2.2.2.1 h).2
  exact good_ofChar χ hχ

theorem good_of_fixed (hq : IsQg k) (x : IrrGL k) (hD : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥) : Good x := by
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport Pr.zel x
  refine ⟨s, hs, fun y hy => Or.inr ⟨hq, y, 1, isSmoothChar_one, ?_, ((clBasic k y).2.2.1 _).symm⟩⟩
  obtain ⟨n, xs, hxs, hcs⟩ := hs
  have H := Pr.dzs _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
    (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hD)
  rw [← hxs] at hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨v, hv, hv0⟩ := H i
  exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩

theorem good_cls_of_fixed (hq : IsQg k) {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (hD : fixed τ.ρ (KOne k (Fin n)) ≠ ⊥) :
    Good (cls τ) :=
  good_of_fixed hq _ (fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hD)

section Close

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E _).injective

theorem Old.close (hε : IsDeligneEps ε) (H : Laws a ha ε rc) : IsRec h rc := ⟨a, ha, ε, hε, H⟩

theorem New.close (H : LawsM a ha ε rc) : IsRecT h rc := cls_of H

theorem Old.artin (hL : LocalLanglandsGL) (h : IsPlaceOver A w) : ∃ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a :=
  let ⟨_, ⟨a, ha, _⟩, _⟩ := hL.1 E Ω A w h
  ⟨a, ha⟩

theorem New.artin (hL : RecTExists) (h : IsPlaceOver A w) : ∃ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a :=
  let ⟨_, a, ha, _⟩ := hL E Ω A w h
  ⟨a, ha⟩

end Close

end UpperTheory.One.M
