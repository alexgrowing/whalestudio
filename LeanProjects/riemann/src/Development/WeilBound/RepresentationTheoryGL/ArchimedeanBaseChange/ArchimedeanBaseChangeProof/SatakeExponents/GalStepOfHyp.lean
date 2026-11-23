import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

structure Pre (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pre (D : Datum E n) : Pre E n := ⟨D.c, D.N, D.h, D.V, D.σ, D.m, D.pos, D.discrete, D.loc, D.inf⟩

def Pre.toDatum (D : Pre E n) (h : ∀ i, IsCsdGL (D.V i)) : Datum E n :=
  ⟨D.c, D.N, D.h, D.V, D.σ, D.m, D.pos, D.discrete, h, D.loc, D.inf⟩

def Pre.Sat (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ b : Fin D.c → Multiset ℂˣ, (∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (D.N i)) ∧
    GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (b i)) ∧ ∑ i, b i = B

def Pre.Reg (D : Pre E n) : Prop := ∀ τ, ∃ lam : DomWeight n, ∑ i, D.m i τ = infOfWeight lam

def ConjPl (w u : HeightOneSpectrum (𝓞 E)) : Prop :=
  u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) ∧ (u ≠ w ∨ ¬ IsSplitAt w)

def Pre.ThetaStable (D : Pre E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ ∀ u, ConjPl w u → D.Sat u (B.map (·⁻¹))

def Pre.cls (D : Pre E n) (i : Fin D.c) (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LocGL.IrrGL (w.adicCompletion E) :=
  GlobalTheory.LocGL.IrrGL.of (D.σ i w).ρ (D.σ i w).smooth (D.σ i w).irred

def WeightEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ τ, ∃ lam, HasWeightAt π τ lam

def Strings : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → ∀ i,
  ∃ (a d : ℕ) (P : CuspSub E a), 1 ≤ a ∧ 1 ≤ d ∧ P.IsUnitary ∧ IsNormalised P ∧ ∀ P', P.Iso P' → AscEmb (D.V i) P' d

def CuspCsd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → D.ThetaStable →
  ∀ i (a d : ℕ) (P : CuspSub E a), 1 ≤ a → 1 ≤ d → P.IsUnitary → IsNormalised P → AscEmb (D.V i) P d → P.IsCsd

def RegAlg {N : ℕ} (n : ℕ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ τ, ∃ m, HasInfCharGL V τ m ∧ m.Nodup ∧ ∀ x ∈ m, ∃ k : ℤ, x = k + ((n : ℂ) - 1) / 2

def RegPart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Pre E n), D.Reg → ∀ i,
  RegAlg n (D.V i)

def AscIso : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N a d : ℕ) (V V' : Submodule ℂ (Sm E N))
  (P : CuspSub E a), 1 ≤ N → IsDiscrete V → IsDiscrete V' → RegAlg n V → P.IsUnitary → IsNormalised P → P.IsCsd →
  AscEmb V P d → AscEmb V' P d →
  ∃ T : V ≃ₗ[ℂ] V', ∀ (o : Op E N) (φ ψ : V), ψ.1 = act o φ.1 → (T ψ).1 = act o (T φ).1

def ThetaAsc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N a d : ℕ) (V : Submodule ℂ (Sm E N))
  (P : CuspSub E a), 1 ≤ N → IsDiscrete V → RegAlg n V → P.IsUnitary → IsNormalised P → P.IsCsd → AscEmb V P d →
  ∃ V' : Submodule ℂ (Sm E N), IsDiscrete V' ∧ AscEmb V' P d ∧
    ∃ T : V ≃ₗ[ℂ] V', ∀ (o : Op E N) (φ ψ : V), ψ.1 = act (thetaOp o) φ.1 → (T ψ).1 = act o (T φ).1

def StringCsd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N a d : ℕ) (V : Submodule ℂ (Sm E N))
  (P : CuspSub E a), 1 ≤ N → IsDiscrete V → RegAlg n V → P.IsUnitary → IsNormalised P → AscEmb V P d → P.IsCsd →
  IsCsdGL V

theorem stringCsd_of (h1 : AscIso) (h2 : ThetaAsc) : StringCsd := by
  intro E _ _ _ n N a d V P hN hV hr hu hn he hc
  obtain ⟨V', hV', he', T, hT⟩ := h2 E n N a d V P hN hV hr hu hn hc he
  obtain ⟨U, hU⟩ := h1 E n N a d V V' P hN hV hV' hr hu hn hc he he'
  refine ⟨T.trans U.symm, fun o φ ψ h => ?_⟩
  have e : U ⟨act o (U.symm (T φ)).1, hV.stable o _ (U.symm (T φ)).2⟩ = T ψ :=
    Subtype.ext (by rw [hU o (U.symm (T φ)) _ rfl, U.apply_symm_apply, hT o φ ψ h])
  simp only [LinearEquiv.trans_apply]
  rw [← e, U.symm_apply_apply]

theorem csd_of (h0 : RegPart) (h1 : Strings) (h2 : CuspCsd) (h3 : StringCsd) (D : Pre E n) (hr : D.Reg) (ht : D.ThetaStable) (i : Fin D.c) :
    IsCsdGL (D.V i) := by
  obtain ⟨a, d, P, ha, hd, hu, hn, he⟩ := h1 E n D hr i
  have e := he P (Setoid.refl (α := CuspSub E a) P)
  exact h3 E n _ a d _ P (D.pos i) (D.discrete i) (h0 E n D hr i) hu hn e (h2 E n D hr ht i a d P ha hd hu hn e)

def ThetaOfCsd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Datum E n), (pre D).ThetaStable

def SplitSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ D D' : Datum E n, Weak π D → Weak π D' →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, (pre D).Sat w B ∧ (pre D').Sat w B

def GalStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n), D.Reg → D'.Reg →
  D.ThetaStable → D'.ThetaStable →
  (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ D'.Sat w B) →
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B

def GalStepOfHyp : Prop := GlobalTheory.Published.GaloisRepOfPolarizedPair → GalStep

def LocRigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n), D.Reg → D'.Reg →
  (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ D'.Sat w B) →
  ∃ e : Fin D.c ≃ Fin D'.c, ∀ i w, D.cls i w = D'.cls (e i) w

def PermSub : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n)
  (e : Fin D.c ≃ Fin D'.c) (w : HeightOneSpectrum (𝓞 E)), (∀ i, D.cls i w = D'.cls (e i) w) →
  ∀ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D'.h w (D'.σ · w)) →
    GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w))

def PermSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D D' : Pre E n)
  (e : Fin D.c ≃ Fin D'.c) (w : HeightOneSpectrum (𝓞 E)), (∀ i, D.cls i w = D'.cls (e i) w) → ∀ B, D.Sat w B → D'.Sat w B

theorem rigid_of (hW : WeightEx) (hT : ThetaOfCsd) (hS : SplitSat) (hG : GalStep) (hL : LocRigid) (hP : PermSub)
    (hQ : PermSat) : Rigid := by
  intro E _ _ _ n _ π hπ D D' hD hD' w
  have r : ∀ X : Datum E n, Weak π X → (pre X).Reg := fun X hX τ => (hW E n π hπ τ).imp fun lam h => hX.1 τ lam h
  obtain ⟨e, he⟩ := hL E n (pre D) (pre D') (r D hD) (r D' hD')
    (hG E n _ _ (r D hD) (r D' hD') (hT E n D) (hT E n D') (hS E n π hπ D D' hD hD'))
  refine ⟨hP E n (pre D) (pre D') e w fun i => he i w, fun B hB => ?_⟩
  obtain ⟨b, hb, hs⟩ := hQ E n (pre D) (pre D') e w (fun i => he i w) _ ⟨B, hB, rfl⟩
  exact ⟨b, hb, hs.symm⟩

def Pre.SplitAt (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w)) ∧
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

def Pre.Weak (π : Submodule ℂ (UA E n → ℂ)) (D : Pre E n) : Prop :=
  (∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam) ∧
    {w | IsSplitAt w ∧ ¬ D.SplitAt π w}.Finite ∧ D.ThetaStable

def PreSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ D : Pre E n, D.Weak π ∧
    (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧ ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ B, D.Sat w B

def PreInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w, IsUnramU π w → ¬ IsSplitAt w → ∃ D : Pre E n, D.Weak π ∧
    ∀ B, D.Sat w B → ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt π w s ϖ q α → B = GlobalTheory.LGrp.bcParam n α

theorem runSplit_of (hW : WeightEx) (h0 : RegPart) (h1 : Strings) (h2 : CuspCsd) (h3 : StringCsd) (h : PreSplit) : RunSplit := by
  intro E _ _ _ hE n hn π hπ S hS1
  obtain ⟨D, hD, hS, hI⟩ := h E hE n hn π hπ S hS1
  have hc := csd_of h0 h1 h2 h3 D (fun τ => (hW E n π hπ τ).imp fun lam h => hD.1 τ lam h) hD.2.2
  exact ⟨D.toDatum hc, ⟨hD.1, hD.2.1⟩, hS, fun w a b => by
    obtain ⟨_, b', hb, _⟩ := hI w a b
    exact ⟨b', hb⟩⟩

theorem runInert_of (hW : WeightEx) (h0 : RegPart) (h1 : Strings) (h2 : CuspCsd) (h3 : StringCsd) (h : PreInert) : RunInert := by
  intro E _ _ _ hE n hn π hπ w a b
  obtain ⟨D, hD, hS⟩ := h E hE n hn π hπ w a b
  have hc := csd_of h0 h1 h2 h3 D (fun τ => (hW E n π hπ τ).imp fun lam h => hD.1 τ lam h) hD.2.2
  exact ⟨D.toDatum hc, ⟨hD.1, hD.2.1⟩, fun B hB => hS _ ⟨B, hB, rfl⟩⟩

theorem field_of (h75 : GlobalTheory.Published.GaloisRepOfPolarizedPair) (hW : WeightEx) (h0 : RegPart) (h1 : Strings) (h2 : CuspCsd)
    (h3 : AscIso) (h4 : ThetaAsc) (hT : ThetaOfCsd) (hS : SplitSat) (hG : GalStepOfHyp) (hL : LocRigid) (hP : PermSub) (hQ : PermSat)
    (hA : PreSplit) (hB : PreInert) : GlobalTheory.Published.BaseChangeIsobaric :=
  baseChangeIsobaric_of (runSplit_of hW h0 h1 h2 (stringCsd_of h3 h4) hA)
    (runInert_of hW h0 h1 h2 (stringCsd_of h3 h4) hB) (rigid_of hW hT hS (hG h75) hL hP hQ)

end PositivityTheory.Rg.BcB.F

end
