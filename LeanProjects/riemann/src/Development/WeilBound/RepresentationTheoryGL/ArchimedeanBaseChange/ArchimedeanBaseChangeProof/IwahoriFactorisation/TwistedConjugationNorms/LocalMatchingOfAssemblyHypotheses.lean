import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

def P_contr_id : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ) (y : Fin n → ℤ)
    (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0),
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * m = tdiag ϖ y * τ

def P_contr_tw : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ)
    (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0),
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * thL n w m = tdiag ϖ y * τ

def TwistedOrbitalVanishing : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : ∀ p : G, f (p⁻¹ * δ * θ p) = 0),
    twOrb θ K δ f = 0

def TwistedOrbitalIndicatorIndex : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G) (K I : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hθK : ∀ k ∈ K, θ k ∈ K) (hI : IsLevel θ K I) (δ : G) (X : Set G)
    (hXc : IsCompact X) (hXI : ∀ i ∈ I, ∀ g : G, (i * g ∈ X ↔ g ∈ X) ∧ (g * i ∈ X ↔ g ∈ X))
    (hC : CentOK θ K I δ) (p₀ : G) (h1 : OneCoset θ I δ X p₀),
    twOrb θ K δ (X.indicator 1) = ((I.relIndex K : ℕ) : ℂ)⁻¹

def P_g1prod : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {G' : Type} [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K I : Subgroup G) (K' I' : Subgroup G')
    (δ : G) (δ' : G') (X : Set G) (X' : Set G') (p₀ : G) (p₀' : G'),
    (OneCoset θ I δ X p₀ → OneCoset θ' I' δ' X' p₀' →
      OneCoset (θ.prodMap θ') (I.prod I') (δ, δ') (X ×ˢ X') (p₀, p₀')) ∧
    (CentOK θ K I δ → CentOK θ' K' I' δ' → CentOK (θ.prodMap θ') (K.prod K') (I.prod I') (δ, δ'))

def TwistedClassSumSingleOrbit : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt f : G → ℂ) (δ₀ : G) (c : ℂ) (hS : δ₀ ∈ S)
    (hinv : ∀ δ ∈ S, ∀ g : G, g⁻¹ * δ * θ g ∈ S)
    (hval : ∀ g : G, wt (g⁻¹ * δ₀ * θ g) * twOrb θ K (g⁻¹ * δ₀ * θ g) f = c)
    (hone : ∀ δ ∈ S, wt δ * twOrb θ K δ f ≠ 0 → ∃ g : G, δ = g⁻¹ * δ₀ * θ g),
    clSum θ K S wt f = c

def P_g2zero : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G) (wt f : G → ℂ)
    (h : ∀ δ ∈ S, wt δ * twOrb θ K δ f = 0),
    clSum θ K S wt f = 0

def TwistedOrbitalProportional : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f₁ f₂ : G → ℂ) (c : ℂ)
    (h : ∀ p : G, f₁ (p⁻¹ * δ * θ p) = c * f₂ (p⁻¹ * δ * θ p)),
    twOrb θ K δ f₁ = c * twOrb θ K δ f₂

def DiagonalConjDistinctValuations : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (v : Fin n → ℤ) (hv : Function.Injective v) (d d' h : GLw n w)
    (hd : (∀ i j : Fin n, i ≠ j → d.val i j = 0) ∧ ∀ i, ordL (d.val i i) = v i)
    (hd' : (∀ i j : Fin n, i ≠ j → d'.val i j = 0) ∧ ∀ i, ordL (d'.val i i) = v i)
    (hh : h⁻¹ * d * h = d'),
    d = d' ∧ ∀ i j : Fin n, i ≠ j → h.val i j = 0

def TwistedConjStrictDiagonalFactor : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ) (x : Fin a → ℤ)
    (hx : StrictAnti x) (τ τ' h : GLw a w) (hτ : τ ∈ TO a w) (hτ' : τ' ∈ TO a w)
    (hh : h⁻¹ * (tdiag ϖ x * τ) * thL a w h = tdiag ϖ x * τ'),
    ∃ z ∈ twCent (thL a w) (tdiag ϖ x * τ), ∃ s ∈ TO a w, h = z * s

def Hilbert90InertPlace : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w),
    (∀ u : w.adicCompletion E, Valued.v u = 1 → cj w u = u → ∃ z, Valued.v z = 1 ∧ z * cj w z = u) ∧
    (∀ u : w.adicCompletion E, u * cj w u = 1 → ∃ z, Valued.v z = 1 ∧ u * cj w z = z)

def P_iw_facts : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (t : GLw a w),
    IsOpen (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ∧ IsCompact (GlobalTheory.LFun.KGL w a : Set (GLw a w)) ∧
    (∀ k ∈ GlobalTheory.LFun.KGL w a, thL a w k ∈ GlobalTheory.LFun.KGL w a) ∧ IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (iwGL a w) ∧
    IsLevel (MonoidHom.id _) (GlobalTheory.LFun.KGL w a) (iwGL a w) ∧ (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 ∧
    IsCompact {g : GLw a w | dcos a w t g ≠ 0}

def P_iwU_facts : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ),
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧
    IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0}

def P_nrm_twconj : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (g δ : GLw a w),
    (nrmL a w (g⁻¹ * δ * thL a w g)).val.charpoly = (nrmL a w δ).val.charpoly

def TwistedDoubleCosetStrictDiagonal : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ) (y : Fin a → ℤ)
    (hy : StrictAnti y) (δ : GLw a w) (hP : ∃ p : GLw a w, dcos a w (tdiag ϖ y) (p⁻¹ * δ * thL a w p) ≠ 0),
    (∃ p₀, OneCoset (thL a w) (iwGL a w) δ {g | dcos a w (tdiag ϖ y) g ≠ 0} p₀) ∧
      CentOK (thL a w) (GlobalTheory.LFun.KGL w a) (iwGL a w) δ ∧ HasVals (nrmL a w δ).val.charpoly (nv y)

def UnitaryHeckeSingleCoset : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0),
    (∃ p₀, OneCoset (MonoidHom.id (UL n w)) (iwU n w b) γ {g | fU n w b ϖ l g ≠ 0} p₀) ∧
      CentOK (MonoidHom.id (UL n w)) (KL n w) (iwU n w b) γ ∧ HasVals γ.1.val.charpoly (wexp n l)

def UnitaryHeckeCentralizerCondition : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (γ : UL n w)
    (hP : ∃ p : UL n w, fU n w b ϖ l (p⁻¹ * γ * p) ≠ 0) (Q₁ Q₂ : (w.adicCompletion E)[X])
    (hQ : γ.1.val.charpoly = Q₁ * Q₂) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic) (hc₁ : IsCsr w Q₁) (hc₂ : IsCsr w Q₂),
    kapSign n w Q₁ γ.1 = 1

def InertDeltaFirstCasePower : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s),
    delta w 1 Q₁ Q₂ = (-qh w) ^ (-vRes n a (lOf x) s)

def P_ext : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (a : ℕ)
    (y : Fin a → ℤ) (hy : StrictAnti y) (Q : (w.adicCompletion E)[X]) (hm : Q.Monic) (hQ : IsCsr w Q)
    (hv : HasVals Q (nv y)),
    ∃ δ : GLw a w, dcos a w (tdiag ϖ y) δ ≠ 0 ∧ (nrmL a w δ).val.charpoly = Q

def P_exu : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hb : IsWitt n w b)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (l : Fin (n / 2) → ℤ) (hl : Cone l) (Q : (w.adicCompletion E)[X])
    (hm : Q.Monic) (hQ : IsCsr w Q) (hv : HasVals Q (wexp n l)),
    ∃ γ : UL n w, fU n w b ϖ l γ ≠ 0 ∧ γ.1.val.charpoly = Q

def P_combine_caseA : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s),
    HasVals (Q₁ * Q₂) (wexp n (lOf x))

def P_split_caseA : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (x : Fin n → ℤ) (hx : StrictAnti x)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic) (hd₁ : Q₁.natDegree = a)
    (hd₂ : Q₂.natDegree = n - a) (hc₁ : IsCsr w Q₁) (hc₂ : IsCsr w Q₂) (hv : HasVals (Q₁ * Q₂) (wexp n (lOf x))),
    ∃ s, CaseA w n a x Q₁ Q₂ s

def P_asmL_A : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s),
    stTw2 a (n - a) w Q₁ Q₂ (phiX n w b ϖ x a) =
      (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹

def P_asmL_B : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (hB : ∀ s, ¬ CaseA w n a x Q₁ Q₂ s),
    stTw2 a (n - a) w Q₁ Q₂ (phiX n w b ϖ x a) = 0

def P_asmR_A : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (s : Finset (Fin (n / 2))) (hA : CaseA w n a x Q₁ Q₂ s),
    delta w 1 Q₁ Q₂ * kapOrb n w Q₁ Q₂ (fU n w b ϖ (lOf x)) =
      (-qh w) ^ (-vRes n a (lOf x) s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹

def P_asmR_B : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)) (Q₁ Q₂ : (w.adicCompletion E)[X]) (hm₁ : Q₁.Monic) (hm₂ : Q₂.Monic)
    (hd₁ : Q₁.natDegree = a) (hd₂ : Q₂.natDegree = n - a) (hs : (Q₁ * Q₂).Separable) (hc₁ : IsCsr w Q₁)
    (hc₂ : IsCsr w Q₂) (hB : ∀ s, ¬ CaseA w n a x Q₁ Q₂ s),
    kapOrb n w Q₁ Q₂ (fU n w b ϖ (lOf x)) = 0

def P_asmReg : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (n a : ℕ) (ha : a ≤ n) (b : GLw n w)
    (hb : IsWitt n w b) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (x : Fin n → ℤ) (hx : StrictAnti x)
    (hc : Cone (lOf x)),
    RegAt2 a (n - a) w (phiX n w b ϖ x a)

end PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
