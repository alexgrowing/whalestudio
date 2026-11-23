import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
  {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ}

variable (σ) in

def RootsIn (n : ℕ) : Prop := ∀ z : ℂ, z ^ n = 1 → z ∈ Set.range σ

theorem rootsIn_iff {n : ℕ} (hn : n ≠ 0) : RootsIn σ n ↔ ∃ z : K, IsPrimitiveRoot z n := by
  have : NeZero n := ⟨hn⟩
  constructor
  · intro h
    have hp := Complex.isPrimitiveRoot_exp n hn
    obtain ⟨z, hz⟩ := h _ hp.pow_eq_one
    refine ⟨z, ?_⟩
    rw [← hz] at hp
    exact hp.of_map_of_injective σ.injective
  · rintro ⟨z, hz⟩ w hw
    obtain ⟨i, -, hi⟩ := (hz.map_of_injective σ.injective).eq_pow_of_pow_eq_one hw
    exact ⟨z ^ i, by rw [map_pow, hi]⟩

variable (σ) in

def LocIn (χ : HChar D.host.E) : Prop := ∀ w x, (χ.loc w x : ℂ) ∈ Set.range σ

theorem LocIn.valuesIn {χ : HChar D.host.E} (h : LocIn σ χ) : χ.ValuesIn 0 σ := by
  intro v _
  obtain ⟨y, hy⟩ := h v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v))
  refine ⟨y, ?_⟩
  simp [Formalism.L2.Host.HChar.valTw, Formalism.L2.Host.HChar.val, Formalism.L2.Host.HChar.locK, hy]

variable (G σ) in

structure CharsIn : Prop where

  mu0 : ∀ j, LocIn σ (L.C.mu0 j)

  xi : ∀ t, LocIn σ (L.xiH t)

  chi : ∀ i, 1 ≤ i → i ≤ D.R.m → LocIn σ (G.ch.chiH i)

  eta : L.C.eta.ValuesIn (1 / 2) σ

  chiPsi : L.C.chiPsi.ValuesIn 0 σ

  del : L.C.del.ValuesIn 0 σ

  del' : L.C.del'.ValuesIn 0 σ

variable (G) in

abbrev pairLat (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True

def halfCoset {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) (k : ℕ) (x₀ : Mx D m n) : Set (Mx D m n) :=
  {x | ∃ u ∈ Λ, IsHalf e u ∧ x = x₀ + k • u}

theorem mem_halfCoset_self {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) (k : ℕ) (x₀ : Mx D m n) :
    x₀ ∈ halfCoset e Λ k x₀ := ⟨0, Λ.zero_mem, (GlobalTheory.SplitScalar.isHalf_iff e 0).2 (smul_zero e), by simp⟩

theorem halfCoset_eq {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {k : ℕ} {x₀ x : Mx D m n} (h : x ∈ halfCoset e Λ k x₀) :
    halfCoset e Λ k x = halfCoset e Λ k x₀ := by
  obtain ⟨u, hu, hue, rfl⟩ := h
  have hue' := (GlobalTheory.SplitScalar.isHalf_iff e u).1 hue
  ext y
  constructor
  · rintro ⟨v, hv, hve, rfl⟩
    refine ⟨u + v, Λ.add_mem hu hv, (GlobalTheory.SplitScalar.isHalf_iff e _).2 ?_, by rw [smul_add, add_assoc]⟩
    rw [smul_add, hue', (GlobalTheory.SplitScalar.isHalf_iff e v).1 hve]
  · rintro ⟨v, hv, hve, rfl⟩
    refine ⟨v - u, Λ.sub_mem hv hu, (GlobalTheory.SplitScalar.isHalf_iff e _).2 ?_, by rw [smul_sub]; abel⟩
    rw [smul_sub, hue', (GlobalTheory.SplitScalar.isHalf_iff e v).1 hve]

def IsCosetDatum {t : T} {p : Pair T} (k : ℕ) (d : FinDatum G t p) : Prop :=
  ∃ x₀, IsHalf d.e x₀ ∧ k • x₀ ∈ pairLat G p ∧ d.fn = (halfCoset d.e (pairLat G p) k x₀).indicator 1

theorem isCosetDatum_ind (t : T) (p : Pair T) (P h e he) : IsCosetDatum 1 (FinDatum.ind G t p P h e he) := by
  refine ⟨0, (GlobalTheory.SplitScalar.isHalf_iff e 0).2 (smul_zero e), by simp, ?_⟩
  refine (GlobalTheory.PlaceModel.halfInd_eq_ind e (pairLat G p)).trans ?_
  dsimp only [FinDatum.ind]
  have hm : ∀ x, x ∈ halfCoset e (pairLat G p) 1 0 ↔ x ∈ pairLat G p ⊓ GlobalTheory.PlaceModel.half (G.pS p) (G.pT p) e := by
    intro x
    rw [AddSubgroup.mem_inf, GlobalTheory.PlaceModel.mem_half]
    constructor
    · rintro ⟨u, hu, hue, rfl⟩
      simpa using ⟨hu, (GlobalTheory.SplitScalar.isHalf_iff e u).1 hue⟩
    · rintro ⟨hx, hxe⟩
      exact ⟨x, hx, (GlobalTheory.SplitScalar.isHalf_iff e x).2 hxe, by simp⟩
  funext x
  by_cases hx : x ∈ pairLat G p ⊓ GlobalTheory.PlaceModel.half (G.pS p) (G.pT p) e
  · rw [Set.indicator_of_mem ((hm x).2 hx), GlobalTheory.PlaceModel.ind, if_pos hx]
    rfl
  · rw [Set.indicator_of_notMem (fun h' => hx ((hm x).1 h')), GlobalTheory.PlaceModel.ind, if_neg hx]

theorem IsCosetDatum.fn_eq {t : T} {p : Pair T} {k : ℕ} {d d' : FinDatum G t p} (h : IsCosetDatum k d) (h' : IsCosetDatum k d')
    (he : d.e = d'.e) {x} (hx : d.fn x ≠ 0) (hx' : d'.fn x ≠ 0) : d.fn = d'.fn := by
  obtain ⟨x₀, -, -, hf⟩ := h
  obtain ⟨x₀', -, -, hf'⟩ := h'
  rw [hf] at hx ⊢
  rw [hf'] at hx' ⊢
  rw [← halfCoset_eq (Set.mem_of_indicator_ne_zero hx), ← halfCoset_eq (Set.mem_of_indicator_ne_zero hx'), he]

section Sums

variable {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t)

def IsCosetExpansion (k : ℕ) (τ : PureDat G t →₀ ℂ) : Prop :=
  0 < k ∧ S.IsExpansion t Φ β τ ∧ ∀ d ∈ τ.support, (∀ j, IsCosetDatum k (d.1 j)) ∧ ∀ i, IsCosetDatum k (d.2 i)

def expDepth : ℕ := sInf {k | ∃ τ, IsCosetExpansion S t Φ β k τ}

variable {S t Φ β}

theorem IsCosetExpansion.exists_expDepth {k τ} (h : IsCosetExpansion S t Φ β k τ) :
    ∃ τ', IsCosetExpansion S t Φ β (expDepth S t Φ β) τ' := Nat.sInf_mem (⟨k, τ, h⟩ : Set.Nonempty {k | ∃ τ, IsCosetExpansion S t Φ β k τ})

private theorem finDatum_ext {t : T} {p : Pair T} {d d' : FinDatum G t p} (hP : d.P = d'.P) (he : d.e = d'.e)
    (hf : d.fn = d'.fn) (hz : d.z = d'.z) : d = d' := by
  cases d
  cases d'
  cases hP
  cases he
  cases hf
  cases hz
  rfl

theorem IsCosetExpansion.coef_eq {k τ} (h : IsCosetExpansion S t Φ β k τ) {d} (hd : d ∈ τ.support) :
    ∃ x y, τ d = ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) := by
  obtain ⟨-, ⟨e, -, hde, hexp⟩, hcos⟩ := h
  choose x₁ hx₁h _ hx₁f using (hcos d hd).1
  choose y₁ hy₁h _ hy₁f using (hcos d hd).2
  have vx : ∀ j, (d.1 j).fn (x₁ j) = 1 := fun j => by
    rw [hx₁f j, Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]
    rfl
  have vy : ∀ i, (d.2 i).fn (y₁ i) = 1 := fun i => by
    rw [hy₁f i, Set.indicator_of_mem (mem_halfCoset_self _ _ _ _)]
    rfl
  refine ⟨x₁, y₁, ?_⟩
  rw [← hexp x₁ y₁ (fun j => ((hde d hd).1 j).2.1 ▸ hx₁h j) (fun i => ((hde d hd).2 i).2.1 ▸ hy₁h i), Finsupp.sum,
    Finset.sum_eq_single d]
  · simp [vx, vy]
  · intro d' hd' hne
    by_contra hnz
    apply hne
    obtain ⟨h12, h3⟩ := mul_ne_zero_iff.1 hnz
    have hj := Finset.prod_ne_zero_iff.1 (mul_ne_zero_iff.1 h12).2
    have hi := Finset.prod_ne_zero_iff.1 h3
    have e1 : ∀ j, d'.1 j = d.1 j := fun j =>
      finDatum_ext (((hde d' hd').1 j).1.trans ((hde d hd).1 j).1.symm)
        (((hde d' hd').1 j).2.1.trans ((hde d hd).1 j).2.1.symm)
        (IsCosetDatum.fn_eq ((hcos d' hd').1 j) ((hcos d hd).1 j)
          (((hde d' hd').1 j).2.1.trans ((hde d hd).1 j).2.1.symm) (hj j (Finset.mem_univ j))
          (by rw [vx j]; exact one_ne_zero))
        (((hde d' hd').1 j).2.2.trans ((hde d hd).1 j).2.2.symm)
    have e2 : ∀ i, d'.2 i = d.2 i := fun i =>
      finDatum_ext (((hde d' hd').2 i).1.trans ((hde d hd).2 i).1.symm)
        (((hde d' hd').2 i).2.1.trans ((hde d hd).2 i).2.1.symm)
        (IsCosetDatum.fn_eq ((hcos d' hd').2 i) ((hcos d hd).2 i)
          (((hde d' hd').2 i).2.1.trans ((hde d hd).2 i).2.1.symm) (hi i (Finset.mem_univ i))
          (by rw [vy i]; exact one_ne_zero))
        (((hde d' hd').2 i).2.2.trans ((hde d hd).2 i).2.2.symm)
    exact Prod.ext (funext e1) (funext e2)
  · intro hn
    exact absurd hd hn

variable (σ S t Φ β)

def JetsIn : Prop :=
  ∀ τ, IsCosetExpansion S t Φ β (expDepth S t Φ β) τ → ∀ d ∈ τ.support, ∀ c : S.Classes t Φ β,
    (∀ (j : Fin D.R.m) a b, S.Z.kk (d.1 j) (S.ptTop c j) (S.ptTop c (j + 1)) a b ∈ Set.range σ) ∧
      ∀ (i : Fin D.R.m) a b, S.Z.kk (d.2 i) (S.ptRow c i) (S.ptRow c (i + 1)) a b ∈ Set.range σ

def PhasesIn : Prop :=
  ∀ (w : locPl G t) x y e, (S.term t Φ β w).datum x y ≠ 0 →
    moved (locGrid G t w) (keepAt G w) ((repsAt G t w).elt (β w)) (Tflip W S.B t Φ w) (fill one_le_sLen x y e) ≠ 0 →
      (psiAt W w.1 (phase x e) : ℂ) ∈ Set.range σ

end Sums

variable (G σ) in

def LRatiosIn (μ₀ : T) (i j : Fin D.R.m) : Prop :=
  ∀ (t : T) (Λ Λ₀ : ℂ → ℂ), GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G μ₀ i j) Λ₀ →
    ∀ s : ℕ, 1 ≤ s → s ≤ bigN D + 1 → Λ₀ s ≠ 0 → Λ s / Λ₀ s ∈ Set.range σ

variable (W) in

structure IsBottomTri (i j : Fin D.R.m) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop where

  rank : A.rank = SqNum.botBig D i j

  rank' : A'.rank = SqNum.botSmall D i j

  std : X.rA.IsStd

  std' : X.rA'.IsStd

  stdW : X.rW.IsStd

  is : X.Is W.ψ W.θ (fun t => L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
    (fun _ => G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (fun t => SqNum.nuH G t i j) (locPl G)

variable (W σ) in

def SumsIn {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  ∃ Ω Ω' : ℂ, Ω ≠ 0 ∧ Ω' ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW,
    (∀ k, IntegrableOn (X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h) X.fd X.m →
      X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω ∈ Set.range σ) ∧
    ∀ k, IntegrableOn (X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h) X.fd' X.m' →
      X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω' ∈ Set.range σ

variable (W σ) in

def BottomIn (i j : Fin D.R.m) : Prop :=
  (∃ (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X) →
    ∃ (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X ∧ SumsIn W σ X

theorem SumsIn.rationalSums {A A' WW : HSp D} {X : Tri T A A' WW} (h : SumsIn W σ X)
    (hi : ∀ t P g, IntegrableOn (X.ker W.ψ W.θ t P g) X.fd X.m) (hi' : ∀ t P g, IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m') :
    X.RationalSums W.ψ W.θ σ := by
  obtain ⟨Ω, Ω', hΩ, hΩ', hs⟩ := h
  refine ⟨Ω, Ω', hΩ, hΩ', fun t g hg => ⟨fun k => ⟨hi t _ g, ?_⟩, fun k => ⟨hi' t _ g, ?_⟩⟩⟩
  · obtain ⟨z, hz⟩ := (hs t g hg).1 k (hi t _ g)
    exact ⟨z, by rw [hz]; field_simp⟩
  · obtain ⟨z, hz⟩ := (hs t g hg).2 k (hi' t _ g)
    exact ⟨z, by rw [hz]; field_simp⟩

variable (σ) in

structure NumbersIn (S : GridChoice W Set.univ) (μ₀ : T) : Prop where

  chars : CharsIn G σ

  eighth : RootsIn σ 8

  roots : ∀ t, ∀ w ∈ locPl G t, RootsIn σ (Ideal.absNorm w.asIdeal ^ depthAt G w)

  phases : ∀ t Φ, ∀ β ∈ S.supp t Φ, PhasesIn σ S t Φ β

  sqrt : ∀ w, (w ∈ S.PA ∨ ∃ t, w ∈ locPl G t) → ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ Set.range σ

  jets : ∀ t Φ, ∀ β ∈ S.supp t Φ, JetsIn σ S t Φ β

  ratios : ∀ i j, LRatiosIn G σ μ₀ i j

  bottom : ∀ i j, BottomIn W σ i j

private theorem valuesIn_of_range_subset {χ : HChar D.host.E} {s : ℝ} (h : χ.ValuesIn s σ) (hσ : Set.range σ ⊆ Set.range σ') :
    χ.ValuesIn s σ' := fun v hv => hσ (h v hv)

theorem NumbersIn.mono {S : GridChoice W Set.univ} {μ₀ : T} (h : NumbersIn σ S μ₀) (hσ : Set.range σ ⊆ Set.range σ') :
    NumbersIn σ' S μ₀ where
  chars :=
    { mu0 := fun j w x => hσ (h.chars.mu0 j w x)
      xi := fun t w x => hσ (h.chars.xi t w x)
      chi := fun i h1 h2 w x => hσ (h.chars.chi i h1 h2 w x)
      eta := valuesIn_of_range_subset h.chars.eta hσ
      chiPsi := valuesIn_of_range_subset h.chars.chiPsi hσ
      del := valuesIn_of_range_subset h.chars.del hσ
      del' := valuesIn_of_range_subset h.chars.del' hσ }
  eighth := fun z hz => hσ (h.eighth z hz)
  roots := fun t w hw z hz => hσ (h.roots t w hw z hz)
  phases := fun t Φ β hβ w x y e h1 h2 => hσ (h.phases t Φ β hβ w x y e h1 h2)
  sqrt := fun w hw => hσ (h.sqrt w hw)
  jets := fun t Φ β hβ τ hτ d hd c =>
    ⟨fun j a b => hσ ((h.jets t Φ β hβ τ hτ d hd c).1 j a b), fun i a b => hσ ((h.jets t Φ β hβ τ hτ d hd c).2 i a b)⟩
  ratios := fun i j t Λ Λ₀ h1 h2 s hs1 hs2 h0 => hσ (h.ratios i j t Λ Λ₀ h1 h2 s hs1 hs2 h0)
  bottom := fun i j hex => by
    obtain ⟨A, A', WW, X, hX, Ω, Ω', hΩ, hΩ', hs⟩ := h.bottom i j hex
    exact ⟨A, A', WW, X, hX, Ω, Ω', hΩ, hΩ', fun t g hg =>
      ⟨fun k hk => hσ ((hs t g hg).1 k hk), fun k hk => hσ ((hs t g hg).2 k hk)⟩⟩

theorem numbersIn_id (S : GridChoice W Set.univ) (μ₀ : T) : NumbersIn (RingHom.id ℂ) S μ₀ where
  chars :=
    { mu0 := fun _ _ _ => ⟨_, rfl⟩
      xi := fun _ _ _ => ⟨_, rfl⟩
      chi := fun _ _ _ _ _ => ⟨_, rfl⟩
      eta := fun _ _ => ⟨_, rfl⟩
      chiPsi := fun _ _ => ⟨_, rfl⟩
      del := fun _ _ => ⟨_, rfl⟩
      del' := fun _ _ => ⟨_, rfl⟩ }
  eighth := fun _ _ => ⟨_, rfl⟩
  roots := fun _ _ _ _ _ => ⟨_, rfl⟩
  phases := fun _ _ _ _ _ _ _ _ _ _ => ⟨_, rfl⟩
  sqrt := fun _ _ => ⟨_, rfl⟩
  jets := fun _ _ _ _ _ _ _ _ _ => ⟨fun _ _ _ => ⟨_, rfl⟩, fun _ _ _ => ⟨_, rfl⟩⟩
  ratios := fun _ _ _ _ _ _ _ _ _ _ _ => ⟨_, rfl⟩
  bottom := fun _ _ ⟨A, A', WW, X, hX⟩ =>
    ⟨A, A', WW, X, hX, 1, 1, one_ne_zero, one_ne_zero, fun _ _ _ => ⟨fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩⟩

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

namespace Choice

variable (ch : Choice R)

variable (σ) in

def FieldIn : Prop := NumbersIn σ ch.S.toGridChoice A.μ0

def FieldOK : Prop := ch.FieldIn D.what₂.embLL

def HasNumberField : Prop :=
  ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ch.FieldIn (algebraMap M ℂ)

variable {ch}

theorem FieldIn.fieldOK (h : ch.FieldIn σ) (hσ : Set.range σ ⊆ Set.range D.what₂.embLL) : ch.FieldOK := NumbersIn.mono h hσ

theorem FieldOK.hasNumberField (h : ch.FieldOK) : ch.HasNumberField := by
  have h' : NumbersIn D.what₂.embLL ch.S.toGridChoice A.μ0 := h
  let f : D.what₂.LL →ₐ[ℚ] ℂ := D.what₂.embLL.toRatAlgHom
  refine ⟨f.fieldRange, LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField f).toLinearEquiv, ?_⟩
  refine NumbersIn.mono h' ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨⟨D.what₂.embLL y, AlgHom.mem_fieldRange.2 ⟨y, rfl⟩⟩, rfl⟩

theorem FieldOK.isRatAt (h : ch.FieldOK) {t Φ β} (hβ : β ∈ ch.S.supp t Φ) {τ}
    (hτ : IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ) {d} (hd : d ∈ τ.support)
    (c : ch.S.Classes t Φ β) :
    (∀ j : Fin D.R.m, ch.S.Z.IsRatAt (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1))) ∧
      ∀ i : Fin D.R.m, ch.S.Z.IsRatAt (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) := by
  have h' : NumbersIn D.what₂.embLL ch.S.toGridChoice A.μ0 := h
  have hj := h'.jets t Φ β hβ τ hτ d hd c
  exact ⟨fun j a b => hj.1 j a b, fun i a b => hj.2 i a b⟩

theorem FieldOK.valLL (h : ch.FieldOK) : Formalism.L2.Host.ValLL D R.C := by
  have h' : NumbersIn D.what₂.embLL ch.S.toGridChoice A.μ0 := h
  exact ⟨fun j => (h'.chars.mu0 j).valuesIn, h'.chars.eta, h'.chars.chiPsi, h'.chars.del, h'.chars.del'⟩

theorem FieldOK.fieldCond (h : ch.FieldOK) (hW : ch.W.Over R) (G' : GlobalTheory.Grid.GridPre R)
    (h1 : ∀ i, 1 ≤ i → i ≤ D.R.m → G'.chiH i = ch.G.ch.chiH i ∧ G'.chi i = ch.G.ch.chi i)
    (h2 : G'.toPlaceDat.W R.Pg = ch.G.pl.W0) (h3 : ∀ w ∈ ch.G.pl.W0, G'.toPlaceDat.depth w = depthAt ch.G w)
    (hL : ∀ i j Λ₀, GlobalTheory.CMVal.IsHeckeL (SqNum.nuH ch.G A.μ0 i j) Λ₀ → ∀ s : ℕ, 1 ≤ s → Λ₀ s ≠ 0)
    (hB : ∀ i j, ∃ (B B' WW : HSp D) (X : Tri T B B' WW), IsBottomTri ch.W i j X)
    (hI : ∀ i j (B B' WW : HSp D) (X : Tri T B B' WW), IsBottomTri ch.W i j X → ∀ t,
      (∀ P g, IntegrableOn (X.ker ch.W.ψ ch.W.θ t P g) X.fd X.m) ∧ ∀ P g, IntegrableOn (X.ker' ch.W.ψ ch.W.θ t P g) X.fd' X.m') :
    FieldCond G' := by
  classical
  have h' : NumbersIn D.what₂.embLL ch.S.toGridChoice A.μ0 := h
  have hψ : ch.W.ψ = R.ψ := hW.1
  have hθ : ch.W.θ = R.θ := hW.2
  have hm : ∀ i : Fin D.R.m, 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := fun i => ⟨by omega, by omega⟩
  have hnu : ∀ (i j : Fin D.R.m) t, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.nuH G' i j t = SqNum.nuH ch.G t i j := by
    intro i j t
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.nuH SqNum.nuH
    rw [(h1 _ (hm i).1 (hm i).2).1]
  refine ⟨h.valLL, ⟨fun i hi1 hi2 => ?_, fun w hw => ?_⟩, fun t => (h'.chars.xi t).valuesIn, fun i j => ?_,
    fun i j => ?_⟩
  · rw [(h1 i hi1 hi2).1]
    exact (h'.chars.chi i hi1 hi2).valuesIn
  · have hw' : w ∈ locPl ch.G A.μ0 := by
      unfold locPl
      rw [← h2]
      exact Finset.mem_union_left _ hw
    have hne : Ideal.absNorm w.asIdeal ^ depthAt ch.G w ≠ 0 :=
      pow_ne_zero _ (fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
    obtain ⟨z, hz⟩ := (rootsIn_iff hne).1 (h'.roots A.μ0 w hw')
    refine ⟨z, ?_⟩
    rw [h3 w (h2 ▸ hw)]
    have hc : Nat.card (kP w) = Ideal.absNorm w.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hc]
    exact hz
  · intro t Λ Λ₀ hΛ hΛ₀ s hs1 hs2
    rw [hnu] at hΛ hΛ₀
    have h0 := hL i j Λ₀ hΛ₀ s hs1
    obtain ⟨ρ, hρ⟩ := h'.ratios i j t Λ Λ₀ hΛ hΛ₀ s hs1 hs2 h0
    exact ⟨ρ, by rw [hρ]; field_simp⟩
  · obtain ⟨B, B', WW, X, hX, hS⟩ := h'.bottom i j (hB i j)
    have hR := SumsIn.rationalSums hS (fun t P g => (hI i j B B' WW X hX t).1 P g) (fun t P g => (hI i j B B' WW X hX t).2 P g)
    rw [hψ, hθ] at hR
    have hX' := hX.is
    rw [hψ, hθ] at hX'
    refine ⟨B, B', WW, X, ?_, ?_, hX.std, hX.std', hX.stdW, ?_, hR⟩
    · rw [hX.rank]
      exact (SqNum.ranks_exact D i j).1
    · rw [hX.rank']
      exact (SqNum.ranks_exact D i j).2.1
    · have hpl : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.places G' = locPl ch.G := by
        funext t
        ext w
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.places, locPl, Finset.mem_union, h2]
      have hb : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.beta G' i j = fun _ => ch.G.ch.chi (D.R.m - i) * R.eta ^ (rankV D i j % 2) := by
        funext t
        unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.beta
        rw [(h1 _ (hm i).1 (hm i).2).2]
        rfl
      have hn : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.nuH G' i j = fun t => SqNum.nuH ch.G t i j := funext (hnu i j)
      rw [hpl, hb, hn]
      exact hX'

end Choice

example (ch : Choice R) (ρ ξ) : (ch.withReal ρ ξ).FieldOK ↔ ch.FieldOK := Iff.rfl

example : RootsIn σ 2 := fun z hz => by
  rcases mul_self_eq_one_iff.1 ((sq z).symm.trans hz) with rfl | rfl
  exacts [⟨1, map_one σ⟩, ⟨-1, by simp⟩]

example (S : GridChoice W Set.univ) (μ₀ : T) : ¬ NumbersIn (Rat.castHom ℂ) S μ₀ := fun h => by
  obtain ⟨x, hx⟩ := h.eighth Complex.I (by rw [show 8 = 4 * 2 from rfl, pow_mul, Complex.I_pow_four, one_pow])
  simpa using congrArg Complex.im hx

end GlobalTheory.RowTest

end
