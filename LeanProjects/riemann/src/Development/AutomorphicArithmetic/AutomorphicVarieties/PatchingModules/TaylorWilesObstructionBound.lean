import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa

abbrev reIu {l : ℕ} [Fact l.Prime] (F : GFrame l) (I : F.St → Subgroup F.G₀) : GFrame l :=
  { F with Iu := I, D0 := ⊥, I0 := ⊥ }

def Norm : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ)
    (r : Resid F O n) (x : Point r) (I : F.St → Subgroup F.G₀), l ≠ 2 → 0 < n → (∀ u, I u ≤ r.Ip u) → x.NiceI ∨ x.NiceE →
    ∃ (x' : NP (reIu F I) n) (j : x.A →+* x'.A), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧
      GDet.ofRep (mat x'.ρ) = (GDet.ofRep (mat x.ρ)).map j ∧ (∀ v i, x'.ψ v i = pushCh j (x.ψ v i)) ∧
      x'.N3 ∧ x'.N4 F.D0 ∧ (x.TypeI → x'.a = n)

structure CohP : Prop where
  lf : LocalFiniteness
  lt : LocalTateDuality
  le : LocalEulerChar
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  gw : GreenbergWiles
  pt : GlobalTheory.Published.PoitouTateNormalised
  tame : GlobalTheory.Published.TameLocal

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  (r : Resid V0.frame O n)

def locOf : Loc where
  Vl := V0.frame.Vl
  finV := V0.frame.finV
  Gv := V0.frame.Gv
  gv := V0.frame.gv
  tv := V0.frame.tv
  tgv := V0.frame.tgv
  cv := V0.frame.cv
  dv := V0.frame.dv
  Iv := V0.frame.Iv
  St := V0.frame.St
  finT := V0.frame.finT
  Gu u := Dec (F := L) (s.A (Subtype.val u))
  cu u := isCompact_iff_compactSpace.1 (isClosed_Dec (F := L) (s.A (Subtype.val u))).isCompact
  Ju u := (Ine (F := L) (s.A (Subtype.val u))).subgroupOf (Dec (F := L) (s.A (Subtype.val u))) ⊓
    ⨅ i, ((r.chib i).comp (V0.pr.comp (Dec (F := L) (s.A (Subtype.val u))).subtype)).ker

def globOf (V : s.Lev) : Glob l (locOf r) where
  Γ := V.frame.Γ
  grp := V.frame.grp
  top := V.frame.top
  tgrp := V.frame.tgrp
  cpt := V.frame.cpt
  tdisc := V.frame.tdisc
  η := V.η
  η_open := V.η_open
  c := V.frame.c
  c_sq := V.frame.c_sq
  η_c := V.η_c
  ε := V.ε
  ε_cont := V.ε_cont
  φ := V.frame.φ
  φ_cont := V.frame.φ_cont
  φu u := V.pr.comp (Dec (F := L) (s.A (Subtype.val u))).subtype
  φu_cont _ := (V.pr_cont continuous_resP).comp continuous_subtype_val

example : (globOf r V0).frame = reIu V0.frame (globOf r V0).frame.Iu := rfl

def residOf : Resid (globOf r V0).frame O n :=
  ⟨r.chib, r.chib_open, r.chib_inj, r.polar, r.psib, r.psib_open, r.th, r.th_comm⟩

theorem residOf_Ip_le (u : V0.frame.St) : (residOf r).Ip u ≤ r.Ip u := by
  rintro g ⟨⟨γ, ⟨h1, -⟩, rfl⟩, h2⟩
  exact ⟨⟨Subtype.val γ, h1, rfl⟩, h2⟩

variable {r} in

def pairOf {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) : Pair (residOf r) B :=
  ⟨u.D, u.ψ, u.cont, u.red, fun v i => ⟨(u.psi v i).cont, (u.psi v i).red, (u.psi v i).mu⟩, u.P, u.Ord,
    fun w g hg => u.I w g (residOf_Ip_le r w hg)⟩

structure TWPl (T : TWGrp (globOf r V0)) where
  V : ℕ → s.Lev
  e : ∀ N, (globOf r (V N)).Hom (T.GN N)
  e_inj : ∀ N, Function.Injective (e N).p
  e_h : ∀ N g, (T.h N).p ((e N).p (toGS Ω (V N).S' g)) = toGS Ω V0.S' g
  v : ℕ → Fin T.q → Plc (Lp L)
  v_inj : ∀ N, Function.Injective (v N)
  v_not : ∀ N j, v N j ∉ s.S
  S_eq : ∀ N, (V N).S' = s.S ∪ Set.range (v N)
  w : ℕ → Fin T.q → Plc L
  B : ℕ → Fin T.q → ValuationSubring Ω
  B_w : ∀ N j, IsPlaceOver (B N j) (w N j)
  B_v : ∀ N j, IsPlaceOver (B N j) (v N j)
  split : ∀ N j, Dec (F := Lp L) (B N j) ≤ (resP L Ω).range
  Nq : ∀ N j, T.Nq N j = normV (w N j)
  fr : ℕ → Fin T.q → G L Ω
  fr_dec : ∀ N j, fr N j ∈ Dec (F := L) (B N j)
  fr_frob : ∀ N j, IsFrob (F := L) (B N j) (normV (w N j)) (fr N j)⁻¹
  τ : ℕ → Fin T.q → G L Ω
  τ_gen : ∀ N j, GlobalTheory.TameQuot.IsProGen L (B N j) l (τ N j)
  ph : ∀ N j, T.ph N j = (e N).p₀ ((V N).pr (fr N j))
  ta : ∀ N j, T.ta N j = (e N).p₀ ((V N).pr (τ N j))
  H_eq : ∀ g : (globOf r V0).Γ, g ∈ T.H ↔ ∃ h : V0.η g = 1, (∀ i, r.chib i ⟨g, h⟩ = 1) ∧
    PadicInt.toZMod ((V0.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1

variable (s) in

def LocCFT : Prop :=
  ∃ d : Vl l L → ℕ, ∑ᶠ v, d v = Module.finrank ℚ (Lp L) ∧ ∀ v : Vl l L,
    Nonempty (LocAb l (Dec (F := L) (s.A v)) ((Ine (F := L) (s.A v)).subgroupOf (Dec (F := L) (s.A v))) (d v))

def ArPl : Prop :=
  CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), V0.S' = s.S →
    PhiCond V0.frame.Γ l ∧ ∀ (q : ℕ) (sg : Fin q → V0.frame.G₀), (∀ j, sg j ∈ V0.frame.G') →
    ∃ T : TWGrp (globOf r V0), Nonempty (TWPl r T) ∧ ∃ e : T.q = q, ∀ j, T.sg j = sg (Fin.cast e j)

def FirstOrderDualArithmeticBound : Prop :=
  CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T)
    (x : NP (globOf r V0).frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A), V0.S' = s.S → LocCFT s →
    (∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) →
    (∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) →
    x.N4 V0.frame.D0 → T.Eig x al → Detects k (Set.range T.sg) →
    T.B1 k (n * Module.finrank ℚ (Lp L) + n * T.q)

def TaylorWilesObstructionBound : Prop :=
  CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T)
    (x : NP (globOf r V0).frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A), V0.S' = s.S →
    (∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) →
    (∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) →
    T.Eig x al → T.B2 k

variable {r} in

def HasAut (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) : Prop :=
  ∀ T : TWGrp (globOf r V0), TWPl r T → Nonempty (TWAut (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)) T)

def PfromAut : Prop :=
  CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), 0 < n → V0.S' = s.S → LocCFT s →
    (∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → HasAut B J → B.P1core J ∧ B.P3core J

end UpperTheory.V.Pa
