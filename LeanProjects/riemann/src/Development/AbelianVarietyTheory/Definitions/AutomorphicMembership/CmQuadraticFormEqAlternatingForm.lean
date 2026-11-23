import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

def duP (P : PreCh) (u : P.Word) : ℝ :=
  (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.k) (StandardLattice.stdLat P.H.E P.R.k)) *
    (StandardLattice.idxColLoc (P.H.g 0) P.R.k ^ P.R.f * StandardLattice.idxColLoc (P.H.g 1) P.R.k ^ P.R.f) *
    ∏ τ : Tau P.R, StandardLattice.dimV (fun i : Fin P.R.k => (((P.hcW u τ).u i : ℚ) : ℝ))

def DsP (P : PreCh) : ℝ :=
  (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) *
    (StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) *
    ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ)

structure Ctx : Type 1 where
  s : Scale
  C : FC
  cD : ℝ
  ch : ℝ
  P : PreCh
  q1 : ℕ
  a : P.R.A → ℤ
  b : P.R.A → ℤ
  c : P.Word → Fin (P.R.k - 2) → Bool
  std : Std C
  ok : ChOK s C cD ch P q1 a b c
  Lv : LevCh P
  du_eq : ∀ u, (Lv.duStar u : ℝ) = duP P u
  Ds_eq : Lv.Dstar = DsP P
  Gam_eq : Lv.GamP = GamS C s P.R

def Ev (p : Ctx → Prop) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∀ K : Ctx, K.C = C → K.cD = cD → K.ch = ch → K.s.eps = eps → x0 ≤ K.s.x → p K

def Ctx.Good (K : Ctx) (C5 c6 Cb : ℝ) : Prop := ChGood K.s K.C C5 c6 Cb K.cD K.ch K.P K.a K.b K.c

def EvG (p : Ctx → Prop) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∀ K : Ctx, K.C = C → K.cD = cD → K.ch = ch → K.s.eps = eps → x0 ≤ K.s.x → K.Good C5 c6 Cb → p K

def Ctx.Over (K : Ctx) (B : Pre) : Prop :=
  ∃ (sp : @Spaces K.P.R K.Lv.host.F K.Lv.host.E _ _ _ _ K.Lv.host.cmStar _) (hT : _) (hY : _) (hA : _) (hV : _) (hz : _),
    B = Pre.ofCh K.P K.Lv sp hT hY hA hV hz ∧ (letI := K.Lv.host.cmStar; DiagSpaces sp)

abbrev Fr (B : Pre) : Type := Chr.HFrame B.host (fun j g => (B.hc g).e j)

def Fr.at (X : Stages) (f : Fr X.B.toPre) : CharFrame X.toD7 :=
  ⟨f.P, f.W, f.mu0, f.eta, f.chiPsi, f.del, f.del', f.isMu0, f.isEta, f.isChi, f.isDel, f.isDel'⟩

def Has (B : Base) (S₀ S₁ S₂ : Finset ℂ) : Prop :=
  (∀ z ∈ S₀, ∃ x ∈ B.Ks, B.embLL x = z) ∧ (∀ z ∈ S₁, ∃ x ∈ B.LL0, B.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B.LL, B.embLL x = z

def Has₂ (B : Base) (S₁ S₂ : Finset ℂ) : Prop := (∀ z ∈ S₁, z ∈ B.fixedCoefficientFieldInComplex) ∧ ∀ z ∈ S₂, z ∈ B.LLC

def Enl (B B' : Base) : Prop :=
  B'.toPre = B.toPre ∧ B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL) ∧
    B'.embLL '' (B'.LL0 : Set B'.LL) = B.embLL '' (B.LL0 : Set B.LL) ∧ Set.range B.embLL ⊆ Set.range B'.embLL

def offSet (B : Pre) : Set ℕ :=
  {p | p ∣ 30 * B.host.condN ∨ (∃ i, p = B.host.g i) ∨ p = B.host.pde ∨ p = B.host.pde' ∨ (∃ u, p = B.T u) ∨
    p = DC.q0H B.host ∨ p ∈ B.host.levelPrimes}

structure TwDat (B : Base) where
  pl : Finset ℕ
  Q : B.places.Pl → Finset (HeightOneSpectrum (𝓞 B.host.E))
  k : B.places.Pl → ℕ
  psi : B.places.Pl → HChar B.host.E
  psi_is : ∀ w, IsPsi (H := B.host) (B.places.resChar w) (Q w) (psi w)
  psi_ord : ∀ w, (psi w).OrderDvd (B.places.resChar w ^ k w)
  psi_tw : ∀ w, Chr.IsTwist B.host (offSet B.toPre) (psi w)
  Q_l : ∀ w, ∀ v ∈ Q w, ((B.places.resChar w : ℕ) : 𝓞 B.host.E) ∉ v.asIdeal
  off : ∀ w, B.places.resChar w ∉ pl → psi w = 1 ∧ k w = 0
  conj : ∀ w, psi (B.places.conj w) = psi w ∧ k (B.places.conj w) = k w

def TwDat.xiTw {B : Base} (T : TwDat B) (f : Fr B.toPre) (w : B.places.Pl) : HChar B.host.E :=
  (if B.places.resChar w = B.host.pde then f.del' else f.del) * T.psi w

def TwDat.set {B : Base} (T : TwDat B) (f : Fr B.toPre) : Set (HChar B.host.E) :=
  {1, f.del, f.del'} ∪ Set.range (T.xiTw f)

def TwDat.Avoids {B : Base} (T : TwDat B) (A : ℕ → Finset ℕ) : Prop :=
  ∀ w, ∀ v ∈ T.Q w, Ideal.absNorm v.asIdeal ∉ A (B.places.resChar w)

def large₂ (K : Ctx) (p : ∀ B : Base, Fr B.toPre → TwDat B → Prop) : Prop :=
  ∃ (S₁ : ∀ B : Pre, Fr B → IntermediateField ℚ ℂ → Finset ℂ)
    (P₁ : ∀ B : Pre, Fr B → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℕ)
    (A : ∀ B : Pre, Fr B → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → ℕ → Finset ℕ)
    (S₂ : ∀ B : Pre, Fr B → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (HChar B.host.E) → Finset ℂ),
    (∀ B f F, ∀ z ∈ S₁ B f F, IsAlgebraic ℚ z) ∧ (∀ B f F F₀ Ξ, ∀ z ∈ S₂ B f F F₀ Ξ, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B), K.Over B.toPre →
      Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) → P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl →
      T.Avoids (A B.toPre f B.KsC B.fixedCoefficientFieldInComplex) → p B f T

def LgOn {Δ : Pre → Type} (Sm : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → Prop) (K : Ctx)
    (p : ∀ B : Base, Fr B.toPre → Δ B.toPre → TwDat B → Prop) : Prop :=
  ∃ (S₁ : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → Finset ℂ)
    (P₁ : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Finset ℕ)
    (A : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → ℕ → Finset ℕ)
    (S₂ : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (HChar B.host.E) → Finset ℂ),
    (∀ B f δ F, ∀ z ∈ S₁ B f δ F, IsAlgebraic ℚ z) ∧ (∀ B f δ F F₀ Ξ, ∀ z ∈ S₂ B f δ F F₀ Ξ, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (f : Fr B.toPre) (δ : Δ B.toPre) (T : TwDat B), K.Over B.toPre → Sm B.toPre f δ B.KsC →
      Has₂ B (S₁ B.toPre f δ B.KsC) (S₂ B.toPre f δ B.KsC B.fixedCoefficientFieldInComplex (T.set f)) → P₁ B.toPre f δ B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl →
      T.Avoids (A B.toPre f δ B.KsC B.fixedCoefficientFieldInComplex) → p B f δ T

def RecFld (B : Pre) (f : Fr B) (D : Fld.FieldDat B) (F : IntermediateField ℚ ℂ) : Prop := Fld.listField D f ≤ F ∧ F ≤ D.Om

def JointFld (B : Pre) (_f : Fr B) (_δ : Unit) (F : IntermediateField ℚ ℂ) : Prop :=
  GlobalTheory.FieldSize.Rich B F ∧ ∀ L : ℝ, GlobalTheory.FieldSize.HostSz B.host L → GlobalTheory.FieldSize.Sz F (GlobalTheory.FieldSize.poR B.R L) (GlobalTheory.FieldSize.poR B.R L)

def LgRec (K : Ctx) (p : ∀ B : Base, Fr B.toPre → Fld.FieldDat B.toPre → TwDat B → Prop) : Prop := LgOn RecFld K p

def LgJoint (K : Ctx) (p : ∀ B : Base, Fr B.toPre → TwDat B → Prop) : Prop := LgOn JointFld K fun B f _ T => p B f T

def EvLgOn {Δ : Pre → Type} (Sm : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → Prop)
    (p : Ctx → ∀ B : Base, Fr B.toPre → Δ B.toPre → TwDat B → Prop) : Prop := Ev fun K => LgOn Sm K (p K)

def EvLg (p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop) : Prop := Ev fun K => large₂ K (p K)

def EvLgOnG {Δ : Pre → Type} (Sm : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → Prop)
    (p : Ctx → ∀ B : Base, Fr B.toPre → Δ B.toPre → TwDat B → Prop) : Prop := EvG fun K => LgOn Sm K (p K)

def EvLgG (p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop) : Prop := EvG fun K => large₂ K (p K)

structure MuIs (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (xi : X.C.Tup → HChar X.B.host.E) : Prop where
  inj : Function.Injective xi
  range : Set.range xi = T.set f
  mu0 : xi X.C.mu0 = 1
  star : xi X.C.muStar = f.del
  star' : xi X.C.muStar' = f.del'
  tw : ∀ w, xi (X.W.muTw w) = T.xiTw f w
  on : ∀ w, X.B.places.resChar w ∈ T.pl → X.W.muAt w = X.W.muTw w
  off : ∀ w, X.B.places.resChar w ∉ T.pl → X.W.muAt w = X.C.mu0

def RecExL (QL : ∀ D : D7, Lay D → Prop) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ cs x0 : ℝ, 0 < cs ∧
      ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool),
        s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
        ∃ (du : P.Word → ℕ) (Ds : ℝ), (∀ u, 0 < du u) ∧ 0 < Ds ∧
          (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) *
            GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) ∧
          ∀ Lv : LevCh P, Lv.duStar = du → Lv.Dstar = Ds → Lv.GamP = GamS C s P.R →
            ∃ (D : D7) (Y : Lay D), Over D P Lv ∧ RecOK s C cD D ∧ LedOK s C cD ch Y a b ∧ LocalQuadraticParts.TWAt D Y.nch Y.xd ∧ QL D Y

def RecAt (QL : ∀ D : D7, Lay D → Prop) : Prop :=
  Ev fun K => ∃ (D : D7) (Y : Lay D), Over D K.P K.Lv ∧ RecOK K.s K.C K.cD D ∧ LedOK K.s K.C K.cD K.ch Y K.a K.b ∧
    LocalQuadraticParts.TWAt D Y.nch Y.xd ∧ QL D Y

abbrev LayProp : Type 1 :=
  ∀ (_ : Scale) (_ : FC) (_ _ : ℝ) (P : PreCh) (_ _ : P.R.A → ℤ) (D : D7), Lay D → Prop

def RecExG (QL : LayProp) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps C8 C5 c6 Cb : ℝ, 0 < eps → eps ≤ ε0 → eps < 1 / 52 → 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ cs x0 : ℝ, 0 < cs ∧
      ∀ (s : Scale) (P : PreCh) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool),
        s.eps = eps → x0 ≤ s.x → ChGood s C C5 c6 Cb cD ch P a b c →
        ∃ (du : P.Word → ℕ) (Ds : ℝ), (∀ u, 0 < du u) ∧ 0 < Ds ∧
          (∀ u, cs * P.R.m * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) *
            GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) ∧
          ∀ Lv : LevCh P, Lv.duStar = du → Lv.Dstar = Ds → Lv.GamP = GamS C s P.R →
            ∃ (D : D7) (Y : Lay D), Over D P Lv ∧ RecOK s C cD D ∧ LedOK s C cD ch Y a b ∧ LocalQuadraticParts.TWAt D Y.nch Y.xd ∧
              QL s C cD ch P a b D Y

def RecAtG (QL : ∀ (_ : Ctx) (D : D7), Lay D → Prop) : Prop :=
  EvG fun K => ∃ (D : D7) (Y : Lay D), Over D K.P K.Lv ∧ RecOK K.s K.C K.cD D ∧ LedOK K.s K.C K.cD K.ch Y K.a K.b ∧
    LocalQuadraticParts.TWAt D Y.nch Y.xd ∧ QL K D Y

def LayProp.at (QL : LayProp) (K : Ctx) : ∀ D : D7, Lay D → Prop := QL K.s K.C K.cD K.ch K.P K.a K.b

def AtLed (QO : ∀ D : D7, Obj D → Prop) : LayProp := fun s C cD ch _ a b _ Y =>
  ∀ p : LedPart C Y, p.L.sc = s → WtEq p.L a b → Val C cD ch p.L → CanonInst p.ta.Gx → QO p.pt.D (Obj.ofPt p.pt)

theorem has₂_iff (B : Base) (S₁ S₂ : Finset ℂ) : Has₂ B S₁ S₂ ↔ Has B ∅ S₁ S₂ :=
  ⟨fun h => ⟨by simp, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

theorem Enl.KsC_eq {B B' : Base} (h : Enl B B') : B'.KsC = B.KsC := SetLike.coe_injective h.2.1

theorem Enl.fixedCoefficientField_eq {B B' : Base} (h : Enl B B') : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := SetLike.coe_injective h.2.2.1

def TwDat.untw (B : Base) (pl : Finset ℕ) : TwDat B where
  pl := pl
  Q _ := ∅
  k _ := 0
  psi _ := 1
  psi_is _ := isPsi_one _
  psi_ord _ := one_pow _
  psi_tw _ := Chr.isTwist_one _ _
  Q_l _ _ h := absurd h (Finset.notMem_empty _)
  off _ _ := ⟨rfl, rfl⟩
  conj _ := ⟨rfl, rfl⟩

theorem finite_offSet (B : Pre) : (offSet B).Finite := by
  have h0 : 30 * B.host.condN ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero B.host.QS_pos.ne' B.host.hyp.1.ne_zero) B.host.hyp.2.1.ne_zero)
  refine (((30 * B.host.condN).divisors.finite_toSet.union (Set.finite_singleton (DC.q0H B.host))).union
    B.host.levelPrimes.finite_toSet).subset ?_
  rintro p (h | ⟨i, rfl⟩ | rfl | rfl | ⟨u, rfl⟩ | rfl | h)
  exacts [.inl (.inl (Nat.mem_divisors.2 ⟨h, h0⟩)), .inr (B.host.g_level i), .inr B.host.pde_level.1, .inr B.host.pde_level.2,
    .inr (B.T_level u), .inl (.inr rfl), .inr h]

theorem mem_offSet_of_dvd_condN (B : Pre) {p : ℕ} (h : p ∣ B.host.condN) : p ∈ offSet B := .inl (h.mul_left _)

theorem mem_offSet_of_mem_avPrimes (X : Stages) {p : ℕ} (hp : p ∈ avPrimes X.toD7) : p ∈ offSet X.B.toPre := by
  simp only [avPrimes, Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hp
  obtain ⟨(rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨u, rfl⟩) | hp, -⟩ := hp
  · exact .inl (Dvd.dvd.mul_right (by norm_num) _)
  · exact .inl (Dvd.dvd.mul_right (by norm_num) _)
  · exact .inr (.inl ⟨0, rfl⟩)
  · exact .inr (.inl ⟨1, rfl⟩)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
  · exact .inr (.inr (.inr (.inr (.inl ⟨u, X.C.A_T u⟩))))
  · have h : X.toD7.host.ccK = ⊤ := X.B.ccK_top
    rw [h, Ideal.absNorm_top] at hp
    simp at hp

theorem TwDat.notMem_avRec (X : Stages) (T : TwDat X.B) (w : X.B.places.Pl) {v : HeightOneSpectrum (𝓞 X.B.host.E)}
    (hv : v ∈ T.Q w) : v ∉ AvRec X.toD7 := by
  obtain ⟨-, h1, -, h2⟩ := (T.psi_tw w).2.2.2 v fun h => ((T.psi_is w).ram v).1 h hv
  exact not_mem_avRec_of_over (D := X.toD7) h1 (fun h => h2 (mem_offSet_of_mem_avPrimes X h)) (Ideal.absNorm_mem _)

section Filter

variable {Δ : Pre → Type} {Sm : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → Prop} {K : Ctx}

theorem lgOn_self : LgOn Sm K fun B f δ _ => Sm B.toPre f δ B.KsC :=
  ⟨fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ _ => ∅, fun _ _ _ _ _ _ => ∅, by simp, by simp,
    fun _ _ _ _ _ h _ _ _ => h⟩

theorem LgOn.imp {p q : ∀ B : Base, Fr B.toPre → Δ B.toPre → TwDat B → Prop} (hp : LgOn Sm K p)
    (h : ∀ B f δ T, K.Over B.toPre → Sm B.toPre f δ B.KsC → p B f δ T → q B f δ T) : LgOn Sm K q := by
  obtain ⟨a, b, c, d, h1, h2, h3⟩ := hp
  exact ⟨a, b, c, d, h1, h2, fun B f δ T x y z u v => h B f δ T x y (h3 B f δ T x y z u v)⟩

theorem LgOn.inter {p q : ∀ B : Base, Fr B.toPre → Δ B.toPre → TwDat B → Prop} (hp : LgOn Sm K p) (hq : LgOn Sm K q) :
    LgOn Sm K fun B f δ T => p B f δ T ∧ q B f δ T := by
  classical
  obtain ⟨a, b, c, d, h1, h2, h3⟩ := hp
  obtain ⟨a', b', c', d', h1', h2', h3'⟩ := hq
  refine ⟨fun B f δ F => a B f δ F ∪ a' B f δ F, fun B f δ F G => b B f δ F G ∪ b' B f δ F G,
    fun B f δ F G l => c B f δ F G l ∪ c' B f δ F G l, fun B f δ F G X => d B f δ F G X ∪ d' B f δ F G X,
    fun B f δ F z hz => (Finset.mem_union.1 hz).elim (h1 B f δ F z) (h1' B f δ F z),
    fun B f δ F G X z hz => (Finset.mem_union.1 hz).elim (h2 B f δ F G X z) (h2' B f δ F G X z),
    fun B f δ T hO hS hH hP hA => ⟨?_, ?_⟩⟩
  · exact h3 B f δ T hO hS ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), fun z hz => hH.2 z (Finset.mem_union_left _ hz)⟩
      (Finset.subset_union_left.trans hP) fun w v hv h => hA w v hv (Finset.mem_union_left _ h)
  · exact h3' B f δ T hO hS ⟨fun z hz => hH.1 z (Finset.mem_union_right _ hz), fun z hz => hH.2 z (Finset.mem_union_right _ hz)⟩
      (Finset.subset_union_right.trans hP) fun w v hv h => hA w v hv (Finset.mem_union_right _ h)

theorem large₂.lgOn {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p) : LgOn Sm K fun B f _ T => p B f T := by
  obtain ⟨a, b, c, d, h1, h2, h3⟩ := hp
  exact ⟨fun B f _ => a B f, fun B f _ => b B f, fun B f _ => c B f, fun B f _ => d B f, fun B f _ => h1 B f,
    fun B f _ => h2 B f, fun B f _ T x _ => h3 B f T x⟩

theorem lg_iff_lgOn {p : ∀ B : Base, Fr B.toPre → TwDat B → Prop} :
    large₂ K p ↔ LgOn (Δ := fun _ => Unit) (fun _ _ _ _ => True) K fun B f _ T => p B f T :=
  ⟨large₂.lgOn, fun ⟨a, b, c, d, h1, h2, h3⟩ => ⟨fun B f => a B f (), fun B f => b B f (), fun B f => c B f (), fun B f => d B f (),
    fun B f => h1 B f (), fun B f => h2 B f (), fun B f T x => h3 B f () T x trivial⟩⟩

theorem large₂.inter {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p) (hq : large₂ K q) :
    large₂ K fun B f T => p B f T ∧ q B f T :=
  lg_iff_lgOn.2 ((lg_iff_lgOn.1 hp).inter (lg_iff_lgOn.1 hq))

theorem large₂.imp {p q : ∀ B : Base, Fr B.toPre → TwDat B → Prop} (hp : large₂ K p)
    (h : ∀ B f T, K.Over B.toPre → p B f T → q B f T) : large₂ K q :=
  lg_iff_lgOn.2 ((lg_iff_lgOn.1 hp).imp fun B f _ T x _ => h B f T x)

theorem lgRec_bounds : LgRec K fun B f D _ => Fld.listField D f ≤ B.KsC ∧ B.KsLeOm D := lgOn_self

end Filter

section Good

theorem recEx_iff_recExG (QO : ∀ D : D7, Obj D → Prop) : RecEx QO ↔ RecExG (AtLed QO) := Iff.rfl

theorem Ctx.Good.level {K : Ctx} {C5 c6 Cb : ℝ} (h : K.Good C5 c6 Cb) :
    K.P.H.levelPrimes = {K.P.H.g 0, K.P.H.g 1, K.P.H.pde, K.P.H.pde', DC.q0H K.P.H} := (ChGood.level h).1

theorem Ctx.Good.cmQuadraticForm_eq_alternatingForm {K : Ctx} {C5 c6 Cb : ℝ} (h : K.Good C5 c6 Cb) : K.q1 = DC.q0H K.P.H := by
  obtain ⟨h1, h2, h3, h4, -⟩ := K.ok.small
  rw [h.level] at h1
  simpa [h2, h3, h4] using h1

theorem evG_of_ev {p : Ctx → Prop} (h : Ev p) : EvG p := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 _ => h K d1 d2 d3 d4 d5⟩

theorem ev_le_splitBound (n : ℕ) : Ev fun K => n ≤ K.P.H.splitBound := by
  refine ⟨1, one_pos, fun eps C8 he _ _ h8 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ hC _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨(n : ℝ) ^ (5 * C8 / eps), fun K h1 _ _ h4 hx => ?_⟩⟩⟩⟩⟩
  have hv : HostVal K.s C8 K.P.H := by rw [← hC, ← h1]; exact K.ok.val
  have he' := hv.eps_div_le_ez
  rw [h4] at he'
  have h0 : 0 < C8 := by linarith
  refine le_trans (Nat.le_floor ?_) hv.split_tie
  calc (n : ℝ) = ((n : ℝ) ^ (5 * C8 / eps)) ^ (eps / C8 / 5) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _), show 5 * C8 / eps * (eps / C8 / 5) = 1 by field_simp, Real.rpow_one]
    _ ≤ K.s.x ^ (eps / C8 / 5) := Real.rpow_le_rpow (by positivity) hx (by positivity)
    _ ≤ K.s.x ^ (K.s.ez / 5) := Real.rpow_le_rpow_of_exponent_le K.s.one_lt_alt.le (by linarith)

theorem EvG.imp {p q : Ctx → Prop} (hp : EvG p) (hpq : ∀ (K : Ctx) (C5 c6 Cb : ℝ), K.Good C5 c6 Cb → p K → q K) : EvG q := by
  obtain ⟨ε0, h0, h⟩ := hp
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 d6 => hpq K _ _ _ d6 (h K d1 d2 d3 d4 d5 d6)⟩

theorem EvG.inter {p q : Ctx → Prop} (hp : EvG p) (hq : EvG q) : EvG fun K => p K ∧ q K := by
  obtain ⟨a, ha, hp⟩ := hp
  obtain ⟨b, hb, hq⟩ := hq
  refine ⟨min a b, lt_min ha hb, fun e C8 C5 c6 Cb he hle h52 h8 => ?_⟩
  obtain ⟨K, hK⟩ := hp e C8 C5 c6 Cb he (hle.trans (min_le_left _ _)) h52 h8
  obtain ⟨K', hK'⟩ := hq e C8 C5 c6 Cb he (hle.trans (min_le_right _ _)) h52 h8
  refine ⟨K.sup K', fun C hC hC8 h => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 ⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩
  obtain ⟨b1, hb1⟩ := hK' C hC hC8 ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  exact ⟨max a3 b3, fun X h1 h2 h3 h4 hx hg =>
    ⟨ha3 X h1 h2 h3 h4 (le_trans (le_max_left _ _) hx) hg, hb3 X h1 h2 h3 h4 (le_trans (le_max_right _ _) hx) hg⟩⟩

theorem evG_good : EvG fun K => ∃ C5 c6 Cb : ℝ, K.Good C5 c6 Cb :=
  ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ _ _ _ _ h => ⟨_, _, _, h⟩⟩⟩⟩⟩⟩

theorem evLgOnG_of_evLgOn {Δ : Pre → Type} {Sm : ∀ B : Pre, Fr B → Δ B → IntermediateField ℚ ℂ → Prop}
    {p : Ctx → ∀ B : Base, Fr B.toPre → Δ B.toPre → TwDat B → Prop} (h : EvLgOn Sm p) : EvLgOnG Sm p := evG_of_ev h

theorem evLgG_of_evLg {p : Ctx → ∀ B : Base, Fr B.toPre → TwDat B → Prop} (h : EvLg p) : EvLgG p := evG_of_ev h

theorem recAtG_of_recAt {QL : ∀ D : D7, Lay D → Prop} (h : RecAt QL) : RecAtG fun _ => QL := evG_of_ev h

theorem RecAtG.imp {QL QL' : ∀ (_ : Ctx) (D : D7), Lay D → Prop} (h : RecAtG QL)
    (hQ : ∀ (K : Ctx) (C5 c6 Cb : ℝ) (D : D7) (Y : Lay D), K.Good C5 c6 Cb → Over D K.P K.Lv → RecOK K.s K.C K.cD D →
      LedOK K.s K.C K.cD K.ch Y K.a K.b → LocalQuadraticParts.TWAt D Y.nch Y.xd → QL K D Y → QL' K D Y) : RecAtG QL' :=
  EvG.imp h fun K C5 c6 Cb hK ⟨D, Y, g1, g2, g3, g4, g5⟩ => ⟨D, Y, g1, g2, g3, g4, hQ K C5 c6 Cb D Y hK g1 g2 g3 g4 g5⟩

theorem recExG_of_recExL {QL : ∀ D : D7, Lay D → Prop} (h : RecExL QL) : RecExG fun _ _ _ _ _ _ _ => QL := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨cs, x0, hcs, h⟩ := h ch hch
  exact ⟨cs, x0, hcs, fun s P a b c d1 d2 d3 => h s P _ a b c d1 d2 d3.ok⟩

end Good

example (K : Ctx) (D : D7) (Y : Lay D) : (AtLed fun _ O => O.L.sc = K.s).at K D Y := fun _ h _ _ _ => h

example (B : Pre) : Fr B = Fld.Chars B := rfl

example (B : Base) (D : Fld.FieldDat B.toPre) (f : Fr B.toPre) (c M : ℕ) (h : B.FieldsOK D f c M) : RecFld B.toPre f D B.KsC :=
  ⟨h.listField_le, h.ksLeOm⟩

example (B : Base) (f : Fr B.toPre) (T : TwDat B) : (1 : HChar B.host.E) ∈ T.set f := Or.inl (Or.inl rfl)

end GlobalTheory.Mem.Top

end
