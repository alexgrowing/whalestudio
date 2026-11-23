import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.DataDIV
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.HTW.Rec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

structure NWord (n : ℕ) where
  up : ZMod n → Bool
  sz : ZMod n → ℕ
  b : ℕ
  w : ℕ
  S : ℕ
  η : ℕ
  m : ℕ
  Mi : ZMod n → ℕ
  hi : ZMod n → ℕ

def ThickN {n : ℕ} (b η : ℕ) (sz : ZMod n → ℕ) (a : ZMod n) : Prop := b ≤ sz a ∧ sz a ≤ b + η

def NWord.win {n : ℕ} (W : NWord n) (a : ZMod n) : Set ℤ :=
  {u | (if W.up a then (W.sz a : ℤ) ≤ u ∧ u ≤ W.sz a + W.S else -(W.sz a : ℤ) - W.S ≤ u ∧ u ≤ -(W.sz a : ℤ)) ∨
    |u| ≤ (W.η : ℤ)}

section Numbers

variable {D : D7} (L : SizeData₂ D)

def hB : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t

def eta₃ : ℝ := L.etaSz + D.R.t + 2

def wB : ℝ :=
  max (L.sc.w'' D.R.n + L.etaSz) ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)

def wP : ℝ := wB L + ((D.R.t : ℝ) + 1) / 2

def jA (l : ℕ) : ℕ := max 1 ⌈Real.logb ((l : ℝ) - 1) (LevelStarExponents.lA L)⌉₊

variable {n : ℕ}

structure WordNum (W : NWord n) : Prop where
  thick_or : ∀ a, ThickN W.b W.η W.sz a ∨ W.sz a ≤ W.w
  h_le : (W.b : ℝ) + W.η + W.S ≤ hB L
  w_le : (W.w : ℝ) ≤ wP L
  S_le : (W.S : ℝ) ≤ L.Sc
  η_le : (W.η : ℝ) ≤ eta₃ L
  m_eq : W.m = D.R.m

structure WordsB (l : ℕ) (C : ℝ) (W : NWord n) : Prop where
  j_lt : jA L l + 1 ≤ n
  par : C * ((jA L l : ℝ) + 1) * (((W.w + W.S + W.η : ℕ) : ℝ) + 1) ≤ (W.b : ℝ)
  clusters : Clusters (ThickN W.b W.η W.sz) (jA L l)

structure WordBox (W : NWord n) : Prop where
  box_le : ∀ a, ((W.Mi a + W.hi a : ℕ) : ℝ) ≤ 2 * hB L
  nt : ∀ a, ¬ ThickN W.b W.η W.sz a →
    ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ wB L ∧ |(W.sz a : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2
  b_lo : L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (W.b : ℝ)
  b_hi : (W.b : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1

end Numbers

def Small {n : ℕ} (W : NWord n) : Prop :=
  1 ≤ W.b ∧ 1 ≤ W.w ∧ 20 * W.w ≤ W.b ∧ 20 * W.η ≤ W.b ∧ 20 * W.S ≤ W.b ∧ ∀ a, W.η < W.sz a

def WordsNT {n : ℕ} (W : NWord n) : Prop :=
  Small W ∧ Alternates W.up ∧ (∃ a, ¬ ThickN W.b W.η W.sz a) ∧ NoThree (ThickN W.b W.η W.sz)

def WordsAT {n : ℕ} (l : ℕ) (W : NWord n) (d : ℕ) : Prop :=
  Even n ∧ (∀ a, W.up a = decide ((a.val + d) % 2 = 1)) ∧ Small W ∧
  (∀ a, W.Mi a = (if W.up a then W.η else W.sz a + W.S) ∧ W.hi a = (if W.up a then W.sz a + W.S else W.η)) ∧
  ∀ M : ℕ, IsGreatest (Set.range W.sz) M → ∀ a,
    ((M : ℝ) + W.S) / 2 ≤ W.sz a ∧
    2 * (((M : ℝ) + W.S + W.η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 +
      (Real.logb l (2 * ((M : ℝ) + W.S + W.η)) + 1)) + W.η + 1 ≤ W.sz a

def IsOrbit {φ : Formalism.HC.Frame} {n : ℕ} (g : ZMod n → φ.GG) (ψ : φ.GG) : Prop :=
  n = orderOf ψ ∧ ∀ a, g a = g 0 * ψ ^ a.val

def recWord {D : D7} (L : SizeData₂ D) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) : NWord n where
  up a := !pos ε (g a)
  sz a := (szT (hcAt D (g a)) j (pos ε (g a))).toNat
  b := bHat L
  w := wHat D
  S := sHat L
  η := etaHat L
  m := D.R.m
  Mi a := if !pos ε (g a) then etaHat L
    else max (etaHat L) ((szT (hcAt D (g a)) j (pos ε (g a))).toNat + sHat L)
  hi a := if !pos ε (g a) then max (etaHat L) ((szT (hcAt D (g a)) j (pos ε (g a))).toNat + sHat L)
    else etaHat L

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}

abbrev Wach (K LL : FinExt l) : Type 1 :=
  LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

variable {P} (W : Wach P K LL)

def Over (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) : Prop :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a

def JumpsAt (T : Lat K LL) (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (S : Set ℤ) : Prop :=
  ∀ τ, Over W τ a → JumpsInV (P.PD K) T.ρ τ S

def JumpsLet (T : Lat K LL) (Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) : Prop :=
  ∀ a, JumpsAt W T a (Set.Icc (-(Mi a : ℤ)) (hi a))

open Classical in

def lowCount [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : Lat K LL) (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (η : ℕ) : ℤ :=
  ∑ τ ∈ Finset.univ.filter (fun τ => Over W τ a), ∑ u ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T.ρ τ u

def Fits (T : Lat K LL) (Wd : NWord (Module.finrank ℚ_[l] ↥(K0 K))) : Prop :=
  IsCrys (P.PD K) T.ρ ∧ (∀ a, JumpsAt W T a (Wd.win a)) ∧ JumpsLet W T Wd.Mi Wd.hi

def IsMatRep (T : Lat K LL) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) : Prop :=
  ∃ e : T.V ≃ₗ[↥LL.1] (Fin k → ↥LL.1), ∀ g v, e (T.ρ g v) = (M g).mulVec (e v)

structure WordLoc {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (Wd : NWord (Module.finrank ℚ_[l] ↥(K0 K))) : Prop where
  unram : K.1 ≤ MaximalUnramifiedExtension l
  split : ∀ _ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1), Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1
  t1 : ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x g => Ms x g) → Fits W T Wd
  t2 : ∀ T : Lat K LL, IsMatRep T M' → Fits W T Wd ∧
    ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a Wd.η ≤ (Wd.m : ℤ)

def Reads {R : Ranks} (H : Host R) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (g : R.GG) : Prop :=
  ∀ x : H.E, τ (c x) = κ (H.sigmaOf g x)

variable (P)

structure JumpIn (D : D7) (j : Fin D.R.m) (ε : ℤˣ) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1)
    {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) : Prop where
  cont : ∀ x, Continuous (Ms x)
  crys : ∀ x, IsCrys (P.PD K) (matRep (Ms x))
  jumps : ∀ x τ g, Reads D.host c κ τ g →
    JumpsInV (P.PD K) (matRep (Ms x)) τ {u | u ∈ jT1 (hcAt D g) j (pos ε g)}
  crys' : IsCrys (P.PD K) (matRep M')
  mult' : ∀ τ g, Reads D.host c κ τ g → ∀ u : ℤ,
    multV (P.PD K) (matRep M') τ u = ((jT2 (hcAt D g) j (pos ε g)).count u : ℕ)

end Local

section Record

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def liftIdx : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

structure Enl where
  LL : FinExt (D.nd.l i)
  inc : Br.LL D.nbr i w hw →+* ↥LL.1

variable {D i w hw} (C : Enl D i w hw)

def Enl.loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1 :=
  mapM C.inc (Br.loc D.nbr i w hw M)

def Enl.base : D.host.E →+* ↥C.LL.1 :=
  C.inc.comp ((Br.toLLK (D.nbr i w hw)).comp ((D.nd.embK i).comp D.embE))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def Enl.Input (ε : ℤˣ) : Prop :=
  JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) C.base
    (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π))

def Enl.WordBase (L : SizeData₂ D) (HW : HWOf D.loc) (hG : Good (D.nbr i w hw).Kw 1 C.LL)
    (Wd : NWord (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw))) : Prop :=
  Br.DegW D.nbr i w hw ∧
  WordLoc (P := D.loc (D.nd.l i)) ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG)
    (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) Wd ∧
  WordNum L Wd

end Record

def InertUnr (D : D7) (p : ℕ) : Prop :=
  p ∉ D.host.small ∧ p ≠ D.host.q ∧ p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1

theorem inertUnr_iff (D : D7) (p : ℕ) : InertUnr D p ↔
    Ne p 2 ∧ p ≠ D.host.q ∧ p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rintro rfl
    exact h1 (Nat.mem_primeFactors.2 ⟨Nat.prime_two,
      (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd, D.host.QS_pos.ne'⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h2.2.2 ?_, h2⟩
    have h' := Nat.mem_primeFactors.1 h
    exact D.host.QS_split p h'.1 h1 h'.2.1

theorem InertUnr.ne_two {D : D7} {p : ℕ} (h : InertUnr D p) : p ≠ 2 := ((inertUnr_iff D p).1 h).1

theorem InertUnr.not_dvd_condN {D : D7} {p : ℕ} (h : InertUnr D p) (hp : p.Prime) : ¬ p ∣ D.host.condN := by
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact h.1 (Nat.mem_primeFactors.2 ⟨hp, h2, D.host.QS_pos.ne'⟩)
    · exact h.2.1 ((Nat.prime_dvd_prime_iff_eq hp D.host.hyp.1).1 h2)
  · exact h.2.2.1 ((Nat.prime_dvd_prime_iff_eq hp D.host.hyp.2.1).1 h1)

def IsRowB {D : D7} (L : SizeData₂ D) (p : ℕ) : Prop :=
  (p : ℝ) < LevelStarExponents.lA L ∧ 4 * D.host.Lw < orderOf (D.R.hH (DV.frobG D p).2)

theorem IsRowB.lt_orderOf {D : D7} {L : SizeData₂ D} {p : ℕ} (h : IsRowB L p) :
    4 * D.host.Lw < orderOf (DV.frobG D p).2 :=
  h.2.trans_le (Nat.le_of_dvd (orderOf_pos _) (orderOf_map_dvd _ _))

def HalfB {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (C₂ : ℝ) : Prop :=
  ∀ (i : D.nd.Loc), InertUnr D (D.nd.l i) → IsRowB L (D.nd.l i) →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ), C.Input r ρ π ε →
      ∃ Wd, C.WordBase r ρ π L HW hG Wd ∧ WordsB L (D.nd.l i) C₂ Wd

def HalfCD {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) : Prop :=
  ∀ (i : D.nd.Loc), InertUnr D (D.nd.l i) →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
    ∀ (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ), C.Input r ρ π ε →
      ∃ Wd, C.WordBase r ρ π L HW hG Wd ∧ WordBox L Wd ∧
        11 ≤ D.nd.l i ∧ (WordsNT Wd ∨ ∃ d, WordsAT (D.nd.l i) Wd d)

end GlobalTheory.HTW.Rec
