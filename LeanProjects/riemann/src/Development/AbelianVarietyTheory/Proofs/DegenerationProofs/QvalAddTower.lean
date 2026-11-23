import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.NestQVal

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem pt_nsmul {R : Type} [CommRing R] [IsDomain R] {D₀ : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D₀ F N) (h1 : ∀ g, ∃! c, ν.Pt g c)
    (h2 : ∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (GtPtF.IsAdd g g' g'' ↔ c'' = c * c'))
    {g : GtPtF D₀ F} {c : N.Gt} (hc : ν.Pt g c) (m : ℕ) : ν.Pt (m • g) (c ^ m) := by
  induction m with
  | zero =>
    obtain ⟨z, hz, -⟩ := h1 0
    have e : z = z * z := (h2 0 0 0 z z z hz hz hz).1 ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (add_zero _).symm)
    have e' : z = 1 := left_eq_mul.1 e
    rw [zero_nsmul, pow_zero, ← e']
    exact hz
  | succ m ih =>
    obtain ⟨z, hz, -⟩ := h1 ((m + 1) • g)
    have e : z = c ^ m * c :=
      (h2 _ _ _ _ _ _ ih hc hz).1 ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (succ_nsmul g m))
    rw [pow_succ, ← e]
    exact hz

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in

theorem _root_.GlobalTheory.NestQVal.qval_add_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIsoQ D D₀ oa F) (N : _root_.GlobalTheory.Ex.NumD F) (ν : _root_.GlobalTheory.Ex.NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  intro E _ _ _ H D R _ _ D₀ _ oa _ _ F _ _ _ I N ν q hPt hAdd hQ hev

  have hzero : ν.Pt 0 1 := by
    obtain ⟨c, hc, -⟩ := hPt 0
    have h := (hAdd 0 0 0 c c c hc hc hc).1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (add_zero 0).symm)
    have : c = 1 := by simpa using (mul_eq_left.1 h.symm)
    simpa [this] using hc
  have hsmul : ∀ (m : ℕ) g c, ν.Pt g c → ν.Pt (m • g) (c ^ m) := by
    intro m g c hc
    induction m with
    | zero => simpa using hzero
    | succ k ih =>
      obtain ⟨c', hc', -⟩ := hPt ((k + 1) • g)
      have h := (hAdd _ _ _ _ _ _ ih hc hc').1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (succ_nsmul g k))
      simpa [h, pow_succ] using hc'
  refine ⟨fun n hn a b => ?_, fun n m hn hm a p hp1 hp2 => ?_⟩
  · obtain ⟨r, hry, hrg, hr⟩ := I.add n hn a b
    obtain ⟨hya, hga⟩ := hev n a
    obtain ⟨hyb, hgb⟩ := hev n b
    obtain ⟨c'', hc'', -⟩ := hPt r.g
    have hc := (hAdd _ _ _ _ _ _ hga hgb hc'').1 hrg
    have hrs : ν.QPt r (q n a * q n b) := by
      refine ⟨?_, ?_⟩
      · simp [hry, ← hya, ← hyb]
      · simpa [hc] using hc''
    exact ((hQ n).2 _ _ _ _ hrs (hev n (a + b))).1 hr
  · obtain ⟨Q, hQy, hQg, hQe⟩ := I.tower n m hn hm a
    obtain ⟨hy, hg⟩ := hev (n * m) a
    have hQp : ν.QPt Q p := by
      refine ⟨?_, ?_⟩
      · rw [hQy, ← hy, hp1]
      · rw [(_root_.GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hQg, hp2]
        exact hsmul m _ _ hg
    exact ((hQ n).2 _ _ _ _ hQp (hev n a)).1 hQe

end GlobalTheory.NestQVal
