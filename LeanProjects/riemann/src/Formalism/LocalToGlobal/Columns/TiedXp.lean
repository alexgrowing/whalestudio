import Formalism.LocalToGlobal.Columns.TiedCls
import Formalism.LocalToGlobal.Columns.TiedCG
import Formalism.LocalToGlobal.Columns.RowFormsAdelic

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenP

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (σ₀ : X.K →+* ℂ) {n : ℕ} [NeZero n]
  (Λ : LevFam X.E X.K n Pr.vGs)

theorem xp_basePi_one : BasePi (∅ : Finset (Pl X.E)) (1 : 𝓞 X.E) where
  dvd r := ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩
  cop := isCoprime_one_left

theorem xp_L_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (Pl E)}
    (d : Deco E n (∅ : Finset (Pl E)) SG) : d.L = d.N := by
  unfold Deco.L
  have : {x | x ∈ d.N ∧ ∀ P : (∅ : Finset (Pl E)), d.f P x = 0} = (d.N : Set (Sp E n)) := by
    ext x
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun P => absurd P.2 (Finset.notMem_empty P.1)⟩
  rw [this, Submodule.span_eq]

def tieLevP : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (ST := ∅) (π := 1) (fun w => (Λ w).H) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)

def clsPG₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  lev := tieLevP hc σ₀ Λ
  y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
  y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
  y_lat := fun c x => by
    have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
    rw [xp_L_eq_N] at h
    exact h
  stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
  stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range c γ.1 γ.2

def clsPG (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    ClsG hc.sig Q.J 1 Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsPG₁ hc σ₀ Λ s hS hs

end GenP

section Rec

variable {d : ColDat} (a : ColArgs d)

abbrev PCl (d : ColDat) : Type := (ptGSD (Pr := d.Pr) d.W d.levP).Cl

def ColDat.reprP (d : ColDat) (c : PCl d) : DecoSet d.X.E (d.R.N d.R.m - 1) ∅ d.Pr.vGs :=
  (ptGSD (Pr := d.Pr) d.W d.levP).outSec.rep c

def crdPr (hS : SpStd d.toColBase) (hH : HostHyp d) :
    StepCrd d.Pr d.σ₀ (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  J := CF.gramP (d.colRec a)
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := fun c => (d.reprP c).1.N
  l0 := stdLat d.X.E (d.R.N d.R.m - 1)
  hJ := gramP_eq a hS
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := rfl
  hl0 := rfl

def PtSurjP (d : ColDat) : Prop := DecoPtSurj d.sp.cm (d.R.N d.R.m - 1) (∅ : Finset (Pl d.X.E)) d.Pr.vGs

def pClsG (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) :=
  clsPG d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH)

def parabolicClassAgreement (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (u : d.what₂.Word) :
    CF.ClsPTied (D := d.colRec a) u where
  lev := (pClsG a hS hH hP).lev
  y := (pClsG a hS hH hP).y
  y_bij := (pClsG a hS hH hP).y_bij
  lat := fun c => (d.reprP c).1.N
  y_lat := (pClsG a hS hH hP).y_lat
  lat_fin := fun c => Module.Finite.iff_fg.2 (d.reprP c).2.lat.fg
  stabI := (pClsG a hS hH hP).stabI
  stabI_inj := (pClsG a hS hH hP).stabI_inj
  stabI_range := (pClsG a hS hH hP).stabI_range

end Rec

end Formalism.L2.Col
