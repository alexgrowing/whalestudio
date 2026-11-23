import Formalism.LocalToGlobal.Columns.TiedCls

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RatSpanG {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def IntSpanG {K : Type} [Field K] (s : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : K) (f : ι → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW Pl w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = s r • Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

structure ValCrd (σ₀ : X.K →+* ℂ) (u : Pr.Word) (i : ℕ) extends
    StepCrd Pr σ₀ (R.N i) (fun c : StCl W Λ u i => ((stepGSD W Λ u i).outSec.rep c).1.L) where
  lt : X.Tau → DomWeight (R.N i)
  hlt : lt = W.lamTrue u i

variable (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ) (c₀ : DiaG X.E (Pr.vT u)) (hS : DecoPtSurj hc (R.N i) (Pr.vT u) Pr.vGs)

@[reducible] def valK (Q : ValCrd W Λ σ₀ u i) :=
  clsG hc hX hPr σ₀ u (Λ i) c₀ (fun c : StCl W Λ u i => (stepGSD W Λ u i).outSec.rep c) hS
    (fun c => (stepGSD W Λ u i).outSec.spec c) Q.toStepCrd

def valEY (Q : ValCrd W Λ σ₀ u i) : FrS X σ₀ (R.N i) ≃ Frames (gramC Q.J Q.emb) := Equiv.refl _

namespace Val

def De (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∃ C : GL (Fin (R.N i)) X.E, cT (hc.sig : X.E →+* X.E) C.1 * C.1 = Q.J ∧
    (∀ x : Fin (R.N i) → X.E, x ∈ Q.l0 ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 X.E) X.E).range) ∧
    ∀ τ (z : FrS X σ₀ (R.N i)), deFr z τ = Q.emb τ C.1.det * ((valEY W Λ σ₀ u i Q z).1 τ).det

def Fi (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ φ : StCl W Λ u i → FrS X σ₀ (R.N i) → ℂ, φ ∈ (stepEv W Λ σ₀ hσ u i).Fi ↔
    (fun c z => φ c ((valEY W Λ σ₀ u i Q).symm z)) ∈
      FiC (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev Q.emb Q.lt (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y

def IpV (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (o : Frames (gramC Q.J Q.emb)), o.IsON → ∀ P ∈ CSpan (W.lamN u i), ∀ P' ∈ CSpan (W.lamN u i),
    (stepEv W Λ σ₀ hσ u i).ip
      (fun z => fnOf _ (shiftOf Q.lt) (fun τ => (o.1 τ)⁻¹) P (valEY W Λ σ₀ u i Q z))
      (fun z => fnOf _ (shiftOf Q.lt) (fun τ => (o.1 τ)⁻¹) P' (valEY W Λ σ₀ u i Q z)) =
    nfAll (W.lamN u i) P' P

def Rat (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ φ : StCl W Λ u i → FrS X σ₀ (R.N i) → ℂ, (∃ x, (stepEv W Λ σ₀ hσ u i).emb x = φ) ↔
    φ ∈ (stepEv W Λ σ₀ hσ u i).Fi ∧ ∀ c, ∃ P ∈ RatSpanG σ₀ (W.lamN u i),
      ∀ z, φ c z = fnOf _ (shiftOf Q.lt) 1 P (valEY W Λ σ₀ u i Q z)

def Lat (Pl : Rows.Places X.K) (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ x : (stepGSD W Λ u i).EqFun, x ∈ (stepGSD W Λ u i).intDel ↔
    ∀ (w : Pl.Pl) (c : StCl W Λ u i) (B : GL (Fin (R.N i)) X.E),
      IsLocBasis (Pl.resChar w) (dualSet (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) B →
      ∃ P ∈ IntSpanG σ₀ Pl w (W.lamN u i),
        ∀ z, (stepEv W Λ σ₀ hσ u i).emb x c z =
          fnOf _ (shiftOf Q.lt) (atInf Q.emb (B⁻¹ : GL (Fin (R.N i)) X.E).1) P (valEY W Λ σ₀ u i Q z)

variable (eV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal})

def Dil (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (v : {P // P ∈ Pr.vT u}) (a : (𝓞 X.E ⧸ v.1.asIdeal)ˣ) (k : ℤ), (k : 𝓞 X.E ⧸ v.1.asIdeal) = a → ∀ c δ,
    IsDia (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev (eV v).1 (eV v).2 k δ →
    (Quotient.mk'' ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y (dilD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) v a c)) :
      Cls (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev) = Quotient.mk'' ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y c * δ)

def DilT (Q : ValCrd W Λ σ₀ u i) : Prop :=
  ∀ (v : {P // P ∈ Pr.vT u}) (a : (𝓞 X.E ⧸ v.1.asIdeal)ˣ) (k : ℤ), (k : 𝓞 X.E ⧸ v.1.asIdeal) = a → ∀ c δ,
    IsDia (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev (eV v).1 (eV v).2 k δ →
    ∀ g ∈ AdFun (valK W Λ hc hX hPr σ₀ u i c₀ hS Q).lev Q.emb,
    (stepEv W Λ σ₀ hσ u i).trPt ((repD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) c).dia1 v a)
      (fun z => g ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y (dilD (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) v a c))
        (valEY W Λ σ₀ u i Q z)) =
      fun z => g ((valK W Λ hc hX hPr σ₀ u i c₀ hS Q).y c * δ) (valEY W Λ σ₀ u i Q z)

end Val

theorem lamTrue_eq_shW (u : Pr.Word) (i : ℕ) :
    W.lamTrue u i = fun τ => shW (W.lamN u i τ) ((i * (R.t + 1) / 2 : ℕ) : ℤ) := by
  funext τ
  have h : ((i * (R.t + 1) / 2 : ℕ) : ℤ) = (i : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
    obtain ⟨b, hb⟩ := R.t_odd
    have h2 : R.t + 1 = 2 * (b + 1) := by omega
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    push_cast
    ring
  unfold Wts.lamTrue shiftW shW
  congr 1
  funext x
  rw [h]
  ring

theorem Val.de (Q : ValCrd W Λ σ₀ u i) : Val.De W Λ hc σ₀ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  refine ⟨1, ?_, ?_, ?_⟩
  · simp [cT]
  · intro x
    simp only [Units.val_one, Matrix.one_mulVec]
    constructor
    · intro hx a
      exact Submodule.mem_one.1 (hx a trivial)
    · intro hx a _
      exact Submodule.mem_one.2 (hx a)
  · intro τ z
    simp only [Units.val_one, Matrix.det_one, map_one, one_mul]
    rfl

theorem Val.ipV (Q : ValCrd W Λ σ₀ u i) : Val.IpV W Λ σ₀ hσ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro o ho P _ P' _
  have h := ipFr_fnOf (gramC (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) (embAt σ₀ X.emb)) (W.lamTrue u i) (stdFrC _) o
    (fun τ => by simp [stdFrC, gramC]) (frame_std _ o ho) P P'
  have h2 : nfAll (W.lamTrue u i) P' P = nfAll (W.lamN u i) P' P := by
    rw [lamTrue_eq_shW]
    exact nfAll_shW _ _ _ _
  rw [← h2]
  exact h

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem lamT_eq (u : d.what₂.Word) (i : ℕ) : CF.lamT (D := d.colRec a) u i = d.W.lamTrue u i :=
  (lamTrue_eq_shW (Pr := d.Pr) d.W u i).symm

def valCrd (hS : SpStd d.toColBase) (hH : HostHyp d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    ValCrd (Pr := d.Pr) d.W d.lev d.σ₀ u i where
  toStepCrd := stepCrd a hS hH u i hi
  lt := CF.lamT (D := d.colRec a) u i
  hlt := lamT_eq a u i

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
  (eV : ((d.colRec a).mem u).A.vT ≃ CF.PlT (d.colRec a) u)

def valuationAgreement
    (hFi : Val.Fi (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i)
      (valCrd a hS hH u i hi))
    (hRat : Val.Rat (Pr := d.Pr) d.W d.lev d.σ₀ d.star_cx u i (valCrd a hS hH u i hi))
    (hLat : Val.Lat (Pr := d.Pr) d.W d.lev d.sp.cm d.σ₀ d.star_cx u i d.what₂.places (valCrd a hS hH u i hi))
    (hDil : Val.Dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i) eV
      (valCrd a hS hH u i hi))
    (hDilT : Val.DilT (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ d.star_cx u i (colDia (X := d.X) (Pr := d.Pr) d.R u i) (hP u i) eV
      (valCrd a hS hH u i hi)) :
    CF.ValTied (D := d.colRec a) u eV i hi (classAgreement a hS hH hP u i hi) where
  eY := valEY (Pr := d.Pr) d.W d.lev d.σ₀ u i (valCrd a hS hH u i hi)
  de := Val.de (Pr := d.Pr) d.W d.lev d.sp.cm d.σ₀ u i (valCrd a hS hH u i hi)
  Fi := hFi
  ipV := fun _ => Val.ipV (Pr := d.Pr) d.W d.lev d.σ₀ d.star_cx u i (valCrd a hS hH u i hi)
  rat := hRat
  lat := hLat
  dil := hDil
  dilT := hDilT

end Rec

end Formalism.L2.Col
