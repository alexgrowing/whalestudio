import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def OrZero {X : Type} [Zero X] (p : X → Prop) (x : X) : Prop := ((∃ y, p y) → p x) ∧ ((¬ ∃ y, p y) → x = 0)

theorem orZero_exists {X : Type} [Zero X] (p : X → Prop) : ∃ x, OrZero p x := by
  by_cases h : ∃ y, p y
  · obtain ⟨y, hy⟩ := h
    exact ⟨y, fun _ => hy, fun hn => absurd ⟨y, hy⟩ hn⟩
  · exact ⟨0, fun h' => absurd h' h, fun _ => rfl⟩

section Weak

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks)

def PItY (k : ℕ) (It : type_of% (R.ItY k)) : Prop := ∀ t, IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t k) (R.ptY t k) It

def PItX (It : type_of% R.ItX) : Prop := ∀ t, IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t) (R.ptX t) It

def PIoY (t : T) (k : ℕ) (io : R.CC t (k + 1) →ₗ[ℂ] R.CC t k) : Prop :=
  Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k) (R.CC t (k + 1)) (R.CC t k) io

def PIoX (t : T) (io : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) →ₗ[ℂ] R.CC t (D.R.m - 1)) : Prop :=
  Lift.IsIo (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t) R.ItX (LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e))
    (R.CC t (D.R.m - 1)) io

def PTh (t : T) (g : (R.HX t).H →ₗ[ℂ] R.HE.H) : Prop :=
  ∀ x, R.HE.e (g x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x))

def PIoP (i : Fin D.R.m) (io : type_of% (R.ioP i)) : Prop :=
  ∀ t, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t) (R.ptP i t) (Delta i) io

def PThF (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, th x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP, Lift.IsThetaP (R.νV i t) (R.fdV i t) (fun g h f => thetaKO (R.ωP i t) h g f) (R.ptP i t) (R.ioP i)
        (LinearMap.range (R.extV i t)) thP ∧
      ∀ x (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        th x (fun ρ => v ρ) = thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

def PThG (i : Fin D.R.m) (t : T) (g : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) : Prop :=
  ∀ x, (R.HW i (sg0 D A)).e (g x) = postOn _ (R.eWf i (sg0 D A)) (R.thF i t x)

abbrev cw_ItY : Prop :=
  ∀ k, k + 1 < D.R.m → OrZero (R.PItY k) (R.ItY k)

abbrev cw_ItX : Prop :=
  OrZero R.PItX R.ItX

abbrev cw_ioY : Prop :=
  ∀ t k, k + 1 < D.R.m → OrZero (R.PIoY t k) (R.ioY t k)

abbrev cw_ioX : Prop :=
  ∀ t, OrZero (R.PIoX t) (R.ioX t)

abbrev cw_Th : Prop :=
  ∀ t, OrZero (R.PTh t) (R.Th t)

structure IsChainW : Prop where
  ωY : R.chain_ωY
  ωX : R.chain_ωX
  vY : R.chain_vY
  vX : R.chain_vX
  ptY : R.chain_ptY
  ptX : R.chain_ptX
  ItY : R.cw_ItY
  ItX : R.cw_ItX
  ioY : R.cw_ioY
  ioX : R.cw_ioX
  Th : R.cw_Th

abbrev tw_ioP : Prop :=
  ∀ i, OrZero (R.PIoP i) (R.ioP i)

abbrev tw_thF : Prop :=
  ∀ i t, OrZero (R.PThF i t) (R.thF i t)

abbrev tw_thG : Prop :=
  ∀ i t, OrZero (R.PThG i t) (R.thG i t)

structure IsThPW : Prop where
  ωP : R.thP_ωP
  vP : R.thP_vP
  pt_theta : R.thP_pt_theta
  ioP : R.tw_ioP
  thF : R.tw_thF
  thG : R.tw_thG

abbrev ex_ItY : Prop :=
  ∀ k, k + 1 < D.R.m → ∃ y, R.PItY k y

abbrev ex_ItX : Prop :=
  ∃ y, R.PItX y

abbrev ex_ioY : Prop :=
  ∀ t k, k + 1 < D.R.m → ∃ y, R.PIoY t k y

abbrev ex_ioX : Prop :=
  ∀ t, ∃ y, R.PIoX t y

abbrev ex_Th : Prop :=
  ∀ t, ∃ y, R.PTh t y

abbrev ex_ioP : Prop :=
  ∀ i, ∃ y, R.PIoP i y

abbrev ex_thF : Prop :=
  ∀ i t, ∃ y, R.PThF i t y

abbrev ex_thG : Prop :=
  ∀ i t, ∃ y, R.PThG i t y

structure ExAt : Prop where
  ItY : R.ex_ItY
  ItX : R.ex_ItX
  ioY : R.ex_ioY
  ioX : R.ex_ioX
  Th : R.ex_Th
  ioP : R.ex_ioP
  thF : R.ex_thF
  thG : R.ex_thG

structure BaseW (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChainW
  thP : R.IsThPW

structure CharW (F : Face D A) : Prop extends R.BaseW F where
  scal : R.IsScal F
  tup : R.IsTup F

variable {R}

theorem chain_of_weak (h : R.IsChainW) (e : R.ExAt) : R.IsChain := ⟨h.ωY, h.ωX, h.vY, h.vX, h.ptY, h.ptX,
  fun t k hk => (h.ItY k hk).1 (e.ItY k hk) t,
  fun t => h.ItX.1 e.ItX t,
  fun t k hk => (h.ioY t k (by omega)).1 (e.ioY t k (by omega)),
  fun t => (h.ioX t).1 (e.ioX t),
  fun t => (h.Th t).1 (e.Th t)⟩

theorem thP_of_weak (h : R.IsThPW) (e : R.ExAt) : R.IsThP := ⟨h.ωP, h.vP, h.pt_theta,
  fun i t => (h.ioP i).1 (e.ioP i) t,
  fun i t x => ((h.thF i t).1 (e.thF i t)).1 x,
  fun i t => ((h.thF i t).1 (e.thF i t)).2,
  fun i t => (h.thG i t).1 (e.thG i t)⟩

end RealDat

end Weak

end Formalism.IndefR.Links

end
