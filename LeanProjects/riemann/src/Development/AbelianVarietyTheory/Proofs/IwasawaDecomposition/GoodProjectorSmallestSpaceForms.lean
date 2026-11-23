import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

section Gen

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem projTie_eq_of_proj {Y : Type*} {C : Submodule ℂ N} {ip : N → N → ℂ} {j : X ≃ₗ[ℂ] C} {f : Y → X} {g : Y → N}
    (hH : HilbTie C ip j) (hP : ProjTie C ip j f g) (y : Y) (p : N) (hp : p ∈ C)
    (hip : ∀ c ∈ C, ip c (g y) = ip c p) : ((j (f y) : C) : N) = p := by
  have h1 : f y = j.symm ⟨p, hp⟩ := by
    refine ext_inner_left ℂ fun x => ?_
    rw [hP x y, hH x (j.symm ⟨p, hp⟩), LinearEquiv.apply_symm_apply]
    exact hip _ (j x).2
  rw [h1, LinearEquiv.apply_symm_apply]

end Gen

section Chain

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

theorem downTo_succ_cast (S : RowSide D EE) (μ : D.what₂.Tup) (n : ℕ) :
    ∀ (j : ℕ) (h : j = n + 1) (z : S.Mult μ j),
      S.downTo μ j z = S.downTo μ n (S.io μ n (cast (congrArg (S.Mult μ) h) z)) := by
  intro j h z
  subst h
  rfl

theorem dnFrom_zero_cast (C : ChainReal D) (b : Bool) (μ : D.what₂.Tup)
    (io : ∀ k, C.CC b μ (k + 1) →ₗ[ℂ] C.CC b μ k) :
    ∀ (n : ℕ) (h : n = 0) (y : C.CC b μ n),
      ((Lift.dnFrom (C.CC b μ) io n y : C.CC b μ 0) : C.Amb 0) = cast (congrArg C.Amb h) (y : C.Amb n) := by
  intro n h y
  subst h
  rfl

theorem mem_CCP_cast (C : ChainReal D) (b : Bool) (μ : D.what₂.Tup) :
    ∀ (n : ℕ) (h : n = 0) (w : C.Amb n), w ∈ C.CCP b μ n → cast (congrArg C.Amb h) w ∈ C.CCP b μ 0 := by
  intro n h w hw
  subst h
  exact hw

set_option maxHeartbeats 2000000 in

theorem iota_eq_gen (X : RowSide D EE) (C : ChainReal D) (b : Bool) (I : RowIds X C b) {n : ℕ}
    {bs : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT} (hR : RowSideReal X C b I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (hok : C.IoOK b μ) (hm : 0 < D.R.m)
    (hLev : ∀ k (_ : k + 1 ≤ D.R.m - 1) (y : C.CC b μ (k + 1)), (y : C.Amb (k + 1)) ∈ C.CCP b μ (k + 1) →
      ((C.ioC b μ k y : C.CC b μ k) : C.Amb k) ∈ C.CCP b μ k)
    (hLevX : ∀ y : C.CCX b μ, (y : C.AmbX) ∈ C.CCXP b μ →
      ((C.ioX b μ y : C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1)) ∈ C.CCP b μ (D.R.m - 1))
    (pE : C.Amb 0 → C.Amb 0)
    (hE : ∀ w : C.Amb 0, w ∈ C.CCP b μ 0 → pE w ∈ C.EEc b ∧ ∀ c ∈ C.EEc b, C.ipE b c w = C.ipE b c (pE w))
    (a : X.Amb μ) (u : C.CCX b μ) (hu : ((I.jX μ hμ ((X.multTop μ).symm a) : C.CCXP b μ) : C.AmbX) = u) :
    ((I.jE (X.iota μ a) : C.EEc b) : C.Amb 0) =
      pE ((Lift.dnFrom (C.CC b μ) (C.ioC b μ) (D.R.m - 1) (C.ioX b μ u) : C.CC b μ 0) : C.Amb 0) := by
  have huP : (u : C.AmbX) ∈ C.CCXP b μ := hu ▸ (I.jX μ hμ ((X.multTop μ).symm a)).2
  by_cases h1 : D.R.m = 1
  ·
    set z := (X.multTop μ).symm a with hz
    have hd : X.downTo μ D.R.m z = X.downTo μ 0 (X.io μ 0 (cast (congrArg (X.Mult μ) h1) z)) :=
      downTo_succ_cast X μ 0 D.R.m h1 z
    have hP := hR.io0X h1 μ hμ hok
    set x := cast (congrArg (X.Mult μ) h1) z with hx
    have hxz : cast (congrArg (X.Mult μ) h1.symm) x = z := by rw [hx]; exact cast_cast _ _ _
    have hincl : Submodule.inclusion (hR.lvlX μ hμ) (I.jX μ hμ (cast (congrArg (X.Mult μ) h1.symm) x)) = u := by
      apply Subtype.ext
      rw [hxz]
      exact hu
    have hw : cast (congrArg C.Amb (show D.R.m - 1 = 0 by omega))
        ((C.ioX b μ (Submodule.inclusion (hR.lvlX μ hμ) (I.jX μ hμ (cast (congrArg (X.Mult μ) h1.symm) x))) :
          C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1)) ∈ C.CCP b μ 0 := by
      rw [hincl]
      exact mem_CCP_cast C b μ _ (by omega) _ (hLevX u huP)
    have key := projTie_eq_of_proj hR.ee hP x _ (hE _ hw).1 (hE _ hw).2
    show ((I.jE ((X.multZero μ) (X.downTo μ D.R.m z)) : C.EEc b) : C.Amb 0) = _
    rw [hd]
    refine key.trans ?_
    rw [hincl, dnFrom_zero_cast C b μ (C.ioC b μ) (D.R.m - 1) (by omega)]
  · have h2 : 2 ≤ D.R.m := by omega

    have claim : ∀ j (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m - 1) (z : X.Mult μ j) (y : C.CC b μ j),
        ((I.jM μ hμ j hj1 hj2 z : C.CCP b μ j) : C.Amb j) = y →
        ((I.jE (X.multZero μ (X.downTo μ j z)) : C.EEc b) : C.Amb 0) =
          pE ((Lift.dnFrom (C.CC b μ) (C.ioC b μ) j y : C.CC b μ 0) : C.Amb 0) := by
      intro j hj1
      induction j, hj1 using Nat.le_induction with
      | base =>
        intro hj2 z y hy
        have hP := hR.io0 h2 μ hμ hok
        have hincl : Submodule.inclusion (hR.lvlP μ hμ 1 le_rfl (by omega)) (I.jM μ hμ 1 le_rfl (by omega) z) = y :=
          Subtype.ext hy
        have hyP : (y : C.Amb 1) ∈ C.CCP b μ 1 := hy ▸ (I.jM μ hμ 1 le_rfl hj2 z).2
        have hw := hLev 0 (by omega) y hyP
        have key := projTie_eq_of_proj hR.ee hP z _ (hE _ (hincl ▸ hw)).1 (hE _ (hincl ▸ hw)).2
        refine key.trans ?_
        rw [hincl]
        rfl
      | succ j hj ih =>
        intro hj2 z y hy
        have hP := hR.io μ hμ hok j hj hj2
        have hincl : Submodule.inclusion (hR.lvlP μ hμ (j + 1) (by omega) hj2) (I.jM μ hμ (j + 1) (by omega) hj2 z) = y :=
          Subtype.ext hy
        have hyP : (y : C.Amb (j + 1)) ∈ C.CCP b μ (j + 1) := hy ▸ (I.jM μ hμ (j + 1) (by omega) hj2 z).2
        have hw' : ((C.ioC b μ j (Submodule.inclusion (hR.lvlP μ hμ (j + 1) (by omega) hj2)
            (I.jM μ hμ (j + 1) (by omega) hj2 z)) : C.CC b μ j) : C.Amb j) ∈ C.CCP b μ j := by
          rw [hincl]
          exact hLev j hj2 y hyP
        have key := ProjTie.eq_of_mem (hR.mult μ hμ j hj (by omega)) hP z hw'
        rw [hincl] at key
        exact ih (by omega) (X.io μ j z) (C.ioC b μ j y) key
    set z := (X.multTop μ).symm a with hz
    have hd : X.downTo μ D.R.m z = X.downTo μ (D.R.m - 1) (X.io μ (D.R.m - 1)
        (cast (congrArg (X.Mult μ) (show D.R.m = D.R.m - 1 + 1 by omega)) z)) :=
      downTo_succ_cast X μ (D.R.m - 1) D.R.m (by omega) z
    have hP := hR.ioTop h2 μ hμ hok
    have hincl : Submodule.inclusion (hR.lvlX μ hμ) (I.jX μ hμ z) = u := Subtype.ext hu
    have hw' : ((C.ioX b μ (Submodule.inclusion (hR.lvlX μ hμ) (I.jX μ hμ z)) : C.CC b μ (D.R.m - 1)) :
        C.Amb (D.R.m - 1)) ∈ C.CCP b μ (D.R.m - 1) := by
      rw [hincl]
      exact hLevX u huP
    have key := ProjTie.eq_of_mem (hR.mult μ hμ (D.R.m - 1) (by omega) le_rfl) hP z hw'
    rw [hincl] at key
    show ((I.jE ((X.multZero μ) (X.downTo μ D.R.m z)) : C.EEc b) : C.Amb 0) = _
    rw [hd]
    exact claim (D.R.m - 1) (by omega) le_rfl _ _ key

end Chain

end GlobalTheory.Mem.R3.DTheta

namespace GlobalTheory.Mem.R3.DTheta

section Spec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem cc_eq (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (b : Bool) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m) :
    (toChainReal R F tupT hm hTop).CC b μ j = R.CC (tupT μ) j := by
  simp only [ChainReal.CC, toChainReal, if_pos hj]
  rfl

theorem ccp_eq (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (b : Bool) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m) :
    (toChainReal R F tupT hm hTop).CCP b μ j = MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)))
      (levChi _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b))) := by
  simp only [ChainReal.CCP, toChainReal, if_pos hj]
  rfl

theorem ioC_val (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (b : Bool) (μ : D.what₂.Tup) (k : ℕ) (hk : k + 1 < D.R.m) (y : (toChainReal R F tupT hm hTop).CC b μ (k + 1))
    (hy : y.1 ∈ R.CC (tupT μ) (k + 1)) :
    ((toChainReal R F tupT hm hTop).ioC b μ k y).1 = (R.ioY (tupT μ) k ⟨y.1, hy⟩).1 := by
  simp only [toChainReal, dif_pos hk]
  rfl

theorem ioX_val (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (b : Bool) (μ : D.what₂.Tup) (u : (toChainReal R F tupT hm hTop).CCX b μ)
    (hu : u.1 ∈ LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) :
    ((toChainReal R F tupT hm hTop).ioX b μ u).1 = (R.ioX (tupT μ) ⟨u.1, hu⟩).1 := by
  rfl

end Spec

end GlobalTheory.Mem.R3.DTheta

namespace GlobalTheory.Mem.R3.DTheta

theorem isIo_transfer {G H S Sinf Ds Dt : Type*} [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] {ν : Measure H} {𝓕 : Set H}
    {th : G → H → S → ℂ} {pt : Sinf → S} {T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {CCs CCs' : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))}
    {CCt CCt' : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))} {io : CCs →ₗ[ℂ] CCt} {io' : CCs' →ₗ[ℂ] CCt'}
    (h : Lift.IsIo ν 𝓕 th pt T CCs CCt io) (hc : ∀ F : CCs', ∃ F' : CCs, F.1 = F'.1 ∧ (io' F).1 = (io F').1) :
    Lift.IsIo ν 𝓕 th pt T CCs' CCt' io' where
  integ F φ v g := by
    obtain ⟨F', h1, -⟩ := hc F
    rw [h1]
    exact h.integ F' φ v g
  eq F φ v g := by
    obtain ⟨F', h1, h2⟩ := hc F
    rw [h1, h2]
    exact h.eq F' φ v g

section Spec2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem dnFrom_val (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (b : Bool) (μ : D.what₂.Tup) : ∀ n, n ≤ D.R.m - 1 → ∀ (y : (toChainReal R F tupT hm hTop).CC b μ n)
      (y' : R.CC (tupT μ) n), y.1 = y'.1 →
      (Lift.dnFrom ((toChainReal R F tupT hm hTop).CC b μ) ((toChainReal R F tupT hm hTop).ioC b μ) n y).1 =
        (Lift.dnFrom (R.CC (tupT μ)) (R.ioY (tupT μ)) n y').1 := by
  intro n
  induction n with
  | zero => intro _ y y' h; exact h
  | succ n ih =>
    intro hn y y' h
    have hy : y.1 ∈ R.CC (tupT μ) (n + 1) := by rw [h]; exact y'.2
    have e : (⟨y.1, hy⟩ : R.CC (tupT μ) (n + 1)) = y' := Subtype.ext h
    refine ih (by omega) _ _ ?_
    rw [ioC_val R F tupT hm hTop b μ n (by omega) y hy, e]

theorem ioOK_of_chain (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hch : R.IsChain) (b : Bool) (μ : D.what₂.Tup) : (toChainReal R F tupT hm hTop).IoOK b μ := by
  refine ⟨fun k hk => ?_, fun _ => ?_⟩
  · refine isIo_transfer (hch.ioY (tupT μ) k hk) fun y => ?_
    have hy : y.1 ∈ R.CC (tupT μ) (k + 1) := by
      rw [← cc_eq R F tupT hm hTop b μ (k + 1) (by omega)]; exact y.2
    exact ⟨⟨y.1, hy⟩, rfl, ioC_val R F tupT hm hTop b μ k (by omega) y hy⟩
  · refine isIo_transfer (hch.ioX (tupT μ)) fun y => ?_
    have hy : y.1 ∈ LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) := by
      rw [hTop (tupT μ)]; exact y.2
    exact ⟨⟨y.1, hy⟩, rfl, ioX_val R F tupT hm hTop b μ y hy⟩

end Spec2

end GlobalTheory.Mem.R3.DTheta

namespace GlobalTheory.Mem.R3.DTheta

section Spec3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def StepLev (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ y : R.CC t (k + 1),
    y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) (R.datYt t (k + 1) (R.levR F b)))
        (levChi _ (R.βY (k + 1)) (R.datYt t (k + 1) (R.levR F b))) →
      (R.ioY t k y).1 ∈ MultT R.θ (R.MY k) (levS _ (R.βY k) (R.datYt t k (R.levR F b)))
        (levChi _ (R.βY k) (R.datYt t k (R.levR F b)))

def TopLev (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (t : T) (y : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)),
    y.1 ∈ MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) →
      (R.ioX t y).1 ∈ MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) (R.levR F b)))
        (levChi _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) (R.levR F b)))

def RowProj (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (t : T) (w : MMap (R.MY 0)),
    w ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 (R.levR F b))) (levChi _ (R.βY 0) (R.datYt t 0 (R.levR F b))) →
      postOn (R.MY 0) R.e0 w ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b)))
          (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 ∧
        ∀ c ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0,
          ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0) R.fd0 c w =
            ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0) R.fd0 c (postOn (R.MY 0) R.e0 w)

def goodProjectorSmallestSpaceForms (R : RealDat D A Ks) (w : AmbT (R.MY 0)) : AmbT (R.MY 0) :=
  PiTensorProduct.lift (postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm w))

theorem hLev_of (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hS : StepLev R F) (b : Bool) (μ : D.what₂.Tup) :
    ∀ k (_ : k + 1 ≤ D.R.m - 1) (y : (toChainReal R F tupT hm hTop).CC b μ (k + 1)),
      (y : (toChainReal R F tupT hm hTop).Amb (k + 1)) ∈ (toChainReal R F tupT hm hTop).CCP b μ (k + 1) →
      (((toChainReal R F tupT hm hTop).ioC b μ k y : (toChainReal R F tupT hm hTop).CC b μ k) :
        (toChainReal R F tupT hm hTop).Amb k) ∈ (toChainReal R F tupT hm hTop).CCP b μ k := by
  intro k hk y hy
  have hy' : y.1 ∈ R.CC (tupT μ) (k + 1) := by
    rw [← cc_eq R F tupT hm hTop b μ (k + 1) (by omega)]; exact y.2
  rw [ccp_eq R F tupT hm hTop b μ (k + 1) (by omega)] at hy
  rw [ccp_eq R F tupT hm hTop b μ k (by omega), ioC_val R F tupT hm hTop b μ k (by omega) y hy']
  exact hS b (tupT μ) k (by omega) ⟨y.1, hy'⟩ hy

theorem hLevX_of (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hT : TopLev R F) (b : Bool) (μ : D.what₂.Tup) :
    ∀ y : (toChainReal R F tupT hm hTop).CCX b μ, (y : (toChainReal R F tupT hm hTop).AmbX) ∈
      (toChainReal R F tupT hm hTop).CCXP b μ →
      (((toChainReal R F tupT hm hTop).ioX b μ y : (toChainReal R F tupT hm hTop).CC b μ (D.R.m - 1)) :
        (toChainReal R F tupT hm hTop).Amb (D.R.m - 1)) ∈ (toChainReal R F tupT hm hTop).CCP b μ (D.R.m - 1) := by
  intro y hy
  have hy' : y.1 ∈ LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) := by
    rw [hTop (tupT μ)]; exact y.2
  rw [ccp_eq R F tupT hm hTop b μ (D.R.m - 1) (by omega), ioX_val R F tupT hm hTop b μ y hy']
  exact hT b (tupT μ) ⟨y.1, hy'⟩ hy

theorem hE_of (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hP : RowProj R F) (b : Bool) (μ : D.what₂.Tup) :
    ∀ w : (toChainReal R F tupT hm hTop).Amb 0, w ∈ (toChainReal R F tupT hm hTop).CCP b μ 0 →
      goodProjectorSmallestSpaceForms R w ∈ (toChainReal R F tupT hm hTop).EEc b ∧ ∀ c ∈ (toChainReal R F tupT hm hTop).EEc b,
        (toChainReal R F tupT hm hTop).ipE b c w = (toChainReal R F tupT hm hTop).ipE b c (goodProjectorSmallestSpaceForms R w) := by
  intro w hw
  rw [ccp_eq R F tupT hm hTop b μ 0 hm] at hw
  obtain ⟨h1, h2⟩ := hP b (tupT μ) _ ((mem_multT R.θ (R.MY 0) _ _ w).1 hw)
  refine ⟨⟨_, h1, rfl⟩, ?_⟩
  rintro c ⟨c', hc', rfl⟩
  show ipMT _ _ _ _ _ = ipMT _ _ _ _ _
  unfold ipMT goodProjectorSmallestSpaceForms
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have e : (PiTensorProduct.lift.symm (PiTensorProduct.lift (postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm w))) :
      MMap (R.MY 0)) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm w) := LinearEquiv.symm_apply_apply _ _
  convert h2 c' hc' using 2
  all_goals first | rfl | exact congrArg _ e

end Spec3

end GlobalTheory.Mem.R3.DTheta

namespace GlobalTheory.Mem.R3.DTheta

section Spec4

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in
theorem thDn_eq_dnFrom (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (b : Bool) (μ : D.what₂.Tup) (u : (toChainReal R F tupT hm hTop).CCX b μ)
    (y' : (R.HX (tupT μ)).H) (hu : u.1 = R.cX.toMap R.prX ((R.HX (tupT μ)).e y')) :
    (Lift.dnFrom ((toChainReal R F tupT hm hTop).CC b μ) ((toChainReal R F tupT hm hTop).ioC b μ) (D.R.m - 1)
      ((toChainReal R F tupT hm hTop).ioX b μ u)).1 = R.thDn (tupT μ) y' := by
  have hu' : u.1 ∈ LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) := ⟨y', hu.symm⟩
  have e1 : R.thDn (tupT μ) y' = (Lift.dnFrom (R.CC (tupT μ)) (R.ioY (tupT μ)) (D.R.m - 1)
      (R.ioX (tupT μ) ((R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e).rangeRestrict y'))).1 := by
    simp only [RealDat.thDn, Lift.thetaDn, LinearMap.comp_apply, Submodule.subtype_apply]
  have e2 : (⟨u.1, hu'⟩ : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) =
      (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e).rangeRestrict y' := Subtype.ext hu
  rw [e1]
  exact dnFrom_val R F tupT hm hTop b μ (D.R.m - 1) le_rfl ((toChainReal R F tupT hm hTop).ioX b μ u)
    (R.ioX (tupT μ) ((R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e).rangeRestrict y'))
    ((ioX_val R F tupT hm hTop b μ u hu').trans (congrArg (fun z => (R.ioX (tupT μ) z).1) e2))

set_option maxHeartbeats 2000000 in

theorem iota_eq_real (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (hch : R.IsChain) (hS : StepLev R F) (hT : TopLev R F) (hP : RowProj R F)
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (b : Bool)
    (I : RowIds X (toChainReal R F tupT hm hTop) b) {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE}
    {ty : Fin n → D.what₂.FT} (hR : RowSideReal X (toChainReal R F tupT hm hTop) b I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (a : X.Amb μ) (y' : (R.HX (tupT μ)).H)
    (hu : (I.jX μ hμ ((X.multTop μ).symm a)).1 = R.cX.toMap R.prX ((R.HX (tupT μ)).e y')) :
    (I.jE (X.iota μ a)).1 = PiTensorProduct.lift (R.HE.e (R.Th (tupT μ) y')) := by
  obtain ⟨u, hu1⟩ : ∃ u : (toChainReal R F tupT hm hTop).CCX b μ, u.1 = (I.jX μ hμ ((X.multTop μ).symm a)).1 :=
    ⟨⟨_, hR.lvlX μ hμ (I.jX μ hμ ((X.multTop μ).symm a)).2⟩, rfl⟩
  have key := iota_eq_gen X (toChainReal R F tupT hm hTop) b I hR μ hμ (ioOK_of_chain R F tupT hm hTop hch b μ) hm
    (hLev_of R F tupT hm hTop hS b μ) (hLevX_of R F tupT hm hTop hT b μ) (goodProjectorSmallestSpaceForms R) (hE_of R F tupT hm hTop hP b μ)
    a u hu1.symm
  refine key.trans ?_
  rw [hch.Th (tupT μ) y', thDn_eq_dnFrom R F tupT hm hTop b μ u y' (hu1.trans hu)]
  rfl

end Spec4

end GlobalTheory.Mem.R3.DTheta

namespace GlobalTheory.Mem.R3.DTheta

section Spec5

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem iota_eq_real' (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (hch : R.IsChain) (hS : StepLev R F) (hT : TopLev R F) (hP : RowProj R F)
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (b : Bool)
    (I : RowIds X (toChainReal R F tupT hm hTop) b) {n : ℕ} {bs : OrthonormalBasis (Fin n) ℂ EE}
    {ty : Fin n → D.what₂.FT} (hR : RowSideReal X (toChainReal R F tupT hm hTop) b I bs ty)
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (a : X.Amb μ) (t : T) (ht : tupT μ = t) (y' : (R.HX t).H)
    (hu : (I.jX μ hμ ((X.multTop μ).symm a)).1 = R.cX.toMap R.prX ((R.HX t).e y')) :
    (I.jE (X.iota μ a)).1 = PiTensorProduct.lift (R.HE.e (R.Th t y')) := by
  subst ht
  exact iota_eq_real R F tupT hm hTop hch hS hT hP X b I hR μ hμ a y' hu

end Spec5

theorem downTo_sharp (D : D7) (μ : D.what₂.Tup) :
    ∀ (j : ℕ) (z : D.what₂.Mult μ j), D.what₂.downTo μ j z = (RowSide.sharp D).downTo μ j z
  | 0, _ => rfl
  | j + 1, z => downTo_sharp D μ j (D.what₂.io μ j z)

theorem iota_sharp (D : D7) (μ : D.what₂.Tup) (a : D.what₂.Amb μ) :
    D.what₂.iota μ a = (RowSide.sharp D).iota μ a := by
  show D.what₂.multZero μ (D.what₂.downTo μ D.R.m ((D.what₂.multTop μ).symm a)) =
    D.what₂.multZero μ ((RowSide.sharp D).downTo μ D.R.m ((D.what₂.multTop μ).symm a))
  rw [downTo_sharp]

end GlobalTheory.Mem.R3.DTheta
