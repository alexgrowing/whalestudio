import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
import Formalism.LocalToGlobal.IndefiniteReal.LinksW

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen

open Formalism.IndefR.PeterssonHilbertSpace

variable {X : Type} [AddCommGroup X] [Module ℂ X]

theorem hermPos_mono {C C' : Submodule ℂ X} {ip : X → X → ℂ} (h : IsHermPos C ip) (hle : C' ≤ C) :
    IsHermPos C' ip where
  fd := by haveI := h.fd; exact Submodule.finiteDimensional_of_le hle
  add x x' y := h.add ⟨x, hle x.2⟩ ⟨x', hle x'.2⟩ ⟨y, hle y.2⟩
  smul s x y := h.smul s ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  herm x y := h.herm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  pos x hx := h.pos ⟨x, hle x.2⟩ (fun e => hx (Subtype.ext (show (x : X) = 0 from congrArg Subtype.val e)))

theorem hermPos_of_ipOn {C : Submodule ℂ X} {ip : X → X → ℂ} (h : Bridge.IPOnG C ip) : IsHermPos C ip :=
  ⟨h.fd, h.add, h.smul, h.herm, h.pos⟩

theorem hMod_of_herm {C : Submodule ℂ X} {ip : X → X → ℂ} (h : IsHermPos C ip) : ∃ M : HMod X, M.Is C ip := by
  have h00 : ip 0 0 = 0 := by simpa using h.add 0 0 0
  let core : InnerProductSpace.Core ℂ C :=
    { inner := fun x y => ip x y
      conj_inner_symm := fun x y => h.herm y x
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · subst hx
          simp [h00]
        · exact (h.pos x hx).le
      add_left := fun x x' y => h.add x x' y
      smul_left := fun x y s => h.smul s x y
      definite := fun x hx => by
        by_contra hne
        have hp := h.pos x hne
        simp only [show ip (x : X) x = 0 from hx, Complex.zero_re, lt_self_iff_false] at hp }
  let M : HMod X :=
    { H := C
      nH := core.toNormedAddCommGroup
      iH := InnerProductSpace.ofCore core.toCore
      fH := h.fd
      e := C.subtype }
  refine ⟨M, ?_, ?_, ?_⟩
  · exact fun a b hab => Subtype.ext hab
  · exact Submodule.range_subtype C
  · intro x y
    rfl

theorem hMod_lift {C : Submodule ℂ X} {ip : X → X → ℂ} {M : HMod X} (hM : M.Is C ip) {K Y : Type} [Field K]
    [AddCommGroup Y] [Module K Y] {σ : K →+* ℂ} (f : Y →ₛₗ[σ] X) (hf : ∀ y, f y ∈ C) :
    ∃ j : Y →ₛₗ[σ] M.H, ∀ y, M.e (j y) = f y := by
  obtain ⟨hinj, hrng, -⟩ := hM
  have hR : ∀ y, f y ∈ LinearMap.range M.e := fun y => by
    rw [hrng]
    exact hf y
  refine ⟨(LinearEquiv.ofInjective M.e hinj).symm.toLinearMap.comp (LinearMap.codRestrict _ f hR), fun y => ?_⟩
  have key : ∀ z : LinearMap.range M.e, M.e ((LinearEquiv.ofInjective M.e hinj).symm z) = z := fun z =>
    congrArg Subtype.val ((LinearEquiv.ofInjective M.e hinj).apply_symm_apply z)
  show M.e ((LinearEquiv.ofInjective M.e hinj).symm (LinearMap.codRestrict _ f hR y)) = f y
  exact (key _).trans rfl

theorem hMod_rep {C : Submodule ℂ X} {ip : X → X → ℂ} {M : HMod X} (hM : M.Is C ip) {G : Type} [Group G]
    (a : G → X →ₗ[ℂ] X) (hst : ∀ g, ∀ x ∈ C, a g x ∈ C) (h1 : ∀ x ∈ C, a 1 x = x)
    (hmul : ∀ g h, ∀ x ∈ C, a (g * h) x = a g (a h x)) :
    ∃ ρ : Representation ℂ G M.H, ∀ g x, M.e (ρ g x) = a g (M.e x) := by
  obtain ⟨hinj, hrng, -⟩ := hM
  have hC : ∀ x, M.e x ∈ C := fun x => by
    rw [← hrng]
    exact LinearMap.mem_range_self M.e x
  have hR : ∀ g x, (a g).comp M.e x ∈ LinearMap.range M.e := fun g x => by
    rw [hrng]
    exact hst g _ (hC x)
  let r : G → M.H →ₗ[ℂ] M.H := fun g =>
    (LinearEquiv.ofInjective M.e hinj).symm.toLinearMap.comp (LinearMap.codRestrict _ ((a g).comp M.e) (hR g))
  have key : ∀ z : LinearMap.range M.e, M.e ((LinearEquiv.ofInjective M.e hinj).symm z) = z := fun z =>
    congrArg Subtype.val ((LinearEquiv.ofInjective M.e hinj).apply_symm_apply z)
  have hr : ∀ g x, M.e (r g x) = a g (M.e x) := fun g x => by
    show M.e ((LinearEquiv.ofInjective M.e hinj).symm (LinearMap.codRestrict _ ((a g).comp M.e) (hR g) x)) = _
    exact (key _).trans rfl
  refine ⟨{ toFun := r, map_one' := ?_, map_mul' := ?_ }, hr⟩
  · ext x
    apply hinj
    rw [hr, h1 _ (hC x), Module.End.one_apply]
  · intro g k
    ext x
    apply hinj
    rw [hr, Module.End.mul_apply, hr, hr, hmul g k _ (hC x)]

end Gen

def IdemClass {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {D : D7} (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop :=
  ∀ a b : G, (idemOf A.X).coeff (a * b * a⁻¹) = (idemOf A.X).coeff b

section Main

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.PeterssonHilbertSpace Formalism.IndefR.Eqv

theorem measDef_exists (hLD : MeasLevDefExists D) (hFund : FundDomExists D) (V : HSp D)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hs : V.SigOK) (hd : V.IsDefinite) (hK : IsLevelA V K) :
    ∃ μ 𝓕, IsMeasDef V K μ 𝓕 := by
  obtain ⟨μ, hμ⟩ := hLD V hs hd K hK
  obtain ⟨𝓕, -, h𝓕⟩ := hFund V
  exact ⟨μ, 𝓕, hμ, h𝓕 μ⟩

theorem onb_exists (V : HSp D) (hs : V.SigOK) (hp : V.IsPosDef) (τ : D.what₂.Tau) :
    ∃ B, IsONBasis (gramAt D V τ) 1 B V.rank := by
  have h0 := hs (tauE D τ)
  rw [hp (tauE D τ)] at h0
  dsimp only at h0
  obtain ⟨e, P, hP⟩ := h0
  have hJ : Formalism.UG.Jpq V.rank 0 = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0
  rw [hJ] at hP
  have hc : (Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin V.rank ⊕ Fin 0) (Fin V.rank ⊕ Fin 0) ℂ)).submatrix e e =
      ((P : Matrix _ _ ℂ).submatrix e e)ᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hg : ((V.gram.map (tauE D τ)).reindex e e).submatrix e e = gramAt D V τ := by
    ext i j; simp [gramAt, Matrix.reindex_apply]
  refine ⟨(P : Matrix _ _ ℂ).submatrix e e, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩
  · have hd : (Matrix.diagonal fun _ : Fin V.rank => (((1 : ℝ)) : ℂ)) = 1 := by
      rw [Complex.ofReal_one]; exact Matrix.diagonal_one
    rw [hd, ← hc, ← hg, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hP]
    exact Matrix.submatrix_one_equiv e
  · simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem RealDat.preliminary_zero_of_model_update {R : RealDat D A Ks} {F : Face D A} (h : R.Pre0 F)
    (HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV) :
    (R.upd1 HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV).Pre0 F := by
  obtain ⟨lev, red_R, red_L, levels, record, ⟨tie, Sb, roots, pl_onto, degR, degL, muVal, etaVal⟩, inf, vpos, cX, cV,
    prX, order, std⟩ := h
  exact ⟨lev, red_R, red_L, levels, record, ⟨tie, Sb, roots, pl_onto, degR, degL, muVal, etaVal⟩, inf, vpos, cX, cV,
    prX, order, std⟩

set_option maxHeartbeats 1000000 in

theorem models_args (hFD : MeasFDExists D) (hLD : MeasLevDefExists D) (hFund : FundDomExists D) (hSp : SpOK D)
    (hLev : LevOK D) (hHC : HCAll D) (hSch : SchurAll D) (hPet : PetAll D) (hSm : SmAll D) (hDim : DimOK D)
    (hAct : ActRep D) (hX : IdemClass A) (Q : RealDat D A Ks → Prop)
    (hQ1 : ∀ R HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV, Q R →
      Q (R.upd1 HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV))
    (R : RealDat D A Ks) (F : Face D A) (h : R.Pre0 F) (hq : Q R)
    (hLift : LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) ∧ ∀ i, LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)) :
    ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ Q R' := by

  obtain ⟨ν0, fd0, hν0⟩ := hFD (Yc D 0) (D.sp.Y_sig _) _ (hLev _ (R.βY 0) (R.dat0 R.triv)).1
  choose νW fdW hνW using fun i : Fin D.R.m =>
    hFD (Wc D i) (D.sp.W_sig _) _ (hLev _ (R.βW i) (R.datWp i R.triv)).1
  choose νX fdX hνX using fun t : T =>
    measDef_exists hLD hFund D.sp.X' _ D.sp.X'_sig hSp.2 (hLev _ R.βX (R.datXt t)).1
  choose νV fdV hνV using fun (i : Fin D.R.m) (t : T) =>
    measDef_exists hLD hFund (Vc D i) _ (D.sp.V_sig _) (fun τ => Or.inl (h.vpos i τ)) (hLev _ (R.βV i) (R.datVt i t)).1
  have hY : ∀ (t : T) (j : ℕ), ∃ (μ : Measure (GA D (Yc D j))) (𝓕 : Set (GA D (Yc D j))),
      (j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) ∧
      (j = D.R.m - 1 → IsMeasDef (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) := by
    intro t j
    by_cases hj : j = D.R.m - 1
    · subst hj
      obtain ⟨μ, 𝓕, hμ⟩ := measDef_exists hLD hFund (Yc D (D.R.m - 1)) _ (D.sp.Y_sig _) hSp.1
        (hLev _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)).1
      exact ⟨μ, 𝓕, fun h2 => absurd h2 (by omega), fun _ => hμ⟩
    · obtain ⟨μ, 𝓕, hμ⟩ := hFD (Yc D j) (D.sp.Y_sig _) _ (hLev _ (R.βY j) (R.datYt t j R.triv)).1
      exact ⟨μ, 𝓕, fun _ => hμ, fun h' => absurd h' hj⟩
  choose νY fdY hνY using hY

  have hθ : IsInfFam R.θ := h.inf
  have herm : ∀ {V : HSp D} {S : D.what₂.Tau → SPar} (_ : V.SigOK) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D))
      (L : LevDat D.host.E ℂ V.rank) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
      IsMeasFD V (lev D.sp.cm V.gram β L) μ 𝓕 →
      IsHermPos (Mult R.θ M (levS V β L) (levChi V β L)) (ipM M μ 𝓕) := by
    intro V S hs M β L μ 𝓕 hμ
    exact isHermPos_mult M μ 𝓕 R.θ _ _ hθ (hHC V hs S R.θ M _ _) (hLev V β L).2 (hSch V hs S R.θ M _ _ μ 𝓕)
      hμ.1.1 hμ.2 (hPet V μ 𝓕 hμ.1.1 hμ.2) (hSm V S M)

  obtain ⟨HE, hHE⟩ := hMod_of_herm (hermPos_mono (herm (D.sp.Y_sig _) (R.MY 0) (R.βY 0) (R.dat0 R.triv) ν0 fd0 hν0)
    (goodPart_le R.θ (R.MY 0) _ _ R.e0))
  have hermW : ∀ i σ, IsHermPos (R.Wall i σ) (ipAt (R.MW i σ) (νW i) (fdW i)) := by
    intro i σ
    have e : ipAt (R.MW i σ) (νW i) (fdW i) = fun x y =>
        ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) * ipM (R.MW i σ) (νW i) (fdW i) x y := by
      funext x y; unfold ipAt; push_cast; rfl
    rw [e]
    exact isHermPos_scale (herm (D.sp.W_sig _) (R.MW i σ) (R.βW i) (R.datWp i R.triv) _ _ (hνW i))
      (Finset.prod_pos fun ρ _ => by exact_mod_cast hDim i σ ρ)
  choose HW hHW using fun i σ => hMod_of_herm (hermW i σ)

  have hermX : ∀ t, IsHermPos (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ) (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) := by
    intro t
    exact hermPos_of_ipOn (Bridge.adInner_ipOn (W := R.cX.W) (R.B.R t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.R t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  have hermV : ∀ i t, IsHermPos (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) := by
    intro i t
    exact hermPos_of_ipOn (Bridge.adInner_ipOn (W := (R.cV i).W) (R.B.L i t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.L i t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  choose HX hHX using fun t => hMod_of_herm (hermX t)
  choose HV hHV using fun i t => hMod_of_herm (hermV i t)
  choose jX hjX using fun t => hMod_lift (hHX t) (R.B.jR t) (fun x => by exact (R.B.R t).pres.extMem_holds x)
  choose jV hjV using fun i t => hMod_lift (hHV i t) (R.B.jL i t) (fun x => by exact (R.B.L i t).pres.extMem_holds x)

  have hActE := hAct (Yc D 0) (R.βY 0) (R.dat0 R.triv) _ R.θ (R.MY 0) hLift.1 (by unfold LevCh.dat0 datY; simp)
  obtain ⟨gE, hgE⟩ := hMod_rep hHE
    (fun g => postOn (R.MY 0) (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)))
    (by
      intro g x hx
      obtain ⟨hxM, hxK⟩ := Submodule.mem_inf.1 hx
      refine Submodule.mem_inf.2 ⟨hActE.1 _ x hxM, ?_⟩
      have hxK' : postOn (R.MY 0) R.e0 x = x := by
        have := LinearMap.mem_ker.1 hxK
        rwa [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      have hc := hActE.2.2.2 G R.eG (RealDat.eC (A := A) D.what₂.embLL)
        (fun a b => by simp only [RealDat.eC]; rw [hX a b]) (R.eG g) x hxM
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact hc.trans (congrArg (fun y => postOn (R.MY 0) (actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)) y) hxK'))
    (by
      intro x hx
      simp only [map_one]; exact hActE.2.1 x (Submodule.mem_inf.1 hx).1)
    (by
      intro g g' x hx
      simp only [map_mul]; exact hActE.2.2.1 _ _ x (Submodule.mem_inf.1 hx).1)
  have hActW := fun (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) =>
    hAct (Wc D i) (R.βW i) (R.datWp i R.triv) _ R.θ (R.MW i σ) (hLift.2 i) (by unfold LevCh.datWp datY; simp)
  choose gW hgW using fun (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) => hMod_rep (hHW i σ)
    (fun g => postOn (R.MW i σ) (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)))
    (fun g x hx => (hActW i σ).1 _ x hx)
    (by
      intro x hx
      simp only [map_one]; exact (hActW i σ).2.1 x hx)
    (by
      intro g g' x hx
      simp only [map_mul]; exact (hActW i σ).2.2.1 _ _ x hx)

  choose BV hBV using fun (i : Fin D.R.m) (τ : D.what₂.Tau) => onb_exists (Vc D i) (D.sp.V_sig _) (h.vpos i) τ
  exact ⟨R.upd1 HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV, ⟨RealDat.preliminary_zero_of_model_update h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, hHX, hHV, hHE, hHW, hgE, hgW, hjX, hjV,
      fun t j h2 => (hνY t j).1 h2, fun t => (hνY t _).2 rfl, hν0, hνX, hνV, hνW, hBV, h.order⟩⟩,
    hQ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq⟩

end Main

section Weak

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin Formalism.IndefR.Eqv

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face D A}

namespace RealDat

variable {R : RealDat D A Ks}

theorem weak_chain_of_theta_update (h : R.IsChainW) (ωP vacP vP ioP thF thG) : (R.upd4 ωP vacP vP ioP thF thG).IsChainW := by
  cases h
  constructor <;> assumption

theorem weak_chain_of_index_update (h : R.IsChainW) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).IsChainW := by
  cases h
  constructor <;> assumption

theorem weak_theta_props_of_index_update (h : R.IsThPW) (nW FW mu twPl err0) : (R.upd5 nW FW mu twPl err0).IsThPW := by
  cases h
  constructor <;> assumption

theorem weak_chain_of_scalar_update (h : R.IsChainW) (kap lam) : (R.upd6 kap lam).IsChainW := by
  cases h
  constructor <;> assumption

theorem weak_theta_props_of_scalar_update (h : R.IsThPW) (kap lam) : (R.upd6 kap lam).IsThPW := by
  cases h
  constructor <;> assumption

end RealDat

set_option maxHeartbeats 2000000 in

theorem chainW_exists (Q : RealDat D A Ks → Prop)
    (hQ3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, Q R → Q (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (R : RealDat D A Ks) (h : R.Pre1 F) (hK : R.KerY) (hq : Q R) :
    ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ R'.IsChainW ∧ R'.FullY ∧ Q R' := by
  choose ItY hY using fun k => orZero_exists (R.PItY k)
  obtain ⟨ItX, hX⟩ := orZero_exists R.PItX
  let R1 := R.upd3 R.ωY R.ωX R.vac R.vacX R.vY R.vX ItY ItX R.ioY R.ioX R.Th
  choose ioY hioY using fun t k => orZero_exists (R1.PIoY t k)
  choose ioX hioX using fun t => orZero_exists (R1.PIoX t)
  let R2 := R.upd3 R.ωY R.ωX R.vac R.vacX R.vY R.vX ItY ItX ioY ioX R.Th
  choose Th hTh using fun t => orZero_exists (R2.PTh t)
  exact ⟨R.upd3 R.ωY R.ωX R.vac R.vacX R.vY R.vX ItY ItX ioY ioX Th, RealDat.preliminary_of_vacuum_update h _ _ _ _ _ _ _ _ _ _ _,
    ⟨fun t k hk => (hK.1.1 t k hk).datum, fun t => (hK.1.2 t).datum, hK.2.1, hK.2.2.1, hK.2.2.2.1,
      hK.2.2.2.2, fun k _ => hY k, hX, fun t k _ => hioY t k, hioX, hTh⟩, hK.1, hQ3 _ _ _ _ _ _ _ _ _ _ _ _ hq⟩

set_option maxHeartbeats 2000000 in

theorem thPW_exists (Q : RealDat D A Ks → Prop) (hQ4 : ∀ R ωP vacP vP ioP thF thG, Q R → Q (R.upd4 ωP vacP vP ioP thF thG))
    (R : RealDat D A Ks) (h : R.Pre1 F) (hc : R.IsChainW) (hf : R.FullY) (hK : R.KerP) (hq : Q R) :
    ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ R'.IsChainW ∧ R'.IsThPW ∧ R'.FullY ∧ R'.FullP ∧ Q R' := by
  choose ioP hio using fun i => orZero_exists (R.PIoP i)
  let R1 := R.upd4 R.ωP R.vacP R.vP ioP R.thF R.thG
  choose thF hF using fun i t => orZero_exists (R1.PThF i t)
  let R2 := R.upd4 R.ωP R.vacP R.vP ioP thF R.thG
  choose thG hG using fun i t => orZero_exists (R2.PThG i t)
  exact ⟨R.upd4 R.ωP R.vacP R.vP ioP thF thG, RealDat.preliminary_of_frame_update h _ _ _ _ _ _, RealDat.weak_chain_of_theta_update hc _ _ _ _ _ _,
    ⟨fun i t => (hK.1 i t).datum, hK.2.1, hK.2.2, hio, hF, hG⟩, RealDat.full_Y_of_theta_update hf _ _ _ _ _ _, hK.1, hQ4 _ _ _ _ _ _ _ hq⟩

theorem kerYQ_exists (hI : Inputs D) (hF : SeedFacts D A Ks F) (Q : RealDat D A Ks → Prop)
    (hQ3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, Q R → Q (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (R : RealDat D A Ks) (h : R.Pre1 F) (hq : Q R) : ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ R'.KerY ∧ Q R' := by
  obtain ⟨ωY, ωX, vac, vacX, vY, vX, hk⟩ := kerY_args hI.weil hI.vac hI.stepVec hI.ptStable hI.cartan hI.selfDual hI.vecTheta hF R h
  exact ⟨_, RealDat.preliminary_of_vacuum_update h _ _ _ _ _ _ _ _ _ _ _, hk, hQ3 _ _ _ _ _ _ _ _ _ _ _ _ hq⟩

theorem kerPQ_exists (hI : Inputs D) (hF : SeedFacts D A Ks F) (Q : RealDat D A Ks → Prop)
    (hQ4 : ∀ R ωP vacP vP ioP thF thG, Q R → Q (R.upd4 ωP vacP vP ioP thF thG))
    (R : RealDat D A Ks) (h : R.Pre1 F) (hc : R.IsChainW) (hf : R.FullY) (hq : Q R) :
    ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ R'.IsChainW ∧ R'.FullY ∧ R'.KerP ∧ Q R' := by
  obtain ⟨ωP, vacP, vP, hk⟩ := exists_localWeil_vacuum_kernel hI.weil hI.vac hI.thPVec hI.ptStable hI.cartan hI.selfDual hI.vecTheta hF R h
  exact ⟨_, RealDat.preliminary_of_frame_update h _ _ _ _ _ _, RealDat.weak_chain_of_theta_update hc _ _ _ _ _ _, RealDat.full_Y_of_theta_update hf _ _ _ _ _ _, hk,
    hQ4 _ _ _ _ _ _ _ hq⟩

theorem analyticW_exists (hI : Inputs D) (hX : IdemClass A) (hL : LiftsAt D A Ks F) (hF : SeedFacts D A Ks F)
    (Q : RealDat D A Ks → Prop)
    (hQ1 : ∀ R HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV, Q R →
      Q (R.upd1 HX HV HE HW gE gW jX jV νY fdY ν0 fd0 νX fdX νV fdV νW fdW BV))
    (hQ3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, Q R → Q (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (hQ4 : ∀ R ωP vacP vP ioP thF thG, Q R → Q (R.upd4 ωP vacP vP ioP thF thG))
    (R : RealDat D A Ks) (h : R.Pre0 F) (hq : Q R) :
    ∃ R' : RealDat D A Ks, R'.Pre1 F ∧ R'.IsChainW ∧ R'.IsThPW ∧ R'.FullY ∧ R'.FullP ∧ Q R' := by
  obtain ⟨R1, p1, q1⟩ := models_args hI.measFD hI.measDef hI.fund hI.sp hI.lev hI.hc hI.schur hI.pet hI.sm hI.dim hI.act hX
    Q hQ1 R F h hq (hL R h)
  obtain ⟨R2, p2, k2, q2⟩ := kerYQ_exists hI hF Q hQ3 R1 p1 q1
  obtain ⟨R3, p3, c3, f3, q3⟩ := chainW_exists Q hQ3 R2 p2 k2 q2
  obtain ⟨R4, p4, c4, f4, k4, q4⟩ := kerPQ_exists hI hF Q hQ4 R3 p3 c3 f3 q3
  exact thPW_exists Q hQ4 R4 p4 c4 f4 k4 q4

end Weak

end Formalism.IndefR.Links

end
