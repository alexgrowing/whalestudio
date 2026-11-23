import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.CoreBC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.Move

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tensor

variable {R R' K K' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup K] [AddCommGroup K'] [AddCommGroup M] [AddCommGroup M']
  [Module R K] [Module R M] [Module R' K'] [Module R' M']

def tensMap (r : R →+* R') (κ : K →+ K') (φ : M →+ M') (hκ : ∀ c a, κ (c • a) = r c • κ a) (hφ : ∀ c x, φ (c • x) = r c • φ x) :
    K ⊗[R] M →+ K' ⊗[R'] M' :=
  TensorProduct.liftAddHom
    { toFun := fun a => (TensorProduct.mk R' K' M' (κ a)).toAddMonoidHom.comp φ
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [TensorProduct.add_tmul] }
    fun c a x => by
      change κ (c • a) ⊗ₜ[R'] φ x = κ a ⊗ₜ[R'] φ (c • x)
      rw [hκ, hφ, TensorProduct.smul_tmul]

theorem tensMap_tmul (r : R →+* R') (κ : K →+ K') (φ : M →+ M') (hκ hφ) (a : K) (x : M) :
    tensMap r κ φ hκ hφ (a ⊗ₜ x) = κ a ⊗ₜ φ x := rfl

theorem tens_ext {P : Type} [AddCommGroup P] {f g : K ⊗[R] M →+ P} (h : ∀ a x, f (a ⊗ₜ x) = g (a ⊗ₜ x)) : f = g :=
  AddMonoidHom.ext fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a x => exact h a x
    | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem symm_smul {r : R ≃+* R'} {φ : M ≃+ M'} (hφ : ∀ c x, φ (c • x) = r c • φ x) (c : R') (x : M') :
    φ.symm (c • x) = r.symm c • φ.symm x :=
  φ.injective (by rw [hφ, φ.apply_symm_apply, φ.apply_symm_apply, r.apply_symm_apply])

def tensEquiv (r : R ≃+* R') (κ : K ≃+ K') (φ : M ≃+ M') (hκ : ∀ c a, κ (c • a) = r c • κ a)
    (hφ : ∀ c x, φ (c • x) = r c • φ x) : K ⊗[R] M ≃+ K' ⊗[R'] M' :=
  AddMonoidHom.toAddEquiv (tensMap r.toRingHom κ.toAddMonoidHom φ.toAddMonoidHom hκ hφ)
    (tensMap r.symm.toRingHom κ.symm.toAddMonoidHom φ.symm.toAddMonoidHom (symm_smul hκ) (symm_smul hφ))
    (tens_ext fun a x => congrArg₂ (· ⊗ₜ[R] ·) (κ.symm_apply_apply a) (φ.symm_apply_apply x))
    (tens_ext fun a x => congrArg₂ (· ⊗ₜ[R'] ·) (κ.apply_symm_apply a) (φ.apply_symm_apply x))

theorem tensEquiv_tmul (r : R ≃+* R') (κ : K ≃+ K') (φ : M ≃+ M') (hκ hφ) (a : K) (x : M) :
    tensEquiv r κ φ hκ hφ (a ⊗ₜ x) = κ a ⊗ₜ φ x := rfl

theorem map_mem_of_span {f : M →+ M'} {r : R → R'} (hf : ∀ c x, f (c • x) = r c • f x) {s : Set M} {B : Submodule R' M'}
    (hs : ∀ x ∈ s, f x ∈ B) {x : M} (hx : x ∈ Submodule.span R s) : f x ∈ B := by
  induction hx using Submodule.span_induction with
  | mem x h => exact hs x h
  | zero => rw [map_zero]; exact B.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact B.add_mem hx hy
  | smul c x _ hx => rw [hf]; exact B.smul_mem _ hx

end Tensor

section Ks

variable {LL LL' LL'' Ks Ks' Ks'' WL WL' WL'' G G' G'' : Type} [Field LL] [Field LL'] [Field LL'']
  [Field Ks] [NumberField Ks] [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL']
  [Field Ks''] [NumberField Ks''] [Algebra Ks'' LL'']
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL' WL'] [Module Ks' WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  [AddCommGroup WL''] [Module LL'' WL''] [Module Ks'' WL''] [Module (𝓞 Ks'') WL''] [IsScalarTower (𝓞 Ks'') Ks'' WL'']
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {W' : (LL' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
  {W'' : (LL'' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W'' σ)] [∀ σ, InnerProductSpace ℂ (W'' σ)]
  [Group G] [Group G'] [Group G'']

structure KsIso (ι : LL →+* LL') (eK : Ks ≃+* Ks') (γ : G ≃* G') (A : Arith.FormsL LL Ks WL W G)
    (A' : Arith.FormsL LL' Ks' WL' W' G') where

  φ : A.WK ≃+ A'.WK

  alg : ∀ c, algebraMap Ks' LL' (eK c) = ι (algebraMap Ks LL c)

  smul : ∀ (c : Ks) (x : A.WK), φ (c • x) = eK c • φ x

  mk_iff : ∀ x : A.WK, (x : WL) ∈ A.MK ↔ (φ x : WL') ∈ A'.MK

  rho : ∀ g (x y : A.WK), A.ρ g x = y ↔ A'.ρ (γ g) (φ x) = φ y

  chi : ∀ g, (A'.chi (γ g) : LL') = ι (A.chi g : LL)

namespace KsIso

def refl (A : Arith.FormsL LL Ks WL W G) : KsIso (RingHom.id LL) (RingEquiv.refl Ks) (MulEquiv.refl G) A A where
  φ := AddEquiv.refl _
  alg _ := rfl
  smul _ _ := rfl
  mk_iff _ := Iff.rfl
  rho _ _ _ := Iff.rfl
  chi _ := rfl

variable {ι : LL →+* LL'} {eK : Ks ≃+* Ks'} {γ : G ≃* G'} {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL' Ks' WL' W' G'}

def trans {ι' : LL' →+* LL''} {eK' : Ks' ≃+* Ks''} {γ' : G' ≃* G''} {A'' : Arith.FormsL LL'' Ks'' WL'' W'' G''}
    (q : KsIso ι eK γ A A') (q' : KsIso ι' eK' γ' A' A'') : KsIso (ι'.comp ι) (eK.trans eK') (γ.trans γ') A A'' where
  φ := q.φ.trans q'.φ
  alg c := (q'.alg _).trans (congrArg ι' (q.alg c))
  smul c x := (congrArg q'.φ (q.smul c x)).trans (q'.smul _ _)
  mk_iff x := (q.mk_iff x).trans (q'.mk_iff _)
  rho g x y := (q.rho g x y).trans (q'.rho _ _ _)
  chi g := (q'.chi _).trans (congrArg ι' (q.chi g))

def copy (q : KsIso ι eK γ A A') {ι₁ : LL →+* LL'} {eK₁ : Ks ≃+* Ks'} {γ₁ : G ≃* G'} (hι : ∀ x, ι₁ x = ι x)
    (hK : ∀ x, eK₁ x = eK x) (hγ : ∀ x, γ₁ x = γ x) : KsIso ι₁ eK₁ γ₁ A A' where
  φ := q.φ
  alg c := by rw [hK, hι, q.alg]
  smul c x := by rw [hK, q.smul]
  mk_iff := q.mk_iff
  rho g x y := by rw [hγ, q.rho]
  chi g := by rw [hγ, hι, q.chi]

theorem stab_iff (q : KsIso ι eK γ A A') :
    (∀ g x, x ∈ A.WK → A.ρ g x ∈ A.WK) ↔ ∀ g x, x ∈ A'.WK → A'.ρ g x ∈ A'.WK := by
  refine ⟨fun h g x hx => ?_, fun h g x hx => ?_⟩
  · have := (q.rho (γ.symm g) (q.φ.symm ⟨x, hx⟩) ⟨_, h _ _ (q.φ.symm ⟨x, hx⟩).2⟩).1 rfl
    rw [γ.apply_symm_apply, q.φ.apply_symm_apply] at this
    exact this ▸ Subtype.property _
  · have := (q.rho g ⟨x, hx⟩ (q.φ.symm ⟨_, h (γ g) _ (q.φ ⟨x, hx⟩).2⟩)).2 (by rw [q.φ.apply_symm_apply])
    exact this ▸ Subtype.property _

end KsIso

end Ks

section OfIso

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL']
  [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']

def KsIso.ofFormsIso {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL Ks' WL' W' G'} (f : NX.FormsIso A A') :
    KsIso (RingHom.id LL) f.eK f.eG A A' where
  φ :=
    { toFun := fun x => ⟨f.e x, (f.wk _).1 x.2⟩
      invFun := fun y => ⟨f.e.symm y, (f.wk _).2 (by rw [f.e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (f.e.symm_apply_apply _)
      right_inv := fun y => Subtype.ext (f.e.apply_symm_apply _)
      map_add' := fun x y => Subtype.ext (map_add f.e x.1 y.1) }
  alg := f.eK_LL
  smul c x := Subtype.ext (by
    change f.e (c • (x : WL)) = f.eK c • f.e x
    rw [← algebraMap_smul LL c, map_smul, ← algebraMap_smul LL (f.eK c), f.eK_LL])
  mk_iff x := f.mkK x
  rho g x y := by
    change _ ↔ A'.ρ (f.eG g) (f.e x) = f.e y
    rw [← f.rho, f.e.injective.eq_iff]
  chi g := congrArg Units.val (f.chi g)

theorem KsIso.ofFormsIso_apply {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL Ks' WL' W' G'} (f : NX.FormsIso A A')
    (x : A.WK) : ((KsIso.ofFormsIso f).φ x : WL') = f.e x := rfl

end OfIso

section BC

variable {Ks L0 : Type} [Field L0] [NumberField L0] [Field Ks] [NumberField Ks] [Algebra Ks L0]
  (L : Type) [Field L] [NumberField L] [Algebra L0 L] [Algebra Ks L] [IsScalarTower Ks L0 L]
  {WL : Type} [AddCommGroup WL] [Module L0 WL] [Module Ks WL] [IsScalarTower Ks L0 WL] [Module (𝓞 Ks) WL]
  [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (L0 →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] {G : Type} [Group G]

def KsIso.bc (A : Arith.FormsL L0 Ks WL W G) :
    KsIso (algebraMap L0 L) (RingEquiv.refl Ks) (MulEquiv.refl G) A (NX.BC.bc L A) where
  φ := (NX.BC.wkE L A).toAddEquiv
  alg c := IsScalarTower.algebraMap_apply Ks L0 L c
  smul c x := (NX.BC.wkE L A).map_smul c x
  mk_iff x :=
    ⟨fun ⟨_, h⟩ => ⟨(NX.BC.wkE L A x).2, fun lp y => (NX.BC.bc_nrm_wkE L A lp y x).trans_le (h lp y)⟩,
      fun ⟨_, h⟩ => ⟨x.2, fun lp y => (NX.BC.bc_nrm_wkE L A lp y x).symm.trans_le (h lp y)⟩⟩
  rho g x y := by
    change _ ↔ (NX.BC.bc L A).ρ g (NX.BC.incl Ks L0 L WL x) = NX.BC.incl Ks L0 L WL y
    rw [NX.BC.bc_rho_incl, (NX.BC.incl_injective Ks L0 L WL).eq_iff]
  chi _ := rfl

theorem KsIso.bc_apply (A : Arith.FormsL L0 Ks WL W G) (x : A.WK) :
    ((KsIso.bc L A).φ x : NX.BC.BCW Ks L0 L WL) = NX.BC.incl Ks L0 L WL x := rfl

theorem KsIso.bc_j (A : Arith.FormsL L0 Ks WL W G) (σ : L →+* ℂ) (x : A.WK) :
    (NX.BC.bc L A).j σ ((KsIso.bc L A).φ x : NX.BC.BCW Ks L0 L WL) = A.j (σ.comp (algebraMap L0 L)) x :=
  NX.BC.bc_j_incl L A σ x

end BC

section Fm

variable {R R' : Ranks} {H : Host R} {H' : Host R'} {what₂ : Rows.Data R} {rows' : Rows.Data R'}
  [NumberField what₂.LL] [StarRing what₂.LL] [NumberField rows'.LL] [StarRing rows'.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {LL0' : IntermediateField ℚ rows'.LL} {N : NData R H what₂} {N' : NData R' H' rows'}
  {tw : NTw R H what₂ LL0 N} {tw' : NTw R' H' rows' LL0' N'}

abbrev fracEquiv {O O' : Type} [CommRing O] [CommRing O'] (κ : O ≃+* O') : FractionRing O ≃+* FractionRing O' :=
  IsFractionRing.ringEquivOfRingEquiv κ

structure Scal (ι : what₂.LL →+* rows'.LL) (e : ↥LL0' ≃+* ↥LL0) (i : tw.Tw) (i' : tw'.Tw) (b : Bool) (κ : tw.O i ≃+* tw'.O i') :
    Prop where

  above : ∀ x : ↥LL0', ι (e x : what₂.LL) = (x : rows'.LL)

  read : ∀ x : ↥LL0', fracEquiv κ (NX.BC.rdTw tw i b (e x)) = NX.BC.rdTw tw' i' b x

variable {S : NX.RatDat tw} {S' : NX.RatDat tw'} {ι : what₂.LL →+* rows'.LL} {e : ↥LL0' ≃+* ↥LL0} {i : tw.Tw} {i' : tw'.Tw}
  {b : Bool} {κ : tw.O i ≃+* tw'.O i'} {eK : S.Ks ≃+* S'.Ks} {γ : S.G ≃* S'.G} {j j' : ℕ}

theorem Scal.read' (s : Scal ι e i i' b κ) {x : ↥LL0} {x' : ↥LL0'} (h : (x' : rows'.LL) = ι (x : what₂.LL)) :
    fracEquiv κ (NX.BC.rdTw tw i b x) = NX.BC.rdTw tw' i' b x' := by
  rw [← s.read, show e x' = x from Subtype.ext (ι.injective ((s.above x').trans h))]

theorem Scal.place (s : Scal ι e i i' b κ) (q : KsIso ι eK γ (S.A j) (S'.A j')) (c : S.Ks) :
    fracEquiv κ (NX.ιK S i b c) = NX.ιK S' i' b (eK c) :=
  s.read' (x := S.kKs c) (x' := S'.kKs (eK c)) (by rw [S.kKs_spec, S'.kKs_spec, q.alg])

def fmOf (s : Scal ι e i i' b κ) (q : KsIso ι eK γ (S.A j) (S'.A j')) : NX.Fm S i j b ≃+ NX.Fm S' i' j' b :=
  tensEquiv (K := NX.KB S i b) (K' := NX.KB S' i' b) (M := NX.FmK S j) (M' := NX.FmK S' j') eK (fracEquiv κ).toAddEquiv q.φ
    (fun c a => (map_mul (fracEquiv κ) (NX.ιK S i b c) a).trans (congrArg (· * _) (s.place q c))) q.smul

variable (s : Scal ι e i i' b κ) (q : KsIso ι eK γ (S.A j) (S'.A j'))

theorem fmOf_tmul (a : NX.KB S i b) (x : NX.FmK S j) :
    fmOf s q (a ⊗ₜ[S.Ks] x : NX.KB S i b ⊗[S.Ks] NX.FmK S j) =
      ((show NX.KB S' i' b from fracEquiv κ a) ⊗ₜ[S'.Ks] (show NX.FmK S' j' from q.φ x) :
        NX.KB S' i' b ⊗[S'.Ks] NX.FmK S' j') := rfl

theorem fmOf_smul (c : FractionRing (tw.O i)) (x : NX.Fm S i j b) : fmOf s q (c • x) = fracEquiv κ c • fmOf s q x :=
  DFunLike.congr_fun (tens_ext (R := S.Ks) (K := NX.KB S i b) (M := NX.FmK S j)
    (f := (fmOf s q).toAddMonoidHom.comp (DistribSMul.toAddMonoidHom (NX.Fm S i j b) c))
    (g := (DistribSMul.toAddMonoidHom (NX.Fm S' i' j' b) (fracEquiv κ c)).comp (fmOf s q).toAddMonoidHom)
    fun a x => congrArg (fun z : NX.KB S' i' b => (z ⊗ₜ[S'.Ks] (show NX.FmK S' j' from q.φ x) :
      NX.KB S' i' b ⊗[S'.Ks] NX.FmK S' j')) (map_mul (fracEquiv κ) c a)) x

theorem fmOf_smulO (c : tw.O i) (x : NX.Fm S i j b) : fmOf s q (c • x) = κ c • fmOf s q x := by
  rw [← algebraMap_smul (FractionRing (tw.O i)) c, fmOf_smul, IsFractionRing.ringEquivOfRingEquiv_algebraMap, algebraMap_smul]

theorem fmOf_mem_Bsup (x : NX.Fm S i j b) : fmOf s q x ∈ NX.Bsup S' i' j' b ↔ x ∈ NX.Bsup S i j b := by
  have h1 : ∀ y : NX.FmK S j, fmOf s q ((1 : NX.KB S i b) ⊗ₜ[S.Ks] y : NX.KB S i b ⊗[S.Ks] NX.FmK S j) =
      ((1 : NX.KB S' i' b) ⊗ₜ[S'.Ks] (show NX.FmK S' j' from q.φ y) : NX.KB S' i' b ⊗[S'.Ks] NX.FmK S' j') := fun y =>
    congrArg (fun z : NX.KB S' i' b => (z ⊗ₜ[S'.Ks] (show NX.FmK S' j' from q.φ y) :
      NX.KB S' i' b ⊗[S'.Ks] NX.FmK S' j')) (map_one (fracEquiv κ))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← (fmOf s q).symm_apply_apply x]
    refine map_mem_of_span (f := (fmOf s q).symm.toAddMonoidHom) (symm_smul (fmOf_smulO s q)) ?_ h
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y, rfl⟩ := q.φ.surjective y
    refine Submodule.subset_span ⟨y, (q.mk_iff y).2 hy, ?_⟩
    exact (fmOf s q).symm_apply_eq.2 (h1 y).symm
  · refine map_mem_of_span (f := (fmOf s q).toAddMonoidHom) (fmOf_smulO s q) ?_ h
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨q.φ y, (q.mk_iff y).1 hy, h1 y⟩

include q in
theorem KsIso.rhoStab_iff : NX.RhoStab S j ↔ NX.RhoStab S' j' := q.stab_iff

include q in
theorem KsIso.chiInLL0 (he : ∀ x : ↥LL0', ι (e x : what₂.LL) = (x : rows'.LL)) (h : NX.ChiInLL0 S j) : NX.ChiInLL0 S' j' := fun g => by
  have h1 := q.chi (γ.symm g)
  rw [γ.apply_symm_apply] at h1
  have h2 := he (e.symm ⟨_, h (γ.symm g)⟩)
  rw [e.apply_symm_apply] at h2
  rw [h1, h2]
  exact Subtype.property _

theorem fmOf_baseChange (u : Module.End S.Ks (NX.FmK S j)) (u' : Module.End S'.Ks (NX.FmK S' j'))
    (hu : ∀ y : NX.FmK S j, q.φ (u y) = u' (q.φ y)) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S j) :
    fmOf s q (Module.End.baseChangeHom S.Ks (NX.KB S i b) (NX.FmK S j) u x) =
      Module.End.baseChangeHom S'.Ks (NX.KB S' i' b) (NX.FmK S' j') u' (fmOf s q x) :=
  DFunLike.congr_fun (tens_ext (R := S.Ks) (K := NX.KB S i b) (M := NX.FmK S j)
    (f := (fmOf s q).toAddMonoidHom.comp (Module.End.baseChangeHom S.Ks (NX.KB S i b) (NX.FmK S j) u).toAddMonoidHom)
    (g := (Module.End.baseChangeHom S'.Ks (NX.KB S' i' b) (NX.FmK S' j') u').toAddMonoidHom.comp (fmOf s q).toAddMonoidHom)
    fun a y => congrArg (fun z : NX.FmK S' j' => ((show NX.KB S' i' b from fracEquiv κ a) ⊗ₜ[S'.Ks] z :
      NX.KB S' i' b ⊗[S'.Ks] NX.FmK S' j')) (hu y)) x

theorem fmOf_actG (hst : NX.RhoStab S j) (hχ : NX.ChiInLL0 S j) (hst' : NX.RhoStab S' j') (hχ' : NX.ChiInLL0 S' j')
    (g : G0g N) (g' : G0g N') (hg : S'.eG.symm g' = γ (S.eG.symm g)) (x : NX.Fm S i j b) :
    fmOf s q (NX.actG S i j b hst hχ g x) = NX.actG S' i' j' b hst' hχ' g' (fmOf s q x) := by
  change fmOf s q ((show FractionRing (tw.O i) from (NX.readLL0 S i b (NX.chiL S j hχ (S.eG.symm g)))⁻¹) •
      (show NX.Fm S i j b from Module.End.baseChangeHom S.Ks (NX.KB S i b) (NX.FmK S j) (NX.rhoKG S j hst (S.eG.symm g)) x)) =
    (show FractionRing (tw'.O i') from (NX.readLL0 S' i' b (NX.chiL S' j' hχ' (S'.eG.symm g')))⁻¹) •
      (show NX.Fm S' i' j' b from
        Module.End.baseChangeHom S'.Ks (NX.KB S' i' b) (NX.FmK S' j') (NX.rhoKG S' j' hst' (S'.eG.symm g')) (fmOf s q x))
  rw [fmOf_smul, hg]
  refine congrArg₂ (· • ·) ?_ (fmOf_baseChange s q _ _ (fun y => Subtype.ext ((q.rho _ y _).1 rfl).symm) x)
  exact (map_inv₀ (fracEquiv κ) _).trans (congrArg _ (s.read' (q.chi _)))

theorem fmOf_restrict (u : Module.End what₂.LL (S.WL j)) (u' : Module.End rows'.LL (S'.WL j'))
    (hs : ∀ x ∈ (S.A j).WK, u x ∈ (S.A j).WK) (hs' : ∀ x ∈ (S'.A j').WK, u' x ∈ (S'.A j').WK)
    (hu : ∀ y : (S.A j).WK, (q.φ ⟨u y, hs _ y.2⟩ : S'.WL j') = u' (q.φ y)) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S j) :
    fmOf s q (Module.End.baseChangeHom S.Ks (NX.KB S i b) (NX.FmK S j)
        ((u.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hs) x) =
      Module.End.baseChangeHom S'.Ks (NX.KB S' i' b) (NX.FmK S' j')
        ((u'.restrictScalars S'.Ks).restrict (p := (S'.A j').WK) (q := (S'.A j').WK) hs') (fmOf s q x) :=
  fmOf_baseChange s q _ _ (fun y => Subtype.ext (hu y)) x

variable (tw' S ι e)

abbrev algKsBC : Algebra S.Ks rows'.LL := (ι.comp (algebraMap S.Ks what₂.LL)).toAlgebra

theorem towKsBC : letI := ι.toAlgebra
    letI := algKsBC S ι
    IsScalarTower S.Ks what₂.LL rows'.LL :=
  letI := ι.toAlgebra
  letI := algKsBC S ι
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def ratDatBC (he : ∀ x : ↥LL0', ι (e x : what₂.LL) = (x : rows'.LL)) (c : G0g N ≃* G0g N') :
    NX.RatDat tw' :=
  letI := ι.toAlgebra
  letI := algKsBC S ι
  haveI := towKsBC S ι
  { Ks := S.Ks
    WL := fun j => NX.BC.BCW S.Ks what₂.LL rows'.LL (S.WL j)
    modWL := fun j => NX.BC.modL S.Ks what₂.LL rows'.LL (S.WL j)
    modKsWL := fun j => NX.BC.modKs S.Ks what₂.LL rows'.LL (S.WL j)
    towWL := fun j => NX.BC.towKsL S.Ks what₂.LL rows'.LL (S.WL j)
    modOLLWL := fun _ => NX.BC.modOL rows'.LL
    towOLLWL := fun _ => NX.BC.towOL rows'.LL
    modOKsWL := fun _ => NX.BC.modOKs rows'.LL
    towOKsWL := fun _ => NX.BC.towOKs rows'.LL
    W := fun j => NX.BC.Wbc what₂.LL rows'.LL (S.W j)
    G := S.G
    eG := S.eG.trans c
    A := fun j => NX.BC.bc rows'.LL (S.A j)
    kKs := e.symm.toRingHom.comp S.kKs
    kKs_spec := fun x => by
      have h := he (e.symm (S.kKs x))
      rw [e.apply_symm_apply, S.kKs_spec] at h
      exact h.symm }

variable (he : ∀ x : ↥LL0', ι (e x : what₂.LL) = (x : rows'.LL)) (c : G0g N ≃* G0g N')

theorem ratDatBC_Ks : (ratDatBC tw' S ι e he c).Ks = S.Ks := rfl

theorem ratDatBC_G : (ratDatBC tw' S ι e he c).G = S.G := rfl

theorem ratDatBC_eG (g : S.G) : (ratDatBC tw' S ι e he c).eG g = c (S.eG g) := rfl

theorem ratDatBC_kKs (x : S.Ks) : (ratDatBC tw' S ι e he c).kKs x = e.symm (S.kKs x) := rfl

theorem ratDatBC_A (j : ℕ) : letI := ι.toAlgebra
    letI := algKsBC S ι
    haveI := towKsBC S ι
    (ratDatBC tw' S ι e he c).A j = NX.BC.bc rows'.LL (S.A j) := rfl

def kBC : S.Ks ≃+* (ratDatBC tw' S ι e he c).Ks := RingEquiv.refl S.Ks

def gBC : S.G ≃* (ratDatBC tw' S ι e he c).G := MulEquiv.refl S.G

def ksBC (j : ℕ) : KsIso ι (kBC tw' S ι e he c) (gBC tw' S ι e he c) (S.A j) ((ratDatBC tw' S ι e he c).A j) :=
  letI := ι.toAlgebra
  letI := algKsBC S ι
  haveI := towKsBC S ι
  KsIso.bc rows'.LL (S.A j)

theorem ratDatBC_rhoStab_iff (j : ℕ) : NX.RhoStab S j ↔ NX.RhoStab (ratDatBC tw' S ι e he c) j :=
  (ksBC tw' S ι e he c j).rhoStab_iff

theorem ratDatBC_chiInLL0 (j : ℕ) (h : NX.ChiInLL0 S j) : NX.ChiInLL0 (ratDatBC tw' S ι e he c) j :=
  (ksBC tw' S ι e he c j).chiInLL0 he h

theorem ksBC_j (j : ℕ) (σ : rows'.LL →+* ℂ) (x : (S.A j).WK) :
    ((ratDatBC tw' S ι e he c).A j).j σ ((ksBC tw' S ι e he c j).φ x : (ratDatBC tw' S ι e he c).WL j) = (S.A j).j (σ.comp ι) x :=
  letI := ι.toAlgebra
  letI := algKsBC S ι
  haveI := towKsBC S ι
  KsIso.bc_j rows'.LL (S.A j) σ x

end Fm

section Cast

def ringCast {A B : Type} [iA : CommRing A] [iB : CommRing B] (h : A = B) (hi : HEq iA iB) : A ≃+* B where
  toEquiv := Equiv.cast h
  map_mul' x y := by subst h; cases hi; rfl
  map_add' x y := by subst h; cases hi; rfl

theorem ringCast_heq {A B : Type} [iA : CommRing A] [iB : CommRing B] (h : A = B) (hi : HEq iA iB) (x : A) :
    HEq (ringCast h hi x) x := cast_heq h x

theorem fracEquiv_ringCast_heq {A B : Type} [iA : CommRing A] [iB : CommRing B] (h : A = B) (hi : HEq iA iB)
    (x : FractionRing A) : HEq (fracEquiv (ringCast h hi) x) x := by
  subst h; cases hi
  exact heq_of_eq (DFunLike.congr_fun (IsFractionRing.ringEquivOfRingEquiv_refl (A := A) (K := FractionRing A)) x)

def mulCast {A B : Type} [iA : Mul A] [iB : Mul B] (h : A = B) (hi : HEq iA iB) : A ≃* B where
  toEquiv := Equiv.cast h
  map_mul' x y := by subst h; cases hi; rfl

def addCast {A B : Type} [iA : AddCommGroup A] [iB : AddCommGroup B] (h : A = B) (hi : HEq iA iB) : A ≃+ B where
  toEquiv := Equiv.cast h
  map_add' x y := by subst h; cases hi; rfl

theorem heq_ring {T T' : Type} {O : T → Type} {O' : T' → Type} {c : ∀ i, CommRing (O i)} {c' : ∀ i, CommRing (O' i)}
    (hT : T = T') (hO : HEq O O') (hc : HEq c c') {i : T} {i' : T'} (hi : HEq i i') : O i = O' i' ∧ HEq (c i) (c' i') := by
  subst hT; cases hO; cases hc; cases hi
  exact ⟨rfl, HEq.rfl⟩

theorem heq_fracMap {T T' : Type} {A O : T → Type} {A' O' : T' → Type} [a : ∀ i, CommRing (A i)] [a' : ∀ i, CommRing (A' i)]
    [c : ∀ i, CommRing (O i)] [c' : ∀ i, CommRing (O' i)] [∀ i, IsDomain (A i)] [∀ i, IsDomain (A' i)]
    [∀ i, IsDomain (O i)] [∀ i, IsDomain (O' i)] [g : ∀ i, Algebra (A i) (O i)] [g' : ∀ i, Algebra (A' i) (O' i)]
    (hT : T = T') (hA : HEq A A') (ha : HEq a a') (hO : HEq O O') (hc : HEq c c') (hg : HEq g g') {i : T} {i' : T'} (hi : HEq i i')
    (n : Function.Injective (algebraMap (A i) (O i))) (n' : Function.Injective (algebraMap (A' i') (O' i')))
    {x : FractionRing (A i)} {x' : FractionRing (A' i')} (hx : HEq x x') :
    HEq (IsFractionRing.map (K := FractionRing (A i)) (L := FractionRing (O i)) n x)
      (IsFractionRing.map (K := FractionRing (A' i')) (L := FractionRing (O' i')) n' x') := by
  subst hT; cases hA; cases ha; cases hO; cases hc; cases hg; cases hi; cases hx
  rfl

theorem heq_fam {T T' : Type} {K : T → Type} {K' : T' → Type} {k : ∀ i, CommRing (K i)} {k' : ∀ i, CommRing (K' i)}
    {M : T → ℕ → Bool → Type} {M' : T' → ℕ → Bool → Type} {a : ∀ i j b, AddCommGroup (M i j b)}
    {a' : ∀ i j b, AddCommGroup (M' i j b)} {m : ∀ i j b, Module (FractionRing (K i)) (M i j b)}
    {m' : ∀ i j b, Module (FractionRing (K' i)) (M' i j b)}
    (hT : T = T') (hK : HEq K K') (hk : HEq k k') (hM : HEq M M') (ha : HEq a a') (hm : HEq m m') {i : T} {i' : T'} (hi : HEq i i')
    (j : ℕ) (b : Bool) : M i j b = M' i' j b ∧ HEq (a i j b) (a' i' j b) ∧
      ∀ (c : FractionRing (K i)) (c' : FractionRing (K' i')) (x : M i j b) (x' : M' i' j b), HEq c c' → HEq x x' →
        HEq (c • x) (c' • x') := by
  subst hT; cases hK; cases hk; cases hM; cases ha; cases hm; cases hi
  exact ⟨rfl, HEq.rfl, fun _ _ _ _ h h' => by cases h; cases h'; rfl⟩

theorem heq_grp {R R' : Ranks} {H : Host R} {H' : Host R'} {P P' : Fin 2 → Type} (hR : R = R') (hH : HEq H H') (hP : P = P') :
    (∀ kv : (Σ k : Fin 2, P k), GL (Fin R.r) (ZMod (H.g kv.1))) = (∀ kv : (Σ k : Fin 2, P' k), GL (Fin R'.r) (ZMod (H'.g kv.1))) ∧
    HEq (inferInstance : Mul (∀ kv : (Σ k : Fin 2, P k), GL (Fin R.r) (ZMod (H.g kv.1))))
      (inferInstance : Mul (∀ kv : (Σ k : Fin 2, P' k), GL (Fin R'.r) (ZMod (H'.g kv.1)))) := by
  subst hR; cases hH; subst hP
  exact ⟨rfl, HEq.rfl⟩

end Cast

structure CopyTw (D D' : D7) (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop
    extends GlobalTheory.TwistChoice.SameExport D D' where

  sp : HEq D.sp D'.sp

  Tau : D.what₂.Tau = D'.what₂.Tau

  eTau : HEq D.eTau D'.eTau

  hc : HEq D.hc D'.hc

  embLL : ∀ x, D'.what₂.embLL (ι x) = D.what₂.embLL x

  LL0 : ∀ x : ↥D'.LL0, ι (e x : D.what₂.LL) = (x : D'.what₂.LL)

  emb0 : ∀ i i', HEq i i' → ∀ x, HEq (D.ntw.emb0 i (e x)) (D'.ntw.emb0 i' x)

  emb0b : ∀ i i', HEq i i' → ∀ x, HEq (D.ntw.emb0b i (e x)) (D'.ntw.emb0b i' x)

  inW1 : ∀ i i', HEq i i' → (D.ntw.NonzeroIndexPlace i ↔ D'.ntw.NonzeroIndexPlace i')

  delta : HEq D.ntw.delta D'.ntw.delta

  B : HEq D.ntw.B D'.ntw.B
  acgB : HEq D.ntw.acgB D'.ntw.acgB
  modB : HEq D.ntw.modB D'.ntw.modB

  Theta : HEq D.ntw.Theta D'.ntw.Theta

  hk : HEq D.ntw.hk D'.ntw.hk

  Bsup : HEq D.nexp.Bsup D'.nexp.Bsup

  embB : HEq D.nexp.embB D'.nexp.embB

  thU : HEq D.nexp.thU D'.nexp.thU

  delU : HEq D.nexp.delU D'.nexp.delU

namespace CopyTw

theorem refl (D : D7) : CopyTw D D (RingHom.id _) (RingEquiv.refl _) where
  toSameExport := .refl D
  sp := HEq.rfl
  Tau := rfl
  eTau := HEq.rfl
  hc := HEq.rfl
  embLL _ := rfl
  LL0 _ := rfl
  emb0 _ _ h _ := by cases h; rfl
  emb0b _ _ h _ := by cases h; rfl
  inW1 _ _ h := by cases h; rfl
  delta := HEq.rfl
  B := HEq.rfl
  acgB := HEq.rfl
  modB := HEq.rfl
  Theta := HEq.rfl
  hk := HEq.rfl
  Bsup := HEq.rfl
  embB := HEq.rfl
  thU := HEq.rfl
  delU := HEq.rfl

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
include h

theorem Tw_eq : D.ntw.Tw = D'.ntw.Tw := eq_of_heq h.set.Tw

theorem instTau : HEq D.what₂.instTau D'.what₂.instTau := Subsingleton.helim (congrArg Fintype h.Tau) _ _

theorem freeB_finB : HEq D.ntw.freeB D'.ntw.freeB ∧ HEq D.ntw.finB D'.ntw.finB := ⟨proof_irrel_heq _ _, proof_irrel_heq _ _⟩

theorem embLL_comp : D'.what₂.embLL.comp ι = D.what₂.embLL := RingHom.ext h.embLL

theorem embLL0_eq (x : ↥D'.LL0) : embLL0 D (e x) = embLL0 D' x := (h.embLL _).symm.trans (congrArg D'.what₂.embLL (h.LL0 x))

theorem map_star (x : D.what₂.LL) : ι (star x) = star (ι x) :=
  D'.what₂.embLL.injective (by rw [h.embLL, D.starLL_cx, D'.starLL_cx, h.embLL])

theorem map_embE {x : D.host.E} {x' : D'.host.E} (hx : HEq x x') : ι (D.embE x) = D'.embE x' := by
  have key : ∀ {R R' : Ranks} {H : Host R} {H' : Host R'}, R = R' → HEq H H' → ∀ {y : H.E} {y' : H'.E}, HEq y y' →
      H.φ₀ y = H'.φ₀ y' := by
    intro R R' H H' h1 h2 y y' h3
    subst h1; cases h2; cases h3
    rfl
  refine D'.what₂.embLL.injective ((h.embLL _).trans ?_)
  exact (DFunLike.congr_fun D.embE_φ₀ x).trans ((key h.gal.R h.gal.host hx).trans (DFunLike.congr_fun D'.embE_φ₀ x').symm)

def grpEquiv : G0g D.nd ≃* G0g D'.nd :=
  mulCast (heq_grp h.gal.R h.gal.host (eq_of_heq h.gal.PlG)).1 (heq_grp h.gal.R h.gal.host (eq_of_heq h.gal.PlG)).2

theorem grpEquiv_heq (g : G0g D.nd) : HEq (h.grpEquiv g) g := cast_heq _ g

theorem grpEquiv_eq_iff {g : G0g D.nd} {g' : G0g D'.nd} : h.grpEquiv g = g' ↔ HEq g g' := cast_eq_iff_heq

variable {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i')

def oEquiv : D.ntw.O i ≃+* D'.ntw.O i' :=
  ringCast (heq_ring h.Tw_eq h.set.O h.set.crO hi).1 (heq_ring h.Tw_eq h.set.O h.set.crO hi).2

theorem oEquiv_heq (x : D.ntw.O i) : HEq (h.oEquiv hi x) x := ringCast_heq _ _ x

theorem frac_heq (x : FractionRing (D.ntw.O i)) : HEq (fracEquiv (h.oEquiv hi) x) x := fracEquiv_ringCast_heq _ _ x

include hi in

theorem sideEmb_heq (b : Bool) (x : ↥D'.LL0) : HEq (sideEmb D.ntw i b (e x)) (sideEmb D'.ntw i' b x) :=
  heq_fracMap h.Tw_eq h.set.O0 h.set.crO0 h.set.O h.set.crO h.set.algO hi (D.ntw.O_inj i) (D'.ntw.O_inj i')
    (by cases b; exacts [h.emb0b i i' hi x, h.emb0 i i' hi x])

theorem scal (b : Bool) : Scal ι e i i' b (h.oEquiv hi) :=
  ⟨h.LL0, fun x => eq_of_heq ((h.frac_heq hi _).trans (h.sideEmb_heq hi b x))⟩

def fmCast (j : ℕ) (b : Bool) : D.nexp.Fm i j b ≃+ D'.nexp.Fm i' j b :=
  addCast (heq_fam h.Tw_eq h.set.O h.set.crO h.frm.Fm h.frm.acgFm h.frm.modFmK hi j b).1
    (heq_fam h.Tw_eq h.set.O h.set.crO h.frm.Fm h.frm.acgFm h.frm.modFmK hi j b).2.1

theorem fmCast_heq (j : ℕ) (b : Bool) (x : D.nexp.Fm i j b) : HEq (h.fmCast hi j b x) x := cast_heq _ x

theorem fmCast_smul (j : ℕ) (b : Bool) (c : FractionRing (D.ntw.O i)) (x : D.nexp.Fm i j b) :
    h.fmCast hi j b (c • x) = fracEquiv (h.oEquiv hi) c • h.fmCast hi j b x :=
  eq_of_heq ((h.fmCast_heq hi j b _).trans ((heq_fam h.Tw_eq h.set.O h.set.crO h.frm.Fm h.frm.acgFm h.frm.modFmK hi j b).2.2
    _ _ _ _ (h.frac_heq hi c).symm (h.fmCast_heq hi j b x).symm))

def eFMove {S : NX.RatDat D.ntw} {S' : NX.RatDat D'.ntw} {eK : S.Ks ≃+* S'.Ks} {γ : S.G ≃* S'.G} {j : ℕ} {b : Bool}
    (q : KsIso ι eK γ (S.A j) (S'.A j)) (eF : D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] NX.Fm S i j b) :
    D'.nexp.Fm i' j b ≃ₗ[FractionRing (D'.ntw.O i')] NX.Fm S' i' j b :=
  { (h.fmCast hi j b).symm.trans (eF.toAddEquiv.trans (fmOf (h.scal hi b) q)) with
    map_smul' := fun c x => by
      change fmOf (h.scal hi b) q (eF ((h.fmCast hi j b).symm (c • x))) =
        c • fmOf (h.scal hi b) q (eF ((h.fmCast hi j b).symm x))
      rw [symm_smul (h.fmCast_smul hi j b), map_smul, fmOf_smul, RingEquiv.apply_symm_apply] }

theorem eFMove_fmCast {S : NX.RatDat D.ntw} {S' : NX.RatDat D'.ntw} {eK : S.Ks ≃+* S'.Ks} {γ : S.G ≃* S'.G} {j : ℕ} {b : Bool}
    (q : KsIso ι eK γ (S.A j) (S'.A j)) (eF : D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] NX.Fm S i j b)
    (x : D.nexp.Fm i j b) : h.eFMove hi q eF (h.fmCast hi j b x) = fmOf (h.scal hi b) q (eF x) :=
  congrArg (fun y => fmOf (h.scal hi b) q (eF y)) ((h.fmCast hi j b).symm_apply_apply x)

abbrev ratDat (S : NX.RatDat D.ntw) : NX.RatDat D'.ntw := ratDatBC D'.ntw S ι e h.LL0 h.grpEquiv

end CopyTw

section Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) (S : NX.RatDat D.ntw)
  {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (j : ℕ) (b : Bool)

def fmMove : NX.Fm S i j b ≃+ NX.Fm (h.ratDat S) i' j b :=
  fmOf (h.scal hi b) (ksBC D'.ntw S ι e h.LL0 h.grpEquiv j)

theorem fmMove_smul (c : FractionRing (D.ntw.O i)) (x : NX.Fm S i j b) :
    fmMove h S hi j b (c • x) = fracEquiv (h.oEquiv hi) c • fmMove h S hi j b x := fmOf_smul _ _ c x

theorem fmMove_mem_Bsup (x : NX.Fm S i j b) : fmMove h S hi j b x ∈ NX.Bsup (h.ratDat S) i' j b ↔ x ∈ NX.Bsup S i j b :=
  fmOf_mem_Bsup _ _ x

theorem fmMove_actG (hst : NX.RhoStab S j) (hχ : NX.ChiInLL0 S j) (hst' hχ') (g : G0g D.nd) (x : NX.Fm S i j b) :
    fmMove h S hi j b (NX.actG S i j b hst hχ g x) =
      NX.actG (h.ratDat S) i' j b hst' hχ' (h.grpEquiv g) (fmMove h S hi j b x) :=
  fmOf_actG _ _ hst hχ hst' hχ' g _ (congrArg S.eG.symm (h.grpEquiv.symm_apply_apply g)) x

end Move

section Models

variable {D D' : D7} {V : HSp D} {V' : HSp D'} {P : D.what₂.Tau → SPar} {P' : D'.what₂.Tau → SPar}

structure SameModel (M : Mult.DSModel V P) (M' : Mult.DSModel V' P') : Prop where
  H : HEq M.H M'.H
  nacg : HEq M.nacg M'.nacg
  ips : HEq M.ips M'.ips
  σ : HEq M.σ M'.σ
  lam : HEq M.lam M'.lam
  ε : HEq M.ε M'.ε
  fr : HEq M.fr M'.fr

theorem SameModel.refl (M : Mult.DSModel V P) : SameModel M M := ⟨.rfl, .rfl, .rfl, .rfl, .rfl, .rfl, .rfl⟩

def SameVec {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (v : M.Vec) (v' : M'.Vec) : Prop :=
  ∀ τ τ', HEq τ τ' → HEq (v τ : M.H τ) (v' τ' : M'.H τ')

theorem SameVec.refl {M : Mult.DSModel V P} (v : M.Vec) : SameVec v v := fun _ _ h => by cases h; rfl

theorem SameVec.eq {M : Mult.DSModel V P} {v v' : M.Vec} (h : SameVec v v') : v = v' :=
  funext fun τ => Subtype.ext (eq_of_heq (h τ τ HEq.rfl))

def SameMap {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (T : Mult.MMap M) (T' : Mult.MMap M') : Prop :=
  ∀ v v', SameVec v v' → ∀ g g', HEq g g' → T v g = T' v' g'

theorem SameMap.refl {M : Mult.DSModel V P} (T : Mult.MMap M) : SameMap T T := fun _ _ h _ _ h' => by
  cases h'; rw [h.eq]

theorem SameMap.eq {M : Mult.DSModel V P} {T T' : Mult.MMap M} (h : SameMap T T') : T = T' :=
  MultilinearMap.ext fun v => funext fun g => h v v (.refl v) g g HEq.rfl

end Models

variable {D D' : D7}

abbrev model (X : RealSide D) (j : Fin D.R.m) := X.R.MW j (sg0 D X.A3.A)

def evidence (X : RealSide D) (j : Fin D.R.m) (x : Fin (X.R.nW j) → D.what₂.LL) : Mult.MMap (model X j) :=
  (X.R.HW j (sg0 D X.A3.A)).e ((X.R.FW j).j (sg0 D X.A3.A) x)

def IsCoef (X : RealSide D)
    (c0L : ∀ j : Fin D.R.m, VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (X.R.cV j).W) : Prop :=
  ∃ gramR c0R, Bridge.FamTie X.R.B X.R.pl (X.R.Sb : Set (Pl D.host.E)) X.R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L

theorem exists_isCoef (X : RealSide D) : ∃ c0L, IsCoef X c0L :=
  let ⟨g, c, c0L, h⟩ := X.char.fam.tie
  ⟨c0L, g, c, h⟩

theorem sign_at_base_place_eq_embedding (X : RealSide D) : sg0 D X.A3.A = D.what₂.embLL := sgAt_mk _ X.R.hv0

structure RealMove (X : RealSide D) (X' : RealSide D') (ι : D.what₂.LL →+* D'.what₂.LL) : Type where

  eK : X.core.Q.c.F ≃+* X'.core.Q.c.F

  γ : X.Γ ≃* X'.Γ

  forms : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → KsIso ι eK γ (X.R.FW j) (X'.R.FW j')

  Pg : HEq X.R.Pg X'.R.Pg

  eG : ∀ g, HEq (X.R.eG g) (X'.R.eG (γ g))

  cG : HEq X.cG X'.cG

  P0 : ∀ g, g ∈ X.F.P0 ↔ γ g ∈ X'.F.P0

  ψ0 : ∀ (g : X.F.P0) (g' : X'.F.P0), γ g = g' → (X'.F.ψ0 g' : D'.what₂.LL) = ι (X.F.ψ0 g : D.what₂.LL)

  ψ : HEq X.R.ψ X'.R.ψ

  θ : HEq X.R.θ X'.R.θ

  eta : HEq X.R.eta X'.R.eta

  mu0 : ∀ (j : Fin D.R.m), HEq (X.R.mu0 ((j : ℕ) + 1)) (X'.R.mu0 ((j : ℕ) + 1))

  Cmu0 : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.C.mu0 j) (X'.R.C.mu0 j')

  delAt : ∀ l, HEq (X.R.C.delAt l) (X'.R.C.delAt l)

  Q : ∀ i' t' P', P' ∈ X'.R.Q t' → P' ∈ D'.ntw.pD i' → ∃ t, ∃ P ∈ X.R.Q t, HEq P P'

  ΛV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.ΛV j) (X'.R.ΛV j')
  ΛW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.ΛW j) (X'.R.ΛW j')
  βV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.βV j) (X'.R.βV j')
  βW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.βW j) (X'.R.βW j')

  BV : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.BV j) (X'.R.BV j')

  vacP : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → HEq (X.R.vacP j) (X'.R.vacP j')

  MW : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → SameModel (model X j) (model X' j')

  v₀ : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    SameVec (X.geo.v₀ j (sg0 D X.A3.A)) (X'.geo.v₀ j' (sg0 D' X'.A3.A))

  read : ∀ (j : Fin D.R.m) (j' : Fin D'.R.m) (h : (j : ℕ) = j') (x : (X.R.FW j).WK),
    SameMap (evidence X j x) (evidence X' j' ((forms j j' h).φ x))

  io : ∃ c0L c0L', IsCoef X c0L ∧ IsCoef X' c0L' ∧ ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    ∀ (u : ∀ τ, lowT (model X j) τ) (u' : ∀ τ, lowT (model X' j') τ), SameVec (M := model X j) (M' := model X' j') (fun τ => u τ) (fun τ => u' τ) →
    ∀ (F : VV D.what₂.LL (FWT.lamV D j)) (F' : VV D'.what₂.LL (FWT.lamV D' j')),
      HEq (MvPolynomial.map ι (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank))
        (F' : Formalism.L2.DIV.Pol D'.what₂.LL D'.what₂.Tau (Vc D' j').rank) →
      HEq (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) (X'.R.ioP j' (PiTensorProduct.tprod ℂ u') (c0L' j' F'))

def TupExt (X : RealSide D) (X' : RealSide D') : Prop :=
  ∀ t : X.T, ∃ t' : X'.T, HEq (X.R.xi t) (X'.R.xi t') ∧ HEq (X.R.Q t) (X'.R.Q t')

theorem TupExt.refl (X : RealSide D) : TupExt X X := fun t => ⟨t, HEq.rfl, HEq.rfl⟩

namespace RealMove

def refl (X : RealSide D) : RealMove X X (RingHom.id _) where
  eK := RingEquiv.refl _
  γ := MulEquiv.refl _
  forms j j' h := Fin.ext h ▸ KsIso.refl (X.R.FW j)
  Pg := HEq.rfl
  eG _ := HEq.rfl
  cG := HEq.rfl
  P0 _ := Iff.rfl
  ψ0 g g' h := by cases Subtype.ext (a1 := g) (a2 := g') h; rfl
  ψ := HEq.rfl
  θ := HEq.rfl
  eta := HEq.rfl
  mu0 _ := HEq.rfl
  Cmu0 _ _ h := by cases Fin.ext h; rfl
  delAt _ := HEq.rfl
  Q _ t P h _ := ⟨t, P, h, HEq.rfl⟩
  ΛV _ _ h := by cases Fin.ext h; rfl
  ΛW _ _ h := by cases Fin.ext h; rfl
  βV _ _ h := by cases Fin.ext h; rfl
  βW _ _ h := by cases Fin.ext h; rfl
  BV _ _ h := by cases Fin.ext h; rfl
  vacP _ _ h := by cases Fin.ext h; rfl
  MW _ _ h := by cases Fin.ext h; exact .refl _
  v₀ _ _ h := by cases Fin.ext h; exact .refl _
  read _ _ h _ := by cases Fin.ext h; exact .refl _
  io := by
    obtain ⟨c, hc⟩ := exists_isCoef X
    refine ⟨c, c, hc, hc, fun j j' h u u' hu F F' hF => ?_⟩
    cases Fin.ext h
    obtain rfl : u = u' := funext fun τ => Subtype.ext (congrFun hu.eq τ)
    obtain rfl : F = F' := Subtype.ext ((MvPolynomial.map_id _).symm.trans (eq_of_heq hF))
    rfl

variable {X : RealSide D} {X' : RealSide D'} {ι : D.what₂.LL →+* D'.what₂.LL} (m : RealMove X X' ι)
include m

theorem Sb : HEq X.R.Sb X'.R.Sb :=
  (heq_of_eq (X.char.allPl : X.R.Sb = X.R.Pg)).trans (m.Pg.trans (heq_of_eq (X'.char.allPl : X'.R.Sb = X'.R.Pg)).symm)

theorem phs (j : Fin D.R.m) (j' : Fin D'.R.m) : X.R.phs j = X'.R.phs j' := (X.phs j).trans (X'.phs j').symm

variable {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
include h

omit m in

theorem fixedEmbedding_comp (X : RealSide D) (X' : RealSide D') : (sg0 D' X'.A3.A).comp ι = sg0 D X.A3.A := by
  rw [sign_at_base_place_eq_embedding, sign_at_base_place_eq_embedding, h.embLL_comp]

theorem cG_eG (g : X.Γ) : X'.cG (X'.R.eG (m.γ g)) = h.grpEquiv (X.cG (X.R.eG g)) := by
  have key : ∀ {R R' : Ranks} {H : Host R} {H' : Host R'} {P P' : Fin 2 → Type} {Q : Finset (Pl H.E)} {Q' : Finset (Pl H'.E)},
      R = R' → HEq H H' → P = P' → HEq Q Q' →
      ∀ {c : G0 Q R.r ≃* ∀ kv : (Σ k : Fin 2, P k), GL (Fin R.r) (ZMod (H.g kv.1))}
        {c' : G0 Q' R'.r ≃* ∀ kv : (Σ k : Fin 2, P' k), GL (Fin R'.r) (ZMod (H'.g kv.1))}, HEq c c' →
        ∀ {x x'}, HEq x x' → HEq (c x) (c' x') := by
    intro R R' H H' P P' Q Q' h1 h2 h3 h4 c c' h5 x x' h6
    subst h1; cases h2; subst h3; cases h4; cases h5; cases h6
    rfl
  exact (h.grpEquiv_eq_iff.2 (key h.gal.R h.gal.host (eq_of_heq h.gal.PlG) m.Pg m.cG (m.eG g))).symm

def ksOf {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (j : Fin D.R.m) :
    KsIso ι ((YS.fi j).eK.trans m.eK) ((YS.fi j).eG.trans m.γ) (S.A ((j : ℕ) + 1)) (X'.R.FW (NX.idxOf D' ((j : ℕ) + 1))) :=
  ((KsIso.ofFormsIso (YS.fi j)).trans (m.forms j (NX.idxOf D' ((j : ℕ) + 1)) (by
    have h1 := j.2
    have h2 : D.R.m = D'.R.m := by rw [h.gal.R]
    change (j : ℕ) = min ((j : ℕ) + 1 - 1) (D'.R.m - 1)
    omega))).copy (fun _ => rfl) (fun _ => rfl) fun _ => rfl

def eFOf {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (kKs' : X'.core.Q.c.F →+* ↥D'.LL0) (hk') {i : D.ntw.Tw}
    {i' : D'.ntw.Tw} (hi : HEq i i') (j : Fin D.R.m) (b : Bool) :
    D'.nexp.Fm i' ((j : ℕ) + 1) b ≃ₗ[FractionRing (D'.ntw.O i')] NX.Fm (NX.ratDatR X'.R X'.cG kKs' hk') i' ((j : ℕ) + 1) b :=
  h.eFMove hi (S' := NX.ratDatR X'.R X'.cG kKs' hk') (m.ksOf h YS j) (YS.eF i _ b (Nat.le_add_left _ _) j.2)

def kKsOf {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (j : Fin D.R.m) : X'.core.Q.c.F →+* ↥D'.LL0 :=
  e.symm.toRingHom.comp (S.kKs.comp ((YS.fi j).eK.trans m.eK).symm.toRingHom)

theorem kKsOf_spec {S : NX.RatDat D.ntw} (YS : NX.NExpRealS X.R X.cG S) (j : Fin D.R.m) (x : X'.core.Q.c.F) :
    ((m.kKsOf (e := e) YS j x : ↥D'.LL0) : D'.what₂.LL) = algebraMap X'.core.Q.c.F D'.what₂.LL x := by
  obtain ⟨c, rfl⟩ := ((YS.fi j).eK.trans m.eK).surjective x
  rw [(m.ksOf h YS j).alg c, ← S.kKs_spec, ← h.LL0]
  exact congrArg (fun y : ↥D.LL0 => ι y) ((e.apply_symm_apply _).trans (congrArg S.kKs (RingEquiv.symm_apply_apply _ c)))

end RealMove

example (σ : CyclotomicField 4 ℚ →+* ℂ) :
    (show ℂ from (NX.BC.bc (CyclotomicField 4 ℚ) NX.BC.testA).j σ
      ((KsIso.bc (CyclotomicField 4 ℚ) NX.BC.testA).φ ⟨1, trivial⟩ : NX.BC.BCW ℚ ℚ (CyclotomicField 4 ℚ) ℚ)) = 1 :=
  (KsIso.bc_j (CyclotomicField 4 ℚ) NX.BC.testA σ ⟨1, trivial⟩).trans (map_one (σ.comp (algebraMap ℚ _)))

example (D : D7) (g : G0g D.nd) (i : D.ntw.Tw) (x : D.ntw.O i) :
    (CopyTw.refl D).grpEquiv g = g ∧ (CopyTw.refl D).oEquiv (i' := i) HEq.rfl x = x := ⟨rfl, rfl⟩

example (D : D7) (ι : D.what₂.LL →+* D.what₂.LL) (e : ↥D.LL0 ≃+* ↥D.LL0) (h : CopyTw D D ι e) : ι = RingHom.id _ :=
  RingHom.ext fun x => D.what₂.embLL.injective (h.embLL x)

example (X : RealSide D) (j : Fin D.R.m) (x : (X.R.FW j).WK) : ((RealMove.refl X).forms j j rfl).φ x = x := rfl

end GlobalTheory.TwInputs.Move

end
