import Formalism.AdmissibleDesigns.BlockTwistedCyclotomic
import Formalism.AdmissibleDesigns.SmulEval

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Map

variable {R G M M' : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (ρ : Representation R G M) (ρ' : Representation R G M') (φ : M →ₗ[R] M')
  (hφ : ∀ g m, φ (ρ g m) = ρ' g (φ m))

def continuousCocycleMap : coZ1s ρ →ₗ[R] coZ1s ρ' where
  toFun c := ⟨fun g => φ ((c : G → M) g), fun g h => by
    show φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρ' g (φ ((c : G → M) h))
    rw [c.2 g h, map_add, hφ]⟩
  map_add' a b := Subtype.ext <| funext fun g => map_add φ ((a : G → M) g) ((b : G → M) g)
  map_smul' r a := Subtype.ext <| funext fun g => map_smul φ r ((a : G → M) g)

def h1Map : H1z ρ →ₗ[R] H1z ρ' :=
  Submodule.mapQ _ _ (continuousCocycleMap ρ ρ' φ hφ) (by
    rintro x ⟨v, hv⟩
    refine ⟨φ v, funext fun g => ?_⟩
    have h : ρ g v - v = (x : G → M) g := congrFun hv g
    show ρ' g (φ v) - φ v = φ ((x : G → M) g)
    rw [← h]
    show ρ' g (φ v) - φ v = φ (ρ g v - v)
    rw [map_sub, hφ])

theorem h1Map_mk (c : coZ1s ρ) :
    h1Map ρ ρ' φ hφ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (continuousCocycleMap ρ ρ' φ hφ c) := rfl

theorem res_h1Map (Dg : Subgroup G) (x : H1z ρ) :
    resH1 ρ' Dg (h1Map ρ ρ' φ hφ x) =
      h1Map (resRep ρ Dg) (resRep ρ' Dg) φ (fun g m => hφ g m) (resH1 ρ Dg x) := by
  induction x using Submodule.Quotient.induction_on with
  | H c => rfl

theorem h1Map_mem_unrH1 {Dg : Subgroup G} {x : H1z ρ} (hx : x ∈ unrH1 ρ Dg) : h1Map ρ ρ' φ hφ x ∈ unrH1 ρ' Dg := by
  unfold unrH1 at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  rw [res_h1Map ρ ρ' φ hφ Dg x, hx, map_zero]

theorem h1Map_mem_lcH1 [TopologicalSpace G] {x : H1z ρ} (hx : x ∈ lcH1 ρ) : h1Map ρ ρ' φ hφ x ∈ lcH1 ρ' := by
  unfold lcH1 at hx ⊢
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨continuousCocycleMap ρ ρ' φ hφ c, ?_, ?_⟩
  · show IsLocallyConstant (φ ∘ (c : G → M))
    exact hc.comp φ
  · first
      | exact (h1Map_mk ρ ρ' φ hφ c).symm
      | rfl

theorem resH1_h1Map_mem_Fsha (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) {x : H1z ρ}
    (hx : resH1 ρ (D w) x ∈ Fsha ρ D Iq qs w) : resH1 ρ' (D w) (h1Map ρ ρ' φ hφ x) ∈ Fsha ρ' D Iq qs w := by
  unfold Fsha at hx ⊢
  rw [res_h1Map ρ ρ' φ hφ (D w) x]
  split_ifs at hx ⊢ with hw
  · exact h1Map_mem_unrH1 (resRep ρ (D w)) (resRep ρ' (D w)) φ (fun g m => hφ g m) hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem h1Map_mem_selRep2 [TopologicalSpace G] {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) {x : H1z ρ}
    (hx : x ∈ selRep2 ρ J JS D (Fsha ρ D Iq qs) P) :
    h1Map ρ ρ' φ hφ x ∈ selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P := by
  unfold selRep2 at hx ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  exact ⟨⟨⟨h1Map_mem_lcH1 ρ ρ' φ hφ h1, fun v => h1Map_mem_unrH1 ρ ρ' φ hφ (h2 v)⟩,
    fun v => h1Map_mem_unrH1 ρ ρ' φ hφ (h3 v)⟩, fun w hw => resH1_h1Map_mem_Fsha ρ ρ' φ hφ D Iq qs w (h4 w hw)⟩

end Map

section Iso

variable {R G M M' : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

theorem len_selRep2_le_of_iso (ρ : Representation R G M) (ρ' : Representation R G M') (h : RepIso ρ ρ')
    {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) :
    Module.length R ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P) ≤
      Module.length R ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P) := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g m, (e.symm : M' →ₗ[R] M) (ρ' g m) = ρ g ((e.symm : M' →ₗ[R] M) m) := by
    intro g m
    apply e.injective
    show e (e.symm (ρ' g m)) = e (ρ g (e.symm m))
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  have hinv : ∀ x, h1Map ρ' ρ (e.symm : M' →ₗ[R] M) he' (h1Map ρ ρ' (e : M →ₗ[R] M') he x) = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H c =>
      rw [h1Map_mk, h1Map_mk]
      congr 1
      exact Subtype.ext (funext fun g => e.symm_apply_apply _)
  let F := (h1Map ρ ρ' (e : M →ₗ[R] M') he).restrict
    (p := selRep2 ρ J JS D (Fsha ρ D Iq qs) P) (q := selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P)
    (fun x hx => h1Map_mem_selRep2 ρ ρ' _ he J JS D Iq qs P hx)
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    rw [LinearMap.restrict_coe_apply, LinearMap.restrict_coe_apply] at h1
    have h2 := congrArg (h1Map ρ' ρ (e.symm : M' →ₗ[R] M) he') h1
    rwa [hinv, hinv] at h2
  exact Module.length_le_of_injective F hF

end Iso

section GlobalTheory

variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def k0 (c' : Fin D.R.t) : {a : Fin D.R.nV // RepresentationBoundsCohomology.blk D.R a = c'.succ} :=
  ⟨Fin.natAdd D.R.r c', RepresentationBoundsCohomology.blkG_natAdd D.R.r D.R.t c'⟩

variable (Dd) in

def blkEquiv (c' : Fin D.R.t) : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ ≃ₗ[D.nd.O i] KO (D.nd.O i) where
  toFun m := m (k0 c')
  invFun x := fun _ => x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv m := funext fun k => congrArg m (Subtype.ext (blkS_eq k.1 k.2)).symm
  right_inv _ := rfl

omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in

theorem chi_ratio (c' : Fin D.R.t) (g : GE D.nd) :
    (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) =
      ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
        (cycE i ^ (-((((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1 : ℕ) : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  have hc := D.nd.chi_def i ((c' : ℕ) + 1) (by omega) (by have := c'.isLt; omega)
  have hn : (-(((((c' : ℕ) + 1 : ℕ)) : ℤ) - 1)) =
      -((((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1 : ℕ) : ℤ) := by
    simp [Fin.val_succ]
  rw [hc, hn]
  simp only [MonoidHom.mul_apply, Units.val_mul, Units.inv_mul_cancel_left]
  simp [cycE, map_zpow]

theorem uRep_blk (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd)
    (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) :
    uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) Dd.r Dd.χ g m =
      ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
        (cycE i ^ (-((((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1 : ℕ) : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i) • m := by
  show uElt Dd.r Dd.χ g • m = _
  rw [uElt, smul_assoc, rS_act hE hN c' g m, hE.blk_smul, smul_smul, ← chi_ratio c' g]
  congr 2
  rw [← map_inv, hE.chi_eval, map_inv]

theorem blkTw_of (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    BlockTwistedCyclotomic i Dd c := by
  induction c using Fin.cases with
  | zero => simp at hc
  | succ k =>
    refine ⟨blkEquiv Dd k, fun g m => ?_⟩
    have h := uRep_blk hE hN k g m
    show blkEquiv Dd k (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k.succ) Dd.r Dd.χ g m) = _
    rw [h, map_smul]
    first
      | rfl
      | simp [koE, Formalism.GaloisCohomology.scalRep]

theorem blkTw_of_def {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) : BlockTwistedCyclotomic i Dd c :=
  blkTw_of (evS_of hD) hN c hc

end GlobalTheory

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem Fall_eq_Fsha (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) :
    Fall i dc Dd F0 c = Fsha (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc)) (I i dc)
      (qsN i dc) := by
  unfold Fall
  induction c using Fin.cases with
  | zero => simp at hc
  | succ k =>
    funext w
    simp only [Fin.cases_succ]
    have h1 : ((k.succ : Fin (D.R.t + 1)) : ℕ) ≠ 1 := by omega
    unfold Fpos Fsha
    simp only [h1, ↓reduceIte]
    split_ifs <;> rfl

theorem selChi_eq (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) :
    selChi (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
        (Fall i dc Dd F0 c) (Io i) (IS i) =
      selRep2 (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (Io i) (IS i) (decs D.host.E (Aw i dc))
        (Fsha (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc))
        (Pall i dc) := by
  rw [Fall_eq_Fsha i dc Dd F0 c hc]
  rfl

theorem tieSel2_of (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) (hB : BlockTwistedCyclotomic i Dd c) (hC : CoefChange (D.nd.l i) (D.nd.O i))
    (hZ : ZlSha i dc ((c : ℕ) - 1)) :
    Module.length (D.nd.O i) ↥(selChi (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (Fall i dc Dd F0 c) (Io i) (IS i)) ≤ ShaN i ((c : ℕ) - 1) := by
  rw [selChi_eq i dc Dd F0 c hc]
  refine le_trans (len_selRep2_le_of_iso _ _ hB (Io i) (IS i) (decs D.host.E (Aw i dc)) (I i dc)
    (qsN i dc) (Pall i dc)) ?_
  have h2 := hC (GE D.nd) (cycE i ^ (-(((c : ℕ) - 1 : ℕ) : ℤ))) (Io i) (IS i) (decs D.host.E (Aw i dc))
    (I i dc) (qsN i dc) (Pall i dc)
  refine le_trans h2 ?_
  unfold ShaN eON
  exact mul_le_mul' le_rfl hZ

theorem tieSel2 (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) (hB : BlockTwistedCyclotomic i Dd c) (hC : CoefChange (D.nd.l i) (D.nd.O i))
    (hZ : ZlSha i dc ((c : ℕ) - 1)) :
    TieSel2 i (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
      (Fall i dc Dd F0 c) (Io i) (IS i) (c : ℕ) :=
  tieSel2_of i dc Dd F0 c hc hB hC hZ

theorem tieSel2_rec [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hC : CoefChange (D.nd.l i) (D.nd.O i))
    (hZ : ∀ e ∈ Finset.Ioo 0 D.R.t, ZlSha i dc e)
    (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (hc : 2 ≤ (c : ℕ)) :
    TieSel2 i (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
      (Fall i dc Dd F0 c) (Io i) (IS i) (c : ℕ) :=
  tieSel2 i dc Dd F0 c hc (blkTw_of_def hD hN c (by omega)) hC
    (hZ _ (Finset.mem_Ioo.2 ⟨by omega, by have := c.isLt; omega⟩))

end Rec

end Formalism.MainNotions.N.K.ShaT

end
