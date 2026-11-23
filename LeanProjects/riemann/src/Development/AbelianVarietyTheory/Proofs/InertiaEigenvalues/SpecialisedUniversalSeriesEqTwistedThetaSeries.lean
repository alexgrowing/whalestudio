import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpecFac

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fock

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem pureTensorO_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (f + f') P =
      pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P := by
  have hA : ∀ k g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g) :=
    fun k g hg => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hg
  have hl : ∀ l : List (FVar D T.rank S.rank),
      l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) (f + f') =
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f +
        l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f' ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f) ∧
      IsThetaFunO ψ S T (l.foldr (fun i g => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) f') := by
    intro l
    induction l with
    | nil => exact ⟨rfl, hf, hf'⟩
    | cons i l ih =>
      simp only [List.foldr_cons]
      refine ⟨?_, hA i _ ih.2.1, hA i _ ih.2.2⟩
      rw [ih.1]
      exact GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ ih.2.1 ih.2.2
  have e : pureTensorO ψ θ S T sS sT BS BT (f + f') =
      pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT f' := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    simp only [pureTensorO, pureTensorL, LinearMap.add_apply, Module.Basis.constr_basis, opPow]
    exact (hl _).1
  rw [e, LinearMap.add_apply]

theorem theta_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a)) :
    IsThetaFunO ψ S T (∑ a ∈ s, c a • f a) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun a ha => GlobalTheory.OrientedHeis.theta_smul _ (hf a ha)

theorem pureTensorO_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO ψ S T (f a))
    (P : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (∑ a ∈ s, c a • f a) P = ∑ a ∈ s, c a • pureTensorO ψ θ S T sS sT BS BT (f a) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
    rwa [zero_smul, zero_smul] at this
  | insert a s ha ih =>
    have hs : ∀ x ∈ s, IsThetaFunO ψ S T (f x) := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      pureTensorO_add hψ hθ sS BS sT BT (GlobalTheory.OrientedHeis.theta_smul _ (hf a (Finset.mem_insert_self a s)))
        (theta_sum s c f hs) P,
      GlobalTheory.FiniteFock.pureTensorO_smul, ih hs]

theorem series_sum {B : Base S T} (hB : B.Good) (ω : PairRep S T) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ a ∈ s, IsThetaFunO B.F.ψ S T (f a)) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T) :
    series B.F ω (∑ a ∈ s, c a • f a) h P g = ∑ a ∈ s, c a * series B.F ω (f a) h P g := by
  simp only [series_apply, Frame.fock]
  rw [pureTensorO_sum hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ s c f hf P, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

end Fock

section Spec

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem coef_add (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a a' : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (a + a'))) : X.Ok i k) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) *
        ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a')) : X.Ok i k) := by
  rw [map_add, ofAdd_add, map_mul, Units.val_mul, map_mul]

open Classical in

theorem coef_prod (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (a : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) :
    ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) =
      ∏ PP, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP (a PP)))) : X.Ok i k) := by
  have e : a = ∑ PP, Pi.single PP (a PP) := (Finset.univ_sum_single a).symm
  conv_lhs => rw [e]
  rw [map_sum, ofAdd_sum, map_prod, Units.coe_prod, map_prod]

open Classical in

theorem locFn_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).locFn (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (fun PP y =>
          ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) := by
  funext y
  simp only [Base.locFn, specLoc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coef_prod ρ Y i b k Q M χ a, Finset.prod_mul_distrib]
  ring

open Classical in

theorem vecAt_specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) :
    (ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) •
        (ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a := by
  rw [Base.vecAt, locFn_specLoc]
  change (ρ.B i j b).F.vecL (ρ.B i j b).G _ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  rfl

theorem coord_open (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) (P : Pl D.host.E) :
    IsOpen ((coord Y i Q M P).ker : Set (G D.host.E N.Om)) := by
  unfold coord
  split_ifs
  · exact Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one])
      (Y.delU_open i Q M)
  · rw [MonoidHom.ker_one]
    exact isOpen_univ

theorem detChar_tw {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : GlobalTheory.UnivChar.IsUnivChar Y)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (hχ : TwOK i k Q (χ.comp (Y.delU i Q M)))
    (g : GA D (Wc D j)) :
    ((detChar (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi g : Circle) : ℂ) =
      ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Multiplicative.toAdd
        (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g)))) :
          X.Ok i k) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym (detRoot (Wc D j) g)
  have hker : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
    Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker)
      (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hg, map_one]) (Y.delU_open i Q M)
  have hn : X.l i ^ M ≠ 0 := NeZero.ne _
  have hpow : (χ.comp (Y.delU i Q M)) σ ^ (X.l i ^ M) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow]
    have e : Y.delU i Q M σ ^ (X.l i ^ M) = 1 := by
      apply Multiplicative.toAdd.injective
      funext v
      rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
      rfl
    rw [e, map_one]
  have hd : Multiplicative.toAdd
      (detChar (Wc D j) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g) =
        fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
    funext PP
    change Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) (detRoot (Wc D j) g)) = _
    rw [ρ.rc.pull_eq (coord_open Y i _ M PP.1) hσ]
  change ((charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) (detRoot (Wc D j) g) : Circle) : ℂ) = _
  rw [charOf_eq ρ.rc (ρ.eOk i b k) hker hσ hn hpow, hd, MonoidHom.comp_apply,
    ← ofAdd_toAdd (Y.delU i Q M σ), delU_eq_spread hY (twSet_of_twOK hχ) (hρ.ch i) σ]

end Spec

theorem specXi_eq_specSer : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      specXi ρ Y i j b k Q M χ h P = specSer ρ Y i j b k Q M χ h P := by
  intro D N X ρ hρ Y hY i j b k Q M χ hχ h P
  classical
  funext g
  have hB := hρ.base i j b
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) :=
    GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint D N X ρ hρ i j b _ (fun _ h => isSplit_of_mem_admissibleConjugatePairPlaces h)
      (hχ.2.1.mono_left (admissibleConjugatePairPlaces_subset i Q M))
  have htheta : ∀ a ∈ (Finset.univ : Finset (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M))),
      IsThetaFunO (ρ.B i j b).F.ψ (Vc D j) (Wc D j) ((ρ.B i j b).vecFam (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))
        (Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j)) a) := fun a _ => by
    have := Base.isThetaFunO_fock_vecAt hB hadm (fun PP y =>
      ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 (a PP) y : ℚ) : ℂ)) 1
    rwa [Frame.fock, GlobalTheory.FiniteFock.pureTensorO_one] at this
  unfold specSer
  rw [twistBy_apply, vecAt_specLoc, series_sum hB _ _ _ _ htheta, detChar_tw hρ hY i j b k Q M χ hχ g]
  unfold specXi
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Setup.xi, Base.xiCoef_apply]
  rw [← Equiv.sum_comp (Equiv.addRight (Multiplicative.toAdd (detChar (Wc D j)
    ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) g))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Equiv.coe_addRight, add_sub_cancel_right, coef_add]
  ring

end GlobalTheory.SpecFac
