import Formalism.AdmissibleDesigns.SelfGood

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Core

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def TBClause (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) (ℓ cB cT deg : ℕ)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw))) : Prop :=
  F ≤ Hc ∧ cT ≤ cB ∧
    (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
      ∀ z : coZ1s (resRep (uRep O (M := M) r χ) Dw),
        (∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : G))) →
        ((ℓ : O) ^ cT) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) Dw)) ∈ F) ∧
    Module.length O (↥(Hc ⊓ divBy F ((ℓ : O) ^ cT)) ⧸
        F.comap (Hc ⊓ divBy F ((ℓ : O) ^ cT)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cT : ℕ∞) * ((deg : ℕ∞) + 1)

def YLoc (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw] : Prop :=
  ∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    IsLocallyConstant fun g : Dw => ψ (yY r χ E (g : G))

end Core

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    (O : Type) [CommRing O] [Algebra O LL]

structure TwLat (e : ℕ) where
  V : Type
  [acg : AddCommGroup V]
  [mLL : Module LL V]
  [mQ : Module Qp V]
  [tQ : IsScalarTower Qp LL V]
  [mO : Module O V]
  [tO : IsScalarTower O LL V]
  [top : TopologicalSpace V]
  [cadd : ContinuousAdd V]
  [csm : ContinuousConstSMul LL V]
  [imt : IsModuleTopology LL V]
  [fd : FiniteDimensional LL V]
  ρ : Representation LL G V
  L : Lattice (O := O) ρ
  cont : ∀ x, Continuous fun g => ρ g x
  mat : IsMatLat (ρ := ρ) L.T (epsTw PD e)

attribute [instance] TwLat.acg TwLat.mLL TwLat.mQ TwLat.tQ TwLat.mO TwLat.tO TwLat.top TwLat.cadd TwLat.csm
  TwLat.imt TwLat.fd

structure YtLat where
  V : Type
  [acg : AddCommGroup V]
  [mLL : Module LL V]
  [mQ : Module Qp V]
  [tQ : IsScalarTower Qp LL V]
  [mO : Module O V]
  [tO : IsScalarTower O LL V]
  [top : TopologicalSpace V]
  [cadd : ContinuousAdd V]
  [csm : ContinuousConstSMul LL V]
  [imt : IsModuleTopology LL V]
  [fd : FiniteDimensional LL V]
  ρ : Representation LL G V
  L : Lattice (O := O) ρ
  cont : ∀ x, Continuous fun g => ρ g x
  p : V →ₗ[LL] LL
  p_inv : ∀ g v, p (ρ g v) = p v
  p_int : ∀ v ∈ L.T, p v ∈ Set.range (algebraMap O LL)
  e₀ : V
  e₀_mem : e₀ ∈ L.T
  p_e₀ : p e₀ = 1

attribute [instance] YtLat.acg YtLat.mLL YtLat.mQ YtLat.tQ YtLat.mO YtLat.tO YtLat.top YtLat.cadd YtLat.csm
  YtLat.imt YtLat.fd

variable {PD LL O}

def YtCrys (Y : YtLat (G := G) (Qp := Qp) LL O) (J : (K →ₐ[Qp] LL) → Set ℤ) : Prop :=
  IsCrys PD Y.ρ ∧ ∀ τ, JumpsInV PD Y.ρ τ (J τ)

end Local

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] (σ : O' ≃+* O)
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : Dw ≃* G)

variable (PD LL O M) in

structure CoefDict (e : ℕ) where
  Ce : TwLat PD LL O e
  u : M ≃+ (Ce.V ⧸ Ce.L.T)
  u_smul : ∀ (a : O') (m : M), u (a • m) = σ a • u m
  u_act : ∀ (g : Dw) (m : M), u (uElt r χ (g : GG) • m) = actD Ce.L (eG g) (u m)

def PsiExt {e : ℕ} (Y : YtLat (G := G) (Qp := Qp) LL O) (Cd : CoefDict PD LL O σ M r χ Dw eG e) : Prop :=
  ∀ ψ : Ymod r χ E →ₗ[O'] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    ∃ φ : Y.V →ₗ[O] (Cd.Ce.V ⧸ Cd.Ce.L.T),
      (∀ g, ∀ y ∈ Y.L.T, Y.p y = 0 → φ (Y.ρ g y) = actD Cd.Ce.L g (φ y)) ∧
      ∀ g : Dw, φ (Y.ρ (eG g) Y.e₀ - Y.e₀) = Cd.u (ψ (yY r χ E (g : GG)))

variable {σ r χ E Dw eG}

def trC {e : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) (z : Dw → M) : G → Cd.Ce.V ⧸ Cd.Ce.L.T :=
  fun g => Cd.u (z (eG.symm g))

theorem actD_mul {e : ℕ} (Ce : TwLat PD LL O e) (g h : G) (x : Ce.V ⧸ Ce.L.T) :
    actD Ce.L (g * h) x = actD Ce.L g (actD Ce.L h x) := by
  refine Submodule.Quotient.induction_on _ x (fun v => ?_)
  simp only [actD, Submodule.mapQ_apply, map_mul]
  all_goals rfl

theorem trC_hf {e t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : Dw → M) (hz : ∀ g : Dw, z g = ψ (yY r χ E (g : GG))) :
    ((PD.p : O) ^ cB) • trC Cd z ∈ HfD PD Cd.Ce.L := by
  obtain ⟨φ, hφ1, hφ2⟩ := hψ ψ hψe
  have hfun : trC Cd z = fun g => φ (Y.ρ g Y.e₀ - Y.e₀) := by
    funext g
    have h := hφ2 (eG.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    simp only [trC, hz]
  rw [hfun]
  exact hTB.1 Y.V Y.ρ Y.L Y.cont hY.1 hY.2 Y.p Y.p_inv Y.p_int Y.e₀ Y.e₀_mem Y.p_e₀ e het
    Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat φ hφ1

theorem trC_mem_Z1D {e : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) [TopologicalSpace Dw]
    (heG : Continuous eG.symm) (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw))
    (hz : IsLocallyConstant (z : Dw → M)) (c : O) : c • trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L := by
  apply Submodule.smul_mem
  show IsLocallyConstant (trC Cd (z : Dw → M)) ∧ ∀ g h, trC Cd (z : Dw → M) (g * h) =
    trC Cd (z : Dw → M) g + actD Cd.Ce.L g (trC Cd (z : Dw → M) h)
  refine ⟨(hz.comp_continuous heG).comp Cd.u, fun g h => ?_⟩
  have hc : (z : Dw → M) (eG.symm g * eG.symm h) = (z : Dw → M) (eG.symm g) +
      resRep (uRep O' (M := M) r χ) Dw (eG.symm g) ((z : Dw → M) (eG.symm h)) := z.2 _ _
  simp only [trC, map_mul]
  rw [hc, map_add]
  congr 1
  have hu := Cd.u_act (eG.symm g) ((z : Dw → M) (eG.symm h))
  rw [MulEquiv.apply_symm_apply] at hu
  exact hu

end Transport

section Record

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Dw (n : ℕ) : Subgroup (GE D.nd) := (Aw i dc n).decompositionSubgroup D.host.E

abbrev Mc (c : Fin (D.R.t + 1)) : Type := blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk c

abbrev ρc (c : Fin (D.R.t + 1)) (n : ℕ) : Representation (D.nd.O i) (Dw i dc n) (Mc i Dd c) :=
  resRep (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (Dw i dc n)

def Hc (c : Fin (D.R.t + 1)) (n : ℕ) : Submodule (D.nd.O i) (H1z (ρc i dc Dd c n)) :=
  Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (ρc i dc Dd c n)

def Fc (c : Fin (D.R.t + 1)) (n : ℕ) : Submodule (D.nd.O i) (H1z (ρc i dc Dd c n)) :=
  if (c : ℕ) = 1 then
    Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (ρc i dc Dd c n) ⊓
      unrH1 (ρc i dc Dd c n) ((Ine (F := D.host.E) (Aw i dc n)).subgroupOf (Dw i dc n))
  else ⊥

def TBTarget (cB : ℕ) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
    TBClause (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc n) (D.nd.l i) cB cB (Formalism.MainNotions.N.locDeg D.host.E (plOf i dc n))
      (Hc i dc Dd c n) (Fc i dc Dd c n)

theorem mem_plSet {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    w ∈ plSet i dc := by
  simp only [plSet, Finset.mem_union]
  exact Or.inl ((dc.cover w).2 hw)

theorem Dw_idx {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Dw i dc (idx i dc w) = Dec (F := D.host.E) (D.nd.plOm.1 w) := by
  have hm := mem_plSet i dc hw
  have hpl : plOf i dc (idx i dc w) = w := by
    simp [plOf, idx, hm]
  simp only [Dw, Aw, hpl, ReciprocityTheory.Gal.Dec]

def eW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    ↥(Dw i dc (idx i dc w)) ≃* Br.G D.nbr i w hw :=
  (MulEquiv.subgroupCongr (Dw_idx i dc hw)).trans (D.nbr i w hw).e

def Jr {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) → Set ℤ :=
  fun τ => {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}

def selfO {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    D.nd.O i ≃+* ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) :=
  (D.nbr i w hw).eO

def TBDict : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∃ (Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL))
        (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)),
        YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
        PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd ∧
        YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w))

end Record

end Formalism.MainNotions.N.K.TB

end
