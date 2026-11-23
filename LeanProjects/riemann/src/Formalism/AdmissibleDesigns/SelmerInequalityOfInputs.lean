import Formalism.AdmissibleDesigns.PiEquiv2
import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.St

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

abbrev HfWS (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.HfW i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev Hf₂S (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Hf₂ i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev FsS (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Fs i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev Hf₁S (w : ℕ) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    Submodule (D.nd.O i) (H1 (resRep (rho1 i Dd) (KHf.Γn i dc w))) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KHf.Hf₁ i dc (rho1 i Dd) w

def FirstBlockLocalConditions (w : ℕ) : Submodule (D.nd.O i) (H1z (QS.resU i dc Dd 0 w)) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Fρ i dc (rowsN i dc) (fun n => QS.resU i dc Dd 0 n)
    (fun n => (((HfWS i r π dc g0 eB e₁ s Dd hD hc n).restrictScalars (D.nd.O i)).map (DatS i r π dc g0 eB e₁ s Dd hD hc n).q).map
      (kRow (DatS i r π dc g0 eB e₁ s Dd hD hc n) _ (uDS i r π dc g0 eB e₁ s Dd hD hc n) (huDS i r π dc g0 eB e₁ s Dd hD hc n)))
    (fun n => KHf.F0col i dc n (resRep (uRep (D.nd.O i) (M := Vr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n))
      (QS.resU i dc Dd 0 n) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)) w

abbrev FS := QS.Fall i dc Dd (FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc)

theorem FS_pos (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) (w : ℕ) : FS i r π dc g0 eB e₁ s Dd hD hc c w = QS.Fpos i dc Dd c w := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.2 hc0
  unfold FS QS.Fall
  first
    | rfl
    | simp only [Fin.cases_succ]
    | exact Fin.cases_succ _

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

abbrev ImS (w : ℕ) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  (Hf₁S i r π dc g0 eB e₁ s Dd hD w).map (gRow (DatS i r π dc g0 eB e₁ s Dd hD hc w) (resRep (rho1 i Dd) (decs D.host.E (Aw i dc) w))
    (piS i Dd hT hrk) (vDS i r π dc g0 eB e₁ s Dd hD hc w) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w) (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w))

def rowLenS (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (FsS i r π dc g0 eB e₁ s Dd hD hc w ⧸ (ImS i r π dc g0 eB e₁ s Dd hD hc hT hrk w).comap (FsS i r π dc g0 eB e₁ s Dd hD hc w).subtype)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem selmer_inequality_of_inputs [IsNoetherian Dd.R' Dd.R']
    [∀ x', IsScalarTower Dd.T' Dd.R' (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')]
    [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    [∀ k, IsScalarTower (D.nd.O i) Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (hP : Formalism.RepresentationBoundsCohomology.ringDataObjects.PrimHyp (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (RepresentationBoundsCohomology.blk D.R) (chiU D.nd i 1) (epsU D.nd i))
    (u0 : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u0 : ℤ_[D.nd.l i]))
    (hK : ∀ [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
          [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [TopologicalSpace Dd.R']
          [IsTopologicalAddGroup Dd.R'] [ContinuousConstSMul (D.nd.O i) Dd.R'] [ContinuousMul Dd.R'],
          RealDisplayAllK (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
            Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ D.R.t (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) (RepresentationBoundsCohomology.blk D.R) Dd.ρk Dd.δO
            (epsU D.nd i) g0 (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)))
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (κ : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) → GE D.nd → Lr i Dd)
    (κz : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) →
      coZ1s (resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) (colIdx i dc l))))
    (u : Col i dc → GE D.nd → D.nd.O i)
    (uz : ∀ l : Col i dc,
      coZ1s (Representation.trivial (D.nd.O i) ↥(decs D.host.E (Aw i dc) (colIdx i dc l)) ↥(Ideal.span {Dd.δO})))
    (hUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
      (((uz l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g : ↥(Ideal.span {Dd.δO})) :
        D.nd.O i) = Dd.δO * u l g)
    (hUnr : KHf.UnrFin i dc Dd.δO uz)
    (hL1 : ∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l)
      (KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l)
      (mapH1 _ _ (eveS i Dd hT hrk) (ev_equiv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l))
        (incl (D.nd.O i) Dd.e₁) (v1S i Dd hT hrk) (eveS i Dd hT hrk) (fun a => rfl))) (e'N i dc e' (colIdx i dc l)))
    (hL2 : ∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l) (KHf.HfE₂ i dc Dd.δO l)
      (mapH1 _ _ (evES i Dd hT) (ev_equiv_triv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l)) (evES i Dd hT)
        (hevES i Dd hT))) (e'N i dc e' (colIdx i dc l)))
    (hG6 : QS.NoFixedVectorOffZ i Dd)
    (hLx : ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ))
    (hRho : InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk) κ
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk))
    (hBKa : ∀ w ∈ rowsN i dc, ∀ a, a ∈ HfWS i r π dc g0 eB e₁ s Dd hD hc w ↔
      ∀ b ∈ Hf₂S i r π dc g0 eB e₁ s Dd hD hc w, cupFG (DatS i r π dc g0 eB e₁ s Dd hD hc w) a b = 0)
    (hTB : ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈ FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1))
    (hChi : ∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
      InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (ShaN i ((c : ℕ) - 1)) (FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
        (QS.ζO i dc) (QS.nQ i dc))
    (hU1 : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), u l (g : GE D.nd) = 0) ∧
      (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), u l g = 1))
    (hLoc1 : InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
      (FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc))
    (hCover : ∀ v, (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.Io i a) ∨
      (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.IS i a) ∨
        ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup ((decs D.host.E (Aw i dc)) w),
          FS i r π dc g0 eB e₁ s Dd hD hc QS.c1 w ≤ unrH1 (QS.resU i dc Dd QS.c1 w) J ∧
          Ine (F := D.host.E) (Av (D := D) v) ≤ J.map ((decs D.host.E (Aw i dc)) w).subtype)
    (hCR : ∀ l : Col i dc, colIdx i dc l ∉ rowsN i dc) (hRQ : ∀ w ∈ rowsN i dc, w ∉ qsN i dc)
    (hTie : TieRow i dc (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) lenRow) :
    SelmerLengthInequality i ρ π dc lenRow e' cB := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  haveI := Topo.rTop_mul_RD i r π g0 eB e₁ s Dd hD
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := Topo.topoHyps i r π dc g0 eB e₁ s Dd hD hc u0 hcyc
  have hA := tensor_lattice_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk (epsU D.nd i)
  have hL := fun w => KLat.rowLat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (D.nd.l i) (Topo.padicCoeff_O i) (Topo.fracTop_O i) w
  have H := hK (Col i dc) (colIdx i dc) (colIdx_inj i dc) (Aw i dc) (plOf i dc) (Av (D := D)) (jN i ρ π dc)
    (e'N i dc e') (rowsN i dc) (qsN i dc) (sN i ρ π) (invariantsLengthSup i dc) (ShaN i) cB (fun _ _ => cB)
    (Lr i Dd) (tensM _ _ _) (v1S i Dd hT hrk) κ (Vr i Dd) (iLM _ _ _) (qVM _ _ _)
    (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc)
    (QS.Vo i) (QS.VS i) (QS.Io i) (QS.IS i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) ({a // RepresentationBoundsCohomology.blk D.R a = 0} → D.nd.O i)
    (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk) (gamM (Dd.ρk 0)) (lamS i Dd hT hrk)
    (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) (uDS i r π dc g0 eB e₁ s Dd hD hc) (huDS i r π dc g0 eB e₁ s Dd hD hc) (vDS i r π dc g0 eB e₁ s Dd hD hc) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk) (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk)
    (FsS i r π dc g0 eB e₁ s Dd hD hc) (Hf₁S i r π dc g0 eB e₁ s Dd hD) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc)
    u (D.nd.s0 i) (Topo.yU i u0) (HfWS i r π dc g0 eB e₁ s Dd hD hc) (Hf₂S i r π dc g0 eB e₁ s Dd hD hc)
    (LeftId (D.nd.O i) Dd.e₁) (incl _ Dd.e₁) (eveS i Dd hT hrk) (fun a => rfl)
    (LeftId (D.nd.O i) Dd.E) (incl _ Dd.E) (evES i Dd hT) (hevES i Dd hT)
    (fun l => KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l)
    (fun l => KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l) (fun l => KHf.HfE₂ i dc Dd.δO l) uz
  have hrows : ∀ w ∈ rowsN i dc, FS i r π dc g0 eB e₁ s Dd hD hc 0 w = (((HfWS i r π dc g0 eB e₁ s Dd hD hc w).restrictScalars (D.nd.O i)).map (DatS i r π dc g0 eB e₁ s Dd hD hc w).q).map
      (kRow (DatS i r π dc g0 eB e₁ s Dd hD hc w) _ (uDS i r π dc g0 eB e₁ s Dd hD hc w) (huDS i r π dc g0 eB e₁ s Dd hD hc w)) := by
    intro w hw
    show FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc w = _
    unfold FirstBlockLocalConditions KHf.Fρ
    rw [if_pos hw]
  obtain ⟨hineq, hv, -⟩ := H t1 t2 t3 t4 t5 (inc_cont (O := D.nd.O i) Dd.e₁) t6 t7 t8 t9 t10 t11 hA.2.2.1 hA.2.2.2.2.1 hA.2.2.2.2.2.1
    hA.2.2.2.2.2.2.1 hUz hUnr hL1 hL2 (fun x' hx => ⟨hG6 x' hx, hLx x' hx⟩) hRho
    (fun w hw => ⟨(t12 w hw).1, (t12 w hw).2, (hL w).1, (hL w).2.1, (hL w).2.2.1, (hL w).2.2.2, hBKa w hw,
      hrows w hw, rfl,
      KHf.im_le_Fs i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w (rho1 i Dd) (piS i Dd hT hrk) (vDS i r π dc g0 eB e₁ s Dd hD hc w) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w)
        (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w)⟩)
    (fun c hc2 => ⟨H0.kernel_length_higher_columns dc hN hD c hc2,
      fun w hw => ⟨by
        have hc0 : c ≠ 0 := fun h => by rw [h] at hc2; simp at hc2
        have hc1 : (c : ℕ) ≠ 1 := by omega
        rw [FS_pos i r π dc g0 eB e₁ s Dd hD hc c hc0 w]
        unfold QS.Fpos
        rw [if_neg (hRQ w hw), if_pos hw, if_neg hc1], le_rfl, hTB c (by omega) w hw⟩, hChi c hc2⟩)
    ⟨hU1.1, hU1.2, fun l => by
        rw [FS_pos i r π dc g0 eB e₁ s Dd hD hc _ (by intro h; have := congrArg Fin.val h; simp at this) _]
        unfold QS.Fpos
        by_cases hq : colIdx i dc l ∈ qsN i dc
        · rw [if_pos hq] <;> exact le_rfl
        · rw [if_neg hq, if_neg (hCR l), if_pos rfl] <;> exact le_rfl,
      fun w hw => ⟨by
        rw [FS_pos i r π dc g0 eB e₁ s Dd hD hc _ (by intro h; have := congrArg Fin.val h; simp at this) _]
        unfold QS.Fpos
        rw [if_neg (hRQ w hw), if_pos hw, if_pos rfl], le_rfl, hTB QS.c1 le_rfl w hw⟩, hLoc1, hCover⟩
  exact ⟨rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk, H0.h0d i dc Dd, IsDiscreteValuationRing.addVal (D.nd.O i) Dd.δO,
    Fintype.card {a // RepresentationBoundsCohomology.blk D.R a = 0}, hv, card_first_block (D := D), hineq, hTie,
    H0.invariants_display_match i r ρ π dc g0 eB e₁ s Dd hD hN⟩

end Formalism.MainNotions.N.K.St

end
