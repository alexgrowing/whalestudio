import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseExP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Imports
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.LocalToGlobal.KernelLattices.ColumnData.XiEquivD
import Formalism.LocalToGlobal.KernelLattices.ColumnData.XiEquivCOf

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section Bridge

variable (D : D7)

theorem embT_ofRec : Cd.TaylorLogMetric.embT (Car.ofRec D) = TaylorLogMetric.embT D := rfl

theorem lamOf_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Cd.TaylorLogMetric.lamOf (Car.ofRec D) cc δ = TaylorLogMetric.lamOf D cc δ := rfl

theorem La_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.TaylorLogMetric.La (Car.ofRec D) (Cd.TaylorLogMetric.tor0 (Car.ofRec D) cc δ) L L' = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := rfl

theorem Iop_ofRec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N')) (G : TaylorLogMetric.VC D N N' → ℂ) :
    Cd.TaylorLogMetric.Iop (Car.ofRec D) (Cd.TaylorLogMetric.tor0 (Car.ofRec D) cc δ) La₁ La₂ G = TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) La₁ La₂ G := rfl

theorem isCurveIdeal_ofRec (cc : Ideal (𝓞 D.host.K)) : Cd.TaylorLogMetric.IsCurveIdeal (Car.ofRec D) cc ↔ TaylorLogMetric.IsCurveIdeal D cc := Iff.rfl

theorem isTwelfthRootDisc_ofData_iff (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Car.ofRec D) cc δ ↔ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ := Iff.rfl

theorem isChi_ofRec (χ : TaylorLogMetric.IdE D → ℂ) : Cd.TaylorLogMetric.IsChi (Car.ofRec D) χ ↔ TaylorLogMetric.IsChi D χ := Iff.rfl

theorem admissible_ofData_iff {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.TaylorLogMetric.admitted (Car.ofRec D) N N' L L' ↔ TaylorLogMetric.admitted D N N' L L' := Iff.rfl

theorem isDgen_ofRec (cD : D.what₂.Tau → ℂ) : Cd.IsDgen (Car.ofRec D) cD ↔ IsDgen D cD := Iff.rfl

variable {D}

def KapChoice.toCar {γ₀ : IsoK D} (k : KapChoice γ₀) : Cd.KapChoice (D := Car.ofRec D) γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

def KapChoice.ofCar {γ₀ : IsoK D} (k : Cd.KapChoice (D := Car.ofRec D) γ₀) : KapChoice γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def Base.toCar (B : Base D cc δ) : Cd.Base (Car.ofRec D) cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := B.kc.toCar

def Base.ofCar (B : Cd.Base (Car.ofRec D) cc δ) : Base D cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := KapChoice.ofCar B.kc

theorem Base.ofCar_toCar (B : Base D cc δ) : Base.ofCar B.toCar = B := rfl

theorem Base.toCar_ofCar (B : Cd.Base (Car.ofRec D) cc δ) : (Base.ofCar B).toCar = B := rfl

theorem Base.kappa_toCar (B : Base D cc δ) : B.toCar.kappa = B.kappa := rfl

theorem Base.stdOK_toCar (B : Base D cc δ) : B.toCar.StdOK ↔ B.StdOK := Iff.rfl

theorem Base.thMM_toCar (B : Base D cc δ) : B.toCar.thMM = B.thMM := rfl

theorem Base.thMoved_toCar (B : Base D cc δ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : B.toCar.thMoved N N' L L' = B.thMoved N N' L L' := rfl

theorem chiFac_ofRec (χ : TaylorLogMetric.IdE D → ℂ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Cd.Base.chiFac (D := Car.ofRec D) χ N N' L L' = Base.chiFac χ N N' L L' := rfl

theorem Base.eNat_toCar (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : B.toCar.eNat χ = B.eNat χ := rfl

theorem Base.eqP_toCar (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : B.toCar.EqP χ ↔ B.EqP χ := Iff.rfl

variable {X : Fields}

def Seam.toCar (s : Seam D X) : Cd.Seam (Car.ofRec D) X := ⟨s.iE, s.iT, s.σ₀⟩

def Seam.ofCar (s : Cd.Seam (Car.ofRec D) X) : Seam D X := ⟨s.iE, s.iT, s.σ₀⟩

theorem Seam.ok_toCar (s : Seam D X) : s.toCar.Ok ↔ s.Ok := Iff.rfl

theorem ambOf_toCar (s : Seam D X) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    Cd.ambOf s.toCar B.toCar χ cD = ambOf s B χ cD := rfl

theorem ambOf_ofCar (s : Cd.Seam (Car.ofRec D) X) (B : Cd.Base (Car.ofRec D) cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    ambOf (Seam.ofCar s) (Base.ofCar B) χ cD = Cd.ambOf s B χ cD := rfl

end Bridge

section OverColDat

variable (d : ColDat)

theorem curve_delta_ne (K : CurveDat d.host d.what₂.embLL d.eTau) : K.δ ≠ 0 := by
  intro h
  have h1 := K.delta_pow_twelve_eq_discr
  rw [h, zero_pow (by norm_num)] at h1
  exact Cd.IntegralLatticeDensity.discrNe (carD d) d.host.ccK d.host.ccK_ne_bot h1.symm

theorem ambIn_nonempty (K : CurveDat d.host d.what₂.embLL d.eTau) (χ : Cd.TaylorLogMetric.IdE (carD d) → ℂ) :
    ∃ I : AmbIn d, I.K = K ∧ I.χ = χ := by
  obtain ⟨B⟩ := Cd.baseExists (carD d) d.host.ccK (Cd.isCurveIdeal_ccK (carD d)) K.δ (curve_delta_ne d K)
  exact ⟨⟨K, B, χ⟩, rfl, rfl⟩

variable {d}

theorem AmbIn.ok_of (I : AmbIn d) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) : I.Ok :=
  ⟨I.B.stdOK (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc, hχ⟩

theorem AmbIn.isDgen (I : AmbIn d) (hM : ∀ τ x, Cd.TaylorLogMetric.embT (carD d) τ x ∈ I.K.M) : Cd.IsDgen (carD d) I.cD :=
  ⟨I.K.M, I.K.nf, hM, fun τ => ⟨I.K.fr τ, rfl, I.K.gen τ⟩⟩

theorem ambIn_ok_nonempty (d : ColDat) (K : CurveDat d.host d.what₂.embLL d.eTau) : ∃ I : AmbIn d, I.K = K ∧ I.Ok := by
  obtain ⟨χ, hχ⟩ := Cd.IntegralLatticeDensity.exists_chi (carD d)
  obtain ⟨I, hK, hI⟩ := ambIn_nonempty d K χ
  exact ⟨I, hK, I.ok_of (hI ▸ hχ)⟩

theorem AmbIn.eqP (I : AmbIn d) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) : I.B.EqP I.χ :=
  Cd.PairingIndexBounds.Eq.SqG.eqP_car I.B (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc I.χ hχ

theorem repN_sd (u : d.Pr.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : IsSdLat (repN (Pr := d.Pr) d.W d.lev u i c) :=
  ⟨((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c).2.lat, ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c).2.uni⟩

set_option maxHeartbeats 1600000 in

theorem AmbIn.xiHyp (I : AmbIn d) (h : d.what₂.embLL.comp d.embE = d.host.φ₀) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) (S : Set ℕ)
    (m0 : Fin d.R.m → Formalism.L2.Host.HChar d.X.E) {n m2 : ℕ} (hm : d.R.m = m2 + 2) (G : ChainGlob (Pr := d.Pr) d.W d.σ₀)
    (rat : ∀ u i, i < d.R.m → I.amb.JetsRat (d.R.N i) (d.R.N (i + 1)) (Sall (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) u)
      (cAof (selD d) _ (cstD d S m0 n) * cBof (selD d) _ (cstD d S m0 n) u))
    (rho : ∀ u, RhoScal (Pr := d.Pr) d.W d.lev d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) G I.amb u) (u : d.Pr.Word) :
    XiHyp (Pr := d.Pr) d.W d.lev d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) I.amb u
      (refXi1 d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) (idxD d S m2) (qe_one (selD d)) m2 (alD d S m2) u) G :=
  xiHypD d S m0 hm G I.amb rfl (fun i _ => I.eSmooth h i (i + 1)) rat
    (fun u i _ c c' => I.chiF_ne h hχ i (i + 1) (repN_sd u i c) (repN_sd u (i + 1) c')) rho u

theorem seamD_lat {n : ℕ} (N : Submodule (𝓞 d.X.E) (Sp d.X.E n)) : (seamD d).lat N = N := by
  ext y
  rw [Cd.Seam.mem_lat]
  exact ⟨fun ⟨x, hx, e⟩ => e ▸ hx, fun h => ⟨y, h, rfl⟩⟩

theorem AmbIn.amb_e (I : AmbIn d) (a b : ℕ) (N : Submodule (𝓞 d.X.E) (Sp d.X.E a)) (N' : Submodule (𝓞 d.X.E) (Sp d.X.E b)) :
    I.amb.e a b N N' = I.B.eNat I.χ a b N N' := by
  have h : I.amb.e a b N N' = I.B.eNat I.χ a b ((seamD d).lat N) ((seamD d).lat N') := rfl
  rw [h, seamD_lat, seamD_lat]

theorem AmbIn.amb_sig (I : AmbIn d) : I.amb.σ₀ = d.σ₀ := rfl

theorem AmbIn.amb_cD (I : AmbIn d) : I.amb.cD = I.cD := rfl

def Car.ofColRec (c : ColRec) : Car := ⟨c.R, c.host, ⟨c.what₂.Tau, c.what₂.card_Tau⟩, c.eTau⟩

theorem car_of_colRec (D : D7) (d : ColDat) (a : ColArgs d) (h : D.colRec = d.colRec a) : Car.ofRec D = carD d :=
  congrArg Car.ofColRec h

end OverColDat

theorem Cd.exists_base_ne (D : Car) : ∃ (δ : ℂ) (B : Cd.Base D D.host.ccK δ), Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ B.StdOK ∧
    ∀ N N' L L', Cd.TaylorLogMetric.admitted D N N' L L' → B.thMoved N N' L L' ≠ 0 := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Cd.TaylorLogMetric.lamOf D D.host.ccK 1)) (by norm_num : 0 < 12)
  have h0 := Cd.twelfth_root_disc_ne_zero D D.host.ccK D.host.ccK_ne_bot hδ
  obtain ⟨B⟩ := Cd.baseExists D D.host.ccK (Cd.isCurveIdeal_ccK D) δ h0
  have hS := B.stdOK (Cd.isCurveIdeal_ccK D) hδ
  exact ⟨δ, B, hδ, hS, fun N N' L L' hA =>
    B.thMoved_ne_zero hS (B.latAll (Cd.isCurveIdeal_ccK D) hδ h0) (B.thZeroMem hS N N') hA⟩

namespace Test

open Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits

def exampleCMData : Car := ⟨R0, H0, ⟨R0.Psi, by rw [card_Psi]; rfl⟩, Equiv.refl _⟩

theorem moved_vacuum_ne_zero_example : ∃ (δ : ℂ) (B : Cd.Base exampleCMData exampleCMData.host.ccK δ),
    B.thMoved 2 4 (Cd.StandardLatticesGL3.stdL exampleCMData 2) (Cd.StandardLatticesGL3.stdL exampleCMData 4) ≠ 0 := by
  obtain ⟨δ, B, -, -, h⟩ := Cd.exists_base_ne exampleCMData
  exact ⟨δ, B, h 2 4 _ _ (Cd.Inhab.Adm_std exampleCMData 2 4 (by decide) (by decide))⟩

end Test

end Formalism.L2.Ker
