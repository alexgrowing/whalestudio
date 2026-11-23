import Formalism.LocalToGlobal.Columns.TiedRec
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CH

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LevelData (D : ColRec) :=
  letI := D.host.cmStar
  ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)

structure HermCols (D : ColRec) where

  lev0 : LevelData D

  lev : ∀ (u : D.what₂.Word) (i : ℕ), 1 ≤ i → i ≤ D.R.m →
    StepLevel D.sp.cm (D.sp.X i) D.host.g (D.mem u).A.T D.R.f

  cls : ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m),
    ClassTie D.sp.cm (D.sp.X i) (lev u i h1 hm).Lb (lev u i h1 hm).U ((D.mem u).C.stab i) (D.clsLat u i)

  vT : ∀ u : D.what₂.Word, (D.mem u).A.vT ≃
    {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

  Fv : ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (vT u v).1.asIdeal)

section Abbr

variable (D : ColRec) (u : D.what₂.Word)

abbrev Ld (i : ℕ) (c : (D.mem u).C.cls i) : Submodule (𝓞 D.host.E) (D.sp.X i).V :=
  Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c)

abbrev GX (i : ℕ) : Subgroup ((D.sp.X i).V ≃ₗ[D.host.E] (D.sp.X i).V) := Formalism.HermitianLatticesTheory.isom (D.sp.X i).hT

abbrev Lk (P : Ideal (𝓞 D.host.E)) (i : ℕ) (c : (D.mem u).C.cls i) : Submodule (𝓞 D.host.E) (D.sp.X i).V :=
  D.clsLat u i c ⊔ P • Ld D u i c

end Abbr

set_option maxHeartbeats 4000000 in

structure AtT (D : ColRec) (u : D.what₂.Word)
    (e : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal})
    (eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (e v).1.asIdeal)) where

  piU : 𝓞 D.host.E
  piU_K : (piU : D.host.E) ∈ D.host.K
  piU_norm : (piU : D.host.E) * D.host.conj (piU : D.host.E) = ((D.mem u).A.T : D.host.E)
  piU_cong : (piU - 1) ∈ Ideal.span
    {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  Pv : (D.mem u).A.vT → Ideal (𝓞 D.host.E)
  Pv_max : ∀ v, (Pv v).IsMaximal
  Pv_pi : ∀ v, piU ∈ Pv v
  Pv_over : ∀ v, (Pv v).comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = (e v).1.asIdeal

  res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v
  res_surj : ∀ v, Function.Surjective (res v)
  res_ker : ∀ v, RingHom.ker (res v) = Pv v
  res_F : ∀ v (a : 𝓞 D.host.F), eF v (res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a)) = Ideal.Quotient.mk _ a

  seen : ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ (v : (D.mem u).A.vT) (x : 𝓞 D.host.E) (y : D.what₂.LL),
      D.what₂.embLL y = D.host.emb (D.eTau ((D.fm u).tauOf w v)).1 (x : D.host.E) →
      ((0 : WithTop ℤ) < D.what₂.places.val w y ↔
        x ∈ (if (D.fm u).seenP w then Pv v else Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (Pv v)))

  disc : ∀ i, i ≤ D.R.m → ∀ c : (D.mem u).C.cls i,
    Nonempty ((Ld D u i c ⧸ (D.clsLat u i c).comap (Ld D u i c).subtype) ≃ₗ[𝓞 D.host.E]
      (𝓞 D.host.E ⧸ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)}))

  pr : ∀ i v (c : (D.mem u).C.cls i), Ld D u i c →+ (D.fm u).lv i v c
  pr_surj : ∀ i, i ≤ D.R.m → ∀ v c, Function.Surjective (pr i v c)
  pr_smul : ∀ i v c (a : 𝓞 D.host.E) (y : Ld D u i c), pr i v c (a • y) = res v a • pr i v c y
  pr_ker : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c), pr i v c y = 0 ↔ (y : (D.sp.X i).V) ∈ Pv v • Ld D u i c

  fv_ker : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c),
    (D.fm u).fv i v c (pr i v c y) = 0 ↔ (y : (D.sp.X i).V) ∈ Lk D u (Pv v) i c

  prk : ∀ i v (c : (D.mem u).C.cls i), Lk D u (Pv v) i c →+ (D.fm u).lk i v c
  prk_surj : ∀ i, i ≤ D.R.m → ∀ v c, Function.Surjective (prk i v c)
  prk_smul : ∀ i v c (a : 𝓞 D.host.E) (y : Lk D u (Pv v) i c), prk i v c (a • y) = res v a • prk i v c y
  prk_ker : ∀ i, i ≤ D.R.m → ∀ v c (y : Lk D u (Pv v) i c),
    prk i v c y = 0 ↔ (y : (D.sp.X i).V) ∈ Pv v • Lk D u (Pv v) i c

  te_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c), (D.fm u).fv i v c (pr i v c y) = 1 →
    ∀ h : ((D.mem u).A.T : D.host.E) • (y : (D.sp.X i).V) ∈ Lk D u (Pv v) i c,
      prk i v c ⟨_, h⟩ = (D.fm u).te i v c

  upG : ∀ i v (c : (D.mem u).C.cls i), Ld D u i c → GX D i

  up_tie : ∀ i, i ≤ D.R.m → ∀ v c (y : Ld D u i c), (D.fm u).fv i v c (pr i v c y) = 1 →
    haveI := (Pv_max v).isPrime
    SameOff (Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (pr i v c y)))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (D.clsLat u i ((D.fm u).up i v c (pr i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Ld D u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Formalism.HermitianLatticesTheory.gmap (upG i v c y).1 (Ld D u i ((D.fm u).up i v c (pr i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Ld D u i c ⊔
          Submodule.span (𝓞 D.host.E) {((D.mem u).A.T : D.host.E)⁻¹ • (y : (D.sp.X i).V)}) ∧
      (∀ (z : Ld D u i ((D.fm u).up i v c (pr i v c y)))
        (hz : ((D.mem u).A.T : D.host.E) • (upG i v c y).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v _ (pr i v _ z) = (D.fm u).fv i v c (pr i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : Ld D u i ((D.fm u).up i v c (pr i v c y)))
        (hz : (upG i v c y).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v' _ (pr i v' _ z) = (D.fm u).fv i v' c (pr i v' c ⟨_, hz⟩))
  dnG : ∀ i v (c : (D.mem u).C.cls i), Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) → GX D i

  dn_tie : ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    haveI := (Pv_max v).isPrime
    SameOff (Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (D.clsLat u i ((D.fm u).dn i v c g))) (D.clsLat u i c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (Pv v) (Formalism.HermitianLatticesTheory.gmap (dnG i v c g).1 (Ld D u i ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Pv v) (D.clsLat u i c) ∧
      (∀ (z : Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ Lk D u (Pv v) i c),
        (D.fm u).fv i v _ (pr i v _ z) = g (prk i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : Ld D u i ((D.fm u).dn i v c g)) (hz : (dnG i v c g).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v' _ (pr i v' _ z) = (D.fm u).fv i v' c (pr i v' c ⟨_, hz⟩))
  dilG : ∀ i v, ((D.mem u).A.Fv v)ˣ → (D.mem u).C.cls i → GX D i

  dil_tie : ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ) c,
      Formalism.HermitianLatticesTheory.gmap (dilG i v a c).1 (D.clsLat u i ((D.fm u).dil i v a c)) = D.clsLat u i c ∧
      (∀ (z : Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v _ (pr i v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c (pr i v c ⟨_, hz⟩)) ∧
      (∀ v', v' ≠ v → ∀ (z : Ld D u i ((D.fm u).dil i v a c)) (hz : (dilG i v a c).1 (z : (D.sp.X i).V) ∈ Ld D u i c),
        (D.fm u).fv i v' _ (pr i v' _ z) = (D.fm u).fv i v' c (pr i v' c ⟨_, hz⟩))

  lattice₂ : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V

  levP : StepLevel0 D.sp.cm D.sp.X' D.host.g (crdLat D.sp.X' D.sp.X'.L0)

  clsP : ClassTie D.sp.cm D.sp.X' (crdLat D.sp.X' D.sp.X'.L0) levP.U (D.fm u).stabilizer₂ lattice₂

  z0 : (D.sp.X D.R.m).V
  cocycle_zero_mem_invariants : z0 ∈ Submodule.span D.host.E {D.sp.z}
  hermitianForm_lastCoordinateUniformizerVector_self : (D.sp.X D.R.m).hT z0 z0 = ((D.mem u).A.T : D.host.E)
  tilG : (D.fm u).clsP → GX D D.R.m

  til_tie : ∀ c : (D.fm u).clsP,
    Formalism.HermitianLatticesTheory.gmap (tilG c).1 (D.clsLat u D.R.m ((D.fm u).til c)) =
      (lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0} ∧
    ∀ v (z : Ld D u D.R.m ((D.fm u).til c)) (a : 𝓞 D.host.E),
      (a : D.host.E) = (D.sp.X D.R.m).hT z0 ((tilG c).1 (z : (D.sp.X D.R.m).V)) →
      (D.fm u).fv D.R.m v _ (pr D.R.m v _ z) = res v a

def Lev0Tied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ u, ColLevelX (H.lev0 u) (fun x => x ∈ D.host.K) (aT u).piU (H.vT u)
    (fun v c z => (D.fm u).fv 0 v c ((aT u).pr 0 v c z))

def Ad0 (D : ColRec) (H : HermCols D) (u : D.what₂.Word) (c c' : (D.mem u).C.cls 0) (γ : GX D 0)
    (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y c')
    (toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) γ.1) (H.vT u v).1

def AdI (D : ColRec) (H : HermCols D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m)
    (c c' : (D.mem u).C.cls i) (γ : GX D i) (v : (D.mem u).A.vT) : Prop :=
  AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c) ((H.cls u i h1 hm).y c')
    (toGLb (D.sp.X i).frame γ.1) (H.vT u v).1

structure AdTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop where
  up0 : ∀ u v c (y : Ld D u 0 c), (D.fm u).fv 0 v c ((aT u).pr 0 v c y) = 1 →
    Ad0 D H u c ((D.fm u).up 0 v c ((aT u).pr 0 v c y)) ((aT u).upG 0 v c y) v
  upI : ∀ u i h1 hm v c (y : Ld D u i c), (D.fm u).fv i v c ((aT u).pr i v c y) = 1 →
    AdI D H u i h1 hm c ((D.fm u).up i v c ((aT u).pr i v c y)) ((aT u).upG i v c y) v
  dn0 : ∀ u v c g, g ≠ 0 → Ad0 D H u c ((D.fm u).dn 0 v c g) ((aT u).dnG 0 v c g) v
  dnI : ∀ u i h1 hm v c g, g ≠ 0 → AdI D H u i h1 hm c ((D.fm u).dn i v c g) ((aT u).dnG i v c g) v
  dil0 : ∀ u v a c, Ad0 D H u c ((D.fm u).dil 0 v a c) ((aT u).dilG 0 v a c) v
  dilI : ∀ u i h1 hm v a c, AdI D H u i h1 hm c ((D.fm u).dil i v a c) ((aT u).dilG i v a c) v

def CofTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ u, D.cOf u * ((aT u).piU : D.host.E) = ((aT D.u₀).piU : D.host.E)

def PiGConst (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (X : Lev0Tied D H aT) : Prop :=
  ∀ u u', (X u).piG = (X u').piG

def stabPLin (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (u : D.what₂.Word)
    (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c) : D.sp.X'.V ≃ₗ[D.host.E] D.sp.X'.V :=
  (toGLb D.sp.X'.frame).symm ((aT u).clsP.stabI c s : GL (Fin D.sp.X'.rank) D.host.E)

def stabMLin (D : ColRec) (H : HermCols D) (u : D.what₂.Word) (h1 : 1 ≤ D.R.m)
    (c : (D.mem u).C.cls D.R.m) (s : (D.mem u).C.stab D.R.m c) :
    (D.sp.X D.R.m).V ≃ₗ[D.host.E] (D.sp.X D.R.m).V :=
  (toGLb (D.sp.X D.R.m).frame).symm
    ((H.cls u D.R.m h1 le_rfl).stabI c s : GL (Fin (D.sp.X D.R.m).rank) D.host.E)

def StabMapTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (h1 : 1 ≤ D.R.m) (c : (D.fm u).clsP) (s : (D.fm u).stabilizer₂ c),
    (∀ x : D.sp.X'.V,
      ((aT u).tilG c).1 (stabMLin D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (D.sp.iX' x))) =
        D.sp.iX' (stabPLin D H aT u c s x)) ∧
    ((aT u).tilG c).1 (stabMLin D H u h1 _ ((D.fm u).stabMap c s) (((aT u).tilG c).1.symm (aT u).z0)) = (aT u).z0

def FvStepTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Type :=
  ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT),
    FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 hm).Lb (H.cls u i h1 hm).y (D.clsLat u i) (H.vT u v).1
      ((D.mem u).A.Fv v) (fun c z => (D.fm u).fv i v c ((aT u).pr i v c z))

def StdTied (D : ColRec) : Prop :=
  (∀ i, i ≤ D.R.m → IsStd (D.sp.X i)) ∧ IsStd D.sp.X'

def BaseTied (D : ColRec) (H : HermCols D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) : Prop :=
  ∀ (u : D.what₂.Word) (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj ((aT u).piU : D.host.E) →
    ((H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 D.host.E)
        (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0) ∧
    ∀ (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m),
      (H.lev u i h1 hm).Lb ⊔ Ideal.span {pb} • dualL D.sp.cm (D.sp.X i) (H.lev u i h1 hm).Lb =
        crdLat (D.sp.X i) (D.sp.X i).L0

structure ColsHerm (D : ColRec) where
  base : HermCols D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  levelZeroCompatibility : Lev0Tied D base atT
  ad : AdTied D base atT
  cof : CofTied D base atT
  piG : PiGConst D base atT levelZeroCompatibility
  stabMap : StabMapTied D base atT
  fvI : FvStepTied D base atT
  std : StdTied D
  baseL : BaseTied D base atT

end Formalism.L2.Col.CH

end
