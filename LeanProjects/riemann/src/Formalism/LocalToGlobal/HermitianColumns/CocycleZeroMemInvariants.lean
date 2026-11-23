import Formalism.LocalToGlobal.HermitianColumns.HermCols

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SameOff {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} (P : Ideal (𝓞 E))
    (A B : Submodule (𝓞 E) S.V) : Prop :=
  ∀ (q : Ideal (𝓞 E)) (hq : q.IsMaximal), q ≠ P → q ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := E) P →
    haveI := hq.isPrime
    Formalism.HermitianLatticesTheory.localization₂ q A = Formalism.HermitianLatticesTheory.localization₂ q B

section Abbr

variable (D : D7) (u : D.what₂.Word)

abbrev Ld (i : ℕ) (c : (D.mem u).C.cls i) : Submodule (𝓞 D.host.E) (D.sp.X i).V :=
  Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c)

abbrev GX (i : ℕ) : Subgroup ((D.sp.X i).V ≃ₗ[D.host.E] (D.sp.X i).V) := Formalism.HermitianLatticesTheory.isom (D.sp.X i).hT

abbrev Lk (P : Ideal (𝓞 D.host.E)) (i : ℕ) (c : (D.mem u).C.cls i) : Submodule (𝓞 D.host.E) (D.sp.X i).V :=
  D.clsLat u i c ⊔ P • Ld D u i c

end Abbr

set_option maxHeartbeats 4000000 in

structure AtT (D : D7) (u : D.what₂.Word)
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

structure AllTied (D : D7) where
  base : HermTied D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  vol : VolumeCompatible D

end Formalism.L2.Herm

end
