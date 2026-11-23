import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.ComplSmulMapENe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

section Local

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

theorem exists_locGL (σE : E →ₐ[F] E) (J : Matrix n n E) (hJ : IsHerm (σE : E →+* E) J) (hdet : IsUnit J.det)
    (R' : Type) [CommRing R'] [Algebra F R'] (φ : E ⊗[F] R' ≃+* R' × R')
    (hφ : ∀ x, φ (sigR σE R' x) = swapR R' (φ x)) :
    ∃ e : UPts σE J R' ≃* GL n R', ∀ X, e X = bc ((RingHom.fst R' R').comp φ.toRingHom) (X : GL n (E ⊗[F] R')) := by
  set ρ : E →+* R' × R' := (φ : E ⊗[F] R' →+* R' × R').comp (inclE (F := F) R') with hρ
  set J1 : Matrix n n R' := J.map ((RingHom.fst R' R').comp ρ) with hJ1
  have hsw : ∀ x : E, ρ (σE x) = swapR R' (ρ x) := by
    intro x
    have h0 := hφ (inclE (F := F) R' x)
    show φ ((σE x) ⊗ₜ[F] (1 : R')) = swapR R' (φ (inclE (F := F) R' x))
    rw [← h0]
    show φ ((σE x) ⊗ₜ[F] (1 : R')) = φ ((Algebra.TensorProduct.map σE (AlgHom.id F R')) (x ⊗ₜ[F] (1 : R')))
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hJs : J.map ρ = splitJ J1 := by
    ext a b
    · rfl
    · have h1 : σE (J b a) = J a b := by
        have := congrFun (congrFun hJ a) b
        simpa [cT] using this
      show (ρ (J a b)).2 = (ρ (J b a)).1
      rw [← h1, hsw]
      rfl
  have hd1 : IsUnit J1.det := by
    rw [hJ1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hsp : ∃ e : UPts σE J R' ≃* UJ (swapR R') (splitJ J1),
      ∀ g, (e g : GL n (R' × R')) = bc (φ : E ⊗[F] R' →+* R' × R') g := by
    rw [← hJs]
    exact Formalism.UG.P.split_group_points F E n σE J R' φ hφ
  obtain ⟨e1, h1⟩ := hsp
  obtain ⟨e2, h2⟩ := Formalism.UG.P.split_unitary_group_iso R' n J1 hd1
  refine ⟨e1.trans e2, fun X => ?_⟩
  rw [MulEquiv.trans_apply, h2, h1]
  rfl

def locGL (σE : E →ₐ[F] E) (J : Matrix n n E) (hJ : IsHerm (σE : E →+* E) J) (hdet : IsUnit J.det)
    (R' : Type) [CommRing R'] [Algebra F R'] (φ : E ⊗[F] R' ≃+* R' × R')
    (hφ : ∀ x, φ (sigR σE R' x) = swapR R' (φ x)) : UPts σE J R' ≃* GL n R' :=
  Classical.choose (exists_locGL σE J hJ hdet R' φ hφ)

theorem locGL_apply (σE : E →ₐ[F] E) (J : Matrix n n E) (hJ : IsHerm (σE : E →+* E) J) (hdet : IsUnit J.det)
    (R' : Type) [CommRing R'] [Algebra F R'] (φ : E ⊗[F] R' ≃+* R' × R')
    (hφ : ∀ x, φ (sigR σE R' x) = swapR R' (φ x)) (X : UPts σE J R') :
    locGL σE J hJ hdet R' φ hφ X = bc ((RingHom.fst R' R').comp φ.toRingHom) (X : GL n (E ⊗[F] R')) :=
  Classical.choose_spec (exists_locGL σE J hJ hdet R' φ hφ) X

end Local

section AtP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

abbrev LocId.plc (I : LocId L p nV W Qq) (v : Fin nV) : HeightOneSpectrum (𝓞 F) := (I.pl v).1

theorem LocId.plc_inj (I : LocId L p nV W Qq) : Function.Injective I.plc :=
  fun _ _ h => I.pl.injective (Subtype.ext h)

def LocId.uGL (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (v : Fin nV) :
    UPts sp.cm.sig sp.gram0 ((I.plc v).adicCompletion F) ≃* GL (Fin R.k) ((I.plc v).adicCompletion F) :=
  locGL sp.cm.sig sp.gram0 sp.baseGram_isHermitian hdet _ (I.spl (I.plc v) (I.pl v).2) (I.spl_sig (I.plc v) (I.pl v).2)

def jP (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) :
    (∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) →* UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) :=
  (secAll F E sp.cm.sig sp.gram0 I.plc I.plc_inj).comp
    (Pi.monoidHom fun v => (I.uGL hdet v).symm.toMonoidHom.comp (Pi.evalMonoidHom _ v))

theorem jP_at (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det)
    (g : ∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) (v : Fin nV) :
    bc ((RingHom.fst _ _).comp (I.spl (I.plc v) (I.pl v).2).toRingHom)
      (bc (prV (E := E) (I.plc v)) (jP I hdet g : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) = g v := by
  show bc _ (bc (prV (E := E) (I.plc v)) (secAll F E sp.cm.sig sp.gram0 I.plc I.plc_inj _ : GL (Fin R.k) _)) = g v
  rw [bc_secAll_same]
  have := locGL_apply sp.cm.sig sp.gram0 sp.baseGram_isHermitian hdet _ (I.spl (I.plc v) (I.pl v).2)
    (I.spl_sig (I.plc v) (I.pl v).2) ((I.uGL hdet v).symm (g v))
  exact this.symm.trans ((I.uGL hdet v).apply_symm_apply (g v))

theorem jP_off (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det)
    (g : ∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) (w' : HeightOneSpectrum (𝓞 F))
    (hw : ((p : ℕ) : 𝓞 F) ∉ w'.asIdeal) :
    bc (prV (E := E) w') (jP I hdet g : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 :=
  bc_secAll_off F E sp.cm.sig sp.gram0 I.plc I.plc_inj w' (fun v h => hw (h ▸ (I.pl v).2)) _

theorem jP_mem_awayP (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det)
    (g : ∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) :
    (jP I hdet g : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ Formalism.L2.Herm.awayFrom₂ L p := by
  refine Subgroup.mem_inf.2 ⟨(jP I hdet g).2, ?_⟩
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
  intro v hv
  rw [jP_off I hdet g v hv]
  exact Subgroup.one_mem _

end AtP

end Formalism.L2.G
