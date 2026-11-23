import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsOrb
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  apply Units.ext; ext x y; rfl

theorem bc_reGL {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : GL (Fin a) R) :
    bc φ (reGL h R g) = reGL h S (bc φ g) := by
  subst h
  rw [reGL_rfl, reGL_rfl]

theorem isHerm_re {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (σ : R →+* R) (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (hh : IsHerm σ J) :
    IsHerm σ J' := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this]; exact hh

theorem det_re {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (hh : IsUnit J.det) :
    IsUnit J'.det := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this]; exact hh

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_mem_UPts {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin a) (E ⊗[F] R)) (hg : g ∈ UPts σ J R) :
    reGL h _ g ∈ UPts σ J' R := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this, reGL_rfl]; exact hg

theorem comp_re {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    {ι : Type} (yG : ι → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (K : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hs : Function.Surjective (fun i => (Quotient.mk'' (yG i) : ClassSet
      ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))))))
    (x : UPts σ J' (FiniteAdeleRing (𝓞 F) F)) :
    ∃ (i : ι) (γ : GL (Fin b) E) (k : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), γ ∈ UJ (σ : E →+* E) J' ∧ k ∈ K ∧
      k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * reGL h _ (yG i).1 * reGL h _ k := by
  subst h
  obtain rfl : J' = J := by ext x y; exact hJ x y
  obtain ⟨i, hi⟩ := hs (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (DoubleCoset.eq _ _ (yG i) x).1 hi
  obtain ⟨γ, hγ, eγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  refine ⟨i, γ, k.1, hγ, Subgroup.mem_subgroupOf.1 hk, k.2, ?_⟩
  rw [reGL_rfl, reGL_rfl, eγ, e]; rfl

end Re

section Away

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem mem_awayP_iff (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (k : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    k ∈ Formalism.L2.Herm.awayFrom₂ L p ↔ k ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) k ∈ L.Uloc w := by
  unfold Formalism.L2.Herm.awayFrom₂
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]

end Away

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D)

set_option maxHeartbeats 4000000 in

theorem locGood_locAt (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) : LocGood (sigD D) (gramN D 0 (Nat.zero_le _)) (locAt X u w hg B) where
  herm := isHerm_re (rank_eq_first_level D.R) _ D.sp.gram0 _ (gramN_zero D) D.sp.baseGram_isHermitian
  det := det_re (rank_eq_first_level D.R) D.sp.gram0 _ (gramN_zero D) (isUnit_det_gram0 D.sp)
  sig := fun v x => (X.g u w hg).spl_sig _ ((X.g u w hg).pl v).2 x
  yG_mem := fun i => reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ ((X.g u w hg).yG i).2
  yG_p := fun i v => by
    have h1 := (X.g u w hg).yG_p i _ ((X.g u w hg).pl v).2
    have h2 := bc_reGL (rank_eq_first_level D.R) (prV (E := D.host.E) ((X.g u w hg).pl v).1) ((X.g u w hg).yG i).1
    rw [h1, map_one] at h2
    exact h2

set_option maxHeartbeats 4000000 in

theorem ptEx_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    PtEx ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) ((T u).cls0).y :=
  ptEx_of (locGood_locAt X u w hg B) _ _ ((T u).cls0).y_bij.2

def SameUloc (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) : Prop :=
  ∀ v, ((T u).cls0).lev.Uloc v = ((X.lev0 u).Uloc v).map (reGL (rank_eq_first_level D.R) _).toMonoidHom

theorem sameUloc_of_joint (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hJ : Joint0 X.lev0 u (T u)) :
    SameUloc X T u := hJ.Uloc_eq

set_option maxHeartbeats 4000000 in

theorem ptAll_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    PtAll ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) ((T u).cls0).y := by
  refine ptAll_of (locGood_locAt X u w hg B) _ _ fun x => ?_
  obtain ⟨i, γ, k, hγ, hk, hkU, e⟩ := comp_re (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) (X.g u w hg).yG
    (Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w)) (X.g u w hg).yG_bij.2 x
  refine ⟨i, γ, reGL (rank_eq_first_level D.R) _ k, hγ, reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ hkU, e,
    fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, ((mem_awayP_iff _ _ k).1 hk).2 w' hw', rfl⟩

set_option maxHeartbeats 4000000 in

theorem awayEx_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)
    (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) :
    ∃ κ : ((T u).cls0).lev.U, (locAt X u w hg B).IsAway i γ κ.1 := by
  refine awayEx_of (locGood_locAt X u w hg B) _ (fun i γ => ?_) i γ
  have h1 : (((X.g u w hg).yG i).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1 ∈ Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w) :=
    (mem_map_conj _ _ _).1 (((X.g u w hg).gamI_range i _).1 ⟨γ, rfl⟩)
  have e : ((locAt X u w hg B).yG i)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((locAt X u w hg B).gamI i γ) * (locAt X u w hg B).yG i = reGL (rank_eq_first_level D.R) _ ((((X.g u w hg).yG i).1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1) := by
    rw [map_mul, map_mul, map_inv, ← bc_reGL]
    rfl
  rw [e]
  obtain ⟨h2, h3⟩ := (mem_awayP_iff _ _ _).1 h1
  refine ⟨reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ h2, fun w' hw' => ?_⟩
  rw [bc_reGL, hU w']
  exact Subgroup.mem_map.2 ⟨_, h3 w' hw', rfl⟩

end Formalism.L2.G
