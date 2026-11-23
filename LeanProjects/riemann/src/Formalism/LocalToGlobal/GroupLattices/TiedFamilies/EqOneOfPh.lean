import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NatActRVtupR
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.FramesTr
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmApply
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.JPMemAwayP
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p}

structure LocGood (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (A : LocAt F E n G) : Prop where
  herm : IsHerm (σ : E →+* E) J
  det : IsUnit J.det
  sig : ∀ v x, A.spl v (sigR σ ((A.pl v).1.adicCompletion F) x) = swapR _ (A.spl v x)
  yG_mem : ∀ i, A.yG i ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)
  yG_p : ∀ i v, bc (prV (E := E) (A.pl v).1) (A.yG i) = 1

namespace LocGood

variable {A : LocAt F E n G} (H : LocGood σ J A)

theorem pl_inj (A : LocAt F E n G) : Function.Injective fun v => (A.pl v).1 :=
  fun _ _ h => A.pl.injective (Subtype.ext h)

def uGL (v : Fin G.P.nV) : UPts σ J ((A.pl v).1.adicCompletion F) ≃* GL (Fin n) ((A.pl v).1.adicCompletion F) :=
  locGL σ J H.herm H.det _ (A.spl v) (H.sig v)

theorem uGL_apply (v : Fin G.P.nV) (X : UPts σ J ((A.pl v).1.adicCompletion F)) :
    H.uGL v X = bc (A.ph v) (X : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) :=
  locGL_apply σ J H.herm H.det _ (A.spl v) (H.sig v) X

def sec (X : ∀ v : Fin G.P.nV, GL (Fin n) ((A.pl v).1.adicCompletion F)) : UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
  secAll F E σ J (fun v => (A.pl v).1) (pl_inj A) fun v => (H.uGL v).symm (X v)

theorem sec_at (X : ∀ v : Fin G.P.nV, GL (Fin n) ((A.pl v).1.adicCompletion F)) (v : Fin G.P.nV) :
    bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (H.sec X : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) = X v := by
  have h1 := bc_secAll_same F E σ J (fun v => (A.pl v).1) (pl_inj A) v fun v => (H.uGL v).symm (X v)
  have h2 : bc (prV (E := E) (A.pl v).1) (H.sec X : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      ((H.uGL v).symm (X v) : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) := h1
  rw [h2, ← H.uGL_apply, MulEquiv.apply_symm_apply]

theorem sec_off (X : ∀ v : Fin G.P.nV, GL (Fin n) ((A.pl v).1.adicCompletion F)) (w : HeightOneSpectrum (𝓞 F))
    (hw : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    bc (prV (E := E) w) (H.sec X : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 :=
  bc_secAll_off F E σ J (fun v => (A.pl v).1) (pl_inj A) w (fun v h => hw (h ▸ (A.pl v).2)) _

include H in

theorem eq_one_of_ph (v : Fin G.P.nV) (x : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F))
    (hx : x ∈ UPts σ J ((A.pl v).1.adicCompletion F)) (h1 : bc (A.ph v) x = 1) : x = 1 := by
  have h2 : H.uGL v ⟨x, hx⟩ = 1 := by rw [H.uGL_apply]; exact h1
  have h3 : (⟨x, hx⟩ : UPts σ J ((A.pl v).1.adicCompletion F)) = 1 := (MulEquiv.map_eq_one_iff _).1 h2
  exact congrArg Subtype.val h3

theorem exists_pl (A : LocAt F E n G) (w : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ v, (A.pl v).1 = w := ⟨A.pl.symm ⟨w, hw⟩, by simp⟩

def ff (A : LocAt F E n G) (a : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ∀ v : Fin G.P.nV, GL (Fin n) ((A.pl v).1.adicCompletion F) :=
  fun v => bc (A.ph v) (bc (prV (E := E) (A.pl v).1) a)

theorem away_at (a : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (ha : a ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Fin G.P.nV) :
    bc (prV (E := E) (A.pl v).1) (((H.sec (ff A a) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ * a) = 1 := by
  apply H.eq_one_of_ph v
  · exact Formalism.UG.P.afsplit_bc_mem σ J (A.pl v).1 _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (H.sec (ff A a)).2) ha)
  · rw [map_mul, map_mul, map_inv, map_inv, H.sec_at]
    exact inv_mul_cancel _

theorem away_off (a : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (w : HeightOneSpectrum (𝓞 F))
    (hw : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    bc (prV (E := E) w) (((H.sec (ff A a) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ * a) =
      bc (prV (E := E) w) a := by
  rw [map_mul, map_inv, H.sec_off _ w hw, inv_one, one_mul]

theorem away_mem (S : StepLevel F E σ J T f bad) (a : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (ha : a ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (haw : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) a ∈ S.Uloc w) :
    ((H.sec (ff A a) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ * a ∈ S.U := by
  rw [S.U_eq]
  refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (H.sec (ff A a)).2) ha, fun w => ?_⟩
  by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
  · obtain ⟨v, rfl⟩ := exists_pl A w hw
    rw [H.away_at a ha v]
    exact Subgroup.one_mem _
  · rw [H.away_off a w hw]
    exact haw w hw

theorem isPt_sec (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    A.IsPt i g (A.yG i * (H.sec (fun v => bc (A.phE v) A.B *
      bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v)) * (bc (A.phE v) A.B)⁻¹) :
        GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) := by
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · rw [map_mul, H.sec_off _ w hw, mul_one]
  · rw [map_mul, H.yG_p, one_mul, H.sec_at]

theorem exists_bases (A : LocAt F E n G) (X : ∀ v : Fin G.P.nV, GL (Fin n) ((A.pl v).1.adicCompletion F)) :
    ∃ g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v), ∀ v, bc (A.phE v) A.B *
      bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v)) * (bc (A.phE v) A.B)⁻¹ = X v := by
  refine ⟨fun v => (castGL A.rk (G.P.Qq v)).symm ((bcE (A.eQ v)).symm ((bc (A.phE v) A.B)⁻¹ * X v * bc (A.phE v) A.B)), fun v => ?_⟩
  have h1 : bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v)
      ((castGL A.rk (G.P.Qq v)).symm ((bcE (A.eQ v)).symm ((bc (A.phE v) A.B)⁻¹ * X v * bc (A.phE v) A.B)))) =
      (bc (A.phE v) A.B)⁻¹ * X v * bc (A.phE v) A.B := by
    rw [MulEquiv.apply_symm_apply]
    exact (bcE (A.eQ v)).apply_symm_apply _
  rw [h1]
  group

end LocGood

variable {cls : Type} {A : LocAt F E n G}

theorem ptEx_of (H : LocGood σ J A) (S : StepLevel F E σ J T f bad) (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hs : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S))) : PtEx S G A yc := by
  intro i g
  set x : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨A.yG i, H.yG_mem i⟩ * H.sec (fun v => bc (A.phE v) A.B *
      bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) (g v)) * (bc (A.phE v) A.B)⁻¹) with hx
  obtain ⟨c, hc⟩ := hs (Quotient.mk'' x)
  obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq _ _ (yc c) x).1 hc
  obtain ⟨γ, hγ, eγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hh)
  refine ⟨c, γ, ⟨k.1, Subgroup.mem_subgroupOf.1 hk⟩, hγ, ?_⟩
  have e2 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * k.1 = x.1 := by
    rw [eγ, e]; rfl
  rw [e2]
  exact H.isPt_sec i g

theorem ptAll_of (H : LocGood σ J A) (S : StepLevel F E σ J T f bad) (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hcomp : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ (i : G.comp) (γ : GL (Fin n) E)
      (a : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), γ ∈ UJ (σ : E →+* E) J ∧ a ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * A.yG i * a ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) a ∈ S.Uloc w) : PtAll S G A yc := by
  intro c
  obtain ⟨i, γ, a, hγ, ha, e, haw⟩ := hcomp (yc c)
  obtain ⟨g, hg⟩ := LocGood.exists_bases A (LocGood.ff A a)
  have hκ := S.U.inv_mem (H.away_mem S a ha haw)
  refine ⟨i, g, γ⁻¹, ⟨_, hκ⟩, Subgroup.inv_mem _ hγ, ?_⟩
  have e2 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ⁻¹ * (yc c).1 *
      (((H.sec (LocGood.ff A a) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))⁻¹ * a)⁻¹ =
      A.yG i * (H.sec (LocGood.ff A a) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    rw [e, map_inv]; group
  rw [e2]
  have := H.isPt_sec i g
  rwa [funext hg] at this

theorem awayEx_of (H : LocGood σ J A) (S : StepLevel F E σ J T f bad)
    (hΓ : ∀ i (γ : (G.lev i).Γ), (A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i ∈
        UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w)
        ((A.yG i)⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * A.yG i) ∈ S.Uloc w)
    (i : G.comp) (γ : (G.lev i).Γ) : ∃ κ : S.U, A.IsAway i γ κ.1 :=
  ⟨⟨_, H.away_mem S _ (hΓ i γ).1 (hΓ i γ).2⟩, fun v => H.away_at _ (hΓ i γ).1 v, fun w hw => H.away_off _ w hw⟩

end Formalism.L2.G
