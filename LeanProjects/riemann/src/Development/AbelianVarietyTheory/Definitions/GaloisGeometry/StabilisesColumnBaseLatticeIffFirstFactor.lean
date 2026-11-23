import Mathlib
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.ClsSEqIffExistsLevCSmul
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitStab
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SelfDualPI
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CompanionOfBaseTied
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex

noncomputable section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.L2 Formalism.L2.G Formalism.MainNotions.G.KAat

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
  {I : LocId L p nV W Qq} {N : ℕ}

theorem pairInt_of_mem_dualL (hc : CMData F E) (S : HSpace E)
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) {b : Fin S.rank → E} (hb : b ∈ Formalism.L2.Herm.dualL hc S Λ) :
    ∀ a ∈ Λ, hform (hc.sig : E →+* E) S.gram a b ∈ (algebraMap (𝓞 E) E).range := by
  intro a ha
  unfold Formalism.L2.Herm.dualL at hb
  induction hb using Submodule.span_induction with
  | mem b hb => exact hb a ha
  | zero => rw [Formalism.UG.P.csScale_hform_zero_right]; exact zero_mem _
  | add b b' _ _ h h' => rw [Formalism.UG.P.csScale_hform_add_right]; exact add_mem h h'
  | smul r b _ h =>
    rw [← algebraMap_smul E r b, Formalism.UG.P.csScale_hform_smul_right]
    exact mul_mem ⟨r, rfl⟩ h

theorem selfDualAt_stepLevelQ {S : HSpace E} {gp' : Fin 2 → ℕ} {T f : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 F))}
    (hc : CMData F E) (X : Formalism.L2.Herm.StepLevelQ hc S gp' T f Q) (v : HeightOneSpectrum (𝓞 F)) (hT : (T : 𝓞 F) ∉ v.asIdeal) :
    SelfDualAt hc.sig S.gram v X.Lb :=
  self_dual_lattice_at F E S.rank hc.sig S.gram v X.Lb T X.Lb_fin
    (fun x hx _y hy => pairInt_of_mem_dualL hc S X.Lb (X.Lb_int hy) x hx)
    (fun y hy => X.Lb_dual y (Submodule.subset_span hy)) hT

end GlobalTheory.Port
end
section

namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.L2 Formalism.L2.G Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}
  (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)

set_option maxHeartbeats 2000000 in

theorem stab_iff (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hdual : SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' Lb)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' Lb ↔
    (∀ a b, (((t.fr w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom) x * t.fr w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((t.fr w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom) x * t.fr w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X.g u w hg).spl w' h) Lb (t.fr w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X.g u w hg).spl w' h) Lb (t.fr w' h)
      (fun y => (X.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X.g u w hg).spl w' h) ((X.g u w hg).spl_alg w' h)) hdual
      (fun s => t.fr_lat w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

theorem levelVL_le (w' : HeightOneSpectrum (𝓞 D.host.F)) :
    levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' Lb ≤ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F) :=
  fun _ hx => hx.1

theorem hypTJC_of_le
    (hU : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      Uloc w' ≤ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' Lb)
    (hdual : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' Lb) : HypTJC t :=
  fun w' h x hx => (stab_iff t w' h (hdual w' h) x (levelVL_le w' (hU w' h hx))).1 (hU w' h hx)

theorem hypTJ_of_ge
    (hU : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' Lb ≤ Uloc w')
    (hdual : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' Lb) : HypTJ t :=
  fun w' h x hx h1 h2 => hU w' h ((stab_iff t w' h (hdual w' h) x hx).2 ⟨h1, h2⟩)

theorem T_not_mem {p T : ℕ} (hp : p.Prime) (hT : ¬ p ∣ T) (w' : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((p : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) : (T : 𝓞 D.host.F) ∉ w'.asIdeal :=
  fun hT' => not_mem_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hT) _ hT' h

section Q

variable {gp : Fin 2 → ℕ} {f : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 D.host.F))}
  (S : Formalism.L2.Herm.StepLevelQ D.sp.cm (D.sp.X (i + 1)) gp (D.mem u).A.T f Q)

theorem hypTJC_stepLevelQ (hLb : Lb = S.Lb) (hUl : Uloc = S.Uloc) : HypTJC t := by
  subst hLb hUl
  exact hypTJC_of_le t (fun w' _ => S.Uloc_lev w')
    (fun w' h => selfDualAt_stepLevelQ D.sp.cm S w' (T_not_mem hg.1 hg.2.2.2.2.2 w' h))

theorem hypTJ_stepLevelQ (hLb : Lb = S.Lb) (hUl : Uloc = S.Uloc) (hgp : ∀ a, ¬ D.what₂.places.resChar w ∣ gp a)
    (hQ : ∀ w' ∈ Q, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal) : HypTJ t := by
  subst hLb hUl
  exact hypTJ_of_ge t
    (fun w' h => (S.Uloc_hyp w' (T_not_mem hg.1 (hgp 0) w' h) (T_not_mem hg.1 (hgp 1) w' h)
      (T_not_mem hg.1 hg.2.2.2.2.2 w' h) (fun hq => hQ w' hq h)).ge)
    (fun w' h => selfDualAt_stepLevelQ D.sp.cm S w' (T_not_mem hg.1 hg.2.2.2.2.2 w' h))

end Q

section Mem

variable {gp : Fin 2 → ℕ} {f : ℕ} (S : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X (i + 1)) gp (D.mem u).A.T f)

end Mem

end GlobalTheory.Port
end
section

namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.L2 Formalism.L2.G Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

def HypTC {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (x : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)),
    x ∈ L.Uloc w →
    (∀ a b, (((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F) ∧
    (∀ a b, ((((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h)⁻¹ : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F)

end Gen

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D) (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u)
  (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)

set_option maxHeartbeats 4000000 in
include hU in

theorem away_of_off (c c' : (D.gat u w hg).comp) (δ : GL (Fin (D.R.N 0)) D.host.E)
    (hδ : δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (hoff : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal →
      bc (prV (E := D.host.E) w') (((locAt X u w hg B).yG c')⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (locAt X u w hg B).yG c) ∈ ((T u).cls0).lev.Uloc w') :
    (reGL (rank_eq_first_level D.R) D.host.E).symm δ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ∧
    (((X.g u w hg).yG c').1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((reGL (rank_eq_first_level D.R) D.host.E).symm δ) * ((X.g u w hg).yG c).1 ∈ Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w) := by
  have hδ0 : (reGL (rank_eq_first_level D.R) D.host.E).symm δ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 :=
    reGL_symm_mem_UJ (rank_eq_first_level D.R) _ _ _ (gramN_zero D) δ hδ
  refine ⟨hδ0, ?_⟩
  have eδ : δ = reGL (rank_eq_first_level D.R) D.host.E ((reGL (rank_eq_first_level D.R) D.host.E).symm δ) := (MulEquiv.apply_symm_apply _ _).symm
  set δ0 := (reGL (rank_eq_first_level D.R) D.host.E).symm δ with hδ0def
  rw [mem_awayP_iff]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((X.g u w hg).yG c').2) (bc_mem hδ0)) ((X.g u w hg).yG c).2,
    fun w' hw' => ?_⟩
  have h1 := hoff w' hw'
  have e1 : ((locAt X u w hg B).yG c')⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ *
      (locAt X u w hg B).yG c = reGL (rank_eq_first_level D.R) _ ((((X.g u w hg).yG c').1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ0 * ((X.g u w hg).yG c).1) := by
    rw [eδ, map_mul, map_mul, map_inv, ← bc_reGL]
    rfl
  rw [e1, bc_reGL, hU w'] at h1
  exact (Subgroup.mem_map_iff_mem (f := (reGL (rank_eq_first_level D.R) _).toMonoidHom) (reGL (rank_eq_first_level D.R) _).injective).1 h1

theorem gamI_inj_locAt (c : (D.gat u w hg).comp) : Function.Injective ((locAt X u w hg B).gamI c) := by
  intro a b hab
  apply (X.g u w hg).gamI_inj c
  apply Subtype.ext
  exact (reGL (rank_eq_first_level D.R) D.host.E).injective hab

set_option maxHeartbeats 4000000 in
include hU in
theorem gamOnto_locAt (c : (D.gat u w hg).comp) : GamOnto ((T u).cls0).lev (locAt X u w hg B) c := by
  intro δ hδ hoff
  obtain ⟨hδ0, hz⟩ := away_of_off X T u hU w hg B c c δ hδ hoff
  obtain ⟨γ, hγ⟩ := ((X.g u w hg).gamI_range c ⟨_, hδ0⟩).2 ((mem_map_conj _ _ _).2 hz)
  refine ⟨γ, ?_⟩
  show reGL (rank_eq_first_level D.R) D.host.E ((X.g u w hg).gamI c γ).1 = δ
  rw [hγ]
  exact MulEquiv.apply_symm_apply _ _

set_option maxHeartbeats 4000000 in
include hU in
theorem compInj_locAt : CompInj ((T u).cls0).lev (locAt X u w hg B) := by
  intro c c' δ hδ hoff
  obtain ⟨hδ0, hz⟩ := away_of_off X T u hU w hg B c c' δ hδ hoff
  apply (X.g u w hg).yG_bij.1
  have hz' := Subgroup.inv_mem _ hz
  refine (DoubleCoset.eq _ _ _ _).2 ⟨⟨_, bc_mem hδ0⟩, Subgroup.mem_subgroupOf.2 ⟨_, hδ0, rfl⟩,
    ⟨_, ((mem_awayP_iff _ _ _).1 hz').1⟩, Subgroup.mem_subgroupOf.2 hz', Subtype.ext ?_⟩
  show ((X.g u w hg).yG c').1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((reGL (rank_eq_first_level D.R) D.host.E).symm δ) * ((X.g u w hg).yG c).1 *
    ((((X.g u w hg).yG c').1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((reGL (rank_eq_first_level D.R) D.host.E).symm δ) * ((X.g u w hg).yG c).1)⁻¹
  group

set_option maxHeartbeats 4000000 in
include hU in
theorem locHypC_locAt (hB : FrRat X u w hg B) (hTc : HypTC (X.g u w hg)) : LocHypC ((T u).cls0).lev (locAt X u w hg B) := by
  refine locHypC_of (rank_eq_first_level D.R) (locAt X u w hg B) _ B rfl (fun v => (X.lev0 u).Uloc v) hU ?_
  intro v x0 hx0
  have hfr := hB _ ((X.g u w hg).pl v).2
  obtain ⟨h1, h2⟩ := hTc _ ((X.g u w hg).pl v).2 x0 hx0
  rw [hfr] at h1 h2
  exact ⟨h1, h2⟩

set_option maxHeartbeats 4000000 in
include hU in

theorem oneHyp_locAt (hB : FrRat X u w hg B) (hT : HypT (X.g u w hg)) (hTc : HypTC (X.g u w hg)) :
    OneHyp ((T u).cls0).toChart.lev (locAt X u w hg B) ((T u).cls0).toChart.y where
  y_bij := ((T u).cls0).y_bij
  good := locGood_locAt X u w hg B
  int := locInt_locAt X u w hg B
  hypP := locHyp_locAt X T u hU w hg B hB hT
  hypC := locHypC_locAt X T u hU w hg B hB hTc
  bad_p := bad_notOver u w hg
  actB := locAt_actB u w hg B hB
  comp := fun x => by
    obtain ⟨i, γ, k, hγ, hk, hkU, e⟩ := comp_re (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) (X.g u w hg).yG
      (Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w)) (X.g u w hg).yG_bij.2 x
    refine ⟨i, γ, reGL (rank_eq_first_level D.R) _ k, hγ, reGL_mem_UPts (rank_eq_first_level D.R) D.sp.cm.sig D.sp.gram0 _ (gramN_zero D) _ _ hkU, e,
      fun w' hw' => ?_⟩
    rw [bc_reGL]
    show _ ∈ ((T u).cls0).lev.Uloc w'
    rw [hU w']
    exact Subgroup.mem_map.2 ⟨_, ((mem_awayP_iff _ _ k).1 hk).2 w' hw', rfl⟩
  gam := fun i γ => by
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
    rw [bc_reGL]
    show _ ∈ ((T u).cls0).lev.Uloc w'
    rw [hU w']
    exact Subgroup.mem_map.2 ⟨_, h3 w' hw', rfl⟩
  gamU := locAt_UJ u w hg B
  inj := gamI_inj_locAt X u w hg B
  onto := gamOnto_locAt X T u hU w hg B
  cinj := compInj_locAt X T u hU w hg B

end GlobalTheory.Port
end
section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}
    {L : ColLevel R F E sp gp C A clsLat}

theorem selfDualAt_col (L : ColLevel R F E sp gp C A clsLat) (v : HeightOneSpectrum (𝓞 F)) (hT : ((A.T : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    SelfDualAt sp.cm.sig sp.gram0 v L.Lb :=
  self_dual_lattice_at F E R.k sp.cm.sig sp.gram0 v L.Lb A.T L.Lb_fin (fun x hx y hy => L.Lb_int y hy x hx) (fun y hy => L.Lb_dual y hy) hT

variable (t : Formalism.L2.Herm.GLevTie L G)

set_option maxHeartbeats 2000000 in

theorem stabilises_columnBaseLattice_iff_firstFactor (w : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (hdual : SelfDualAt sp.cm.sig sp.gram0 w L.Lb)
    (x : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)) (hx : x ∈ UPts sp.cm.sig sp.gram0 (w.adicCompletion F)) :
    x ∈ levelVL sp.cm.sig sp.gram0 w L.Lb ↔
    (∀ a b, (((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F) ∧
    (∀ a b, ((((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h)⁻¹ : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F) := by
  have hs : SplitStabL sp.cm.sig sp.gram0 w (t.spl w h) L.Lb (t.fr w h) :=
    splitStabL_of sp.cm.sig sp.gram0 w (t.spl w h) L.Lb (t.fr w h) (fun y => t.spl_sig w h y)
      (split_integral_completion F E w (t.spl w h) (t.spl_alg w h)) hdual (fun s => t.fr_lat w h s)
  have key : ∀ y : w.adicCompletion F,
      y ∈ (algebraMap (w.adicCompletionIntegers F) (w.adicCompletion F)).range ↔ y ∈ w.adicCompletionIntegers F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective F w)]
  simp only [key]

theorem hypTC_col (hT : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → ((A.T : ℕ) : 𝓞 F) ∉ w.asIdeal) : HypTC t :=
  fun w h x hx => (stabilises_columnBaseLattice_iff_firstFactor t w h (selfDualAt_col L w (hT w h)) x (L.Uloc_le w hx)).1 (L.Uloc_lev w hx)

theorem hypT_col (hT : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → ((A.T : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (hgp : ∀ a (w : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → ((gp a : ℕ) : 𝓞 F) ∉ w.asIdeal) : HypT t :=
  fun w h x hx h1 h2 => by
    rw [L.Uloc_hyp w (hgp 0 w h) (hgp 1 w h) (hT w h)]
    exact (stabilises_columnBaseLattice_iff_firstFactor t w h (selfDualAt_col L w (hT w h)) x hx).2 ⟨h1, h2⟩

end Gen

section Rec

variable {D : D7}

theorem nat_not_mem {p n : ℕ} (hp : p.Prime) (hn : ¬ p ∣ n) (w' : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((p : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) : (n : 𝓞 D.host.F) ∉ w'.asIdeal :=
  fun hn' => not_mem_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hn) _ hn' h

theorem not_dvd_g {u : D.what₂.Word} {w : D.what₂.places.Pl} (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (a : Fin 2) :
    ¬ D.what₂.places.resChar w ∣ D.host.g a := fun hd =>
  hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hg.1 (D.host.g_prime a)).1 hd) ▸ D.host.g_level a)

variable (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

theorem hypTC_rec : HypTC (X.g u w hg) := hypTC_col _ (fun w' h => nat_not_mem hg.1 hg.2.2.2.2.2 w' h)

theorem hypT_rec : HypT (X.g u w hg) :=
  hypT_col _ (fun w' h => nat_not_mem hg.1 hg.2.2.2.2.2 w' h) (fun a w' h => nat_not_mem hg.1 (not_dvd_g hg a) w' h)

variable {X} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {c : LatCmp D}

theorem oneHyp_rec (K : CmpTied D X T Gt c) (hJ : Joint0 X.lev0 u (T u)) :
    OneHyp ((T u).cls0).toChart.lev (locAt X u w hg K.B) ((T u).cls0).toChart.y :=
  oneHyp_locAt X T u (sameUloc_of_joint X T u hJ) w hg K.B (K.fr_B u w hg) (hypT_rec X u w hg) (hypTC_rec X u w hg)

end Rec

section Top

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Dx cX}

end Top

end GlobalTheory.Port

end

end
