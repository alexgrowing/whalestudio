import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepAdmRec
import Formalism.LocalToGlobal.InertKernelTheory.ScalG
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepLt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.GlobalTheoryTheory.Comp
open scoped TensorProduct

namespace Formalism.L2.KerInert.AdmGA

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E]

def OK (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Lb : Submodule (𝓞 E) (Fin N → E))
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Prop :=
  Even N ∧ (∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co) ∧
    (∀ M : Submodule (𝓞 E) (Fin N → E), IsLat M → IsLat (dl sp.cm.sig J M)) ∧ IsLat Lb ∧
    IsLat (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb) ∧
    dl sp.cm.sig J (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb) = Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb ∧
    y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)

theorem reindex_refl' {N : ℕ} (J : Matrix (Fin N) (Fin N) E) :
    J.reindex (finCongr (rfl : N = N)) (finCongr (rfl : N = N)) = J := by
  ext i j
  simp [Matrix.reindex_apply]

theorem map_reE_refl {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Lb.map (((Formalism.L2.PairingIndexBounds.F.reE (E := E) (rfl : N = N) : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
      (Fin N → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E)) = Lb := by
  ext x
  show x ∈ Lb.map _ ↔ x ∈ Lb
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_refl {A : Type} [CommRing A] {N : ℕ} (y : GL (Fin N) A) :
    Formalism.L2.PairingIndexBounds.F.reGL (R := A) (finCongr (rfl : N = N)) y = y := by
  ext i j
  simp [Formalism.L2.PairingIndexBounds.F.reGL, Matrix.coe_reindexAlgEquiv]

theorem OK_re (sp : Spaces R F E) {N n : ℕ} (h : N = n) {J : Matrix (Fin N) (Fin N) E} {a : 𝓞 E}
    {Lb : Submodule (𝓞 E) (Fin N → E)} {y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hok : OK sp J a Lb y) :
    OK sp (J.reindex (finCongr h) (finCongr h)) a
      (Lb.map (((Formalism.L2.PairingIndexBounds.F.reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin n → E)) :
        (Fin N → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)))
      (Formalism.L2.PairingIndexBounds.F.reGL (R := E ⊗[F] FiniteAdeleRing (𝓞 F) F) (finCongr h) y) := by
  subst h
  rw [reindex_refl', map_reE_refl, reGL_refl]
  exact hok

theorem sd_of_OK (sp : Spaces R F E) {N n : ℕ} (h : N = n) {J : Matrix (Fin N) (Fin N) E} {a : 𝓞 E}
    {Lb : Submodule (𝓞 E) (Fin N → E)} {y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hok : OK sp J a Lb y)
    (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (dt : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) :
    Even n ∧ IsSDLat E n (Formalism.L2.PairingIndexBounds.F.PtD.re (F := F) h
      (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J
        (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb))) g dt).N := by
  obtain ⟨hev, hco, hJ, hLb, hM0, hsd, hy⟩ := hok
  exact ⟨h ▸ hev, Formalism.L2.KerInert.RepRec.isSD_re h
    (Formalism.L2.KerInert.RepRec.isSD_core (sp := sp) J hJ hco y hy hLb a rfl hM0 hsd) g dt⟩

end Gen

section Charts

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

def ChartOK (cp : ChartPts X D) (a : 𝓞 D.host.E) (j : ℕ) (La : X.Lt j) : Prop :=
  OK D.sp (cp.J j La) a (cp.Lb j La) (cp.y j La)

theorem kerN_sd (cp : ChartPts X D) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) (j : ℕ) (La : X.Lt j)
    (hok : ChartOK cp a j La) :
    Even ((X.Pj j).m + 1) ∧ IsSDLat D.host.E ((X.Pj j).m + 1) ((fdOfCharts cp a bad).kerN j La) :=
  sd_of_OK D.sp (cp.hk j La).symm hok (LinearEquiv.refl _ _) (Matrix.GeneralLinearGroup.det (cp.y j La))

theorem admissible_of_charts (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (cp : ChartPts X D) (a : 𝓞 D.host.E)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h0 : ∀ j (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ChartOK cp a j L0)
    (h1 : ∀ j (La' : X.Lt (j + 1)), (X.Pj (j + 1)).IsLatTup La'.2 → ChartOK cp a (j + 1) La') :
    Formalism.L2.KerInert.KG.AdmG X hfin D (fdOfCharts cp a bad) := by
  intro j L0 hL0 La' hLa'
  obtain ⟨e1, s1⟩ := kerN_sd cp a bad j L0 (h0 j L0 hL0)
  obtain ⟨e2, s2⟩ := kerN_sd cp a bad (j + 1) La' (h1 j La' hLa')
  exact ⟨e1, e2, s1, s2⟩

theorem admissible_of_charts_lattices (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (cp : ChartPts X D) (a : 𝓞 D.host.E)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h : ∀ j (La : X.Lt j), (X.Pj j).IsLatTup La.2 → ChartOK cp a j La) :
    Formalism.L2.KerInert.KG.AdmG X hfin D (fdOfCharts cp a bad) :=
  admissible_of_charts hfin cp a bad (fun j L0 hL0 => h j L0 (repOf_lat X.Lv hfin j L0 hL0)) (fun j La' hLa' => h (j + 1) La' hLa')

theorem admissible_small_of_charts (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (cp : ChartPts X D) (a : 𝓞 D.host.E)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h : ∀ j (La : X.Lt j), j ≤ X.mm → (X.Pj j).IsLatTup La.2 → ChartOK cp a j La) :
    Formalism.L2.KerInert.RepLt.AdmGLt X hfin D (fdOfCharts cp a bad) := by
  intro j hj L0 hL0 La' hLa'
  obtain ⟨e1, s1⟩ := kerN_sd cp a bad j L0 (h j L0 (Nat.le_of_lt hj) (repOf_lat X.Lv hfin j L0 hL0))
  obtain ⟨e2, s2⟩ := kerN_sd cp a bad (j + 1) La' (h (j + 1) La' hj hLa')
  exact ⟨e1, e2, s1, s2⟩

end Charts

section At

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ Formalism.L2.Forms
open Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)

section Unfold

variable {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem chAt_succ_J (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).J = (Formalism.L2.Forms.gramN D (i + 1) hi).reindex (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm) (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm) := by
  rw [chAt, dif_pos hi]

theorem chAt_succ_Lb (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).Lb = ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb.map
      (((reE (E := D.host.E) (n := ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) (by exact ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm) : _ ≃ₗ[D.host.E] _) :
        _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E)) := by
  rw [chAt, dif_pos hi]

set_option maxHeartbeats 400000 in
theorem chAt_succ_y (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).y = reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
      (Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
        (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (Formalism.L2.Forms.gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  rw [chAt, dif_pos hi]

theorem chAt_fill (i : ℕ) (hi : ¬ i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).J = 1 ∧
      (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).Lb = Submodule.span (𝓞 D.host.E) (Set.range fun k => Pi.single k (1 : D.host.E)) ∧
      (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).y = 1 := by
  rw [chAt, dif_neg hi]
  exact ⟨rfl, rfl, rfl⟩

end Unfold

def OrthTieAt (L0 : Lev0Data D u w h) : Prop :=
  (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) L0.J co) ∧
    ∀ i (hi : i + 1 ≤ D.R.m), ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D (i + 1) hi) co

def DualTieAt (L0 : Lev0Data D u w h) : Prop :=
  (∀ M : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E), IsLat M → IsLat (dl D.sp.cm.sig L0.J M)) ∧
    ∀ i (hi : i + 1 ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E)),
      IsLat M → IsLat (dl D.sp.cm.sig (Formalism.L2.Forms.gramN D (i + 1) hi) M)

def ATieAt (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) : Prop :=
  (IsLat L0.Lb ∧ IsLat (compan (sp := D.sp) L0.J a L0.Lb) ∧
      dl D.sp.cm.sig L0.J (compan (sp := D.sp) L0.J a L0.Lb) = compan (sp := D.sp) L0.J a L0.Lb) ∧
    ∀ i (hi : i + 1 ≤ D.R.m) (β : (I.at' i hi).st.Ch),
      IsLat ((I.at' i hi).st.K β).lev.Lb ∧
      IsLat (compan (sp := D.sp) (Formalism.L2.Forms.gramN D (i + 1) hi) a ((I.at' i hi).st.K β).lev.Lb) ∧
      dl D.sp.cm.sig (Formalism.L2.Forms.gramN D (i + 1) hi) (compan (sp := D.sp) (Formalism.L2.Forms.gramN D (i + 1) hi) a ((I.at' i hi).st.K β).lev.Lb) =
        compan (sp := D.sp) (Formalism.L2.Forms.gramN D (i + 1) hi) a ((I.at' i hi).st.K β).lev.Lb

def UnitTieAt (L0 : Lev0Data D u w h) : Prop :=
  (∀ La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt 0, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj 0).IsLatTup La.2 →
    ∃ x, L0.A.IsPt La.1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om 0 La.2) x ∧
      x ∈ UPts (sigD D) L0.J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
    ∀ i (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)), ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).IsLatTup La.2 →
      ∃ x, ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2 (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
        x ∈ UPts (sigD D) (Formalism.L2.Forms.gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def FillTieAt (a : 𝓞 D.host.E) : Prop :=
  ∀ i, ¬ i + 1 ≤ D.R.m →
    OK D.sp (1 : Matrix (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1)) (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1)) D.host.E) a
      (Submodule.span (𝓞 D.host.E) (Set.range fun k => Pi.single k (1 : D.host.E))) 1

def LocalModelLatticesAdmissible : Prop :=
  ∀ (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (L0 : Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    OrthTieAt L0 → DualTieAt L0 → ATieAt I L0 a → UnitTieAt Ch std vp unif eO eO_spec dG dG_spec om I L0 →
    FillTieAt Ch std vp unif eO eO_spec dG dG_spec om a →
    Formalism.L2.KerInert.KG.AdmG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin D (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad)

variable {Ch std vp unif eO eO_spec dG dG_spec om I} in
set_option maxHeartbeats 400000 in

theorem chartOK_zero (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (hO : OrthTieAt L0) (hD : DualTieAt L0) (hA : ATieAt I L0 a)
    (hU : UnitTieAt Ch std vp unif eO eO_spec dG dG_spec om I L0) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt 0)
    (hLa : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj 0).IsLatTup La.2) :
    ChartOK (cpAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc) a 0 La := by
  have hok : OK D.sp L0.J a L0.Lb _ :=
    ⟨Formalism.BasicNotions.factNEven D.R 0, hO.1, hD.1, hA.1.1, hA.1.2.1, hA.1.2.2, (Classical.epsilon_spec (hU.1 La hLa)).2⟩
  exact OK_re D.sp L0.A.rk.symm hok

variable {Ch std vp unif eO eO_spec dG dG_spec om I} in
set_option maxHeartbeats 400000 in

theorem chartOK_succ (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (hO : OrthTieAt L0) (hD : DualTieAt L0) (hA : ATieAt I L0 a)
    (hU : UnitTieAt Ch std vp unif eO eO_spec dG dG_spec om I L0) (i : ℕ) (hi : i + 1 ≤ D.R.m)
    (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) (hLa : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).IsLatTup La.2) :
    ChartOK (cpAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc) a (i + 1) La := by
  have hok : OK D.sp (Formalism.L2.Forms.gramN D (i + 1) hi) a
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb _ :=
    ⟨Formalism.BasicNotions.factNEven D.R (i + 1), hO.2 i hi, hD.2 i hi, (hA.2 i hi _).1, (hA.2 i hi _).2.1, (hA.2 i hi _).2.2,
      (Classical.epsilon_spec (hU.2 i hi La hLa)).2⟩
  have key := OK_re D.sp ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm hok
  show OK D.sp (chAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc (i + 1) La).J a
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc (i + 1) La).Lb
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc (i + 1) La).y
  rw [chAt_succ_J, chAt_succ_Lb, chAt_succ_y]
  exact key

variable {Ch std vp unif eO eO_spec dG dG_spec om I} in
set_option maxHeartbeats 400000 in

theorem chartOK_fill (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (hF : FillTieAt Ch std vp unif eO eO_spec dG dG_spec om a)
    (i : ℕ) (hi : ¬ i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    ChartOK (cpAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc) a (i + 1) La := by
  obtain ⟨e1, e2, e3⟩ := chAt_fill Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc i hi La
  show OK D.sp (chAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc (i + 1) La).J a
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc (i + 1) La).Lb
    (chAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc (i + 1) La).y
  rw [e1, e2, e3]
  exact hF i hi

set_option maxHeartbeats 400000 in

theorem local_model_lattices_admissible : LocalModelLatticesAdmissible Ch std vp unif eO eO_spec dG dG_spec om I := by
  intro hfin L0 a bad hO hD hA hU hF
  refine admissible_of_charts_lattices hfin (cpAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc) a bad ?_
  intro j
  cases j with
  | zero => exact chartOK_zero L0 a hO hD hA hU
  | succ i =>
    intro La hLa
    by_cases hi : i + 1 ≤ D.R.m
    · exact chartOK_succ L0 a hO hD hA hU i hi La hLa
    · exact chartOK_fill L0 a hF i hi La

def LocalModelLatticesAdmissibleSmall : Prop :=
  ∀ (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (L0 : Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    Fl.mm ≤ D.R.m →
    OrthTieAt L0 → DualTieAt L0 → ATieAt I L0 a → UnitTieAt Ch std vp unif eO eO_spec dG dG_spec om I L0 →
    Formalism.L2.KerInert.RepLt.AdmGLt (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin D (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad)

set_option maxHeartbeats 400000 in

theorem local_model_lattices_admissible_small : LocalModelLatticesAdmissibleSmall Ch std vp unif eO eO_spec dG dG_spec om I := by
  intro hfin L0 a bad hmm hO hD hA hU
  refine admissible_small_of_charts hfin (cpAt Ch std vp unif eO eO_spec dG dG_spec om I L0.A L0.J L0.Lb L0.Uloc) a bad ?_
  intro j
  cases j with
  | zero => intro La _ hLa; exact chartOK_zero L0 a hO hD hA hU La hLa
  | succ i =>
    intro La hj hLa
    exact chartOK_succ L0 a hO hD hA hU i (le_trans hj hmm) La hLa

end At

end Formalism.L2.KerInert.AdmGA
