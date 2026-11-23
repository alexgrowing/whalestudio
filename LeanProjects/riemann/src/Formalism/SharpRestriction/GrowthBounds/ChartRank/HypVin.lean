import Formalism.SharpRestriction.GrowthBounds.ChartComparison.IntAtJIffN
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PValIntN

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem le_dual_chart {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (c : cl) :
    ∀ x ∈ lat c, x ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (lat c) := by
  intro x hx x' hx'
  have hglob : ∀ z ∈ lat c, z ∈ Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
    intro z hz
    exact (K.y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ K.lev.Lb, ∀ b ∈ K.lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := K.lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) K.lev.Lb 1 hm (K.y c).1
    (K.y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwL_descent _ _ _ h

open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB in

theorem exB_of_lat {i : ℕ} (hi : i ≤ D.R.m) (q : ℕ) [Fact q.Prime] (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
    (hL : Submodule.IsLattice D.host.E L) :
    ∃ B' : GL (Fin (D.R.N i)) D.host.E, IsLocBasis q (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L) B' := by
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL
  have hsp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL
  obtain ⟨B, hB⟩ := exists_isLocBasis q _ _ (fg_of_le_bnd hd hle) hsp
  refine ⟨B, ?_⟩
  have e : ((Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L) :
      Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L := span_dualSet _ _ _
  rwa [e] at hB

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

structure LatIn (S : StepIn M i hi G) (w : D.what₂.places.Pl) (β : S.Ch) : Prop where
  prime : p.Prime
  resChar : D.what₂.places.resChar w = p
  siteGood_prime_torsion : ¬ p ∣ S.T
  alg : ∀ v (a : ((S.loc β).pl v).1.adicCompletion D.host.F),
    (S.loc β).spl v ((1 : D.host.E) ⊗ₜ[D.host.F] a) = (a, a)
  base : ∀ v (t : Fin (D.R.N i) → ((S.loc β).pl v).1.adicCompletion D.host.F),
    (∃ x ∈ Formalism.L2.Herm.locL ((S.loc β).pl v).1 (S.K β).lev.Lb, ∀ a, ((S.loc β).spl v (x a)).1 = t a) ↔
      ∀ a, (((bc ((S.loc β).phE v) (S.loc β).B)⁻¹ : GL (Fin (D.R.N i)) (((S.loc β).pl v).1.adicCompletion D.host.F)) :
        Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) _).mulVec t a ∈ ((S.loc β).pl v).1.adicCompletionIntegers D.host.F
  lat : ∀ cl : {c // S.chOf c = β}, Submodule.IsLattice D.host.E (S.lat cl.1)
  chi : ∀ κ : (S.K β).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
    D.what₂.embLL r = ((S.K β).lev.chi κ : ℂ)

set_option maxHeartbeats 8000000 in

theorem valIntN_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl)
    (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (hfrac : IsFractionRing G.O G.Kf)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap G.O G.Kf))
    (L : ∀ β, LatIn S w β) : S.ValIntN e w := by
  intro β
  have hp := (L β).prime
  have hpw := (L β).resChar
  subst hpw
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  exact valIntAt_of (S := (S.K β).lev) (emb := embT D) (embLL := D.what₂.embLL) (G := S.charts.gat β)
    (e := e) (A := S.loc β) (pos := S.pos) (embV := S.embN β) (yc := (S.K β).y) weylLatticeDescent_holds hfrac (tEL D) (tEL_emb D)
    (intW D.what₂.places w) hR0 (M.lam i) (H β).wt ((H β).toHyp hS).ex
    (fun cl B' => IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B')
    (fun cl => exB_of_lat hi (D.what₂.places.resChar w) (S.lat cl.1) ((L β).lat cl))
    (fun a Lt cl g γ κ hg hγ hpt B' hB' v s => by
      exact latO_of (tEL D) (H β).pos_emb
        (fun x => by rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive])
        (H β).std γ hγ B' Lt
        (fun v => by
          rw [hg v]
          exact latW_gen (S.K β).lev (S.loc β) (H β).int hp (L β).siteGood_prime_torsion (L β).alg (L β).base (S.lat cl.1) ((S.K β).y cl)
            ((S.K β).y_lat cl) (le_dual_chart (S.K β) cl) B' hB' a g γ κ hpt v)
        (fun v a b => gramW_gen (S.K β).lev (S.loc β) (H β).int hp (L β).siteGood_prime_torsion (L β).alg
          (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (S.lat cl.1) ((S.K β).y cl) ((S.K β).y_lat cl) (le_dual_chart (S.K β) cl)
          B' hB' v a b) v s)
    (L β).chi

end Formalism.MainNotions.G.CmpJ.PValIntN

end
