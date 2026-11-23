import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletionStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FnlAway
open scoped TensorProduct

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem exists_place {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (j : ℕ) (hj : j ≤ D.R.m) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), ∃ h : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal,
      IsOver v (seamP t.seam P.1) ∧ v ∈ plUnder D.host.F (ssRec t u μ) := by
  classical
  obtain ⟨hSS, -⟩ := t.rd_chain u μ
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Formalism.L2.Col.Primes.vT Formalism.L2.Col.divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((St j hj).T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    rw [H.T_eq j hj, ← t.T_rec u, ← map_natCast (RingOfIntegers.mapRingEquiv t.seam.iE), mem_seamP]
    exact hT
  have hT0 : (((St j hj).T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [H.T_eq j hj, ← t.T_rec u]
    exact Nat.cast_ne_zero.2 (t.pr_ok.T_prime _).ne_zero
  have hmem : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hTQ
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)),
    Ideal.IsPrime.comap _, fun h => hT0 (by rw [h] at hmem; exact (Ideal.mem_bot.1 hmem))⟩
  refine ⟨v, hmem, rfl, seamP t.seam P.1, ?_, rfl⟩
  refine (mem_ssRec t u μ P.1).2 ?_
  rw [hSS]
  unfold Sall
  exact Finset.mem_union.2 (Or.inl P.2)

theorem prV_pullV_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (c : GL (Fin N) E) (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x) (y : Fin N → E) (l : Fin N) :
    prV (E := E) v (pullV (F := F) (ratA F c * x₁) y l) = prV (E := E) v (pullV (F := F) (ratA F c * x) y l) := by
  have key : ∀ z : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), prV (E := E) v (pullV (F := F) z y l) =
      ((((bc (prV (E := E) v) z)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (iA F E (y i))) l := by
    intro z
    rw [← map_inv]
    exact RingHom.map_mulVec (prV (E := E) v) _ _ l
  rw [key, key, map_mul, map_mul, h]

theorem mem_latS_of_latCo {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (hint : ∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E)
    (hy : y ∈ latCo sp J c a x Lb) :
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) :=
  GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion sp J hJ c a x hx Lb hfin hspan hint v y hy

theorem fnl_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N j)), w ∈ p.deco.1.at P.1 → w ∈ p₁.deco.1.at P.1 → p₁.deco.1.f P w = p.deco.1.f P w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H j hj β x x₁ p p₁ hp hp₁ hag P w hw hw₁
  obtain ⟨v, hTv, hov, hvU⟩ := exists_place H j hj P
  have hxv := hag v hvU
  obtain ⟨s, hs, hsw⟩ := (mem_locP _ _ _).1 hw
  obtain ⟨s', hs', hsw'⟩ := (mem_locP _ _ _).1 hw₁
  have h1 : (s' * s) • w ∈ p.deco.1.N := by rw [mul_smul]; exact Submodule.smul_mem _ _ hsw
  have h2 : (s' * s) • w ∈ p₁.deco.1.N := by rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsw'
  have hmem : ∀ (y : UA D j hj) (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β y q →
      ∀ w' ∈ q.deco.1.N, (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F (A.crd j hj) * y.1)
        (fun b => t.seam.iE (w' b)) l)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) := by
    intro y q hq w' hw'
    have hy : (fun b => t.seam.iE (w' b)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a y.1 ((St j hj).K β).lev.Lb := by
      rw [← hq.lat]
      exact Submodule.subset_span ⟨w', hw', rfl⟩
    exact mem_latS_of_latCo D.sp (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) (A.crd j hj) a y.1 y.2
      _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hy
  let z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) :=
    ⟨_, hmem x p hp _ h1⟩
  have e1 := hp.fnl P v hTv hov _ h1 z rfl
  have e2 := hp₁.fnl P v hTv hov _ h2 z (by
    funext l
    exact (prV_pullV_congr v (A.crd j hj) x.1 x₁.1 hxv _ l).symm)
  have e3 : p₁.deco.1.f P ((s' * s) • w) = p.deco.1.f P ((s' * s) • w) := e2.trans e1.symm
  rw [p₁.deco.2.f_smul P _ w hw₁, p.deco.2.f_smul P _ w hw] at e3
  haveI hP := P.1.isPrime
  have hu : Ideal.Quotient.mk P.1.asIdeal (s' * s) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hm => (hP.mem_or_mem hm).elim hs' hs
  exact mul_left_cancel₀ hu e3

end GlobalTheory.TwV.FnlAway

end
