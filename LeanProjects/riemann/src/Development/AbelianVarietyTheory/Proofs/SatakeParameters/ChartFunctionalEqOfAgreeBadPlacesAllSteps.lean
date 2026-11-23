import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeVectorLocalMemDualBaseCompletionStatement
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwV.FnlAwayCpl

section Loc
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem f_eq_on_at {d d₁ : Deco E n ST SG} (hd : d.Ok) (hd₁ : d₁.Ok) (P : ST) (hat : d₁.at P.1 = d.at P.1)
    (h : ∀ w ∈ d.N, w ∈ d₁.N → d₁.f P w = d.f P w) : ∀ y ∈ d.at P.1, d₁.f P y = d.f P y := by
  intro y hy
  have hy₁ : y ∈ d₁.at P.1 := hat ▸ hy
  obtain ⟨s, hs, hsy⟩ := (mem_locP P.1 d.N y).1 hy
  obtain ⟨s₁, hs₁, hsy₁⟩ := (mem_locP P.1 d₁.N y).1 hy₁
  have hw : (s * s₁) • y ∈ d.N := by
    rw [mul_comm, mul_smul]; exact d.N.smul_mem s₁ hsy
  have hw₁ : (s * s₁) • y ∈ d₁.N := by
    rw [mul_smul]; exact d₁.N.smul_mem s hsy₁
  have e := h _ hw hw₁
  rw [hd₁.f_smul P _ y hy₁, hd.f_smul P _ y hy] at e
  have hne : Ideal.Quotient.mk P.1.asIdeal (s * s₁) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hm => (P.1.isPrime.mem_or_mem hm).elim hs hs₁
  letI := Ideal.Quotient.field P.1.asIdeal
  exact mul_left_cancel₀ hne e
end Loc

section Pull
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem prV_pullV_congr (v : HeightOneSpectrum (𝓞 F)) {g g₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : bc (prV (E := E) v) g₁ = bc (prV (E := E) v) g) (u : Fin N → E) :
    (fun l => prV (E := E) v (pullV (F := F) g₁ u l)) = fun l => prV (E := E) v (pullV (F := F) g u l) := by
  have h' : bc (prV (E := E) v) g₁⁻¹ = bc (prV (E := E) v) g⁻¹ := by rw [map_inv, map_inv, h]
  funext l
  unfold pullV
  rw [RingHom.map_mulVec, RingHom.map_mulVec]
  have h2 : ((g₁⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) =
      ((g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := congrArg Units.val h'
  rw [h2]
end Pull
end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV.FnlAwayCpl
section Z
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem exists_latS_pullV (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (hint : ∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb)
    (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E) (hu : u ∈ latCo sp J crd a x Lb) :
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) :=
  GlobalTheory.T.companionLatticeVector_local_mem_dualBaseCompletion sp J crd a x hx hJ Lb hfin hspan hint v u hu
end Z
end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV.FnlAwayCpl

theorem exists_place {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    {A : AdData t u μ St} {dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt} {a : 𝓞 D.host.E}
    (hTie : AdTie A dtU a) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) ∧
      (∀ j (hj : j ≤ D.R.m), (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) ∧ v ∈ plUnder D.host.F (ssRec t u μ) := by
  classical
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Primes.vT divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : (((D.mem u).A.T : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.T_rec u, ← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    have := (mem_seamP t.seam P.1 _).2 hT
    rwa [map_natCast] at this
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [← t.T_rec u]
    exact_mod_cast (t.pr_ok.T_prime (t.word u)).ne_zero
  have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hTQ
  refine ⟨⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _,
    fun h0 => hT0 (by rw [h0] at hTv; exact (Submodule.mem_bot _).1 hTv)⟩, rfl, fun j hj => ?_, ?_⟩
  · rw [hTie.T_eq j hj]; exact hTv
  · have hSS : P.1 ∈ (t.rd u μ).SS := by
      rw [((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1]
      exact Finset.mem_union_left _ P.2
    exact ⟨_, (mem_ssRec t u μ P.1).2 hSS, rfl⟩

end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV

open Formalism.L2.Forms

set_option maxHeartbeats 2000000 in
open FnlAwayCpl in

theorem fnl_eq_of_away_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hag P hat
  obtain ⟨v, hov, hTv, hvU⟩ := exists_place hTie P
  have hfnl := hp.fnl P v (hTv j hj) hov
  have hfnl₁ := hp₁.fnl P v (hTv j hj) hov
  refine f_eq_on_at p.deco.2 p₁.deco.2 P hat fun w hw hw₁ => ?_
  have hu : (fun l => t.seam.iE (w l)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x.1 ((St j hj).K β).lev.Lb := by
    rw [← hp.lat]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  obtain ⟨z, hz⟩ := exists_latS_pullV D.sp (gramN D j hj) (A.crd j hj) a x.1 x.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) ((St j hj).K β).lev.Lb
    ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hu
  have hg : bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd j hj) * x₁.1) = bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd j hj) * x.1) := by
    rw [map_mul, map_mul, hag v hvU]
  rw [hfnl₁ w hw₁ z (hz.trans (prV_pullV_congr v hg _).symm), hfnl w hw z hz]

end GlobalTheory.TwV
