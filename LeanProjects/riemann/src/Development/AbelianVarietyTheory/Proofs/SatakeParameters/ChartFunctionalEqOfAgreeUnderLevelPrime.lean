import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentPullbackLatticeVectorMemDualSpanStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepPointPulledDualVectorMemLocalBaseLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

namespace GlobalTheory.FnlAway

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem T_mem_under {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (P : t.Pr.vT (t.word u))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : IsOver v (seamP t.seam P.1)) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have h1 : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    have := Ideal.absNorm_mem P.1.asIdeal
    rwa [t.pr_ok.vT_norm _ P.1 P.2] at this
  rw [t.T_rec] at h1
  have h2 := (mem_seamP t.seam P.1 _).2 h1
  rw [map_natCast] at h2
  unfold IsOver at hv
  rw [hv, Ideal.mem_comap, map_natCast]
  exact h2

theorem prV_pullV_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (g g₁ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : bc (prV (E := E) v) g₁ = bc (prV (E := E) v) g) (w : Fin n → E) (l : Fin n) :
    prV (E := E) v (pullV (F := F) g₁ w l) = prV (E := E) v (pullV (F := F) g w l) := by
  have key : ∀ k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), prV (E := E) v (pullV (F := F) k w l) =
      ∑ j, ((bc (prV (E := E) v) k)⁻¹ : GL (Fin n) _).1 l j * prV (E := E) v (Formalism.L2.Col.iA F E (w j)) := by
    intro k
    rw [← map_inv]
    unfold pullV
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  rw [key, key, h]

set_option maxHeartbeats 6000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem exists_unit_one_add_generator {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad)
    (crd : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Fin (D.R.N i) → D.host.E) (hw : w ∈ latCo D.sp (gramN D i hi) crd a x.1 lev.Lb) :
    ∃ z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)),
      z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F crd * x.1) w l) := by
  let M := latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb))
  have hint : ∀ c : 𝓞 D.host.E, inclE (F := D.host.F) (v.adicCompletion D.host.F) (c : D.host.E) ∈ intV D.host.E v :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)
  let φ : (Fin (D.R.N i) → D.host.E) → (Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
    fun l k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)
  have hadd : ∀ l₁ l₂, φ (l₁ + l₂) = φ l₁ + φ l₂ := by
    intro l₁ l₂
    funext k
    simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hzero : φ 0 = 0 := by
    funext k
    simp [φ, pullV, Matrix.mulVec, dotProduct]
  have hsmul : ∀ (c : 𝓞 D.host.E) l, φ (c • l) = (⟨_, hint c⟩ : intV D.host.E v) • φ l := by
    intro c l
    funext k
    simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show c • l j = (c : D.host.E) * l j from Algebra.smul_def c (l j), map_mul, map_mul, map_mul, map_mul, mul_left_comm]
    congr 1
  have hmem : ∀ l ∈ compan (sp := D.sp) (gramN D i hi) a (latAd x.1 lev.Lb), φ l ∈ M := by
    intro l hl
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := Submodule.mem_sup.1 hl
    rw [hadd]
    refine M.add_mem (GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span i hi lev x v l₁ h₁) ?_
    refine Submodule.smul_induction_on h₂ ?_ ?_
    · intro r hr s hs
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [hsmul]
      refine M.smul_mem _ ?_
      induction hs using Submodule.span_induction with
      | mem s hs => exact GlobalTheory.T.stepPoint_pulledDualVector_mem_localBaseLattice i hi lev x v s hs
      | zero => rw [hzero]; exact M.zero_mem
      | add p q _ _ hp hq => rw [hadd]; exact M.add_mem hp hq
      | smul c s _ h => rw [hsmul]; exact M.smul_mem _ h
    · intro p q hp hq
      rw [hadd]
      exact M.add_mem hp hq
  unfold latCo at hw
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hw
  refine ⟨⟨_, hmem l hl⟩, funext fun k => congrArg (prV (E := D.host.E) v) (congrFun ?_ k)⟩
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  symm
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, toLE_apply, ← map_inv]
  show ((((crd⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).map (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) *ᵥ _) j = _
  refine (RingHom.map_mulVec _ _ _ j).symm.trans ?_
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in

theorem fnl_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree y hy
  have hat := GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree
  set v := HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1) with hvdef
  have hvo : IsOver v (seamP t.seam P.1) := by
    unfold IsOver
    rw [hvdef, HeightOneSpectrum.under_asIdeal]
  have hTv : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    rw [htie.T_eq]
    exact T_mem_under t u P v hvo
  have hd := p.deco.2
  have hd₁ := p₁.deco.2
  obtain ⟨s, hs, hsy⟩ := (mem_locP P.1 _ y).1 hy
  have hy₁ : y ∈ p₁.deco.1.at P.1 := hat ▸ hy
  obtain ⟨s₁, hs₁, hsy₁⟩ := (mem_locP P.1 _ y).1 hy₁
  have hsP : s * s₁ ∉ P.1.asIdeal := fun h => (P.1.isPrime.mem_or_mem h).elim hs hs₁
  have hw : (s * s₁) • y ∈ p.deco.1.N := by
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ hsy
  have hw₁ : (s * s₁) • y ∈ p₁.deco.1.N := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hsy₁
  have hlat : (fun l => t.seam.iE (((s * s₁) • y) l)) ∈
      latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb := by
    rw [← hp.lat]
    exact Submodule.subset_span ⟨_, hw, rfl⟩
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator i hi ((St i hi).K β).lev (A.crd i hi) a x v _ hlat
  have e1 := hp.fnl P v hTv hvo _ hw z hz
  have hz₁ : z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F (A.crd i hi) * x₁.1)
      (fun b => t.seam.iE (((s * s₁) • y) b)) l) := by
    have hbc : bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1) =
        bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1) :=
      ((MonoidHom.map_mul _ _ _).trans (congrArg (bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi)) * ·) (hagree v hvo))).trans
        (MonoidHom.map_mul _ _ _).symm
    refine hz.trans (funext fun l => ?_)
    exact (prV_pullV_congr (F := D.host.F) (E := D.host.E) v (ratA D.host.F (A.crd i hi) * x.1)
      (ratA D.host.F (A.crd i hi) * x₁.1) hbc (fun b => t.seam.iE (((s * s₁) • y) b)) l).symm
  have e2 := hp₁.fnl P v hTv hvo _ hw₁ z hz₁
  have f1 := hd.f_smul P (s * s₁) y hy
  have f2 := hd₁.f_smul P (s * s₁) y hy₁
  haveI := P.1.isPrime
  have hne : Ideal.Quotient.mk P.1.asIdeal (s * s₁) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hne
  rw [← f1, ← f2, e1, e2]

end GlobalTheory.FnlAway
