import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GLInvMulCongrOneModUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPowStatement

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameAgree

theorem inv_mul_cong {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K) (hπ0 : π ≠ 0)
    (hπ : Valued.v π < 1) (a a₁ : GL (Fin N) K)
    (ha : ∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1)
    (ha₁ : ∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) :
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 :=
  GlobalTheory.T.GL_inv_mul_congr_one_mod_uniformizer π hπ0 hπ a a₁ ha ha₁

theorem glint_of_cong {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ)
    (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b)))
    (hg' : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) :
    g ∈ GLint E n P ∧ ∀ w ∈ stdAt E n P, ((qOf P : E) ^ d)⁻¹ • (g w - w) ∈ stdAt E n P :=
  GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow P d g hg hg'

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

abbrev locM (Q : HeightOneSpectrum (𝓞 E)) : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →* GL (Fin N) (Q.adicCompletion E) :=
  bc (GlobalTheory.Mem.Col2.adAt F Q)

theorem congAt_loc (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : CongAt (F := F) Q n k) : ∀ a b, Valued.v ((algebraMap E (Q.adicCompletion E) (((qOf Q : ℕ) : E) ^ n))⁻¹ *
      (((locM Q k : GL (Fin N) (Q.adicCompletion E)) : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) - 1) a b) ≤ 1 := by
  have hι : IsAdIso (GlobalTheory.Mem.Col2.afIso F E) := ⟨GlobalTheory.Mem.Col2.afIso_tmul_one F E, GlobalTheory.Mem.Col2.mem_rInt_iff F E⟩
  intro a b
  have h1 := hι.val_le (h a b)
  have e1 : ∀ z, GlobalTheory.Mem.Col2.afIso F E z Q = GlobalTheory.Mem.Col2.adAt F Q z := fun z => rfl
  rw [e1, map_mul, GlobalTheory.Mem.Col2.adAt_inclE, map_inv₀, Matrix.sub_apply, map_sub] at h1
  have e2 : GlobalTheory.Mem.Col2.adAt F Q ((1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) =
      (1 : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) a b := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2] at h1
  rw [Matrix.sub_apply]
  exact h1

theorem loc_agree (Q : HeightOneSpectrum (𝓞 E)) {x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : bc (prV (E := E) (Q.under (𝓞 F))) x₁ = bc (prV (E := E) (Q.under (𝓞 F))) x) : locM Q x₁ = locM Q x := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have h1 := congrArg (fun g : GL (Fin N) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => Units.val g a b) h
  change prV (E := E) (Q.under (𝓞 F)) ((x₁ : Matrix (Fin N) (Fin N) _) a b) =
    prV (E := E) (Q.under (𝓞 F)) ((x : Matrix (Fin N) (Fin N) _) a b) at h1
  have h0 : prV (E := E) (Q.under (𝓞 F)) ((x₁ : Matrix (Fin N) (Fin N) _) a b - (x : Matrix (Fin N) (Fin N) _) a b) = 0 := by
    rw [map_sub, sub_eq_zero]; exact h1
  have h2 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h0 Q rfl
  rw [map_sub, sub_eq_zero] at h2
  exact h2

theorem val_alg (Q : HeightOneSpectrum (𝓞 E)) (e : E) :
    Valued.v (algebraMap E (Q.adicCompletion E) e) = Q.valuation E e :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q e

theorem intAt_of_val (Q : HeightOneSpectrum (𝓞 E)) (c m o : E)
    (h : Valued.v ((algebraMap E (Q.adicCompletion E) c)⁻¹ * (algebraMap E (Q.adicCompletion E) m - algebraMap E (Q.adicCompletion E) o)) ≤ 1) :
    IntAt Q (c⁻¹ * (m - o)) := by
  rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val, ← val_alg, map_mul, map_inv₀, map_sub]
  exact h

theorem one_entry {E₀ : Type} [Field E₀] (Q : HeightOneSpectrum (𝓞 E)) (ψ : E₀ ≃+* E) (a b : Fin N) :
    (1 : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) a b = algebraMap E (Q.adicCompletion E) (ψ ((1 : Matrix (Fin N) (Fin N) E₀) a b)) := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Loc

theorem map_expr {E₀ E : Type} [Field E₀] [Field E] (σ : E₀ ≃+* E) (q d : ℕ) (m o : E₀) :
    ((q : E) ^ d)⁻¹ * (σ m - σ o) = σ (((q : E₀) ^ d)⁻¹ * (m - o)) := by
  simp [map_mul, map_inv₀, map_pow, map_natCast, map_sub]

theorem qOf_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [← (RingOfIntegers.mapRingEquiv s.iE).apply_symm_apply y, mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro hy; exact ⟨_, hy, rfl⟩
    · rintro ⟨z, hz, e⟩
      rw [(RingOfIntegers.mapRingEquiv s.iE).injective e] at hz
      exact hz
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (seamP s P).asIdeal (RingOfIntegers.mapRingEquiv s.iE) hI).toEquiv).symm

theorem intAt_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (e : X.E) :
    IntAt (seamP s P) (s.iE e) ↔ IntAt P e := by
  have hc : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv s.iE y) = s.iE (algebraMap (𝓞 X.E) X.E y) :=
    fun y => rfl
  constructor
  · rintro ⟨r, c, hc', h⟩
    refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
    · rw [← mem_seamP s, RingEquiv.apply_symm_apply]; exact hc'
    · apply s.iE.injective
      rw [map_mul, ← hc, ← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact h
  · rintro ⟨r, c, hc', h⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, RingOfIntegers.mapRingEquiv s.iE c, ?_, ?_⟩
    · rw [mem_seamP s]; exact hc'
    · rw [hc, hc, ← map_mul, h]

end GlobalTheory.FrameAgree

namespace GlobalTheory.FrameAgree

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem core (hTie : AdTie A dtU a) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j) (hp : IsPtAd A a j hj β x p) (hp₁ : IsPtAd A a j hj β x₁ p₁)
    (hx : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1)
    (P : SB t μ) : ∀ a b, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (LinearMap.toMatrix' ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm).toLinearMap a b -
        (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) t.X.E) a b)) := by
  set Q := seamP t.seam P.1 with hQdef
  have hQ : Q ∈ ssRec t u μ := (mem_ssRec t u μ P.1).2 (by rw [hTie.isChainTop.1]; classical exact Finset.mem_union.2 (Or.inr P.2))
  have hv : Q.under (𝓞 D.host.F) ∈ plUnder D.host.F (ssRec t u μ) := ⟨Q, hQ, rfl⟩
  have hag := loc_agree Q (hx _ hv)
  have c0 := congAt_loc Q _ _ (hp.frame P)
  have c1 := congAt_loc Q _ _ (hp₁.frame P)
  have hD : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hq0 : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hπ0 : algebraMap D.host.E (Q.adicCompletion D.host.E) (((qOf Q : ℕ) : D.host.E) ^ (t.cst μ).D P) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap D.host.E _).injective]
    exact pow_ne_zero _ (by exact_mod_cast hq0)
  have hπ : Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (((qOf Q : ℕ) : D.host.E) ^ (t.cst μ).D P)) < 1 := by
    rw [val_alg, map_pow]
    refine pow_lt_one₀ zero_le' ?_ (by omega)
    have e : ((qOf Q : ℕ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (qOf Q : 𝓞 D.host.E) := by rw [map_natCast]
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (Q.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key := inv_mul_cong _ hπ0 hπ _ _ c0 c1
  have hs : (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm =
      (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P := by
    ext w; rfl
  have e : (locM Q (((ratA D.host.F) (A.crd j hj) * x.1 * (ratA D.host.F) (A.fb j hj β P))⁻¹ *
        (ratA D.host.F) ((seamGL t.seam) (frsF t.sel (t.tup μ) p P))))⁻¹ *
      locM Q (((ratA D.host.F) (A.crd j hj) * x₁.1 * (ratA D.host.F) (A.fb j hj β P))⁻¹ *
        (ratA D.host.F) ((seamGL t.seam) (frsF t.sel (t.tup μ) p₁ P))) =
      locM Q (ratA D.host.F (seamGL t.seam ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm))) := by
    rw [hs]
    simp only [map_mul, map_inv]
    rw [hag]
    group
  rw [e] at key
  intro a b
  have k := key a b
  obtain ⟨g, hg⟩ : ∃ g, g = (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm := ⟨_, rfl⟩
  rw [← hg] at k ⊢
  have ent : ((locM Q (ratA D.host.F (seamGL t.seam g)) : GL (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) :
      Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) a b =
      algebraMap D.host.E _ (t.seam.iE (LinearMap.toMatrix' g.toLinearMap a b)) := by
    show GlobalTheory.Mem.Col2.adAt D.host.F Q (inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) a b)) = _
    rw [GlobalTheory.Mem.Col2.adAt_inclE]
    rfl
  have one : (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) a b =
      algebraMap D.host.E _ (t.seam.iE ((1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) t.X.E) a b)) := by
    exact one_entry Q t.seam.iE a b
  rw [Matrix.sub_apply, ent, one] at k
  have k2 := intAt_of_val Q _ _ _ k
  rw [hQdef, qOf_seamP, map_expr] at k2
  exact (intAt_seamP t.seam P.1 _).1 k2

end GlobalTheory.FrameAgree

namespace GlobalTheory.FrameAgree

theorem frame_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : SB t μ, (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm ∈ GLint t.X.E (D.R.N j) P.1 ∧
    ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ •
      ((frsF t.sel (t.tup μ) p P).symm (frsF t.sel (t.tup μ) p₁ P w) - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have h1 := core hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have h2 := core hTie j hj β x₁ x p₁ p hp₁ hp (fun v hv => (hx v hv).symm) P
  have hsymm : ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm).symm =
      (frsF t.sel (t.tup μ) p P).trans (frsF t.sel (t.tup μ) p₁ P).symm := by
    ext w; rfl
  exact glint_of_cong P.1 ((t.cst μ).D P) _ h1 (by rw [hsymm]; exact h2)

end GlobalTheory.FrameAgree
