import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtStalkInvariantDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.OmegaRankGen

theorem exists_relDim (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ d, SmoothOfRelativeDimension d G.hom := by
  haveI := hG.smooth
  haveI : IsIntegral G.left := isIntegral_left_of_isSemiAbelian G
  obtain ⟨x⟩ : Nonempty (Sp R) := inferInstance
  exact exists_dim_of_preconnected G.hom (η[G].left x)

theorem relDim_eq_of_card (R K : Type) [CommRing R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
    (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G)
    (hP : IsProper (pullback.snd G.hom (spMap (algebraMap R K)))) (d : ℕ) (hd : SmoothOfRelativeDimension d G.hom)
    (p g : ℕ) (hp : p.Prime) (hc : Nat.card (Tors G p K) = p ^ (2 * g)) : d = g := by
  let f : Sp K ⟶ Sp R := spMap (algebraMap R K)
  let G₀ : Over (Sp K) := (Over.pullback f).obj G
  have h := isGrpPullback_pullback G f
  have hG₀ : IsSemiAbelian G₀ := IsSemiAbelian.pullback _ _ hG
  have hA : IsAbelianScheme G₀ := ⟨hG₀.comm, hG₀.smooth, hP, hG₀.geomConnected⟩
  have hd₀ : SmoothOfRelativeDimension d G₀.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hd
  have hcard := card_torsion_abelianVariety K G₀ d p hA hd₀ (by exact_mod_cast hp.ne_zero)
  let T : Over (Sp K) := 𝟙_ (Over (Sp K))
  have hc' : T.hom ≫ f = (SpAlg R K).hom := Category.id_comp _
  let ρ : SpAlg R K ⟶ Over.mk (T.hom ≫ f) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hc')
  let Φ : (T ⟶ G₀) →* (SpAlg R K ⟶ G) := (preHom ρ).comp (pushHom h T)
  have hΦ : ∀ x, (Φ x).left = x.left ≫ pullback.fst G.hom f := fun x => Category.id_comp _
  have hb : Function.Bijective Φ := by
    refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm)), fun a => ?_⟩
    · rw [← hΦ, ← hΦ, e]
    · exact ⟨Over.homMk (h.1.lift a.left T.hom ((Over.w a).trans hc'.symm)) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext ((hΦ _).trans (h.1.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective Φ hb
  have e1 : {x : T ⟶ G₀ // x ^ p = 1} ≃ Tors G p K := e.toEquiv.subtypeEquiv fun x => by
    show _ ↔ e x ^ p = 1
    rw [← map_pow, EmbeddingLike.map_eq_one_iff]
  rw [← Nat.card_congr e1, hcard] at hc
  have := Nat.pow_right_injective hp.two_le hc
  omega

open GlobalTheory.SqZeroPt in

def wmodEquiv (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [QuasiSeparated G.hom] [Smooth G.hom] :
    Wmod G ≃ₗ[R] Pdiv.omega G :=
  LinearEquiv.ofBijective
    ({ toFun := fun w : Wmod G => GlobalTheory.LieVB.toOmega G w
       map_add' := map_add (GlobalTheory.LieVB.toOmega G)
       map_smul' := fun a w => by exact GlobalTheory.LieVB.toOmega_smul (G := G) a w } : Wmod G →ₗ[R] Pdiv.omega G)
    (GlobalTheory.OmegaGlobal.toOmega_bijective R G
      ⟨GlobalTheory.LieVB.tangent_injective R G, GlobalTheory.LieVB.TangentSurj.tangent_surjective R G⟩)

theorem finrank_of_rankAtStalk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] (d : ℕ)
    (h : ∀ p, Module.rankAtStalk (R := R) M p = d) (k : Type) [Field k] [Algebra R k] :
    Module.finrank k (k ⊗[R] M) = d := by
  have := Module.rankAtStalk_baseChange (R := R) (M := M) (S := k) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at this
  exact this.trans (h _)

theorem finrank_omega : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (spMap (algebraMap R K))) → ∀ (p g : ℕ), p.Prime → Nat.card (Tors G p K) = p ^ (2 * g) → ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] Pdiv.omega G) = g := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG hP p g hp hc k _ _
  obtain ⟨d, hd⟩ := exists_relDim R G hG
  obtain rfl := relDim_eq_of_card R K G hG hP d hd p g hp hc
  haveI := hG.smooth
  haveI := hd
  have hV := GlobalTheory.LieVB.isVB_omega G d
  have hfr : ∀ x : Sp R, ∃ (U : (Sp R).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega G, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s := fun x => by
    obtain ⟨U, e, hx, he⟩ := hV x
    exact ⟨U, d, e, hx, he⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.FramesFGP.finite_projective_wmod R G hfr
  let e := wmodEquiv R G
  haveI : Module.Finite R (Pdiv.omega G) := Module.Finite.equiv e
  haveI : Module.Projective R (Pdiv.omega G) := Module.Projective.of_equiv e
  exact finrank_of_rankAtStalk d (fun q => (congrFun (Module.rankAtStalk_eq_of_equiv e.symm) q).trans
    (GlobalTheory.T.rank_at_stalk_invariant_differentials R G d hV q)) k

end GlobalTheory.OmegaRankGen
