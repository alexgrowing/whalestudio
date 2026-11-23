import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {U : X.Opens} (hU : IsAffineOpen U) {D : Set X} (hD : Dense D)
    (r : Γ(X, U)) (h : ∀ (k : Type) [Field k] (φ : Γ(X, U) →+* k), Set.range (spMap φ ≫ hU.fromSpec) ⊆ D → φ r = 0) :
    r = 0 := by
  have dn : Dense (hU.fromSpec ⁻¹' D) := hD.preimage hU.fromSpec.isOpenEmbedding.isOpenMap
  have mem : ∀ P : PrimeSpectrum Γ(X, U), r ∈ P.asIdeal := by
    intro P
    by_contra hP
    obtain ⟨Q, hQ1, hQ2⟩ := dn.inter_open_nonempty (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(X, U)))
      (PrimeSpectrum.basicOpen r).isOpen ⟨P, hP⟩
    apply hQ1
    haveI : Q.asIdeal.IsPrime := Q.2
    let φ : Γ(X, U) →+* Q.asIdeal.ResidueField := algebraMap _ _
    refine Ideal.algebraMap_residueField_eq_zero.1 (h _ φ ?_)
    rintro _ ⟨q, rfl⟩
    have e : (spMap φ) q = Q := by
      haveI : q.asIdeal.IsPrime := q.2
      have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      apply PrimeSpectrum.ext
      show Ideal.comap φ q.asIdeal = Q.asIdeal
      rw [hq, ← RingHom.ker_eq_comap_bot]
      exact Ideal.ker_algebraMap_residueField _
    rw [Scheme.Hom.comp_apply, e]
    exact hQ2
  have hn : r ∈ nilradical Γ(X, U) := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    exact fun I hI => mem ⟨I, hI⟩
  exact (mem_nilradical.1 hn).eq_zero

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X}

theorem eig_of_points {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j))
    (hbas : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) (a : 𝓞 E) (s : R) (j₀ : Fin n)
    (P : ∀ (k : Type) [Field k], (R →+* k) → Prop)
    (hz : ∀ r : R, (∀ (k : Type) [Field k] (φ : R →+* k), P k φ → φ r = 0) → r = 0)
    (hpt : ∀ (k : Type) [Field k] (φ : R →+* k), P k φ →
      (spMap (dualMap φ) ≫ v j₀) ≫ (t.act.act a).left = spMap (epsMul (φ s)) ≫ spMap (dualMap φ) ≫ v j₀) :
    v j₀ ≫ (t.act.act a).left = spMap (epsMul s) ≫ v j₀ := by
  classical
  let T : Fin n → TanM x t.G := fun j => GlobalTheory.LieMet.tanOf (hv j)
  have hT : (tv (T j₀)).left = v j₀ := rfl
  rw [← hT]
  refine (GlobalTheory.ShFam.Pad.Pull.eig_iff (T j₀) a s).2 ?_
  obtain ⟨c, hc, -⟩ := hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (T j₀)))
  have hc' : actR t.act a (T j₀) = ∑ j, c j • T j := (GlobalTheory.LieMet.isComb_iff T c _).1 hc
  have key : ∀ j, c j = if j = j₀ then s else 0 := fun j => by
    rw [← sub_eq_zero]
    refine hz _ fun k _ φ hφ => ?_
    rw [map_sub, sub_eq_zero]
    have hx : spMap φ ≫ x = spMap φ ≫ x := rfl
    have hv' := fun j => GlobalTheory.LieMet.isTan_map φ hx (hv j)
    have hb' := GlobalTheory.GradedPieces.basis_map φ hx hv hbas
    let T' : Fin n → TanM (spMap φ ≫ x) t.G := fun j => GlobalTheory.LieMet.tanOf (hv' j)
    have c1 := GlobalTheory.GradedPieces.comb_map φ hx hc
    have hw' : (tv (φ s • T' j₀)).left = spMap (dualMap φ) ≫ (tv (actR t.act a (T j₀))).left :=
      (hpt k φ hφ).symm
    have c2 : IsCombAtG t (spMap φ ≫ x) (fun j => spMap (dualMap φ) ≫ v j)
        (fun j => φ (if j = j₀ then s else 0)) (spMap (dualMap φ) ≫ (tv (actR t.act a (T j₀))).left) := by
      rw [← hw']
      refine (GlobalTheory.LieMet.isComb_iff T' _ _).2 ?_
      simp only [apply_ite φ, map_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact congrFun ((hb' _ (GlobalTheory.LieMet.isTan_map φ hx (GlobalTheory.LieMet.isTan_tv _))).unique c1 c2) j
  rw [hc']
  simp only [key, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Generic

theorem base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) {b : Z.i.c.V W →+* Γ(Z.X, U)} (hb : hU.fromSpec ≫ Z.s = spMap b)
    {k : Type} [Field k] {φ : Γ(Z.X, U) →+* k} {a' : Fin Z.m} {φ' : Γ(Z.X, (Z.U a').1) →+* k}
    (h : spMap φ' ≫ Z.chart a' = spMap φ ≫ hU.fromSpec) (y : Z.i.c.V W) : φ (b y) = φ' (Z.alg a' y.1) := by
  have e : spMap (φ.comp b) = spMap ((φ'.comp (Z.alg a')).comp (Z.i.c.V W).subtype) := by
    rw [← ModelRelProbe.spMap_comp, ← ModelRelProbe.spMap_comp, ← GlobalTheory.ShFam.Pad.Pull.affineOpenChart_comp_structure_eq_spMap Z h, Z.π_s, Category.assoc, hb]
  exact congrArg (fun f => f y) (congrArg CommRingCat.Hom.hom
    (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) e))

theorem eig_of_intFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (b : Z.i.c.V W →+* Γ(Z.X, U)), hU.fromSpec ≫ Z.s = spMap b → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (a : 𝓞 E) (h : embK Z.i.c τ a ∈ Z.i.c.V W), w τ i ≫ ((Y Z.i).t.act.act a).left = spMap (epsMul (b ⟨_, h⟩)) ≫ w τ i := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z U hU w hw b hb τ i a h
  obtain ⟨n, v, e, he, hv, hbas⟩ := hw.1 τ
  have := GlobalTheory.ShFam.Pad.Pull.isReduced_model Z
  rw [← he i]
  refine eig_of_points hv hbas a (b ⟨_, h⟩) (e i)
    (fun k _ φ => Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) (fun r hr => eq_zero_of_dense hU Z.dense r hr)
    fun k _ φ hr => ?_
  have hF2 := hw.2 k φ hr
  unfold GlobalTheory.LocM.Pre.FlagAt at hF2
  obtain ⟨a', φ', hch, hF, -⟩ := hF2
  have eig := (hF.1 τ i).2 a
  have hs : φ (b ⟨_, h⟩) = (φ'.comp (Z.alg a')) (embK Z.i.c τ a) := base_eq Z hU hb hch ⟨_, h⟩
  simp only [Vecs.bc] at eig
  rw [← hs, ← he i] at eig
  exact eig

end GlobalTheory.HTLine
