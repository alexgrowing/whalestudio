import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TvELeft
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffRing

open TrivSqZeroExt (inl inr)

theorem existsUnique_coeff_alg {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {dd : Fin n → Fld G.left}
    (hdd : ∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0)
      (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f))
    {C : Type} [CommRing C] [Algebra R C] (y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C ⟶ G)
    {V : G.left.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ y.left ⁻¹ᵁ V) (δ : Γ(G.left, V) → C)
    (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = evalPt y.left V h f * δ f' + evalPt y.left V h f' * δ f)
    (hbase : ∀ r, δ (constFn G.hom V r) = 0) :
    ∃! c : Fin n → C, ∀ f, δ f = ∑ a, c a * evalPt y.left V h (dd a V f) := by
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G :=
    ReciprocityTheory.ChartRestriction.G.Chart.spMap (TrivSqZeroExt.inlAlgHom R C C) ≫ y
  have hz : ⊤ ≤ z.left ⁻¹ᵁ V := fun t _ => h (Set.mem_univ _)
  have ez : ∀ s, evalPt z.left V hz s = inl (evalPt y.left V h s) := fun s =>
    evalPt_spMap_comp (TrivSqZeroExt.inlAlgHom R C C).toRingHom y.left V h hz s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.InvFieldBasis.exists_dualHom (evalPt y.left V h) δ hadd hmul
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hV ψ
  have hxp : x ≫ G.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C)).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap R (DualNumber C)) fun a => ?_).trans rfl
    rw [← evalPt_constFn G.hom x V hx, ex, hψ, hbase, evalPt_constFn G.hom y.left V h a,
      GlobalTheory.InvFieldBasis.evalPt_congr (Over.w y) ⊤ le_rfl le_rfl]
    have e2 : evalPt (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) C).hom ⊤ le_rfl
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = algebraMap R C a :=
      evalPt_spMap (algebraMap R C) a
    rw [e2, TrivSqZeroExt.inr_zero, add_zero]
    exact (TrivSqZeroExt.algebraMap_eq_inl' R C C _).symm
  let w : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber C) ⟶ G := Over.homMk x hxp
  have ext : ∀ {B : Type} [CommRing B] [Algebra R B] (u u' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G),
      u.left = u'.left → u = u' := fun u u' e => Over.OverMorphism.ext e
  let fstR : DualNumber C →ₐ[R] C := TrivSqZeroExt.fstHom R C C
  let J : Ideal (DualNumber C) := RingHom.ker fstR
  have memJ : ∀ a : DualNumber C, a ∈ J ↔ a.fst = 0 := fun a => RingHom.mem_ker
  have hJ : J ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    rw [Ideal.mem_bot]
    have ea : a = inr a.snd := TrivSqZeroExt.ext ((memJ a).1 ha) rfl
    have eb : b = inr b.snd := TrivSqZeroExt.ext ((memJ b).1 hb) rfl
    rw [ea, eb, TrivSqZeroExt.inr_mul_inr]
  let g : C →ₐ[R] DualNumber C ⧸ J := (Ideal.Quotient.mkₐ R J).comp (TrivSqZeroExt.inlAlgHom R C C)
  have hg : Ideal.Quotient.mkₐ R J = g.comp fstR := by
    refine AlgHom.ext fun a => ?_
    change Ideal.Quotient.mk J a = Ideal.Quotient.mk J (inl a.fst)
    refine Ideal.Quotient.eq.2 ((memJ _).2 ?_)
    simp
  have t1 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ z = y := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp]
    have : fstR.comp (TrivSqZeroExt.inlAlgHom R C C) = AlgHom.id R C := AlgHom.ext fun _ => rfl
    rw [this, ReciprocityTheory.ChartRestriction.G.Chart.spMap_id, Category.id_comp]
  have t2 : ReciprocityTheory.ChartRestriction.G.Chart.spMap fstR ≫ w = y := by
    refine ext _ _ ?_
    rw [Over.comp_left]
    have h' : ⊤ ≤ (spMap fstR.toRingHom ≫ x) ⁻¹ᵁ V := fun t _ => hx (Set.mem_univ _)
    refine ext_evalPt hV h' h (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ x V hx h' f).trans ?_
    rw [ex, hψ]
    exact add_zero _
  have hred : ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ z =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (Ideal.Quotient.mkₐ R J) ≫ w := by
    rw [hg, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, Category.assoc, t1, t2]
  obtain ⟨c, hc, hcu⟩ := GlobalTheory.SqZero.existsUnique_eq_lieExp_mul hv hJ hred
  have key : ∀ c' : Fin n → C, (w = GlobalTheory.SqZero.lieExp v (fun i => inr (c' i))
      (fun i => TrivSqZeroExt.inr_mul_inr _ _ _) * z) ↔
      ∀ f, δ f = ∑ a, c' a * evalPt y.left V h (dd a V f) := by
    intro c'
    obtain ⟨h₁, H₁⟩ := hdd (DualNumber C) (fun i => inr (c' i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _) z V hz
    constructor
    · intro e f
      have := H₁ f
      rw [← GlobalTheory.InvFieldBasis.evalPt_congr (show x = _ from congrArg (fun u => u.left) e) V hx h₁,
        ex, hψ] at this
      simp only [ez] at this
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).1 this
    · intro e
      refine ext _ _ (ext_evalPt hV hx h₁ (RingHom.ext fun f => ?_))
      rw [H₁]
      change evalPt x V hx f = _
      rw [ex, hψ]
      simp only [ez]
      exact (GlobalTheory.InvFieldBasis.dual_eq_iff _ _ _ _).2 (e f)
  have hinr : ∀ a : J, (a : DualNumber C) = inr (a : DualNumber C).snd := fun a =>
    TrivSqZeroExt.ext ((memJ _).1 a.2) rfl
  refine ⟨fun i => (c i : DualNumber C).snd, (key _).1 (hc.trans ?_), fun c' hc' => ?_⟩
  · rw [GlobalTheory.SqZero.lieExp_congr v (fun i => hinr (c i)) _ (fun i => TrivSqZeroExt.inr_mul_inr _ _ _)]
  · have hmem : ∀ i, inr (c' i) ∈ J := fun i => (memJ _).2 rfl
    have := hcu (fun i => ⟨inr (c' i), hmem i⟩) ((key c').2 hc')
    funext i
    exact congrArg (fun d : Fin n → J => (d i : DualNumber C).snd) this

theorem existsUnique_coeff_affine_ring : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (v : Fin n → (epsR R ⟶ G)), IsLieBasis v → ∀ (dd : Fin n → Fld G.left),
    (∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + ∑ i, e i * GlobalTheory.TangentOrigin.evalPt z.left O h (dd i O f)) →
    ∀ (V V' : G.left.Opens), IsAffineOpen V → IsAffineOpen V' → V' ≤ V → ∀ (δ : Γ(G.left, V) → Γ(G.left, V')),
    (∀ f f', δ (f + f') = δ f + δ f') → (∀ f f', δ (f * f') = rsT f V' * δ f' + rsT f' V' * δ f) →
    (∀ r, δ (constFn G.hom V r) = 0) →
    ∃! c : Fin n → Γ(G.left, V'), ∀ f, δ f = ∑ a, c a * rsT (dd a V f) V' := by
  intro R _ G _ _ _ n v hv dd hdd V V' hV hV' hle δ hadd hmul hbase
  obtain ⟨t, ht, et⟩ := exists_evalPt_eq (R := Γ(G.left, V')) hV' (RingHom.id _)
  letI : Algebra R Γ(G.left, V') := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) Γ(G.left, V') ⟶ G :=
    Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
  have h : ⊤ ≤ y.left ⁻¹ᵁ V := fun s hs => hle (ht hs)
  have ev : ∀ s, evalPt y.left V h s = rsT s V' := fun s => by
    refine (evalPt_res t hle h ht s).symm.trans ?_
    rw [et, GlobalTheory.KS.rsT, dif_pos hle]
    rfl
  have := existsUnique_coeff_alg hv hdd y hV h δ hadd (by simpa only [ev] using hmul) hbase
  simpa only [ev] using this

end GlobalTheory.VertCoeffRing
