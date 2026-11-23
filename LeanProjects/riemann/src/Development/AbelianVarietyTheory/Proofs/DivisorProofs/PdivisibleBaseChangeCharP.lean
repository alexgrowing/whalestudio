import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

theorem exists_eq_one_tmul {R K M : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup M] [Module R M] [Module.Finite R M] (y : K ⊗[R] M)
    (hy : ∀ δ : M →ₗ[R] R, LinearMap.liftBaseChange K (Algebra.linearMap R K ∘ₗ δ) y ∈ (1 : Submodule R K)) :
    ∃ m : M, y = 1 ⊗ₜ m := by
  classical
  let j : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors R) j y
  have hs' : (s : R) • y = j m := hs
  have hs0 : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  haveI : Module.IsTorsionFree R (K ⊗[R] M) := Module.IsTorsionFree.trans K
  let b := Module.Free.chooseBasis R (LinearMap.range j)
  have key : ∀ i, ∃ r : R, b.repr (j.rangeRestrict m) i = (s : R) * r := fun i => by
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hy (b.coord i ∘ₗ j.rangeRestrict))
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    have e := congrArg (LinearMap.liftBaseChange K (Algebra.linearMap R K ∘ₗ (b.coord i ∘ₗ j.rangeRestrict))) hs'
    rw [← algebraMap_smul K, map_smul, ← hr] at e
    rw [map_mul]
    simpa [j] using e.symm
  choose r hr using key
  have e : j.rangeRestrict m = (s : R) • ∑ i, r i • b i := by
    rw [← b.sum_repr (j.rangeRestrict m), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr, mul_smul]
  obtain ⟨m', hm'⟩ := (∑ i, r i • b i).2
  refine ⟨m', smul_right_injective _ (nonZeroDivisors.coe_ne_zero s) ?_⟩
  exact hs'.trans ((congrArg Subtype.val e).trans (congrArg ((s : R) • ·) hm'.symm))

section Tangent

variable {p : ℕ} {R : Type} [CommRing R] {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G]

theorem FinTower.one_y (s : FinTower Γ G) (n : ℕ) (B : Type) [CommRing B] [Algebra R B] :
    spOver (1 : WithConv (Γ.A n →ₐ[R] B)).ofConv ≫ s.y n = 1 :=
  map_one (MonoidHom.mk' (fun φ : WithConv (Γ.A n →ₐ[R] B) => spOver φ.ofConv ≫ s.y n) (s.mul n B))

theorem FinTower.isTangent_iff (s : FinTower Γ G) (n : ℕ) (ψ : Γ.A n →ₐ[R] DualNumber R) :
    IsTangent (spOver ψ ≫ s.y n) ↔ ∀ a, (ψ a).fst = Coalgebra.counit a := by
  constructor
  · intro h a
    have e := (GrpTangent.epsScale_zero_comp h).trans (s.one_y n _).symm
    rw [epsScale_eq, ← Category.assoc, spOver_comp] at e
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using congrArg TrivSqZeroExt.fst (DFunLike.congr_fun (s.inj n _ _ _ e) a)
  · intro h
    have h1 : IsTangent (1 : epsR R ⟶ G) := (GrpTangent.isTangent_iff _).2 (MonObj.comp_one _)
    rw [← s.one_y n] at h1
    refine Eq.trans ?_ h1
    rw [Over.comp_left, Over.comp_left, spOver_left, spOver_left, ← Category.assoc, ← Category.assoc,
      ← Cris.spMap_comp, ← Cris.spMap_comp]
    refine congrArg (spMap · ≫ (s.y n).left) (RingHom.ext fun a => ?_)
    simpa using h a

theorem lieCorr_apply (hp : (p : R) = 0) {t : Γ.TorsionTower G} {x : Γ.Lie} {ψ : Γ.A 1 →ₐ[R] DualNumber R}
    (h : t.LieCorr x (spOver ψ ≫ t.y 1)) (w : Γ.omega) (a : Γ.A 1) (ha : dUnit R a = w.1 1) :
    x w = (ψ a).snd := by
  obtain ⟨ψ', h1, h2⟩ := h.2 1
  rw [epsRedPow, ← Category.assoc, spOver_comp] at h1
  have e := h2 w a ha
  rw [t.inj 1 _ _ _ h1, AlgHom.comp_apply, snd_epsTo, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq,
    Ideal.mem_span_singleton, pow_one, hp, zero_dvd_iff, sub_eq_zero] at e
  exact e

theorem exists_der {B : Type} [CommRing B] [Bialgebra R B] (ψ : B →ₐ[R] DualNumber R)
    (h : ∀ a, (ψ a).fst = Coalgebra.counit a) : ∃ δ : Cot R B →ₗ[R] R, ∀ a, δ (dUnit R a) = (ψ a).snd :=
  ⟨AugCot.lift _ (TrivSqZeroExt.sndHom R R ∘ₗ ψ.toLinearMap) fun a b => by simp [h, mul_comm],
    fun _ => AugCot.lift_d ..⟩

end Tangent

section Fibre

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

def epsBC (K : Type) [CommRing K] [Algebra R K] {B : Type} [CommRing B] [Algebra R B] (ψ : B →ₐ[R] DualNumber R) :
    K ⊗[R] B →ₐ[K] DualNumber K :=
  Algebra.TensorProduct.lift (Algebra.ofId K _) ((epsTo R K).comp ψ) fun _ _ => Commute.all _ _

theorem epsBC_tmul {B : Type} [CommRing B] [Algebra R B] (ψ : B →ₐ[R] DualNumber R) (k : K) (a : B) :
    epsBC K ψ (k ⊗ₜ a) = k • epsTo R K (ψ a) := by
  simp [epsBC, Algebra.smul_def]

theorem fst_epsBC {B : Type} [CommRing B] [Bialgebra R B] {ψ : B →ₐ[R] DualNumber R}
    (h : ∀ a, (ψ a).fst = Coalgebra.counit a) (b : K ⊗[R] B) : (epsBC K ψ b).fst = Coalgebra.counit (R := K) b := by
  induction b with
  | zero => simp
  | add x y hx hy => simp only [map_add, TrivSqZeroExt.fst_add, hx, hy]
  | tmul k a => simp [epsBC_tmul, h, Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_epsBC {B : Type} [CommRing B] [Bialgebra R B] {ψ : B →ₐ[R] DualNumber R}
    (h : ∀ a, (ψ a).fst = Coalgebra.counit a) {δ : Cot R B →ₗ[R] R} (hδ : ∀ a, δ (PDiv.dUnit R a) = (ψ a).snd)
    (y : K ⊗[R] Cot R B) (b : K ⊗[R] B) (hb : PDiv.dUnit K b = PDiv.liftSemi (toBaseChange R K B).cot y) :
    (epsBC K ψ b).snd = LinearMap.liftBaseChange K (Algebra.linearMap R K ∘ₗ δ) y := by
  obtain ⟨D, hD⟩ := exists_der _ (fst_epsBC (K := K) h)
  rw [← hD, hb]
  clear hb
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k m =>
    obtain ⟨a, rfl⟩ := AugCot.d_surjective _ m
    rw [PDiv.liftSemi_tmul, map_smul, SemiBialgHom.cot_d, hD, toBaseChange_apply, epsBC_tmul, one_smul, snd_epsTo, ← hδ]
    rfl

variable {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G] {s : FinTower Γ G} {𝒜 : PDivGroup p K}
  {A : Over (Sp K)} [GrpObj A] {t : 𝒜.TorsionTower A} {φ : A.left ⟶ G.left} {κ : Γ.baseChange K ⟶ 𝒜}

abbrev fibrePt (κ : Γ.baseChange K ⟶ 𝒜) (n : ℕ) (ψ : Γ.A n →ₐ[R] DualNumber R) : 𝒜.A n →ₐ[K] DualNumber K :=
  (epsBC K ψ).comp (κ.app n : 𝒜.A n →ₐ[K] (Γ.baseChange K).A n)

theorem FinTower.IsIncl.fibrePt_left (h : s.IsIncl t φ κ) (n : ℕ) (ψ : Γ.A n →ₐ[R] DualNumber R) :
    (spOver (fibrePt κ n ψ) ≫ t.y n).left ≫ φ =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap R K)) ≫ (spOver ψ ≫ s.y n).left := by
  have e : spMap (fibrePt κ n ψ : 𝒜.A n →+* DualNumber K) =
      spMap (epsBC K ψ : K ⊗[R] Γ.A n →+* DualNumber K) ≫ spMap (κ.app n : 𝒜.A n →+* (Γ.baseChange K).A n) :=
    Cris.spMap_comp (κ.app n : 𝒜.A n →+* (Γ.baseChange K).A n) (epsBC K ψ : K ⊗[R] Γ.A n →+* DualNumber K)
  rw [Over.comp_left, Over.comp_left, spOver_left, spOver_left, e, Category.assoc, Category.assoc, h n,
    ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
  refine congrArg (spMap · ≫ (s.y n).left) (RingHom.ext fun a => ?_)
  exact (epsBC_tmul ψ (1 : K) a).trans (one_smul _ _)

theorem lieCorr_fibrePt (hp : (p : K) = 0) {ψ : Γ.A 1 →ₐ[R] DualNumber R}
    (h : ∀ a, (ψ a).fst = Coalgebra.counit a) {δ : Cot R (Γ.A 1) →ₗ[R] R} (hδ : ∀ a, δ (PDiv.dUnit R a) = (ψ a).snd)
    {x : 𝒜.Lie} (hx : t.LieCorr x (spOver (fibrePt κ 1 ψ) ≫ t.y 1)) (w : 𝒜.omega) (y : K ⊗[R] Cot R (Γ.A 1))
    (hy : PDiv.cotMap (κ.app 1) (w.1 1) = PDiv.liftSemi (toBaseChange R K (Γ.A 1)).cot y) :
    x w = LinearMap.liftBaseChange K (Algebra.linearMap R K ∘ₗ δ) y := by
  obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 1)
  rw [lieCorr_apply hp hx w a ha]
  exact snd_epsBC h hδ y _ (by rw [← hy, ← ha]; exact (PDiv.cotMap_d _ _).symm)

end Fibre

theorem mem_intForms_iff (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A]
    (φ : A.left ⟶ G.left) (_ : IsSemiAbelian G) (hφ : IsGrpPullback A G (spMap (algebraMap R K)) φ)
    (Γ : PDivGroup p R) (s : FinTower Γ G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (κ : Γ.baseChange K ⟶ 𝒜)
    (hp : (p : R) = 0) (hκ : s.IsIncl t φ κ) (hA : IsAbelianScheme A) (e : GlobalTheory.Published.DeRhamVectorExtension.Family p)
    (hF : e.Filtered) (hT : e.Tangent) (hn : IsNilpotent (p : K)) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]
    [Module R (primDR A)] [IsScalarTower R K (primDR A)] (c : primDR A) :
    c ∈ intForms G A φ ↔ e hn hA t c ∈ latOmega κ := by
  have hp' : (p : K) = 0 := by rw [← map_natCast (algebraMap R K), hp, map_zero]
  have hval : ∀ (h : HdR A) (w : 𝒜.omega), e hn hA t c = 𝒜.rigOfOmega w →
      h c = 𝒜.lieUnivToLie ((e hn hA t).symm.dualMap h) w := fun h w hw =>
    (e.lie_apply hn hA t h c).symm.trans (congrArg (e.lie hn hA t h) hw)
  constructor
  · rintro ⟨hc, hint⟩
    obtain ⟨w, hw⟩ := (hF hn hA t).le ⟨c, hc, rfl⟩
    obtain ⟨y, hy⟩ := (liftSemi_toBaseChange_cot_bijective R K (Γ.A 1)).2 (PDiv.cotMap (κ.app 1) (w.1 1))
    haveI : Module.Finite R (Cot R (Γ.A 1)) := .of_surjective _ (AugCot.d_surjective _)
    obtain ⟨m, rfl⟩ := exists_eq_one_tmul y fun δ => by
      let ψ : Γ.A 1 →ₐ[R] DualNumber R := AugCot.toSqZero _ δ
      have h1 : ∀ a, (ψ a).fst = Coalgebra.counit a := AugCot.fst_toSqZero _ δ
      have h2 : ∀ a, δ (PDiv.dUnit R a) = (ψ a).snd := fun a => (AugCot.snd_toSqZero _ δ a).symm
      have h3 : IsTangent (spOver (fibrePt κ 1 ψ) ≫ t.y 1) :=
        ((FinTower.ofTower t).isTangent_iff 1 _).2 fun a =>
          (fst_epsBC h1 _).trans (CoalgHomClass.counit_comp_apply (κ.app 1) a)
      haveI : IsAdicComplete (Ideal.span {(p : K)}) K := by
        rw [hp', Ideal.span_singleton_zero]; infer_instance
      obtain ⟨x, hx, -⟩ := t.existsUnique_lieCorr h3
      obtain ⟨X, rfl⟩ : ∃ X, 𝒜.lieUnivToLie X = x :=
        LinearMap.dualMap_surjective_of_injective (𝒜.rigOfOmega_injective_of_eq_zero hp') x
      obtain ⟨h, rfl⟩ := (e hn hA t).symm.dualMap.surjective X
      rw [← lieCorr_fibrePt hp' h1 h2 hx w y hy.symm, ← hval h w hw.symm]
      exact hint _ _ h ((s.isTangent_iff 1 ψ).2 h1) (hκ.fibrePt_left 1 ψ) ((hT hn hA t h _).2 hx)
    obtain ⟨w₀, rfl⟩ := (Γ.omegaLevel_one_bijective hp).2 m
    refine ⟨w, w₀, hw.symm, ((Γ.baseChange K).omegaLevel_one_bijective hp').1 ?_⟩
    exact hy.symm.trans (one_smul K _)
  · rintro ⟨w, w₀, hw, h₀⟩
    refine ⟨?_, fun v v' h hv hv' hh => ?_⟩
    · obtain ⟨c', hc', e'⟩ := (hF hn hA t).ge ⟨w, hw.symm⟩
      exact (e hn hA t).injective e' ▸ hc'
    · haveI : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
      obtain ⟨ψ, rfl⟩ := s.surj 1 (DualNumber R) v (by
        rw [GrpTangent.pow_eq_epsScale_comp hv, pow_one, hp, GrpTangent.epsScale_zero_comp hv])
      have h1 := (s.isTangent_iff 1 ψ).1 hv
      obtain ⟨δ, h2⟩ := exists_der ψ h1
      obtain rfl : v' = spOver (fibrePt κ 1 ψ) ≫ t.y 1 := Over.OverMorphism.ext
        (hφ.1.hom_ext (hv'.trans (hκ.fibrePt_left 1 ψ).symm) ((Over.w _).trans (Over.w _).symm))
      rw [hval h w hw, lieCorr_fibrePt hp' h1 h2 ((hT hn hA t h _).1 hh) w (1 ⊗ₜ w₀.1 1)
        ((congrArg (fun z : (Γ.baseChange K).omega => z.1 1) h₀).trans (one_smul K _).symm)]
      exact Submodule.mem_one.2 ⟨δ (w₀.1 1), by simp⟩

end GlobalTheory.BadPt
