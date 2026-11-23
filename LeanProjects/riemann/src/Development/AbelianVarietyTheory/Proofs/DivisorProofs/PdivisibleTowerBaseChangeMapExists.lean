import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open Coalgebra Bialgebra WithConv
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

section

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {G : Over (Sp R)} [GrpObj G]
  {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left} {Γ : PDivGroup p R} (s : FinTower Γ G)
  (h : IsGrpPullback A G (spMap (algebraMap R K)) φ)

def FinTower.pts (n : ℕ) (B : Type) [CommRing B] [Algebra R B] :
    WithConv (Γ.A n →ₐ[R] B) →* (SpAlg R B ⟶ G) :=
  MonoidHom.mk' (fun x => spOver x.ofConv ≫ s.y n) (s.mul n B)

def FinTower.fibreY (n : ℕ) : SpAlg K (K ⊗[R] Γ.A n) ⟶ A :=
  ((ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 (K ⊗[R] Γ.A n) fun _ => rfl).2
    (spOver Algebra.TensorProduct.includeRight ≫ s.y n)).choose

theorem FinTower.fibreY_left (n : ℕ) : (s.fibreY h n).left ≫ φ =
    spMap (toBaseChange R K (Γ.A n)).toRingHom ≫ (s.y n).left :=
  congrArg Over.Hom.left ((ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 (K ⊗[R] Γ.A n)
    fun _ => rfl).2 (spOver Algebra.TensorProduct.includeRight ≫ s.y n)).choose_spec

theorem FinTower.ptsDown_fibreY (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Algebra K B]
    (hB : ∀ r, algebraMap R B r = algebraMap K B (algebraMap R K r))
    (x : WithConv (K ⊗[R] Γ.A n →ₐ[K] B)) :
    ptsDown (grpMor_of_isGrpPullback h) B hB (spOver x.ofConv ≫ s.fibreY h n) =
      s.pts n B ((toBaseChange R K (Γ.A n)).pts B hB x) :=
  Over.OverMorphism.ext (by
    rw [ptsDown_left, Over.comp_left, Category.assoc, FinTower.fibreY_left, spOver_left,
      ← Category.assoc, ← Cris.spMap_comp]
    rfl)

def FinTower.fibrePts (n : ℕ) (B : Type) [CommRing B] [Algebra K B] :
    WithConv (K ⊗[R] Γ.A n →ₐ[K] B) →* (SpAlg K B ⟶ A) :=
  MonoidHom.mk' (fun x => spOver x.ofConv ≫ s.fibreY h n) fun x y => by
    let _ : Algebra R B := ((algebraMap K B).comp (algebraMap R K)).toAlgebra
    refine (ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 B fun _ => rfl).1 ?_
    rw [_root_.map_mul, s.ptsDown_fibreY, s.ptsDown_fibreY, s.ptsDown_fibreY,
      _root_.map_mul, _root_.map_mul]

theorem FinTower.fibrePts_injective (n : ℕ) (B : Type) [CommRing B] [Algebra K B] :
    Function.Injective (s.fibrePts h n B) := fun x y e => by
  let _ : Algebra R B := ((algebraMap K B).comp (algebraMap R K)).toAlgebra
  have e' := congrArg (ptsDown (grpMor_of_isGrpPullback h) B fun _ => rfl) e
  exact (toBaseChange_pts_bijective K B _).1 (ofConv_injective (s.inj n B _ _
    ((s.ptsDown_fibreY h n B _ x).symm.trans (e'.trans (s.ptsDown_fibreY h n B _ y)))))

theorem FinTower.fibreY_pow (n : ℕ) : s.fibreY h n ^ p ^ n = 1 := by
  have e : s.fibrePts h n _ (toConv (AlgHom.id K _)) = s.fibreY h n := by
    change spOver (AlgHom.id K _) ≫ _ = _
    rw [spOver_id, Category.id_comp]
  rw [← e, ← map_pow, (Γ.baseChange K).pts_pow_self, map_one]

theorem FinTower.res_fibreY (n : ℕ) :
    spOver ((Γ.baseChange K).res n : K ⊗[R] Γ.A (n + 1) →ₐ[K] K ⊗[R] Γ.A n) ≫ s.fibreY h (n + 1) =
      s.fibreY h n := by
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  rw [Over.comp_left, Category.assoc, s.fibreY_left, s.fibreY_left, ← s.res n,
    Over.comp_left, spOver_left, spOver_left, ← Category.assoc, ← Category.assoc,
    ← Cris.spMap_comp, ← Cris.spMap_comp]
  rfl

variable {𝒜 : PDivGroup p K} (t : 𝒜.TorsionTower A)

def FinTower.inclAlg (n : ℕ) : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n := t.lift n _ (s.fibreY_pow h n)

theorem FinTower.pts_inclAlg (n : ℕ) (B : Type) [CommRing B] [Algebra K B]
    (x : WithConv (K ⊗[R] Γ.A n →ₐ[K] B)) :
    t.pts n B (toConv (x.ofConv.comp (s.inclAlg h t n))) = s.fibrePts h n B x := by
  rw [TorsionTower.pts_apply, ofConv_toConv, ← spOver_comp, Category.assoc, FinTower.inclAlg, t.lift_y]
  rfl

def FinTower.inclApp (n : ℕ) : 𝒜.A n →ₐc[K] K ⊗[R] Γ.A n :=
  (SemiBialgHom.ofPts (σ := RingHom.id K) (s.inclAlg h t n : 𝒜.A n →+* K ⊗[R] Γ.A n)
    (s.inclAlg h t n).commutes
    (fun a => by
      have e := s.pts_inclAlg h t n K 1
      rw [map_one, ← map_one (t.pts n K)] at e
      exact DFunLike.congr_fun (congrArg ofConv (t.pts_injective n K e)) a)
    (fun B _ i j hB x y x₀ y₀ hx hy a => by
      obtain rfl : i = j := Algebra.algebra_ext _ _ hB
      obtain rfl : x₀ = toConv (x.ofConv.comp (s.inclAlg h t n)) := ofConv_injective (AlgHom.ext hx)
      obtain rfl : y₀ = toConv (y.ofConv.comp (s.inclAlg h t n)) := ofConv_injective (AlgHom.ext hy)
      have e := s.pts_inclAlg h t n B (x * y)
      rw [map_mul, ← s.pts_inclAlg h t, ← s.pts_inclAlg h t, ← map_mul] at e
      exact (DFunLike.congr_fun (congrArg ofConv (t.pts_injective n B e)) a).symm)).toBialgHom

theorem FinTower.inclApp_y (n : ℕ) :
    spOver (s.inclApp h t n : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n) ≫ t.y n = s.fibreY h n :=
  t.lift_y n _ (s.fibreY_pow h n)

def FinTower.incl : Γ.baseChange K ⟶ 𝒜 :=
  ⟨s.inclApp h t, fun n => BialgHom.coe_toAlgHom_injective (t.inj (n + 1) _ _ _ (by
    change spOver (((Γ.baseChange K).res n : K ⊗[R] Γ.A (n + 1) →ₐ[K] K ⊗[R] Γ.A n).comp
      (s.inclApp h t (n + 1) : 𝒜.A (n + 1) →ₐ[K] K ⊗[R] Γ.A (n + 1))) ≫ _ =
      spOver ((s.inclApp h t n : 𝒜.A n →ₐ[K] K ⊗[R] Γ.A n).comp (𝒜.res n : 𝒜.A (n + 1) →ₐ[K] 𝒜.A n)) ≫ _
    rw [← spOver_comp, ← spOver_comp, Category.assoc, Category.assoc, t.res, s.inclApp_y, s.inclApp_y,
      s.res_fibreY]))⟩

theorem FinTower.isIncl_incl : s.IsIncl t φ (s.incl h t) := fun n => by
  rw [← Category.assoc]
  exact (congrArg (·.left ≫ φ) (s.inclApp_y h t n)).trans (s.fibreY_left h n)

theorem FinTower.inclApp_surjective (n : ℕ) : Function.Surjective (s.inclApp h t n) := by
  let f : 𝒜.A n →+* K ⊗[R] Γ.A n := s.inclAlg h t n
  have : Epi (CommRingCat.ofHom f) := ⟨fun {Z} u v e => by
    have e' : ∀ a, u.hom (s.inclAlg h t n a) = v.hom (s.inclAlg h t n a) := fun a =>
      congrArg (fun k : CommRingCat.of (𝒜.A n) ⟶ Z => k.hom a) e
    let _ : Algebra K Z := (u.hom.comp (algebraMap K _)).toAlgebra
    let u' : K ⊗[R] Γ.A n →ₐ[K] Z := { u.hom with commutes' := fun _ => rfl }
    let v' : K ⊗[R] Γ.A n →ₐ[K] Z := { v.hom with
      commutes' := fun r => by
        have := e' (algebraMap K _ r)
        rw [AlgHom.commutes] at this
        exact this.symm }
    have e2 : toConv u' = toConv v' := s.fibrePts_injective h n Z (by
      rw [← s.pts_inclAlg h t, ← s.pts_inclAlg h t]
      exact congrArg (t.pts n Z <| toConv ·) (AlgHom.ext e'))
    exact CommRingCat.hom_ext (congrArg (fun k => k.ofConv.toRingHom) e2)⟩
  refine RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom f) ?_
  refine RingHom.Finite.of_comp_finite (f := algebraMap K (𝒜.A n)) ?_
  have e : f.comp (algebraMap K (𝒜.A n)) = algebraMap K _ := RingHom.ext (s.inclAlg h t n).commutes
  exact e ▸ RingHom.finite_algebraMap.2 inferInstance

include h in

theorem isCommMonObj_of_isGrpPullback [IsCommMonObj G] : IsCommMonObj A := by
  have key : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := fun T x y => by
    let d : (T ⟶ A) → (Over.mk (T.hom ≫ spMap (algebraMap R K)) ⟶ G) := fun z =>
      Over.homMk (z.left ≫ φ) (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
    refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [← h.2 T x y (d x) (d y) rfl rfl, ← h.2 T y x (d y) (d x) rfl rfl, mul_comm]
  refine ⟨?_⟩
  have e := key _ (snd A A) (fst A A)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, lift_snd_fst, Category.id_comp] at e
  exact e

theorem FinTower.tangent_mem_range [IsLocalRing R] [IsCommMonObj G] (hs : Smooth G.hom) (hp : (p : R) = 0)
    {w : epsR K ⟶ A} (hw : IsTangent w) : w ∈ MonoidHom.mrange (s.fibrePts h 1 (DualNumber K)) := by
  have := isCommMonObj_of_isGrpPullback h
  obtain ⟨d, v, hv⟩ := Chart.exists_isLieBasis G hs
  obtain ⟨v', hv', e⟩ := exists_isLieBasis_baseChange R K (algebraMap R K) G A φ h hs d v hv
  obtain ⟨c, ⟨u, hu, rfl⟩, -⟩ := hv'.2 w hw
  refine Submonoid.list_prod_mem _ fun z hz => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  obtain ⟨x₀, hx₀⟩ := s.surj 1 (DualNumber R) (v i) (by
    rw [GrpTangent.pow_eq_epsScale_comp (hv.1 i), pow_one, hp, GrpTangent.epsScale_zero_comp (hv.1 i)])
  let _ : Algebra R (DualNumber K) := ((algebraMap K _).comp (algebraMap R K)).toAlgebra
  let j : DualNumber R →ₐ[R] DualNumber K :=
    { (epsScaleR (c i)).comp (Chart.dualMapR (algebraMap R K)) with
      commutes' := fun r => by
        change _ = algebraMap K _ (algebraMap R K r)
        ext <;> simp [epsScaleR, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl'] }
  obtain ⟨x, hx⟩ := (toBaseChange_pts_bijective (R := R) K (DualNumber K) fun _ => rfl).2 (toConv (j.comp x₀))
  refine ⟨x, (ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 (DualNumber K) fun _ => rfl).1 ?_⟩
  refine (s.ptsDown_fibreY h 1 _ _ x).trans (Over.OverMorphism.ext ?_)
  rw [hx, ptsDown_left, hu, Category.assoc, e, ← hx₀, ← Category.assoc, ← Cris.spMap_comp, Over.comp_left,
    ← Category.assoc, spOver_left, ← Cris.spMap_comp]
  rfl

end

theorem exists_isIncl (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A]
    (φ : A.left ⟶ G.left) (hG : IsSemiAbelian G) (h : IsGrpPullback A G (spMap (algebraMap R K)) φ)
    (Γ' : PDivGroup p R) (s : FinTower Γ' G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (hp : (p : R) = 0) :
    ∃ κ : Γ'.baseChange K ⟶ 𝒜, s.IsIncl t φ κ ∧ Function.Surjective (κ.app 1) ∧
      Function.Bijective (omegaMap _ _ κ) := by
  have := hG.comm
  have hK : (p : K) = 0 := by rw [← map_natCast (algebraMap R K), hp, map_zero]
  refine ⟨s.incl h t, s.isIncl_incl h t, s.inclApp_surjective h t 1, ?_⟩
  have hc : Function.Bijective (cotMap (s.inclApp h t 1)) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, fun w => ?_⟩
    · refine (Module.forall_dual_apply_eq_zero_iff K w).1 fun f => ?_
      obtain ⟨a, rfl⟩ := AugCot.d_surjective _ w
      let ψ : 𝒜.A 1 →ₐ[K] DualNumber K := AugCot.toSqZero _ f
      have hψ : IsTangent (G := A) (spOver ψ ≫ t.y 1) := by
        have h1 := congrArg Over.Hom.left ((t.eq_one_iff 1 ((TrivSqZeroExt.fstHom K K K).comp ψ)).2
          fun a => AugCot.fst_toSqZero _ f a)
        rw [← spOver_comp, Category.assoc, Over.comp_left, Hom.one_def, Over.comp_left] at h1
        refine h1.trans ?_
        have h2 : (toUnit (SpAlg K K)).left = 𝟙 (Sp K) := Cris.spMap_id K
        exact (congrArg (· ≫ η[A].left) h2).trans (Category.id_comp _)
      obtain ⟨x, hx⟩ := s.tangent_mem_range h hG.smooth hp hψ
      have h3 : ∀ a, x.ofConv (s.inclApp h t 1 a) = ψ a := DFunLike.congr_fun
        (t.inj 1 _ _ _ ((s.pts_inclAlg h t 1 _ x).trans hx))
      have h4 : ∀ b, (x.ofConv b).fst = counitAlgHom K _ b := fun b => by
        obtain ⟨a, rfl⟩ := s.inclApp_surjective h t 1 b
        rw [h3, AugCot.fst_toSqZero]
        exact (CoalgHomClass.counit_comp_apply (s.inclApp h t 1) a).symm
      have h5 := congrArg (AugCot.ofSqZero _ x.ofConv h4) hw
      rw [cotMap_d, AugCot.ofSqZero_d, h3, AugCot.snd_toSqZero, map_zero] at h5
      exact h5
    · obtain ⟨b, rfl⟩ := AugCot.d_surjective _ w
      obtain ⟨a, rfl⟩ := s.inclApp_surjective h t 1 b
      exact ⟨dUnit K a, cotMap_d _ a⟩
  have e : (Γ'.baseChange K).omegaLevel 1 ∘ omegaMap _ _ (s.incl h t) =
    cotMap (s.inclApp h t 1) ∘ 𝒜.omegaLevel 1 := rfl
  exact (Function.Bijective.of_comp_iff' ((Γ'.baseChange K).omegaLevel_one_bijective hK) _).1
    (e ▸ hc.comp (𝒜.omegaLevel_one_bijective hK))

end GlobalTheory.BadPt
