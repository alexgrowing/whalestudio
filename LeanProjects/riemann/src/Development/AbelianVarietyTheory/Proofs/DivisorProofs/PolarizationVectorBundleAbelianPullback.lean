import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackFstComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfGenerization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt.Fibre

section Frames

variable {X Y : Scheme.{0}} {I : Type} [Fintype I] {k : Type} [CommRing k]

theorem frame_pb (f : Y ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
    {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
  have := (he.pullback f).res h
  exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ this

abbrev ofFn (k : Type) [CommRing k] : Γ(Sp k, ⊤) →+* k := (Scheme.ΓSpecIso (.of k)).hom.hom

theorem cst_ofFn (a : Γ(Sp k, ⊤)) : cst k (ofFn k a) = a := Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of k)) a

theorem ofFn_cst (a : k) : ofFn k (cst k a) = a := Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of k)) a

theorem exists_coord {M : (Sp k).Modules} {e : I → Γ(M, ⊤)} (he : IsFrame e) (s : Γ(M, ⊤)) :
    ∃ c : I → k, s = ∑ i, cst k (c i) • e i := by
  refine ⟨fun i => ofFn k ((he.basis le_rfl).repr s i), ?_⟩
  conv_lhs => rw [← (he.basis le_rfl).sum_repr s]
  simp only [cst_ofFn, IsFrame.basis_apply, Twist.resM_self]

theorem coord_inj {M : (Sp k).Modules} {e : I → Γ(M, ⊤)} (he : IsFrame e) {c d : I → k}
    (h : ∑ i, cst k (c i) • e i = ∑ i, cst k (d i) • e i) : c = d := by
  have H := (he ⊤ le_rfl).1 (a₁ := fun i => cst k (c i)) (a₂ := fun i => cst k (d i))
    (by simpa only [Fintype.linearCombination_apply, Twist.resM_self] using h)
  funext i
  rw [← ofFn_cst (c i), ← ofFn_cst (d i)]
  exact congrArg _ (congrFun H i)

theorem pb_induction {T : Scheme.{0}} (ξ : Sp k ⟶ T) (D : T.Modules) [D.IsQuasicoherent] {V : T.Opens}
    (hV : IsAffineOpen V) (hξ : ⊤ ≤ ξ ⁻¹ᵁ V) (P : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) → Prop)
    (h₁ : ∀ s, P (pullbackSections ξ D hξ s)) (h₂ : ∀ c s, P s → P (cst k c • s))
    (h₃ : ∀ s t, P s → P t → P (s + t)) (s : Γ((Scheme.Modules.pullback ξ).obj D, ⊤)) : P s := by
  letI := QCoh.appLEAlgebra ξ hξ
  letI := QCoh.appLEModule ξ ((Scheme.Modules.pullback ξ).obj D) hξ
  haveI := QCoh.appLE_isScalarTower ξ ((Scheme.Modules.pullback ξ).obj D) hξ
  have H := QCoh.isBaseChange_pullbackSections ξ D (isAffineOpen_top _) hV hξ
  induction s using H.inductionOn with
  | zero => exact map_zero (pullbackSections ξ D hξ) ▸ h₁ 0
  | tmul s => exact h₁ s
  | smul r t ih => exact cst_ofFn r ▸ h₂ _ _ ih
  | add t t' ih ih' => exact h₃ _ _ ih ih'

theorem appLE_cst {k' : Type} [CommRing k'] (φ : k →+* k') (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (a : k) :
    (spMap φ).appLE ⊤ ⊤ h (cst k a) = cst k' (φ a) :=
  (appLE_top (spMap φ) _).trans congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a).symm

theorem ofFn_appLE {k' : Type} [CommRing k'] (φ : k →+* k') (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (z : Γ(Sp k, ⊤)) :
    ofFn k' ((spMap φ).appLE ⊤ ⊤ h z) = φ (ofFn k z) := by
  conv_lhs => rw [← cst_ofFn z, appLE_cst, ofFn_cst]

theorem spMap_fromSpec {T : Scheme.{0}} (ξ : Sp k ⟶ T) {V : T.Opens} (hV : IsAffineOpen V) (hξ : ⊤ ≤ ξ ⁻¹ᵁ V) :
    spMap ((ofFn k).comp (ξ.appLE V ⊤ hξ).hom) ≫ hV.fromSpec = ξ := by
  have h := hV.SpecMap_appLE_fromSpec ξ (isAffineOpen_top _) hξ
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change Spec.map (ξ.appLE V ⊤ hξ ≫ (Scheme.ΓSpecIso (.of k)).hom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, h, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

end Frames

section Reads

variable {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K] {f : Sp R ⟶ X} {f₀ : T ⟶ X}
  {ξ : Sp K ⟶ T} (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {I : Type} [Fintype I] {U : X.Opens} {V : T.Opens}
  (hU : ⊤ ≤ f ⁻¹ᵁ U) (hVU : V ≤ f₀ ⁻¹ᵁ U) (hξ : ⊤ ≤ ξ ⁻¹ᵁ V)

include hU in

theorem resSec_iff {A : X.Modules} [A.IsQuasicoherent] {ε : I → Γ(A, U)} (hε : IsFrame ε)
    (P : Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤) → Prop) :
    (∃ t, P (resSec w A t)) ↔ ∃ r : I → R,
      P (∑ i, cst K (algebraMap R K (r i)) • pullbackSections ξ _ hξ (pullbackSections f₀ A hVU (ε i))) := by
  have key (r : I → R) : resSec w A (∑ i, cst R (r i) • pullbackSections f A hU (ε i)) =
      ∑ i, cst K (algebraMap R K (r i)) • pullbackSections ξ _ hξ (pullbackSections f₀ A hVU (ε i)) := by
    unfold resSec
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (congrArg _ (QCoh.pullbackSections_smul _ _ _ _ _)).trans ?_
    rw [Scheme.Modules.Hom.app_smul, appLE_cst]
    exact congrArg _ (Vert.DivPull.pullbackSquare_app w A hU _ hVU hξ (ε i))
  refine ⟨fun ⟨t, ht⟩ => ?_, fun ⟨r, hr⟩ => ⟨_, (key r).symm ▸ hr⟩⟩
  obtain ⟨r, rfl⟩ := exists_coord (frame_pb f hε hU) t
  exact ⟨r, key r ▸ ht⟩

variable {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]

theorem mem_span_iff (x : I → H) (c : H) :
    c ∈ Submodule.span R (Set.range x) ↔ ∃ r : I → R, c = ∑ i, algebraMap R K (r i) • x i := by
  simp only [Submodule.mem_span_range_iff_exists_fun, algebraMap_smul, eq_comm]

theorem mem_dual_span (β : LinearMap.BilinForm K H) (x : I → H) (c : H) :
    c ∈ β.dualSubmodule (Submodule.span R (Set.range x)) ↔ ∀ i, ∃ r, algebraMap R K r = β c (x i) := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  refine ⟨fun h i => Submodule.mem_one.1 (h _ (Submodule.subset_span ⟨i, rfl⟩)), fun h y hy => ?_⟩
  obtain ⟨r, rfl⟩ := (mem_span_iff (K := K) x y).1 hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_one.2 (h i))

variable {A B : X.Modules} {D : T.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent] [D.IsQuasicoherent]
  {a : (Scheme.Modules.pullback f₀).obj A ⟶ D} {b : D ⟶ (Scheme.Modules.pullback f₀).obj B} {z : a ≫ b = 0}

include hU in

theorem reads_of_frames [DecidableEq I] (hs : (ShortComplex.mk a b z).ShortExact) (hV : IsAffineOpen V)
    {ε : I → Γ(A, U)} (hε : IsFrame ε) {θ : I → Γ(B, U)} (hθ : IsFrame θ)
    (E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H) (hE : ∀ (c : K) s, E (toFn c • s) = c • E s)
    (β : LinearMap.BilinForm K H) {β₀ : D ⟶ dual D}
    (hβ : ∀ s t, β (E (pullbackSections ξ D hξ s)) (E (pullbackSections ξ D hξ t)) =
      ofFn K (ξ.appLE V ⊤ hξ (dualApp (β₀.app V s) le_rfl t)))
    {p : (Scheme.Modules.pullback f₀).obj B ⟶ dual ((Scheme.Modules.pullback f₀).obj A)}
    (hp : b ≫ p = β₀ ≫ dualMap a)
    (hδ : ∀ i j, dualApp (p.app V (pullbackSections f₀ B hVU (θ j))) le_rfl (pullbackSections f₀ A hVU (ε i)) =
      if i = j then 1 else 0)
    (x : I → H) (hx : ∀ i, x i = E (pullbackSections ξ D hξ (a.app V (pullbackSections f₀ A hVU (ε i))))) :
    Reads w a b E β (Submodule.span K (Set.range x)) (Submodule.span R (Set.range x)) ∧
      ∃ s : I → Γ(D, V), (∀ i, b.app V (s i) = pullbackSections f₀ B hVU (θ i)) ∧
        (∀ i j, β (E (pullbackSections ξ D hξ (s j))) (x i) = if i = j then 1 else 0) ∧
        ∀ c : H, ∃ k d : I → K, c = ∑ i, k i • x i + ∑ i, d i • E (pullbackSections ξ D hξ (s i)) ∧
          ∀ i, β c (x i) = d i := by
  have := hs.epi_g
  have := hs.mono_f
  have := QCoh.isQuasicoherent_pullback f₀ A
  have := QCoh.isQuasicoherent_pullback f₀ B
  choose s hsb using fun i => QCoh.surjective_app_of_epi b hV (pullbackSections f₀ B hVU (θ i))
  have ex : Function.Exact (a.app V) (b.app V) := QCoh.exact_app_of_exact_of_mono hs.exact V
  have fε := frame_pb f₀ hε hVU
  have fθ := frame_pb f₀ hθ hVU
  have fY := frame_pb ξ fθ hξ
  let a' := ((Scheme.Modules.pullback ξ).map a).app ⊤
  let b' := ((Scheme.Modules.pullback ξ).map b).app ⊤
  let Xs (i : I) := pullbackSections ξ D hξ (a.app V (pullbackSections f₀ A hVU (ε i)))
  let Zs (i : I) := pullbackSections ξ D hξ (s i)
  have hE' (c : I → K) (t : I → _) : E (∑ i, cst K (c i) • t i) = ∑ i, c i • E (t i) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hE _ _
  have dec (m : Γ((Scheme.Modules.pullback ξ).obj D, ⊤)) :
      ∃ k d : I → K, m = ∑ i, cst K (k i) • Xs i + ∑ i, cst K (d i) • Zs i := by
    refine pb_induction ξ D hV hξ (fun m => ∃ k d : I → K, m = ∑ i, cst K (k i) • Xs i + ∑ i, cst K (d i) • Zs i)
      (fun t => ?_) ?_ ?_ m
    · let d := (fθ.basis le_rfl).repr (b.app V t)
      obtain ⟨u, hu⟩ := (ex (t - ∑ i, d i • s i)).1 (by
        rw [map_sub, map_sum, sub_eq_zero]
        conv_lhs => rw [← (fθ.basis le_rfl).sum_repr (b.app V t)]
        simp only [IsFrame.basis_apply, Twist.resM_self, Scheme.Modules.Hom.app_smul, hsb, d])
      refine ⟨fun i => ofFn K (ξ.appLE V ⊤ hξ ((fε.basis le_rfl).repr u i)), fun i => ofFn K (ξ.appLE V ⊤ hξ (d i)), ?_⟩
      conv_lhs => rw [eq_add_of_sub_eq hu.symm, ← (fε.basis le_rfl).sum_repr u]
      simp only [map_add, map_sum, IsFrame.basis_apply, Twist.resM_self, Scheme.Modules.Hom.app_smul,
        QCoh.pullbackSections_smul, cst_ofFn, Xs, Zs]
    · rintro c _ ⟨k, d, rfl⟩
      exact ⟨fun i => c * k i, fun i => c * d i, by simp only [smul_add, Finset.smul_sum, map_mul, mul_smul]⟩
    · rintro _ _ ⟨k, d, rfl⟩ ⟨k', d', rfl⟩
      exact ⟨fun i => k i + k' i, fun i => d i + d' i, by
        simp only [map_add, add_smul, Finset.sum_add_distrib]; abel⟩
  have ab (t) : b.app V (a.app V t) = 0 := ex.apply_apply_eq_zero t
  have hb (k d : I → K) : b' (∑ i, cst K (k i) • Xs i + ∑ i, cst K (d i) • Zs i) =
      ∑ i, cst K (d i) • pullbackSections ξ _ hξ (pullbackSections f₀ B hVU (θ i)) := by
    simp only [b', Xs, Zs, map_add, map_sum, Scheme.Modules.Hom.app_smul, QCoh.pullback_map_app_pullbackSections, ab,
      hsb, map_zero, smul_zero, Finset.sum_const_zero, zero_add]
  have ha (k : I → K) : a' (∑ i, cst K (k i) • pullbackSections ξ _ hξ (pullbackSections f₀ A hVU (ε i))) =
      ∑ i, cst K (k i) • Xs i := by
    simp only [a', Xs, map_sum, Scheme.Modules.Hom.app_smul, QCoh.pullback_map_app_pullbackSections]
  have hp' (t u) : dualApp (β₀.app V t) le_rfl (a.app V u) = dualApp (p.app V (b.app V t)) le_rfl u :=
    congr(dualApp (($hp).app V t) le_rfl u).symm
  have hE₂ (k d : I → K) : E (∑ i, cst K (k i) • Xs i + ∑ i, cst K (d i) • Zs i) =
      ∑ i, k i • x i + ∑ i, d i • E (Zs i) := by
    rw [map_add, hE', hE']; simp only [hx, Xs]
  have hβ' (k d : I → K) (j : I) : β (∑ i, k i • x i + ∑ i, d i • E (Zs i)) (x j) = d j := by
    simp [hx, Zs, hβ, hp', ab, hsb, hδ, apply_ite (ξ.appLE V ⊤ hξ), apply_ite (ofFn K), LinearMap.sum_apply]
  refine ⟨⟨fun m => ?_, fun m => ?_, fun m => ?_, fun t => ?_⟩, s, hsb, fun i j => ?_, fun c => ?_⟩
  · rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun h => ?_, fun ⟨k, hk⟩ => ?_⟩
    · obtain ⟨k, d, rfl⟩ := dec m
      obtain rfl : d = 0 := coord_inj fY (((hb k d).symm.trans h).trans (by simp))
      exact ⟨k, by rw [hE₂]; simp⟩
    · obtain rfl : m = ∑ i, cst K (k i) • Xs i + ∑ i, cst K ((0 : I → K) i) • Zs i :=
        E.injective (by rw [hE₂, ← hk]; simp)
      exact (hb k 0).trans (by simp)
  · rw [mem_span_iff (K := K), resSec_iff w hU hVU hξ hε fun t => m = a' t]
    refine exists_congr fun r => ?_
    rw [ha, ← E.injective.eq_iff, hE']
    simp only [hx, Xs]
  · rw [mem_dual_span, resSec_iff w hU hVU hξ hθ fun t => b' m = t]
    obtain ⟨k, d, rfl⟩ := dec m
    simp only [hE₂, hβ', hb]
    exact ⟨fun h => by choose r hr using h; exact ⟨r, by simp only [hr]⟩,
      fun ⟨r, hr⟩ i => ⟨r i, (congrFun (coord_inj fY hr) i).symm⟩⟩
  · obtain ⟨d, rfl⟩ := exists_coord fY t
    exact ⟨_, hb 0 d⟩
  · simp only [hx, hβ, hp', hsb, hδ, apply_ite (ξ.appLE V ⊤ hξ), apply_ite (ofFn K), map_one, map_zero]
  · obtain ⟨m, rfl⟩ := E.surjective c
    obtain ⟨k, d, rfl⟩ := dec m
    exact ⟨k, d, hE₂ k d, fun i => by rw [hE₂, hβ']⟩

theorem frob_span [DecidableEq I] {σ : K →+* K} {q : ℕ} (hσ : ∀ a, σ a = a ^ q) (F : H →ₛₗ[σ] H)
    (β : LinearMap.BilinForm K H) {x y z : I → H} (hx : ∀ i, F (x i) = 0) (hy : ∀ i, F (y i) = z i)
    (hδ : ∀ i j, β (y j) (x i) = if i = j then 1 else 0)
    (dec : ∀ c : H, ∃ k d : I → K, c = ∑ i, k i • x i + ∑ i, d i • y i ∧ ∀ i, β c (x i) = d i) :
    Submodule.span K (Set.range F) = Submodule.span K (Set.range z) ∧
      Submodule.span R (F '' (β.dualSubmodule (Submodule.span R (Set.range x)) : Set H)) =
        Submodule.span R (Set.range z) := by
  have key (k d : I → K) : F (∑ i, k i • x i + ∑ i, d i • y i) = ∑ i, d i ^ q • z i := by
    simp [map_smulₛₗ, hx, hy, hσ]
  refine ⟨le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_),
    le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨k, d, rfl, -⟩ := dec c
    exact (Submodule.mem_span_range_iff_exists_fun K).2 ⟨_, (key k d).symm⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, hy i⟩
  · rintro _ ⟨c, hc, rfl⟩
    choose r hr using (mem_dual_span β x c).1 hc
    obtain ⟨k, d, rfl, h⟩ := dec c
    exact (mem_span_iff (K := K) z _).2 ⟨fun i => r i ^ q, by simp only [key, map_pow, hr, h]⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨_, (mem_dual_span β x _).2 fun i => ⟨if i = j then 1 else 0, by
      rw [hδ, apply_ite (algebraMap R K), map_one, map_zero]⟩, hy j⟩

theorem exists_equiv [Algebra Γ(T, V) K] (hσ : ∀ r, algebraMap Γ(T, V) K r = ofFn K (ξ.appLE V ⊤ hξ r))
    {δ : I → Γ(D, V)} (hδ : IsFrame δ) {M : Type*} [AddCommGroup M] [Module Γ(T, V) M] (e : Γ(D, V) ≃ₗ[Γ(T, V)] M)
    (ν : M →ₛₗ[algebraMap Γ(T, V) K] H) (hν : Function.Bijective (liftSemi ν)) :
    ∃ E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H, (∀ (c : K) s, E (toFn c • s) = c • E s) ∧
      ∀ s, E (pullbackSections ξ D hξ s) = ν (e s) := by
  let b' := (Algebra.TensorProduct.basis K ((hδ.basis le_rfl).map e)).map (LinearEquiv.ofBijective _ hν)
  have hb (i : I) : b' i = ν (e (hδ.basis le_rfl i)) := by
    simp [b', -IsFrame.basis_apply]
  let b₁ := (hδ.pullback ξ).basis hξ
  let E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H := b₁.equivFun.toAddEquiv.trans
    ((AddEquiv.piCongrRight fun _ => (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toAddEquiv).trans
      b'.equivFun.symm.toAddEquiv)
  have hE (s) : E s = ∑ i, ofFn K (b₁.repr s i) • b' i := b'.equivFun_symm_apply _
  refine ⟨E, fun c s => ?_, fun s => ?_⟩
  · rw [hE, hE, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]
    exact congrArg (· • _) (ofFn_cst c)
  · rw [hE]
    conv_rhs => rw [← (hδ.basis le_rfl).sum_repr s, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smulₛₗ, hσ, hb]
    exact congrArg (fun z => ofFn K z • _) (hδ.pullback_basis_repr ξ le_rfl hξ s i)

end Reads

section Tangent

open GlobalTheory.HodgeSub.Nat GlobalTheory.TanFibre GlobalTheory.Conormal
open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

theorem relDim {T : Scheme.{0}} {A : Over T} [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ} (hg : IsVB (omega A) g) :
    SmoothOfRelativeDimension g A.hom := by
  have := hA.smooth
  have := hA.geomConnected
  have := hA.proper
  refine CharZeroPts.smoothOfRelativeDimension_of_generization A.hom g fun y =>
    ⟨A.left.residueField y, inferInstance, A.left.fromSpecResidueField y, fun u => ?_, fun m hm => ?_⟩
  · exact specializes_of_eq (Scheme.fromSpecResidueField_apply y u)
  · let x := A.left.fromSpecResidueField y ≫ A.hom
    letI : GrpObj ((Over.pullback x).obj A) := Functor.grpObjObj
    have hp : IsGrpPullback ((Over.pullback x).obj A) A x _ := isGrpPullback_pullback A x
    have : SmoothOfRelativeDimension m ((Over.pullback x).obj A).hom := hm
    have : QuasiSeparated ((Over.pullback x).obj A).hom := MorphismProperty.of_isPullback hp.1 inferInstance
    exact (isVB_omega _ m).rank_unique (isVB_omega_of_isGrpPullback hp hg)

theorem omegaBase_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (h' : IsGrpPullback G'' G' f' φ') {f'' : S'' ⟶ S} {φ'' : G''.left ⟶ G.left}
    (h'' : IsGrpPullback G'' G f'' φ'') (e : f' ≫ f = f'') (e' : φ' ≫ φ = φ'') {U : S.Opens} {V : S'.Opens}
    {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V) (hW' : W ≤ f'' ⁻¹ᵁ U) (s : Γ(omega G, U)) :
    (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) =
      (omegaBase h'').app W (pullbackSections f'' _ hW' s) := by
  subst e e'
  have k {U : S.Opens} {V : S'.Opens} {W : S''.Opens} (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ f' ⁻¹ᵁ V)
      (hW' : W ≤ (f' ≫ f) ⁻¹ᵁ U) (s : Γ(omega G, U)) :
      ((Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
        omegaBase h').app W (pullbackSections (f' ≫ f) _ hW' s) =
      (omegaBase h').app W (pullbackSections f' _ hW ((omegaBase h).app V (pullbackSections f _ hV s))) := by
    rw [← QCoh.app_app, ← QCoh.app_app, Vert.DivPull.pullbackComp_inv_app f' f _ hV hW]
    exact congrArg _ (QCoh.pullback_map_app_pullbackSections f' _ _ _)
  have : (Scheme.Modules.pullbackComp f' f).inv.app (omega G) ≫ (Scheme.Modules.pullback f').map (omegaBase h) ≫
      omegaBase h' = omegaBase h'' := by
    refine pullback_hom_ext (sec_hom η[G]) fun W a => ?_
    have k₁ := le_of_sq (unitSec_comp h) (le_refl (unitSec G ⁻¹ᵁ W)) le_rfl
    have k₂ := le_of_sq (unitSec_comp h') k₁ le_rfl
    refine (k le_rfl le_rfl le_rfl (dUnit G le_rfl a)).trans ?_
    rw [omegaBase_dUnit h le_rfl le_rfl k₁ le_rfl, omegaBase_dUnit h' k₁ le_rfl k₂ le_rfl]
    exact (congrArg _ (appLE_appLE rfl _ _ le_rfl a)).trans (omegaBase_dUnit h'' le_rfl le_rfl k₂ le_rfl a).symm
  rw [← this, k hV hW]

variable {k : Type} [CommRing k] {C : Scheme.{0}} {G : Over C} [GrpObj G] {x : Sp k ⟶ C} {B : Over (Sp k)} [GrpObj B]
  {ψ : B.left ⟶ G.left}

theorem tan_w (hp : IsGrpPullback B G x ψ) (v : epsR k ⟶ B) :
    (v.left ≫ ψ) ≫ G.hom = (specO k (DualNumber k)).hom ≫ x := by
  rw [Category.assoc, hp.1.w, ← Category.assoc]
  exact congrArg (· ≫ x) (Over.w v)

theorem tan_we (hp : IsGrpPullback B G x ψ) {v : epsR k ⟶ B} (hv : IsTangent v) :
    sec (epsZero k) ≫ v.left ≫ ψ = x ≫ unitSec G := by
  rw [← Category.assoc]
  exact (congrArg (· ≫ ψ) hv).trans (unitSec_comp hp)

theorem tv_omegaBase (hp : IsGrpPullback B G x ψ) {v : epsR k ⟶ B} (hv : IsTangent v)
    (t : Γ((Scheme.Modules.pullback x).obj (omega G), ⊤)) :
    tv ((omegaBase hp).app ⊤ t) v hv = ofFn k ((form (tan_w hp v) (tan_we hp hv)).app ⊤ t) :=
  congr(ofFn k (($(form_eq_fibre hp (epsZero_comp_of_isTangent hv) (tan_w hp v) (tan_we hp hv))).app ⊤ t)).symm

theorem tv_baseChange [QuasiSeparated G.hom] (hp : IsGrpPullback B G x ψ) {k' : Type} [CommRing k'] (σ : k →+* k')
    {x' : Sp k' ⟶ C} {B' : Over (Sp k')} [GrpObj B'] {ψ' : B'.left ⟶ G.left} (hp' : IsGrpPullback B' G x' ψ')
    (ex : spMap σ ≫ x = x') {v : epsR k ⟶ B} (hv : IsTangent v) {v' : epsR k' ⟶ B'} (hv' : IsTangent v')
    (ev : spMap (Formalism.L2.Pj.dualMap σ) ≫ v.left ≫ ψ = v'.left ≫ ψ') {U : C.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (s : Γ(omega G, U)) :
    tv ((omegaBase hp').app ⊤ (pullbackSections x' _ h' s)) v' hv' =
      σ (tv ((omegaBase hp).app ⊤ (pullbackSections x _ h s)) v hv) := by
  rw [tv_omegaBase, tv_omegaBase]
  refine (congrArg (ofFn k') (form_baseChange (sec_hom η[G]) σ (tan_w hp v) (tan_we hp hv) (tan_w hp' v')
    (tan_we hp' hv') ex ev h h' s)).trans (ofFn_appLE σ _ _)

theorem tv_sum {I : Type} [Fintype I] (c : I → k) (σ : I → Γ(omega B, ⊤)) {v : epsR k ⟶ B} (hv : IsTangent v) :
    tv (∑ i, cst k (c i) • σ i) v hv = ∑ i, c i * tv (σ i) v hv := by
  let L : omega B ⟶ structureModule (Sp k) := cotMap (T' := specO k (DualNumber k)) v (epsZero_comp_of_isTangent hv) ≫ (epsIso k).hom
  change ofFn k (L.app ⊤ _) = ∑ i, c i * ofFn k (L.app ⊤ _)
  rw [map_sum]
  refine (map_sum (ofFn k) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Scheme.Modules.Hom.app_smul]
  exact (map_mul (ofFn k) _ _).trans (by rw [ofFn_cst])

theorem exists_tangent [QuasiSeparated G.hom] (hp : IsGrpPullback B G x ψ) {n : ℕ} {U : C.Opens}
    {ε : Fin n → Γ(omega G, U)} (hε : IsFrame ε) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : Fin n → k) :
    ∃ (v : epsR k ⟶ B) (hv : IsTangent v),
      ∀ i, tv ((omegaBase hp).app ⊤ (pullbackSections x _ h (ε i))) v hv = c i := by
  obtain ⟨L, hL⟩ := exists_hom_of_isFrame (frame_pb x hε h) fun l => cst k (c l)
  obtain ⟨v₀, w, we, hv⟩ := exists_form_eq (sec_hom η[G]) L
  let v : epsR k ⟶ B := Over.homMk (hp.1.lift v₀ _ w) (hp.1.lift_snd _ _ _)
  have e : v.left ≫ ψ = v₀ := hp.1.lift_fst _ _ _
  have ht : IsTangent v := hp.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans (we.trans (unitSec_comp hp).symm)))
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans
      ((sec_hom (epsZero k)).trans (sec_hom η[B]).symm)))
  refine ⟨v, ht, fun i => ?_⟩
  have e₁ : form (tan_w hp v) (tan_we hp ht) = form w we := by congr 1
  rw [tv_omegaBase, ← ofFn_cst (c i), ← hL, ← hv, e₁]
  rfl

theorem good_pull (P : Published.AbelianDeRham) {T : Scheme.{0}} {A : Over T} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) {V : T.Opens} (hV : IsAffineOpen V) {K : Type} [CommRing K]
    [Algebra Γ(T, V) K] {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ (onAff A hV).left}
    (hφ : IsGrpPullback A' (onAff A hV) (spMap (algebraMap Γ(T, V) K)) φ) {ξ : Sp K ⟶ T} {φK : A'.left ⟶ A.left}
    (hK : IsGrpPullback A' A ξ φK) (e : spMap (algebraMap Γ(T, V) K) ≫ hV.fromSpec = ξ)
    (e' : φ ≫ pullback.fst A.hom hV.fromSpec = φK) (hξ : ⊤ ≤ ξ ⁻¹ᵁ V) {s : Γ(omega A, V)}
    {c : primDR (onAff A hV)} (hc : HodgeSub.Corr A hV s c) (h' : HdR A') :
    Good ((omegaBase hK).app ⊤ (pullbackSections ξ _ hξ s)) ((bcMor hφ).pull c) h' := by
  have hA₁ := DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
  have hg₁ := DeRhamSheaf.VB.smooth_onAff A hg hV
  have hA₂ := PolPull.isAbelianScheme_of_isGrpPullback hA hK
  have hg₂ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hK.1 hg
  have H := (P.2.1 _ _ g hA₁ hg₁).1
  have H' := (P.2.1 _ _ g hA₂ hg₂).1
  obtain ⟨hm, hF⟩ := P.2.2.1 _ _ g hA₁ hg₁ _ _ φ hφ
  obtain ⟨_, _, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim P.1 hA₁ hg₁
  have := hA.proper
  have := hA₂.proper
  have hp : IsGrpPullback (onAff A hV) A hV.fromSpec _ := isGrpPullback_pullback A hV.fromSpec
  refine mem_of_corr hφ hm (Good _ ((bcMor hφ).pull c)) (Good.zero H')
    (fun _ _ ↦ Good.add H') (fun r _ ↦ Good.smul H' r) ?_ h'
  intro l l' hl u' hu'
  obtain ⟨u, hu, -⟩ := H.1 l
  obtain ⟨u'', eu⟩ := ArcQ.NormalForm.exists_baseChange hφ u
  obtain rfl := (H'.1 _).unique hu' (hu.baseChange (hφ := hφ) hF H' hl eu)
  refine (hl c).trans (Eq.trans ?_ (tv_baseChange hp _ hK e hu.1 hu'.1
    (by rw [← e', ← Category.assoc, ← Category.assoc, eu]) hV.fromSpec_preimage_self.ge hξ s).symm)
  exact congrArg _ ((hc u l hu (tan_w hp u) (tan_we hp hu.1)).trans (tv_omegaBase hp hu.1 _).symm)

theorem forms_eq_span {R K : Type} [CommRing R] [Field K] [Algebra R K] [QuasiSeparated G.hom] [Smooth G.hom]
    {f : Sp R ⟶ C} {G' : Over (Sp R)} [GrpObj G'] {φ' : G'.left ⟶ G.left} (h' : IsGrpPullback G' G f φ')
    {A' : Over (Sp K)} [GrpObj A'] {χ : A'.left ⟶ G'.left} (hχ : IsGrpPullback A' G' (spMap (algebraMap R K)) χ)
    {ξ : Sp K ⟶ C} {ψ : A'.left ⟶ G.left} (hK : IsGrpPullback A' G ξ ψ) (e : spMap (algebraMap R K) ≫ f = ξ)
    (e' : χ ≫ φ' = ψ) (H : LieExact A') {n : ℕ} {U : C.Opens} {ε : Fin n → Γ(omega G, U)} (hε : IsFrame ε)
    (hU : ⊤ ≤ f ⁻¹ᵁ U) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U) {y : Fin n → primDR A'} (hy : ∀ i, y i ∈ PrimitiveSubmodule A')
    (hv : ∀ i h, Good ((omegaBase hK).app ⊤ (pullbackSections ξ _ hξ (ε i))) (y i) h)
    [Module R (primDR A')] [IsScalarTower R K (primDR A')] :
    PrimitiveSubmodule A' = Submodule.span K (Set.range y) ∧ intForms G' A' χ = Submodule.span R (Set.range y) := by
  have : QuasiSeparated A'.hom := MorphismProperty.of_isPullback hK.1 ‹_›
  have : Smooth A'.hom := MorphismProperty.of_isPullback hK.1 ‹_›
  have hF : PrimitiveSubmodule A' = Submodule.span K (Set.range y) := by
    refine le_antisymm (fun c hc => ?_) (Submodule.span_le.2 (Set.range_subset_iff.2 hy))
    obtain ⟨l, hl⟩ := HodgeSubSurj.exists_form hc
    obtain ⟨s, hs⟩ := HodgeSubSurj.exists_omega l
    obtain ⟨d, rfl⟩ := exists_coord ((frame_pb ξ hε hξ).map_iso (omegaBase hK)) s
    refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨d, sub_eq_zero.1
      ((Module.forall_dual_apply_eq_zero_iff K _).1 fun h => ?_)⟩
    obtain ⟨v, hhv, -⟩ := H.1 h
    have e₁ := (hl v h hhv).trans ((hs ⟨v, (HodgeSubSurj.isTangent_iff_ptMap v).1 hhv.1⟩).trans (tv_sum d _ hhv.1))
    rw [map_sub, e₁, map_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => (map_smul h _ _).trans (congrArg (d i * ·) (hv i h v hhv))
  have key (i : Fin n) (v : epsR R ⟶ G') (v' : epsR K ⟶ A') (h : HdR A') (t : IsTangent v)
      (ev : v'.left ≫ χ = spMap (Formalism.L2.Pj.dualMap (algebraMap R K)) ≫ v.left) (hh : IsLieImage h v') :
      h (y i) = algebraMap R K (tv ((omegaBase h').app ⊤ (pullbackSections f _ hU (ε i))) v t) := by
    rw [hv i h v' hh, tv_baseChange h' _ hK e t hh.1 (by rw [← e', ← Category.assoc, ← Category.assoc, ev]) hU hξ]
  refine ⟨hF, le_antisymm (fun c hc => ?_) (Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
    ⟨hy i, fun v v' h t ev hh => Submodule.mem_one.2 ⟨_, (key i v v' h t ev hh).symm⟩⟩))⟩
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hF ▸ hc.1)
  have (j : Fin n) : ∃ r, algebraMap R K r = d j := by
    obtain ⟨v, t, hvt⟩ := exists_tangent h' hε hU (Pi.single j 1)
    obtain ⟨v', ev⟩ := ArcQ.NormalForm.exists_baseChange hχ v
    obtain ⟨h, hh⟩ := H.2 v' (ArcQ.NormalForm.isTangent_baseChange hχ ev t)
    have := Submodule.mem_one.1 (hc.2 v v' h t ev hh)
    rw [map_sum] at this
    simp only [map_smul, key _ v v' h t ev hh, hvt] at this
    simpa [Pi.single_apply, apply_ite (algebraMap R K)] using this
  choose r hr using this
  exact (mem_span_iff (K := K) y _).2 ⟨r, by simp only [hr]⟩

end Tangent

section Pairing

open GlobalTheory.Published.AbelianDeRham (bcMor)

theorem exists_pairing {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {B : Over (Sp R)} [GrpObj B]
    {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ B.left} (hφ : IsGrpPullback A' B (spMap (algebraMap R K)) φ)
    [Module.Finite R (primDR B)] [Module.Projective R (primDR B)] (hm : (bcMor hφ).IsBC)
    {φ₀ : HdR B →ₗ[R] HdR B →ₗ[R] R} {ψ : HdR A' →ₗ[K] HdR A' →ₗ[K] K}
    (hψ : ∀ x x' y y', (bcMor hφ).Corr x x' → (bcMor hφ).Corr y y' → ψ x' y' = algebraMap R K (φ₀ x y))
    (β₀ : primDR B →ₗ[R] HdR B) (h : ∀ c y, φ₀ (β₀ c) y = y c) :
    ∃ β : primDR A' →ₗ[K] HdR A', (∀ s y, ψ (β s) y = y s) ∧
      ∀ c c', β ((bcMor hφ).pull c) ((bcMor hφ).pull c') = algebraMap R K (β₀ c c') := by
  let e := LinearEquiv.ofBijective _ hm
  let β : primDR A' →ₗ[K] HdR A' := liftSemi (hm.bcMap.comp β₀) ∘ₗ e.symm.toLinearMap
  have hβ (c) : (bcMor hφ).Corr (β₀ c) (β ((bcMor hφ).pull c)) := by
    have : (bcMor hφ).pull c = e (1 ⊗ₜ c) := (one_smul K ((bcMor hφ).pull c)).symm
    refine hm.corr_iff.2 ?_
    rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, liftSemi_tmul, one_smul]
    rfl
  refine ⟨β, fun s y => ?_, hβ⟩
  obtain ⟨z, rfl⟩ := hm.2 s
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul x c =>
    rw [liftSemi_tmul, map_smul, map_smul, map_smul, LinearMap.smul_apply]
    congr 1
    refine HodgeSub.Nat.mem_of_corr hφ hm (fun y => ψ (β ((bcMor hφ).pull c)) y = y ((bcMor hφ).pull c)) (by simp)
      (fun a b ha hb => by rw [map_add, ha, hb, LinearMap.add_apply])
      (fun r a ha => by rw [map_smul, ha, LinearMap.smul_apply]) (fun l l' hl => ?_) y
    rw [hψ _ _ _ _ (hβ c) hl, h, hl]

def secForm {T : Scheme.{0}} {D : T.Modules} (β₀ : D ⟶ dual D) {V : T.Opens} {M : Type*} [AddCommGroup M]
    [Module Γ(T, V) M] (e : Γ(D, V) ≃ₗ[Γ(T, V)] M) : M →ₗ[Γ(T, V)] Module.Dual Γ(T, V) M where
  toFun c := dualApp (β₀.app V (e.symm c)) le_rfl ∘ₗ e.symm.toLinearMap
  map_add' a b := by rw [map_add, map_add, dualApp_add, LinearMap.add_comp]
  map_smul' r a := by
    rw [map_smul, Scheme.Modules.Hom.app_smul, dualApp_smul, LB.resG_self, LinearMap.smul_comp, RingHom.id_apply]

theorem secForm_apply {T : Scheme.{0}} {D : T.Modules} (β₀ : D ⟶ dual D) {V : T.Opens} {M : Type*} [AddCommGroup M]
    [Module Γ(T, V) M] (e : Γ(D, V) ≃ₗ[Γ(T, V)] M) (s t : Γ(D, V)) :
    secForm β₀ e (e s) (e t) = dualApp (β₀.app V s) le_rfl t := by
  simp [secForm]

theorem frobDR_pull (q : ℕ) [Fact q.Prime] {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (hR : (q : R) = 0)
    (hK : (q : K) = 0) {B : Over (Sp R)} [GrpObj B] {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ B.left}
    (hφ : IsGrpPullback A' B (spMap (algebraMap R K)) φ) (c : primDR B) :
    frobDR q K hK A' ((bcMor hφ).pull c) = (bcMor hφ).pull (frobDR q R hR B c) := by
  have k := (frobMor q R hR B (cast_left q R hR B)).comp (bcMor hφ)
  exact (GrpMor.pull_pull _ _ k (fun r => by simp [frobR_apply]) (frob_naturality _ _ _ _) c).trans
    (GrpMor.pull_pull _ _ k (fun _ => rfl) rfl c).symm

theorem primPull_pull {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {B : Over (Sp R)} [GrpObj B]
    {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ B.left} (hφ : IsGrpPullback A' B (spMap (algebraMap R K)) φ)
    (a : B ⟶ B) (a' : A' ⟶ A') [IsMonHom a] [IsMonHom a'] (e : a'.left ≫ φ = φ ≫ a.left) (c : primDR B) :
    (bcMor hφ).pull (primPull (dp0 R) (𝟙 _) a c) = primPull (dp0 K) (𝟙 _) a' ((bcMor hφ).pull c) := by
  have k := (homMor (dp0 R) (𝟙 _) a).comp (bcMor hφ)
  exact (GrpMor.pull_pull _ _ k (fun _ => rfl) rfl c).trans
    (GrpMor.pull_pull _ (homMor (dp0 K) (𝟙 _) a') k (fun _ => rfl) e c).symm

end Pairing

open GlobalTheory.DeRhamSheaf (onAff)
open GlobalTheory.Published.AbelianDeRham (bcMor)
open GlobalTheory.DualPull (theta dualApp_theta)

set_option maxHeartbeats 2000000 in

theorem main : GlobalTheory.Published.AbelianDeRham → ∀ (O : Type) [CommRing O] (c : O →+* O) (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct O G) (T : Scheme.{0}) (f₀ : T ⟶ C) (A : Over T) [GrpObj A] (j : OAct O A) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G f₀ φ), IsAbelianScheme A → ∀ P : LB (A ⊗ A).left, P.IsLB → ∀ (g : ℕ) (hg : IsVB (omega G) g) (d₀ : DieuDatumOn q k c i g f₀), IsDRDatumOn q k c i j h P hg d₀ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hK : (q : K) = 0) (f : Sp R ⟶ C) (ξ : Sp K ⟶ T) (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) (G' : Over (Sp R)) [GrpObj G'] (φ' : G'.left ⟶ G.left), IsGrpPullback G' G f φ' → ∀ (A' : Over (Sp K)) [GrpObj A'] (j' : OAct O A') (φK : A'.left ⟶ A.left), IsActPull j' j ξ φK → ∀ χ : A'.left ⟶ G'.left, IsGrpPullback A' G' (spMap (algebraMap R K)) χ → χ ≫ φ' = φK ≫ φ → ∀ m : (A' ⊗ A').left ⟶ (A ⊗ A).left, m ≫ (fst A A).left = (fst A' A').left ≫ φK → m ≫ (snd A A).left = (snd A' A').left ≫ φK → ∀ [Module R (primDR A')] [IsScalarTower R K (primDR A')], ∃ (ψ : HdR A' →ₗ[K] HdR A' →ₗ[K] K) (β : primDR A' →ₗ[K] HdR A') (E : Γ((Scheme.Modules.pullback ξ).obj d₀.D, ⊤) ≃+ primDR A'), IsCorrForm (dp0 K) (𝟙 _) A' A' (P.pull m) ψ ∧ (∀ s y, ψ (β s) y = y s) ∧ (∀ (a : K) s, E (toFn a • s) = a • E s) ∧ (∀ x s, E ((act (pullAct d₀.ρ ξ) x).app ⊤ s) = (haveI := j'.hom x; primPull (dp0 K) (𝟙 _) (j'.act x)) (E s)) ∧ Reads w d₀.a d₀.b E β (PrimitiveSubmodule A') (intForms G' A' χ) ∧ Reads w d₀.u d₀.v E β (conjDR q K hK A') (Submodule.span R (frobDR q K hK A' '' (LinearMap.BilinForm.dualSubmodule β (intForms G' A' χ) : Set (primDR A')))) := by
  intro PR O _ c q _ k _ _ C _ G _ hG i T f₀ A _ j φ h hA P hP g hg d₀ hd R _ _ _ K _ _ _ hK f ξ w G' _ φ' h' A' _ j'
    φK hj χ hχ eχ m hm₁ hm₂ _ _
  obtain ⟨e, β₀, Ψ, -, hρ, ha, hβ, hΨ, eb, eu, ev⟩ := hd
  have hC := natCast_eq_zero C q k
  have hT := cast_eq_zero q k f₀
  have := hG.smooth
  have := hA.proper
  have := hg.isQuasicoherent
  have := hg.dual.isQuasicoherent
  have := (hg.frobPull q hC).isQuasicoherent
  have := (hg.dual.frobPull q hC).isQuasicoherent
  have := d₀.isVB.isQuasicoherent
  obtain ⟨U, ε, hxU, hε⟩ := hg (f (IsLocalRing.closedPoint R))
  have hU : ⊤ ≤ f ⁻¹ᵁ U := fun y _ => ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open U.2 hxU
  have hξU : ⊤ ≤ (ξ ≫ f₀) ⁻¹ᵁ U := w ▸ fun y _ => hU trivial
  obtain ⟨V, δ, hV, hxV, hVU, hδ⟩ := d₀.isVB.exists_affine (V := f₀ ⁻¹ᵁ U) (x := ξ (default : PrimeSpectrum K))
    (hξU trivial)
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ V := fun y _ => by
    obtain rfl : y = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hxV
  letI : Algebra Γ(T, V) K := ((ofFn K).comp (ξ.appLE V ⊤ hξ).hom).toAlgebra
  have eξ : spMap (algebraMap Γ(T, V) K) ≫ hV.fromSpec = ξ := spMap_fromSpec ξ hV hξ
  have hp : IsGrpPullback (onAff A hV) A hV.fromSpec _ := isGrpPullback_pullback A hV.fromSpec
  obtain ⟨φV, e₁, e₂⟩ : ∃ φV : A'.left ⟶ (onAff A hV).left, φV ≫ pullback.fst A.hom hV.fromSpec = φK ∧
      φV ≫ (onAff A hV).hom = A'.hom ≫ spMap (algebraMap Γ(T, V) K) :=
    ⟨pullback.lift φK (A'.hom ≫ spMap (algebraMap Γ(T, V) K)) (by rw [hj.1.1.w, Category.assoc, eξ]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hφ : IsGrpPullback A' (onAff A hV) (spMap (algebraMap Γ(T, V) K)) φV :=
    hp.cancel (hj.1.congr eξ.symm e₁.symm) e₂
  have hgA := relDim hA (isVB_omega_of_isGrpPullback h hg)
  have hA₁ := DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
  have hg₁ := DeRhamSheaf.VB.smooth_onAff A hgA hV
  have H' := (PR.2.1 _ _ g (PolPull.isAbelianScheme_of_isGrpPullback hA hj.1)
    ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hj.1.1 hgA)).1
  obtain ⟨hm, hF⟩ := PR.2.2.1 _ _ g hA₁ hg₁ _ _ φV hφ
  obtain ⟨_, _, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim PR.1 hA₁ hg₁
  obtain ⟨E, hE, hE'⟩ := exists_equiv hξ (fun _ => rfl) hδ (e V hV) (bcMor hφ).pull hm
  obtain ⟨m₀, φ₀, hm₀₁, hm₀₂, hc₀, -, hφ₀⟩ := hβ V hV
  obtain ⟨m', hm₁', hm₂'⟩ : ∃ m' : (A' ⊗ A').left ⟶ (onAff A hV ⊗ onAff A hV).left,
      m' ≫ (fst (onAff A hV) (onAff A hV)).left = (fst A' A').left ≫ φV ∧
      m' ≫ (snd (onAff A hV) (onAff A hV)).left = (snd A' A').left ≫ φV :=
    ⟨pullback.lift ((fst A' A').left ≫ φV) ((snd A' A').left ≫ φV)
      (by rw [Category.assoc, Category.assoc, e₂, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have em : m = m' ≫ m₀ := by
    refine pullback.hom_ext ?_ ?_
    · change m ≫ (fst A A).left = (m' ≫ m₀) ≫ (fst A A).left
      rw [hm₁, Category.assoc, hm₀₁, reassoc_of% hm₁', e₁]
    · change m ≫ (snd A A).left = (m' ≫ m₀) ≫ (snd A A).left
      rw [hm₂, Category.assoc, hm₀₂, reassoc_of% hm₂', e₁]
  obtain ⟨ψ, hψ, hψ'⟩ := hc₀.pull (pull_isLB hP _) (bcMor hφ) (bcMor hφ) hm₁' hm₂' (pull_isLB hP m)
    (LBIso.chartPull (chartPullPull _ m') (chartPullSame P _ _ _ m' fun _ => em)
      (Cris.ChernExists.lbIso_refl (pull_isLB hP m₀)))
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_pairing hφ hm hψ' (secForm β₀ (e V hV)) fun s y => by
    obtain ⟨s, rfl⟩ := (e V hV).surjective s
    exact hφ₀ s _ y (secForm_apply β₀ _ s)
  have hβ₃ (s t : Γ(d₀.D, V)) : β (E (pullbackSections ξ _ hξ s)) (E (pullbackSections ξ _ hξ t)) =
      ofFn K (ξ.appLE V ⊤ hξ (dualApp (β₀.app V s) le_rfl t)) := by
    rw [hE', hE', hβ₂, secForm_apply]
    rfl
  have δ₁ (i j : Fin g) : dualApp ((theta f₀ (omega G)).app V (pullbackSections f₀ _ hVU (hε.coord j))) le_rfl
      (pullbackSections f₀ _ hVU (ε i)) = if i = j then 1 else 0 := by
    have := hε.dualApp_coord_frame j i le_rfl
    rw [Twist.resM_self] at this
    rw [dualApp_theta f₀ _ le_rfl, this, apply_ite (f₀.appLE U V hVU), map_one, map_zero]
  have p₁ : d₀.b ≫ theta f₀ (omega G) = β₀ ≫ dualMap d₀.a := by
    have := congrArg (· ≫ dualMap (omegaBase h)) eb
    simpa only [lieRes, omegaRes, lieBase, asIso_hom, asIso_inv, Category.assoc, ← dualMap_comp, IsIso.hom_inv_id,
      IsIso.hom_inv_id_assoc, dualMap_id, Category.comp_id] using this
  obtain ⟨r₁, s, hs, hs₁, hs₂⟩ := reads_of_frames (R := R) w hU hVU hξ d₀.exact₁ hV hε hε.dual E hE β hβ₃ p₁ δ₁ _
    fun _ => rfl
  have ea (t) : d₀.a.app V t = ((omegaRes h).inv ≫ d₀.a).app V ((omegaRes h).hom.app V t) := by
    rw [QCoh.app_app, Iso.hom_inv_id_assoc]
  obtain ⟨F₁, N₁⟩ := forms_eq_span h' hχ (hj.1.comp h) w eχ H' hε hU hξU
    (y := fun i => E (pullbackSections ξ _ hξ (d₀.a.app V (pullbackSections f₀ _ hVU (ε i)))))
    (fun i => by
      rw [hE', hF, ea]
      exact Submodule.subset_span ⟨_, (ha V hV _).1, rfl⟩)
    fun i l => by
      rw [hE', ea, ← omegaBase_comp h hj.1 _ rfl rfl hVU hξ]
      exact good_pull PR hA hgA hV hφ hj.1 eξ e₁ hξ (ha V hV _).2 l
  let iL := frobLieRes h q hC hT hg
  let iω := frobOmegaRes h q hC hT
  have eL (l : Γ(Lie G, U)) : iL.hom.app V (pullbackSections f₀ _ hVU (pullbackSections (frob C q hC) _ (le_refl U) l)) =
      pullbackSections (frob T q hT) _ (le_refl V) ((lieBase h).app V (pullbackSections f₀ _ hVU l)) :=
    (congrArg (((frobPull q hT).map (lieBase h)).app V) (Vert.DivPull.pullbackSquare_app
      (frob_naturality q hC f₀ hT).symm _ (le_refl U) hVU hVU (le_refl V) l)).trans
      (QCoh.pullback_map_app_pullbackSections _ _ _ _)
  have eω (l : Γ(omega G, U)) : iω.hom.app V (pullbackSections f₀ _ hVU (pullbackSections (frob C q hC) _ (le_refl U) l)) =
      pullbackSections (frob T q hT) _ (le_refl V) ((omegaBase h).app V (pullbackSections f₀ _ hVU l)) :=
    (congrArg (((frobPull q hT).map (omegaBase h)).app V) (Vert.DivPull.pullbackSquare_app
      (frob_naturality q hC f₀ hT).symm _ (le_refl U) hVU hVU (le_refl V) l)).trans
      (QCoh.pullback_map_app_pullbackSections _ _ _ _)
  have eF (t : Γ(d₀.D, V)) : frobDR q K hK A' (E (pullbackSections ξ _ hξ t)) = E (pullbackSections ξ _ hξ
      ((iL.inv ≫ d₀.u).app V (pullbackSections (frob T q hT) _ (le_refl V) ((lieBase h).app V (d₀.b.app V t))))) := by
    rw [hE', hE', frobDR_pull q (SS.FrobField.cast_zero hT V) hK hφ, ← hΨ V hV t, ← eu, ← QCoh.app_app,
      QCoh.pullback_map_app_pullbackSections]
    rfl
  have p₂ : d₀.v ≫ iω.hom ≫ (frobPull q hT).map (cartierDualToBidual (omega A)) ≫ theta (frob T q hT) (Lie A) ≫ dualMap iL.hom =
      β₀ ≫ dualMap d₀.u := by
    have := congrArg (· ≫ dualMap iL.hom) ev
    simpa only [iL, Category.assoc, ← dualMap_comp, Iso.hom_inv_id_assoc] using this
  have δ₂ (i j : Fin g) : dualApp ((iω.hom ≫ (frobPull q hT).map (cartierDualToBidual (omega A)) ≫ theta (frob T q hT) (Lie A) ≫
      dualMap iL.hom).app V (pullbackSections f₀ _ hVU (pullbackSections (frob C q hC) _ (le_refl U) (ε j)))) le_rfl
      (pullbackSections f₀ _ hVU (pullbackSections (frob C q hC) _ (le_refl U) (hε.coord i))) =
      if i = j then 1 else 0 := by
    rw [← QCoh.app_app, ← QCoh.app_app, ← QCoh.app_app, dualApp_dualMap, eL, eω,
      QCoh.pullback_map_app_pullbackSections, dualApp_theta _ _ le_rfl, dualSheafSectionApply_toBidual, Twist.resM_self, lieBase,
      ← QCoh.app_app, dualApp_dualMap, QCoh.app_app, IsIso.hom_inv_id, Scheme.Modules.Hom.id_app,
      AddCommGrpCat.id_apply, δ₁, apply_ite ((frob T q hT).appLE V V _), map_one, map_zero]
    exact if_congr eq_comm rfl rfl
  obtain ⟨r₂, -⟩ := reads_of_frames (R := R) w hU hVU hξ d₀.exact₂ hV (frame_pb (frob C q hC) hε.dual (le_refl U))
    (frame_pb (frob C q hC) hε (le_refl U)) E hE β hβ₃ p₂ δ₂ _ fun _ => rfl
  obtain ⟨F₂, N₂⟩ := frob_span (R := R) (frobR_apply q K hK) (frobDR q K hK A') β
    (z := fun i => E (pullbackSections ξ _ hξ (d₀.u.app V (pullbackSections f₀ _ hVU
      (pullbackSections (frob C q hC) _ (le_refl U) (hε.coord i))))))
    (fun i => by rw [eF, QCoh.app_app d₀.a, d₀.w₁]; simp)
    (fun i => by rw [eF, hs, ← eL, QCoh.app_app, Iso.hom_inv_id_assoc]) hs₁ hs₂
  refine ⟨ψ, β, E, hψ, hβ₁, hE, fun x t => ?_, by rw [F₁, N₁]; exact r₁, by rw [conjDR, N₁, F₂, N₂]; exact r₂⟩
  have := j.hom x
  have := j'.hom x
  refine pb_induction ξ d₀.D hV hξ (fun t => E ((act (pullAct d₀.ρ ξ) x).app ⊤ t) =
    primPull (dp0 K) (𝟙 _) (j'.act x) (E t)) (fun t => ?_) (fun a t ht => ?_) (fun a b ha hb => ?_) t
  · rw [act_pullAct, QCoh.pullback_map_app_pullbackSections, hE', hE', hρ]
    refine primPull_pull hφ _ _ (hp.1.hom_ext ?_ ?_) _
    · rw [Category.assoc, e₁, hj.2, Category.assoc, ← e₁, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  · rw [Scheme.Modules.Hom.app_smul]
    exact (hE _ _).trans ((congrArg _ ht).trans ((map_smul _ _ _).symm.trans (congrArg _ (hE _ _).symm)))
  · rw [map_add, map_add, ha, hb, map_add, map_add]

end GlobalTheory.BadPt.Fibre
