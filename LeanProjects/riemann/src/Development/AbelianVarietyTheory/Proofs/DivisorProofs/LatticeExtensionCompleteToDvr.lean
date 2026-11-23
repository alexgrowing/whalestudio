import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullback_map_app_pullbackSections pullbackSections_smul)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt.Descent

section Algebra

variable {R S K L : Type} [CommRing R] [CommRing S] [CommRing K] [CommRing L]
  {H H' : Type} [AddCommGroup H] [Module K H] [AddCommGroup H'] [Module L H']

def Lat (φ : R →+* K) {n : ℕ} (e : Fin n → H) (s : H) : Prop := ∃ r : Fin n → R, s = ∑ i, φ (r i) • e i

theorem Lat.add {φ : R →+* K} {n : ℕ} {e : Fin n → H} {s t : H} (hs : Lat φ e s) (ht : Lat φ e t) :
    Lat φ e (s + t) := by
  obtain ⟨r, rfl⟩ := hs
  obtain ⟨r', rfl⟩ := ht
  exact ⟨r + r', by simp [add_smul, Finset.sum_add_distrib]⟩

theorem Lat.smul {φ : R →+* K} {n : ℕ} {e : Fin n → H} {s : H} (c : R) (hs : Lat φ e s) :
    Lat φ e (φ c • s) := by
  obtain ⟨r, rfl⟩ := hs
  exact ⟨c • r, by simp [Finset.smul_sum, mul_smul]⟩

theorem Lat.sub {φ : R →+* K} {n : ℕ} {e : Fin n → H} {s t : H} (hs : Lat φ e s) (ht : Lat φ e t) :
    Lat φ e (s - t) := by
  simpa [sub_eq_add_neg] using hs.add (ht.smul (-1))

theorem lat_iff_repr {φ : R →+* K} {n : ℕ} (e : Module.Basis (Fin n) K H) (s : H) :
    Lat φ e s ↔ ∀ i, e.repr s i ∈ φ.range := by
  constructor
  · rintro ⟨r, rfl⟩ i
    rw [e.repr_sum_self]
    exact ⟨r i, rfl⟩
  · intro h
    choose r hr using h
    exact ⟨r, by simp only [hr, e.sum_repr]⟩

variable {φ : R →+* K} {ψ : S →+* L} {θ : K →+* L} {n : ℕ} {e : Module.Basis (Fin n) K H}
  {e' : Module.Basis (Fin n) L H'} {j : H →+ H'}

theorem repr_map (hj : ∀ (c : K) x, j (c • x) = θ c • j x) (he : ∀ i, j (e i) = e' i) (x : H) (i : Fin n) :
    e'.repr (j x) i = θ (e.repr x i) := by
  conv_lhs => rw [← e.sum_repr x]
  simp only [map_sum j, hj, he]
  rw [e'.repr_sum_self]

theorem lat_map_iff (hint : ∀ x, θ x ∈ ψ.range ↔ x ∈ φ.range) (hj : ∀ (c : K) x, j (c • x) = θ c • j x)
    (he : ∀ i, j (e i) = e' i) (x : H) : Lat ψ e' (j x) ↔ Lat φ e x := by
  simp only [lat_iff_repr, repr_map hj he, hint]

theorem exists_eq_map_add (hden : ∀ y, ∃ x, y - θ x ∈ ψ.range) (hj : ∀ (c : K) x, j (c • x) = θ c • j x)
    (he : ∀ i, j (e i) = e' i) (y : H') : ∃ x, Lat ψ e' (y - j x) := by
  choose c hc using fun i => hden (e'.repr y i)
  refine ⟨∑ i, c i • e i, (lat_iff_repr _ _).2 fun i => ?_⟩
  rw [map_sub, Finsupp.sub_apply, repr_map hj he, e.repr_sum_self]
  exact hc i

theorem exists_lat_iff [IsNoetherianRing R] (hint : ∀ x, θ x ∈ ψ.range ↔ x ∈ φ.range)
    (hb : ∀ y, ∃ r, IsUnit (φ r) ∧ θ (φ r) * y ∈ ψ.range) (hj : ∀ (c : K) x, j (c • x) = θ c • j x)
    (he : ∀ i, j (e i) = e' i) {m : ℕ} (g : Fin m → H') :
    ∃ (k : ℕ) (v : Fin k → H), ∀ s, Lat φ v s ↔ Lat ψ g (j s) := by
  classical
  letI : Module R H := Module.compHom H φ
  have hs (r : R) (x : H) : r • x = φ r • x := rfl
  have hc (r : R) : θ (φ r) ∈ ψ.range := (hint _).2 ⟨r, rfl⟩
  let Λ : Submodule R H :=
    { carrier := {s | Lat ψ g (j s)}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := fun hx hy => by
        rw [Set.mem_setOf_eq, map_add]; exact Lat.add hx hy
      smul_mem' := fun r x hx => by
        obtain ⟨c, hc⟩ := hc r
        rw [Set.mem_setOf_eq, hs, hj, ← hc]; exact Lat.smul c hx }
  choose q hq hq' using fun p : Fin m × Fin n => hb (e'.repr (g p.1) p.2)
  obtain ⟨u, hu⟩ : IsUnit (φ (∏ p, q p)) := by
    rw [map_prod]; exact IsUnit.prod_univ_iff.2 hq
  have hg (k : Fin m) (i : Fin n) : θ u * e'.repr (g k) i ∈ ψ.range := by
    rw [hu, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (k, i)), map_mul, map_mul, _root_.mul_assoc]
    exact mul_mem (hc _) (hq' (k, i))
  have hle : Λ ≤ Submodule.span R (Set.range fun i => (u⁻¹ : Kˣ).val • e i) := by
    rintro s ⟨c, hc⟩
    have : Lat φ e (u.val • s) := by
      rw [← lat_map_iff hint hj he, lat_iff_repr, hj, hc]
      intro i
      simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.finset_sum_apply, smul_eq_mul, Finset.mul_sum]
      exact sum_mem fun k _ => by
        rw [mul_left_comm]; exact mul_mem ⟨_, rfl⟩ (hg k i)
    obtain ⟨r, hr⟩ := this
    refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨r, ?_⟩
    have : s = (u⁻¹ : Kˣ).val • u.val • s := by rw [smul_smul, Units.inv_mul, one_smul]
    rw [this, hr, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hs, smul_comm]
  have hfg : Λ.FG := (Submodule.fg_span (Set.finite_range _)).of_le hle
  obtain ⟨k, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  refine ⟨k, v, fun s => ?_⟩
  change _ ↔ s ∈ Λ
  rw [← hv, Submodule.mem_span_range_iff_exists_fun]
  exact exists_congr fun r => eq_comm

end Algebra

section Completion

open IsLocalRing

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev Cpl : Type := AdicCompletion (maximalIdeal R) R

def toCpl : K →+* FractionRing (Cpl R) :=
  IsFractionRing.lift (A := R) (g := (algebraMap (Cpl R) (FractionRing (Cpl R))).comp (algebraMap R (Cpl R)))
    ((IsFractionRing.injective (Cpl R) (FractionRing (Cpl R))).comp (algebraMap_adicCompletion_injective_of_dvr R))

theorem toCpl_algebraMap (r : R) :
    toCpl R K (algebraMap R K r) = algebraMap (Cpl R) (FractionRing (Cpl R)) (algebraMap R (Cpl R) r) :=
  IsFractionRing.lift_algebraMap _ _

theorem toCpl_mem_iff (x : K) :
    toCpl R K x ∈ (algebraMap (Cpl R) (FractionRing (Cpl R))).range ↔ x ∈ (algebraMap R K).range := by
  refine ⟨fun ⟨s, hs⟩ => ?_, fun ⟨r, hr⟩ => ⟨_, by rw [← hr, toCpl_algebraMap]⟩⟩
  rcases ValuationRing.isInteger_or_isInteger R x with h | ⟨r, hr⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  have h1 : algebraMap R (Cpl R) r * s = 1 := by
    apply IsFractionRing.injective (Cpl R) (FractionRing (Cpl R))
    rw [map_mul, hs, ← toCpl_algebraMap R K, hr, ← map_mul, inv_mul_cancel₀ hx, map_one, map_one]
  obtain ⟨u, rfl⟩ := (isUnit_map_iff (algebraMap R (Cpl R)) r).1 (IsUnit.of_mul_eq_one _ h1)
  refine ⟨(u⁻¹ : Rˣ), ?_⟩
  rw [← inv_inv x, ← hr]
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem exists_mul_mem (y : FractionRing (Cpl R)) : ∃ r : R, r ≠ 0 ∧
    toCpl R K (algebraMap R K r) * y ∈ (algebraMap (Cpl R) (FractionRing (Cpl R))).range := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Cpl R) y
  have hb' := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb'
    (irreducible_algebraMap_adicCompletion_of_dvr hπ)
  refine ⟨π ^ n, pow_ne_zero _ hπ.ne_zero, u * a, ?_⟩
  have : algebraMap (Cpl R) (FractionRing (Cpl R)) b ≠ 0 := by simpa using hb'
  rw [toCpl_algebraMap, map_pow (algebraMap R _), ← hu, map_mul, map_mul]
  field_simp

theorem exists_sub_mem (y : FractionRing (Cpl R)) : ∃ x : K,
    y - toCpl R K x ∈ (algebraMap (Cpl R) (FractionRing (Cpl R))).range := by
  obtain ⟨r, hr, s, hs⟩ := exists_mul_mem R K y
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hπ
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (s.1 n)
  have h1 : s - algebraMap R (Cpl R) z ∈ (maximalIdeal R) ^ n • (⊤ : Submodule R (Cpl R)) := by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
    simpa [AdicCompletion.eval, sub_eq_zero] using hz.symm
  have h2 : (maximalIdeal R) ^ n = Ideal.span {r} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hu, Ideal.span_singleton_mul_right_unit u.isUnit]
  rw [h2, Submodule.ideal_span_singleton_smul] at h1
  obtain ⟨t, -, ht⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  have hr' : algebraMap R K r ≠ 0 := by simpa using hr
  refine ⟨algebraMap R K z / algebraMap R K r, t, ?_⟩
  apply mul_left_cancel₀ ((map_ne_zero (toCpl R K)).2 hr')
  rw [mul_sub, ← hs, ← map_mul (toCpl R K), mul_div_cancel₀ _ hr', toCpl_algebraMap, toCpl_algebraMap, ← map_mul,
    ← map_sub, ← ht, Algebra.smul_def]

end Completion

section Sheaf

variable {X T Y Y' : Scheme.{0}}

def fnHom (K : Type) [CommRing K] : K →+* Γ(Sp K, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem fnHom_bijective (K : Type) [CommRing K] : Function.Bijective (fnHom K) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv

theorem appLE_fnHom {K L : Type} [CommRing K] [CommRing L] (θ : K →+* L) (x : K) :
    (spMap θ).appLE ⊤ ⊤ le_top (fnHom K x) = fnHom L (θ x) := by
  have h : (spMap θ).appLE ⊤ ⊤ le_top = (spMap θ).appTop := Scheme.Hom.appLE_eq_app _
  rw [h]
  exact congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom θ)) x).symm

def pullTop (c : Y' ⟶ Y) (ξ : Y ⟶ T) (M : T.Modules) :
    Γ((Scheme.Modules.pullback ξ).obj M, ⊤) →+ Γ((Scheme.Modules.pullback (c ≫ ξ)).obj M, ⊤) where
  toFun s := ((Scheme.Modules.pullbackComp c ξ).hom.app M).app ⊤ (pullbackSections c _ (V := ⊤) le_top s)
  map_zero' := by rw [map_zero, map_zero]
  map_add' s t := by rw [map_add, map_add]

variable (c : Y' ⟶ Y) (ξ : Y ⟶ T) {M N : T.Modules}

theorem pullTop_smul (r : Γ(Y, ⊤)) (s : Γ((Scheme.Modules.pullback ξ).obj M, ⊤)) :
    pullTop c ξ M (r • s) = (c.appLE ⊤ ⊤ le_top).hom r • pullTop c ξ M s :=
  (congrArg (((Scheme.Modules.pullbackComp c ξ).hom.app M).app ⊤) (pullbackSections_smul c _ le_top r s)).trans
    (Scheme.Modules.Hom.app_smul _ _ _)

theorem pullTop_map (a : M ⟶ N) (s : Γ((Scheme.Modules.pullback ξ).obj M, ⊤)) :
    pullTop c ξ N (((Scheme.Modules.pullback ξ).map a).app ⊤ s) =
      ((Scheme.Modules.pullback (c ≫ ξ)).map a).app ⊤ (pullTop c ξ M s) :=
  (congrArg (((Scheme.Modules.pullbackComp c ξ).hom.app N).app ⊤)
    (pullback_map_app_pullbackSections c ((Scheme.Modules.pullback ξ).map a) le_top s).symm).trans
    (Vert.DivPull.app_app_eq ((Scheme.Modules.pullbackComp c ξ).hom.naturality a) ⊤ _)

theorem pullTop_pull {V : T.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ V) (h' : ⊤ ≤ (c ≫ ξ) ⁻¹ᵁ V) (m : Γ(M, V)) :
    pullTop c ξ M (pullbackSections ξ M h m) = pullbackSections (c ≫ ξ) M h' m :=
  (congrArg (((Scheme.Modules.pullbackComp c ξ).hom.app M).app ⊤)
    (Vert.DivPull.pullbackComp_inv_app c ξ M h le_top h' m).symm).trans
    congr(($((Scheme.Modules.pullbackComp c ξ).inv_hom_id_app M)).app ⊤ (pullbackSections (c ≫ ξ) M h' m))

theorem isFrame_pull {r : ℕ} (hM : IsVB M r) {V : T.Opens} {W : Y.Opens} {e : Fin r → Γ(M, V)} (he : IsFrame e)
    (h : W ≤ ξ ⁻¹ᵁ V) : IsFrame fun i => pullbackSections ξ M h (e i) := by
  haveI := hM.isQuasicoherent
  have := (he.pullback ξ).res h
  exact (funext fun i => res_pullbackSections ξ M le_rfl h (e i) :) ▸ this

theorem exists_basis {F : Y.Modules} {r : ℕ} {e : Fin r → Γ(F, ⊤)} (he : IsFrame e) :
    ∃ b : Module.Basis (Fin r) Γ(Y, ⊤) Γ(F, ⊤), ⇑b = e :=
  ⟨he.basis le_rfl, funext fun i => (he.basis_apply _ i).trans (Twist.resM_self _ _)⟩

theorem exists_frame {R : Type} [CommRing R] [IsLocalRing R] (f : Sp R ⟶ T) {r : ℕ} (hM : IsVB M r) :
    ∃ (V : T.Opens) (e : Fin r → Γ(M, V)), ⊤ ≤ f ⁻¹ᵁ V ∧ IsFrame e := by
  obtain ⟨V, e, hx, he⟩ := hM (f (IsLocalRing.closedPoint R))
  exact ⟨V, e, ((IsLocalRing.closedPoint_mem_iff _).1 hx).ge, he⟩

theorem exact_top [IsAffine Y] {P : T.Modules} {a : M ⟶ N} {b : N ⟶ P} {w : a ≫ b = 0}
    (hS : (ShortComplex.mk a b w).ShortExact) {r s t : ℕ} (h₁ : IsVB M r) (h₂ : IsVB N s) (h₃ : IsVB P t) :
    Function.Injective (((Scheme.Modules.pullback ξ).map a).app ⊤) ∧
      Function.Exact (((Scheme.Modules.pullback ξ).map a).app ⊤) (((Scheme.Modules.pullback ξ).map b).app ⊤) ∧
      Function.Surjective (((Scheme.Modules.pullback ξ).map b).app ⊤) := by
  haveI := h₁.isQuasicoherent
  haveI := h₂.isQuasicoherent
  haveI := h₃.isQuasicoherent
  haveI := hS.epi_g
  haveI : Mono ((Scheme.Modules.pullback ξ).map a) := FlagPull.mono_pullback_map_f ξ _ hS h₃
  haveI : Epi ((Scheme.Modules.pullback ξ).map b) := (QCoh.exact_map_pullback ξ hS.exact).2
  haveI : Mono ((ShortComplex.mk a b w).map (Scheme.Modules.pullback ξ)).f := ‹_›
  exact ⟨QCoh.app_injective_of_mono _ _, QCoh.exact_app_of_exact_of_mono (QCoh.exact_map_pullback ξ hS.exact).1 ⊤,
    QCoh.app_surjective_of_epi_of_isAffineOpen _ (isAffineOpen_top Y)⟩

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T}

theorem resSec_iff (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {A : X.Modules} {r : ℕ} (hA : IsVB A r) {U : X.Opens}
    {e : Fin r → Γ(A, U)} (he : IsFrame e) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ ξ ⁻¹ᵁ (f₀ ⁻¹ᵁ U))
    (s : Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤)) :
    (∃ t, s = resSec w A t) ↔ Lat ((fnHom K).comp (algebraMap R K))
      (fun i => pullbackSections ξ _ h' (pullbackSections f₀ A le_rfl (e i))) s := by
  have key (c : Fin r → R) : resSec w A (∑ i, fnHom R (c i) • pullbackSections f A h (e i)) =
      ∑ i, (fnHom K).comp (algebraMap R K) (c i) • pullbackSections ξ _ h' (pullbackSections f₀ A le_rfl (e i)) := by
    rw [resSec, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pullbackSections_smul, Scheme.Modules.Hom.app_smul, appLE_fnHom]
    exact congrArg _ (Vert.DivPull.pullbackSquare_app w A h le_top le_rfl h' (e i))
  obtain ⟨b, hb⟩ := exists_basis (isFrame_pull f hA he h)
  constructor
  · rintro ⟨t, rfl⟩
    choose c hc using fun i => (fnHom_bijective R).2 (b.repr t i)
    refine ⟨c, Eq.trans (congrArg _ ?_) (key c)⟩
    conv_lhs => rw [← b.sum_repr t, hb]
    simp only [hc]
  · rintro ⟨c, rfl⟩
    exact ⟨_, (key c).symm⟩

end Sheaf

section Descend

variable {X T : Scheme.{0}} {R K S L : Type} [CommRing R] [Field K] [Algebra R K] [CommRing S] [Field L] [Algebra S L]
  {θ : K →+* L} {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T} {g : Sp S ⟶ Sp R}

theorem fn_mem_range_iff (x : K) : fnHom K x ∈ ((fnHom K).comp (algebraMap R K)).range ↔ x ∈ (algebraMap R K).range :=
  exists_congr fun _ => (fnHom_bijective K).1.eq_iff

theorem fn_int (hint : ∀ x, θ x ∈ (algebraMap S L).range ↔ x ∈ (algebraMap R K).range) (x : Γ(Sp K, ⊤)) :
    ((spMap θ).appLE ⊤ ⊤ le_top).hom x ∈ ((fnHom L).comp (algebraMap S L)).range ↔
      x ∈ ((fnHom K).comp (algebraMap R K)).range := by
  obtain ⟨x, rfl⟩ := (fnHom_bijective K).2 x
  rw [appLE_fnHom, fn_mem_range_iff, fn_mem_range_iff, hint]

theorem fn_den (hden : ∀ y, ∃ x, y - θ x ∈ (algebraMap S L).range) (y : Γ(Sp L, ⊤)) :
    ∃ x, y - ((spMap θ).appLE ⊤ ⊤ le_top).hom x ∈ ((fnHom L).comp (algebraMap S L)).range := by
  obtain ⟨y, rfl⟩ := (fnHom_bijective L).2 y
  obtain ⟨x, hx⟩ := hden y
  exact ⟨fnHom K x, by rwa [appLE_fnHom, ← map_sub, fn_mem_range_iff]⟩

theorem fn_bound (hb : ∀ y, ∃ r : R, IsUnit (algebraMap R K r) ∧ θ (algebraMap R K r) * y ∈ (algebraMap S L).range)
    (y : Γ(Sp L, ⊤)) : ∃ r : R, IsUnit ((fnHom K).comp (algebraMap R K) r) ∧
      ((spMap θ).appLE ⊤ ⊤ le_top).hom ((fnHom K).comp (algebraMap R K) r) * y ∈
        ((fnHom L).comp (algebraMap S L)).range := by
  obtain ⟨y, rfl⟩ := (fnHom_bijective L).2 y
  obtain ⟨r, hr, hx⟩ := hb y
  exact ⟨r, hr.map (fnHom K), by rwa [RingHom.comp_apply, appLE_fnHom, ← map_mul, fn_mem_range_iff]⟩

variable [IsLocalRing R] (hint : ∀ x, θ x ∈ (algebraMap S L).range ↔ x ∈ (algebraMap R K).range)
  (hden : ∀ y, ∃ x, y - θ x ∈ (algebraMap S L).range) (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀)
  (w' : spMap (algebraMap S L) ≫ g ≫ f = (spMap θ ≫ ξ) ≫ f₀)

include hint hden in

theorem resSec_descend {A : X.Modules} {r : ℕ} (hA : IsVB A r) :
    (∀ x, (∃ t, pullTop (spMap θ) ξ _ x = resSec w' A t) ↔ ∃ t, x = resSec w A t) ∧
      ∀ y, ∃ x t, y - pullTop (spMap θ) ξ _ x = resSec w' A t := by
  obtain ⟨U, e, h, he⟩ := exists_frame f hA
  have h₁ : ⊤ ≤ (g ≫ f) ⁻¹ᵁ U := le_top.trans (g.preimage_mono h)
  have h₂ : ⊤ ≤ ξ ⁻¹ᵁ (f₀ ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← w]
    exact le_top.trans ((spMap (algebraMap R K)).preimage_mono h)
  have h₃ : ⊤ ≤ (spMap θ ≫ ξ) ⁻¹ᵁ (f₀ ⁻¹ᵁ U) := le_top.trans ((spMap θ).preimage_mono h₂)
  have he₀ := isFrame_pull f₀ hA he le_rfl
  obtain ⟨b, hb⟩ := exists_basis (isFrame_pull ξ (hA.pullback f₀) he₀ h₂)
  obtain ⟨b', hb'⟩ := exists_basis (isFrame_pull (spMap θ ≫ ξ) (hA.pullback f₀) he₀ h₃)
  have hbb (i : Fin r) : pullTop (spMap θ) ξ _ (b i) = b' i := by
    rw [hb, hb']; exact pullTop_pull _ _ _ _ _
  refine ⟨fun x => ?_, fun y => ?_⟩
  · rw [resSec_iff w hA he h h₂, resSec_iff w' hA he h₁ h₃, ← hb, ← hb']
    exact lat_map_iff (fn_int hint) (pullTop_smul _ _) hbb x
  · obtain ⟨x, hx⟩ := exists_eq_map_add (fn_den hden) (pullTop_smul _ _) hbb y
    exact ⟨x, (resSec_iff w' hA he h₁ h₃ _).2 (hb' ▸ hx)⟩

include hint hden in

theorem latSeq_descend {A B : X.Modules} {D : T.Modules} {a : (Scheme.Modules.pullback f₀).obj A ⟶ D}
    {b : D ⟶ (Scheme.Modules.pullback f₀).obj B} {z : a ≫ b = 0} (hS : (ShortComplex.mk a b z).ShortExact) {r s t : ℕ}
    (hA : IsVB A r) (hD : IsVB D s) (hB : IsVB B t) {Λ : Γ((Scheme.Modules.pullback (spMap θ ≫ ξ)).obj D, ⊤) → Prop}
    (hΛ : ∀ x y, Λ x → Λ y → Λ (x - y)) (h : LatSeq w' a b Λ) :
    LatSeq w a b fun x => Λ (pullTop (spMap θ) ξ D x) := by
  obtain ⟨-, hex, hsurj⟩ := exact_top ξ hS (hA.pullback f₀) hD (hB.pullback f₀)
  obtain ⟨hinj', hex', -⟩ := exact_top (spMap θ ≫ ξ) hS (hA.pullback f₀) hD (hB.pullback f₀)
  obtain ⟨hA₁, hA₂⟩ := resSec_descend hint hden w w' hA
  obtain ⟨hB₁, -⟩ := resSec_descend hint hden w w' hB
  refine ⟨fun x => ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩, fun y => ⟨?_, fun hy => ?_⟩⟩
  · obtain ⟨u, rfl⟩ := (hex x).1 h₂
    obtain ⟨v, hv⟩ := (h.1 _).1 ⟨h₁, by rw [← pullTop_map, h₂, map_zero]⟩
    rw [pullTop_map] at hv
    obtain ⟨v', rfl⟩ := (hA₁ u).1 ⟨v, hinj' hv⟩
    exact ⟨v', rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨v', hv⟩ := (hA₁ _).2 ⟨v, rfl⟩
    exact ⟨((h.1 _).2 ⟨v', by rw [pullTop_map, hv]⟩).1, hex.apply_apply_eq_zero _⟩
  · rintro ⟨x, hx, rfl⟩
    exact (hB₁ _).1 ((h.2 _).1 ⟨_, hx, (pullTop_map _ _ _ _).symm⟩)
  · obtain ⟨x', hx', e'⟩ := (h.2 _).2 ((hB₁ y).2 hy)
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨u', hu'⟩ := (hex' (x' - pullTop (spMap θ) ξ D x)).1 (by rw [map_sub, e', pullTop_map, sub_self])
    obtain ⟨u, v, hv⟩ := hA₂ u'
    refine ⟨x + ((Scheme.Modules.pullback ξ).map a).app ⊤ u, ?_, by rw [map_add, hex.apply_apply_eq_zero, add_zero]⟩
    have := hΛ _ _ hx' ((h.1 _).2 ⟨v, rfl⟩).1
    rw [← hv, map_sub, hu', ← pullTop_map] at this
    convert this using 1
    rw [map_add]
    abel

end Descend

theorem hasLatticesDvr_of_complete : ∀ (X T : Scheme.{0}) (f₀ : T ⟶ X) (O : Type) [CommRing O] (A B A' B' : X.Modules) (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r a b a' b' : ℕ), IsVB A a → IsVB B b → IsVB A' a' → IsVB B' b' → ∀ d₀ : DatumOn α β α' β' r f₀, HasLatticesComplete d₀ → HasLatticesDvr d₀ := by
  intro X T f₀ O _ A B A' B' α β α' β' r a b a' b' hA hB hA' hB' d H R _ _ _ _ K _ _ _ f ξ w
  haveI : IsAlgClosed (IsLocalRing.ResidueField (Cpl R)) :=
    IsAlgClosed.of_ringEquiv _ _ (RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R))
  have w' : spMap (algebraMap (Cpl R) (FractionRing (Cpl R))) ≫ spMap (algebraMap R (Cpl R)) ≫ f =
      (spMap (toCpl R K) ≫ ξ) ≫ f₀ := by
    rw [Category.assoc, ← w, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun x => (toCpl_algebraMap R K x).symm
  obtain ⟨n, e, h₁, h₂, h₃⟩ := H (Cpl R) (FractionRing (Cpl R)) _ _ w'
  obtain ⟨V, m, hV, hm⟩ := exists_frame ξ d.isVB
  have hV' : ⊤ ≤ (spMap (toCpl R K) ≫ ξ) ⁻¹ᵁ V := le_top.trans ((spMap (toCpl R K)).preimage_mono hV)
  obtain ⟨c, hc⟩ := exists_basis (isFrame_pull ξ d.isVB hm hV)
  obtain ⟨c', hc'⟩ := exists_basis (isFrame_pull (spMap (toCpl R K) ≫ ξ) d.isVB hm hV')
  have hcc (i : Fin r) : pullTop (spMap (toCpl R K)) ξ _ (c i) = c' i := by
    rw [hc, hc']; exact pullTop_pull _ _ _ _ _
  obtain ⟨k, v, hv⟩ := exists_lat_iff (fn_int (toCpl_mem_iff R K))
    (fn_bound fun y => (exists_mul_mem R K y).imp fun r hr => ⟨Ne.isUnit (by simpa using hr.1), hr.2⟩)
    (pullTop_smul _ _) hcc e
  have hv' : InLat R v = fun s => InLat (Cpl R) e (pullTop (spMap (toCpl R K)) ξ d.D s) :=
    funext fun s => propext (hv s)
  have hsub (x y) (hx : InLat (Cpl R) e x) (hy : InLat (Cpl R) e y) : InLat (Cpl R) e (x - y) :=
    Lat.sub (φ := (fnHom _).comp (algebraMap (Cpl R) (FractionRing (Cpl R)))) hx hy
  refine ⟨k, v, ?_⟩
  rw [hv']
  refine ⟨fun x s hs => ?_,
    latSeq_descend (toCpl_mem_iff R K) (exists_sub_mem R K) w w' d.exact₁ hA d.isVB hB hsub h₂,
    latSeq_descend (toCpl_mem_iff R K) (exists_sub_mem R K) w w' d.exact₂ hA' d.isVB hB' hsub h₃⟩
  have := h₁ x _ hs
  rw [act_pullAct, ← pullTop_map] at this
  exact this

end GlobalTheory.BadPt.Descent
