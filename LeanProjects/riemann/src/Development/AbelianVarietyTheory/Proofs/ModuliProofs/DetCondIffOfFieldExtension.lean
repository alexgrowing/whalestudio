import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetExtend

theorem exists_oAct_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) : ∃ a' : OAct O ((Over.pullback f).obj G), ∀ c, a'.act c = (Over.pullback f).map (a.act c) :=
  ⟨{ act := fun c => (Over.pullback f).map (a.act c)
     hom := fun c => by have := a.hom c; infer_instance
     one := by rw [a.one, CategoryTheory.Functor.map_id]
     mul := fun x y => by rw [a.mul, CategoryTheory.Functor.map_comp]
     add := fun x y => by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _ }, fun _ => rfl⟩

theorem lieMult_fibre {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) {G : Over S} [GrpObj G] {O : Type}
    [CommRing O] (a : OAct O G) (a' : OAct O ((Over.pullback x).obj G))
    (h : ∀ c, a'.act c = (Over.pullback x).map (a.act c)) {k' : Type} [Field k'] (y : Sp k' ⟶ Sp k)
    (τ : O →+* k') (n : ℕ) : LieMult a' y τ n ↔ LieMult a (y ≫ x) τ n :=
  LiePull.lieMult_pull O _ _ G _ x _ a a' (isGrpPullback_pullback G x)
    (fun c => by rw [h]; exact pullback.lift_fst _ _ _) k' y τ n

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap eigLat IsUnivChart) in

theorem lieMult_iff_finrank {k : Type} [Field k] {O : Type} [CommRing O] {G : Over (Sp k)} [GrpObj G]
    (act : OAct O G) [∀ a, IsMonHom (act.act a)] {n : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (τ : O →+* k) (N : ℕ) :
    LieMult act (𝟙 (Sp k)) τ N ↔ Module.finrank k (eigLat hx act.act (fun a => τ a)) = N := by
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G) ≃* (epsR k ⟶ G) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left = η[G].left := Category.id_comp _
  let P : (epsR k ⟶ G) → Prop := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w
  have hP : ∀ w, IsLieEigen act (𝟙 _) τ w ↔ P (e w) := fun w =>
    and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl)
  have key : LieMult act (𝟙 (Sp k)) τ N ↔ ∃ v : Fin N → (epsR k ⟶ G), (∀ i, P (v i)) ∧
      ∀ w, P w → ∃! c : Fin N → k, IsLieComb c v w :=
    ⟨LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ) (Q := P)
      (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left) hP
      (fun c u v => by rw [he, he]; rfl) N,
    LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ) (P := P)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
      (fun w => by rw [hP, e.apply_symm_apply]) (fun c u v => by rw [he', he']; rfl) N⟩
  have mem : ∀ c, c ∈ eigLat hx act.act (fun a => τ a) ↔ P (tvec (x := x) c) := fun c => by
    rw [Chart.mem_eigLat_iff]
    exact ⟨fun h => ⟨(Chart.isTan_iff _).1 (Chart.isTan_tvec hx c), fun a => (Chart.tvec_eig_iff hx _ _ _).2 (h a)⟩,
      fun h a => (Chart.tvec_eig_iff hx _ _ _).1 (h.2 a)⟩
  have ex : ∀ w, P w → ∃ c : eigLat hx act.act (fun a => τ a), w = tvec (x := x) c := fun w hw => by
    have h : w = tvec (x := x) _ := Chart.tcoord_spec hx w ((Chart.isTan_iff _).2 hw.1)
    exact ⟨⟨_, (mem _).2 (h ▸ hw)⟩, h⟩
  have comb : ∀ (b : Fin N → eigLat hx act.act (fun a => τ a)) (c : eigLat hx act.act (fun a => τ a))
      (d : Fin N → k), IsLieComb d (fun i => tvec (x := x) (b i)) (tvec (x := x) c) ↔
        Fintype.linearCombination k b d = c := fun b c d => by
    refine (Chart.isLieComb_iff d _ _).trans ?_
    obtain ⟨h, E⟩ := Chart.prodPts_tan hx d (fun i => tvec (x := x) (b i)) fun i => Chart.isTan_tvec hx _
    have E' : prodPts d (fun i => tvec (x := x) (b i)) = tvec (x := x) _ := Chart.tcoord_spec hx _ h
    rw [E', E, Subtype.ext_iff, Fintype.linearCombination_apply]
    simp only [Chart.tcoord_tvec, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    exact ⟨fun h => (Chart.tvec_inj hx h).symm, fun h => by rw [h]⟩
  rw [key]
  constructor
  · rintro ⟨v, hv, H⟩
    choose b hb using fun i => ex _ (hv i)
    obtain rfl : v = fun i => tvec (x := x) (b i) := funext hb
    rw [← (LinearEquiv.ofBijective (Fintype.linearCombination k b) ((Function.bijective_iff_existsUnique _).2
      fun c => (existsUnique_congr (comb b c)).1 (H _ ((mem _).1 c.2)))).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq _ _ h
    refine ⟨fun i => tvec (x := x) (b i), fun i => (mem _).1 (b i).2, fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := ex w hw
    refine (existsUnique_congr (comb b c)).2 ((Function.bijective_iff_existsUnique _).1 ?_ _)
    convert b.equivFun.symm.bijective using 1
    ext r
    simp [Fintype.linearCombination_apply]

open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat fB pushR dualMapA) in

theorem lieMult_extend {S : Scheme.{0}} {G : Over S} [GrpObj G] [Smooth G.hom] {K Ω : Type} [Field K] [Field Ω]
    (i : K →+* Ω) (x : Sp K ⟶ S) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* K) (N : ℕ) :
    LieMult act (spMap i ≫ x) (i.comp τ) N ↔ LieMult act x τ N := by
  let _ := i.toAlgebra
  obtain ⟨a₁, h₁⟩ := exists_oAct_pullback x act
  have E₁ := lieMult_fibre x act a₁ h₁ (𝟙 _) τ N
  rw [Category.id_comp] at E₁
  rw [← E₁, ← lieMult_fibre x act a₁ h₁]
  have : Smooth ((Over.pullback x).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom x))
  generalize_proofs at *
  set G₁ := (Over.pullback x).obj G
  obtain ⟨a₂, h₂⟩ := exists_oAct_pullback (fB K Ω) a₁
  have E₂ := lieMult_fibre (fB K Ω) a₁ a₂ h₂ (𝟙 _) (i.comp τ) N
  rw [Category.id_comp] at E₂
  refine E₂.symm.trans ?_
  have := a₁.hom
  have := a₂.hom
  obtain ⟨n, y, hy⟩ := Chart.univChartLoc G₁
  obtain ⟨y', hy', hc⟩ := Chart.tanBC_alg (R' := Ω) G₁ n y hy
  have hpt : ∀ c : Fin n → K, pushR G₁ (tvec (x := y') (algebraMap K Ω ∘ c)) =
      Chart.spMap (dualMapA K Ω) ≫ tvec (x := y) c := fun c =>
    Over.OverMorphism.ext (by rw [Chart.pushR_left, hc c]; rfl)
  have hL : ∀ a (c : Fin n → K), tmap hy' (a₂.act a) (algebraMap K Ω ∘ c) =
      algebraMap K Ω ∘ tmap hy (a₁.act a) c := fun a c => by
    apply Chart.tvec_inj hy'
    apply Chart.pushR_inj G₁
    rw [Chart.tvec_tmap hy', h₂, Chart.pushR_map, hpt, hpt, Chart.tvec_tmap hy, Category.assoc]
  have hr : Module.finrank K (eigLat hy a₁.act fun a => τ a) =
      Module.finrank Ω (eigLat hy' a₂.act fun a => i.comp τ a) :=
    Chart.finrank_eig_bc (fun a => tmap hy (a₁.act a)) (fun a => tmap hy' (a₂.act a)) hL τ
  rw [lieMult_iff_finrank a₂ hy', lieMult_iff_finrank a₁ hy, hr]

theorem exists_factor {O K Ω : Type} [CommRing O] [Algebra.IsIntegral ℤ O] [Field K] [IsAlgClosed K] [Field Ω]
    (i : K →+* Ω) (σ : O →+* Ω) : ∃ τ : O →+* K, i.comp τ = σ := by
  let _ := i.toAlgebra
  have h : ∀ a, σ a ∈ i.range := fun a => by
    have h₀ : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
    have h₁ : IsIntegral K (σ a) := h₀.tower_top
    exact minpoly.mem_range_of_degree_eq_one K _
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h₁))
  let e : K ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun a b hab => i.injective (congrArg Subtype.val hab), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (σ.codRestrict _ h), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (σ.codRestrict _ h a))

end GlobalTheory.DetExtend

theorem GlobalTheory.detCond_iff_of_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) [IsAlgClosed K] [CharZero K] (act : OAct (𝓞 E) G) (ρ : K), Smooth G.hom → (DetCond D act (spMap i ≫ x) (i ρ) ↔ DetCond D act x ρ) := by
  intro E _ _ _ H D S G _ K Ω _ _ i x _ _ act ρ _
  have key : ∀ τ : 𝓞 E →+* K,
      ((i.comp τ H.rt = i ρ → LieMult act (spMap i ≫ x) (i.comp τ) D.p) ∧
        (i.comp τ H.rt ≠ i ρ → LieMult act (spMap i ≫ x) (i.comp τ) D.q)) ↔
      ((τ H.rt = ρ → LieMult act x τ D.p) ∧ (τ H.rt ≠ ρ → LieMult act x τ D.q)) := fun τ => by
    rw [DetExtend.lieMult_extend, DetExtend.lieMult_extend, RingHom.comp_apply, Ne, i.injective.eq_iff]
  refine ⟨fun h τ => (key τ).1 (h _), fun h σ => ?_⟩
  obtain ⟨τ, rfl⟩ := DetExtend.exists_factor i σ
  exact (key τ).2 (h τ)
