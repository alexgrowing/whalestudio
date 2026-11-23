import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

noncomputable section

namespace GlobalTheory.SS.InvFrame

theorem exists_det_ne_zero {F S : Type} [Field F] {n : ℕ} (D : Fin n → S → F) (h : LinearIndependent F D) :
    ∃ t : Fin n → S, (Matrix.of fun i j => D i (t j)).det ≠ 0 := by
  have hs := span_flip_eq_top_iff_linearIndependent.2 h
  obtain ⟨f, hf, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range (flip D))
  have e : Module.finrank F (Submodule.span F (Set.range (flip D))) = n := by
    rw [hs, finrank_top, Module.finrank_fin_fun]
  choose t ht using hf
  refine ⟨fun j => t (j.cast e.symm), ?_⟩
  have h2 := hli.comp (Fin.cast e.symm) (Fin.cast_injective _)
  refine ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)).ne_zero
  have e2 : (Matrix.of fun i j : Fin n => D i (t (j.cast e.symm))).col = f ∘ Fin.cast e.symm :=
    funext fun j => ht _
  rw [e2]
  exact h2

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis constFn)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.KS GlobalTheory.KS.InvField

theorem value_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{0}}
    (φ : Γ(X, U) ⟶ T) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso T).hom.hom (pbT (Spec.map φ ≫ hU.fromSpec) f ⊤) = φ.hom f := by
  have ht : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  rw [pbT_of_le _ ht']
  have h1 : hU.fromSpec.appLE U ⊤ ht = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h2 : (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso T).hom = φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, h1, Category.assoc, Iso.inv_comp_eq,
      ← Scheme.ΓSpecIso_naturality]
    congr 1
  exact congrArg (fun q => q.hom f) h2

theorem value_constFn_id {T : Type} [CommRing T] (a : T) :
    (Scheme.ΓSpecIso (.of T)).hom.hom (constFn (𝟙 (Sp T)) ⊤ a) = a := by
  have h : (𝟙 (Sp T) : Sp T ⟶ Sp T).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 (Sp T)) (U := ⊤)).trans rfl
  rw [constFn, h]
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso (.of T)).inv_hom_id

variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))} [GrpObj G] [IsCommMonObj G]

theorem exists_independent [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {S F : Type} [CommRing S] [Algebra K S] [Field F] [Algebra K F] (j : sp (R₀ := K) S ⟶ G)
    [IsOpenImmersion j.left] (u : S →ₐ[K] F) :
    ∃ D : Fin n → S → F, LinearIndependent F D ∧ ∀ k, ∃ φ : S →ₐ[K] DualNumber F,
      spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v k) *
        (spMap ((inlS K F).comp u) ≫ j) ∧ ∀ a, (φ a).snd = D k a := by
  obtain ⟨χ, hχ, hfst⟩ := exists_chart_pt_of_nil j (TrivSqZeroExt.fstHom K F (Fin n → F))
    (fun a => ⟨inl a, rfl⟩) (fun a ha => ⟨2, by
      rw [pow_two]; exact mul_eq_zero_of_sq (ker_fst_sq (R := K) (S := F) (Fin n → F)) ha ha⟩)
    (lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) *
      (spMap ((TrivSqZeroExt.inlAlgHom K F (Fin n → F)).comp u) ≫ j)) u (by
      rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), one_mul, ← Category.assoc,
        spMap_comp]
      rfl)
  have hfst : ∀ a, (χ a).fst = u a := AlgHom.congr_fun hfst
  let φ : (Fin n → F) → (S →ₐ[K] DualNumber F) := fun c => (vecTo (inlS K F) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = tanExp v c * (spMap ((inlS K F).comp u) ≫ j) := fun c => by
    rw [← spMap_comp, Category.assoc, ← hχ, MonObj.comp_mul, comp_lieExp, ← Category.assoc, spMap_comp]
    congr 1
    · exact lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _
    · congr 2
      exact AlgHom.ext fun a => by simp [vecTo_apply]
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, c k * (χ a).snd k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  refine ⟨fun k a => (χ a).snd k, Fintype.linearIndependent_iff.2 fun c hc k => ?_,
    fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using congrFun hc a)
    have h3 := mul_right_cancel ((hφ c).symm.trans (this ▸ hφ 0))
    have h4 := (expBij (DualNumber F) hv _ (ker_fst_sq (R := K) (S := F) F)).1 _ _ (fun _ => rfl) (fun _ => rfl) _ _ h3
    exact TrivSqZeroExt.inr_injective (congrFun h4 k)
  · rw [hφ]
    congr 1
    refine (Finset.prod_eq_single k (fun i _ hi => epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
      (by simp [Pi.single_eq_of_ne hi]) _) (by simp)).trans ?_
    congr 3
    simp
  · rw [hφ2]
    simp [Pi.single_apply]

omit [IsCommMonObj G] in

theorem value_invDer {v : epsR K ⟶ G} {dd : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(G.left, W)} (hd : IsInvDer v dd)
    {U : G.left.Opens} (hU : IsAffineOpen U) [Algebra K Γ(G.left, U)] (j : sp (R₀ := K) Γ(G.left, U) ⟶ G)
    (hj : j.left = hU.fromSpec) {F : Type} [Field F] [Algebra K F] (u : Γ(G.left, U) →ₐ[K] F)
    (φ : Γ(G.left, U) →ₐ[K] DualNumber F)
    (hφ : spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v) *
        (spMap ((inlS K F).comp u) ≫ j)) (f : Γ(G.left, U)) : (φ f).snd = u (dd U f) := by
  let w : sp (R₀ := K) (DualNumber F) ⟶ epsR K ⊗ G :=
    lift (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))) (spMap ((inlS K F).comp u) ≫ j)
  have e1 : w.left ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, ← hφ, Over.comp_left, hj]
    rfl
  have e2 : w.left ≫ (snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom ((inlS K F).comp u).toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, hj]
    rfl
  have e3 : w.left ≫ (fst (epsR K) G).left = 𝟙 _ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
      (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)).toRingHom := by
    rw [← Over.comp_left, lift_fst, Category.id_comp]
    rfl
  have hw : ⊤ ≤ w.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, e2]
    exact fun q _ => hU.fromSpec_preimage_self.ge (x := Spec.map _ q) trivial
  have key : ∀ f : Γ(G.left, U), ((Scheme.ΓSpecIso (.of (DualNumber F))).hom.hom (pbT w.left
      (pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ U)) ⊤) : DualNumber F) =
      inl (u f) + inr 1 * inl (u (dd U f)) := fun f => by
    rw [hd U f, pbT_add, pbT_mul, pbT_pbT _ _ le_rfl hw, pbT_pbT _ _ le_rfl hw, pbT_constFn _ _ hw, e2, e3,
      constFn_spMap, map_add, map_mul]
    refine congrArg₂ _ (value_fromSpec hU _ _) (congrArg₂ _ ?_ (value_fromSpec hU _ _))
    refine Eq.trans ?_ (epsTo_eps (R := K) (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))
    exact value_constFn_id _
  by_cases h : (snd (epsR K) G).left ⁻¹ᵁ U ≤ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ U
  · have := key f
    rw [pbT_pbT _ _ h hw, e1] at this
    have h5 := congrArg TrivSqZeroExt.snd ((value_fromSpec hU _ f).symm.trans this)
    simpa using h5
  · have := key 1
    rw [show pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left (1 : Γ(G.left, U))
      ((snd (epsR K) G).left ⁻¹ᵁ U) = 0 from dif_neg h, pbT_zero, map_zero] at this
    simpa using congrArg TrivSqZeroExt.fst this

theorem exists_mem_basicOpen [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (D : Fin n → VF G) (hd : ∀ i, IsInvDer (v i) fun W f => (D i).D W f) (x : G.left) :
    ∃ (U : G.left.Opens) (t : Fin n → Γ(G.left, U)), x ∈ G.left.basicOpen (jac D U t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  letI : Algebra K Γ(G.left, U) := (Spec.preimage (hU.fromSpec ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) Γ(G.left, U) ⟶ G := Over.homMk hU.fromSpec (Spec.map_preimage _).symm
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx
  have := PrimeSpectrum.isPrime p
  let u : Γ(G.left, U) →ₐ[K] (PrimeSpectrum.asIdeal p).ResidueField := IsScalarTower.toAlgHom _ _ _
  obtain ⟨δ, hδ, hφ⟩ := exists_independent hv j u
  obtain ⟨t, ht⟩ := exists_det_ne_zero δ hδ
  refine ⟨U, t, ?_⟩
  have h1 : u (jac D U t) ≠ 0 := by
    rw [jac, AlgHom.map_det]
    refine (congrArg Matrix.det (Matrix.ext fun i k => ?_)).trans_ne ht
    obtain ⟨φ, h2, h3⟩ := hφ i
    exact (value_invDer (hd i) hU j rfl u φ h2 (t k)).symm.trans (h3 _)
  have h2 : p ∈ hU.fromSpec ⁻¹ᵁ G.left.basicOpen (jac D U t) := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact fun h => h1 (Ideal.algebraMap_residueField_eq_zero.2 h)
  exact h2

end GlobalTheory.SS.InvFrame

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.SS.exists_isFrame : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  intro K _ A _ _ g hg
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  choose dd hdd using fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).1
  have hp := fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).2 _ (hdd i)
  let D : Fin g → VF A := fun i =>
    { D := fun U => AddMonoidHom.mk' (dd i U) ((hp i).1 U)
      leibniz := (hp i).2.1
      const := (hp i).2.2.2.1
      res := fun U V h a => by
        have := (hp i).2.2.1 U V a h
        rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h] at this
        exact this }
  refine ⟨D, by rwa [Fintype.card_fin], fun x => ?_⟩
  obtain ⟨U, t, hx⟩ := InvFrame.exists_mem_basicOpen hv D hdd x
  have hle := A.left.basicOpen_le (jac D U t)
  refine ⟨_, fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i), hx, ?_⟩
  have e : jac D _ (fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i)) =
      (A.left.presheaf.map (homOfLE hle).op).hom (jac D U t) := by
    exact (congrArg Matrix.det (Matrix.ext fun i k => (D i).res U _ hle (t k))).trans
      (RingHom.map_det (A.left.presheaf.map (homOfLE hle).op).hom (Matrix.of fun i k => (D i).D U (t k))).symm
  rw [e]
  exact A.left.toRingedSpace.isUnit_res_basicOpen (jac D U t)

end

end
