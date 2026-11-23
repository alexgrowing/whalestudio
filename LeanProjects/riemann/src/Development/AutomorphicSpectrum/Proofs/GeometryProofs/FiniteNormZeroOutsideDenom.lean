import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFieldExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianTripleSpreadsOut
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRing
import Development.WeilBound.CoreStatements.SesquilinearFractions.NBasic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.LinePointFrame

theorem alg_descend {O K T : Type} [CommRing O] [Field K] [AddCommGroup T] [Module K T] (ρ : O →+* Module.End K T)
    (σ : O →+* K) {N n : ℕ} (t : Fin N → T) (ht : Submodule.span K (Set.range t) = ⊤) (u : Fin n → T)
    (h1 : ∀ i, u i ∈ eigSp ρ σ) (h2 : ∀ e ∈ eigSp ρ σ, ∃! cf : Fin n → K, e = ∑ i, cf i • u i) :
    ∃ Z : Set K, Z.Finite ∧ ∀ (V : Type) [CommRing V] (g : V →+* K) (M : Type) [AddCommGroup M] [Module V M]
      (b : M →+ T) (s : Fin N → M) (ρV : O →+* Module.End V M) (σV : O →+* V), Function.Injective g →
      Z ⊆ Set.range g → Function.Injective b → (∀ c x, b (c • x) = g c • b x) → (∀ i, b (s i) = t i) →
      Submodule.span V (Set.range s) = ⊤ → (∀ a x, b (ρV a x) = ρ a (b x)) → g.comp σV = σ →
      ∃ u' : Fin n → M, (∀ i, b (u' i) = u i) ∧ (∀ i, u' i ∈ eigSp ρV σV) ∧
        ∀ e ∈ eigSp ρV σV, ∃! cf : Fin n → V, e = ∑ i, cf i • u' i := by
  classical
  have hli : LinearIndependent K u := Fintype.linearIndependent_iff.2 fun g hg i => by
    have := (h2 0 (Submodule.zero_mem _)).unique hg.symm (y₂ := 0) (by simp)
    exact congrFun this i
  obtain ⟨L, hL⟩ := (Fintype.linearCombination K u).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli.fintypeLinearCombination_injective)
  have hL' : ∀ cf : Fin n → K, L (∑ i, cf i • u i) = cf := fun cf => by
    have := LinearMap.congr_fun hL cf
    simpa [Fintype.linearCombination_apply] using this
  have ha : ∀ k, ∃ a : Fin N → K, ∑ i, a i • t i = u k := fun k =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (ht ▸ Submodule.mem_top)
  choose a ha using ha
  refine ⟨Set.range (fun x : Fin n × Fin N => a x.1 x.2) ∪ Set.range (fun x : Fin n × Fin N => L (t x.2) x.1),
    (Set.finite_range _).union (Set.finite_range _), ?_⟩
  intro V _ g M _ _ b s ρV σV hg hZ hb hsm hs hsp hρ hσ
  choose a' ha' using fun k i => hZ (Or.inl ⟨(k, i), rfl⟩)
  choose l' hl' using fun k i => hZ (Or.inr ⟨(k, i), rfl⟩)
  have hbu : ∀ k, b (∑ i, a' k i • s i) = u k := fun k => by
    rw [map_sum, ← ha k]
    exact Finset.sum_congr rfl fun i _ => by rw [hsm, hs, ha']
  have heig : ∀ x, x ∈ eigSp ρV σV ↔ b x ∈ eigSp ρ σ := fun x => by
    rw [EigBase.mem_eigSp, EigBase.mem_eigSp]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hσ, RingHom.comp_apply, ← hsm, hb.eq_iff]
  have hsum : ∀ cf : Fin n → V, b (∑ k, cf k • ∑ i, a' k i • s i) = ∑ k, g (cf k) • u k := fun cf => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hsm, hbu]
  refine ⟨fun k => ∑ i, a' k i • s i, hbu, fun k => (heig _).2 (by rw [hbu]; exact h1 k), fun e he => ?_⟩
  obtain ⟨cf, hcf, -⟩ := h2 _ ((heig e).1 he)
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 (hsp ▸ Submodule.mem_top : e ∈ _)
  have hc : ∀ k, cf k = g (∑ i, x i * l' k i) := fun k => by
    rw [← hL' cf, ← hcf, ← hx, map_sum, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, hs, map_smul, map_mul, hl']
    rfl
  have he' : e = ∑ k, (∑ i, x i * l' k i) • ∑ i, a' k i • s i := hb (by
    rw [hsum, hcf]
    exact Finset.sum_congr rfl fun k _ => by rw [hc])
  refine ⟨fun k => ∑ i, x i * l' k i, he', fun y hy => funext fun k => hg ?_⟩
  have e1 := congrArg b (hy.symm.trans he')
  rw [hsum, hsum] at e1
  exact congrFun ((hL' _).symm.trans ((congrArg L e1).trans (hL' _))) k

theorem lie_lift {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {R R' : Type} [CommRing R]
    [CommRing R'] (g : R →+* R') {x : Sp R ⟶ S} {x' : Sp R' ⟶ S} (hx : x' = spMap g ≫ x) {V V' : Type}
    [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R' V'] (M : LieModel G x V) (M' : LieModel G x' V') :
    ∃ b : V →+ V', (∀ e, (M'.pt (b e)).left = spMap (dualMap g) ≫ (M.pt e).left) ∧
      (∀ c e, b (c • e) = g c • b e) ∧ Submodule.span R' (Set.range b) = ⊤ ∧
      (Function.Injective g → Function.Injective b) := by
  letI := g.toAlgebra
  subst hx
  obtain ⟨T, _, _, _, _, M'', j, hl, hj⟩ := GlobalTheory.T.exists_lie_model_base_change S G R R' x V M
  obtain ⟨f, hf, -⟩ := lieModel_existsUnique_equiv S G R' _ T V' M'' M'
  refine ⟨f.toLinearMap.toAddMonoidHom.comp j.toAddMonoidHom, fun e => ?_, fun c e => ?_, ?_, fun hg => ?_⟩
  · have := hl e
    show (M'.pt (f (j e))).left = _
    rw [hf]
    simpa [LieModel.Lifts] using this
  · show f (j (c • e)) = g c • f (j e)
    rw [j.map_smul, ← algebraMap_smul R' c (j e), f.map_smul]
    rfl
  · refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨z, rfl⟩ := f.surjective y
    induction z using hj.inductionOn with
    | zero => simp
    | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
    | smul s n h => rw [map_smul]; exact Submodule.smul_mem _ _ (h trivial)
    | add m n h h' => rw [map_add]; exact Submodule.add_mem _ (h trivial) (h' trivial)
  · haveI : Module.Projective R V := (LieProj.lie_finite_projective_baseChange S G R x V M).2.1
    haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hg
    intro a c hac
    have h1 : j a = j c := f.injective hac
    refine Module.Flat.tensorProduct_mk_injective R V R' (hj.equiv.injective ?_)
    simpa [hj.equiv_tmul] using h1

theorem span_map {R R' V V' : Type} [CommRing R] [CommRing R'] [AddCommGroup V] [Module R V] [AddCommGroup V']
    [Module R' V'] (g : R →+* R') (b : V →+ V') (hb : ∀ c e, b (c • e) = g c • b e)
    (h : Submodule.span R' (Set.range b) = ⊤) {N : ℕ} {s : Fin N → V} (hs : Submodule.span R (Set.range s) = ⊤) :
    Submodule.span R' (Set.range fun i => b (s i)) = ⊤ := by
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hs ▸ Submodule.mem_top : e ∈ _)
  rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [hb]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem frame_descend {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {R K : Type}
    [CommRing R] [Field K] (f : R →+* K) (x : Sp R ⟶ S) (xK : Sp K ⟶ S) (hx : xK = spMap f ≫ x) {O : Type}
    [CommRing O] (act : OAct O G) (σ : O →+* K) {n : ℕ} (v : Fin n → (epsAt xK ⟶ G)) (hv : IsEigFrame act xK σ v) :
    ∃ Z : Set K, Z.Finite ∧ ∀ (V : Type) [CommRing V] (g : V →+* K) (r : R →+* V) (σV : O →+* V) (xV : Sp V ⟶ S),
      Function.Injective g → Z ⊆ Set.range g → g.comp r = f → g.comp σV = σ → xV = spMap r ≫ x →
      ∃ v' : Fin n → (epsAt xV ⟶ G), IsEigFrame act xV σV v' ∧
        ∀ i, (v i).left = spMap (dualMap g) ≫ (v' i).left := by
  obtain ⟨MR, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨T, _, _, ⟨MK⟩⟩ := lieModel_exists S G K xK
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G K xK T MK O act.act act.hom act.one act.mul act.add
  haveI : Module.Finite R MR := (LieProj.lie_finite_projective_baseChange S G R x MR M).1
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := MR)
  obtain ⟨jK, hjK, hsK, hspK, -⟩ := lie_lift f hx M MK
  choose u hu using fun i => MK.onto (v i) (hv.1 i).1
  obtain rfl : (fun k => MK.pt (u k)) = v := funext hu
  obtain ⟨h1, h2⟩ := (LieEigFrame.isEigFrame_pt_iff S K G xK T MK O act ρ σ n u hρ).1 hv
  obtain ⟨Z, hZ, H⟩ := alg_descend ρ σ _ (span_map f jK hsK hspK hs) u h1 h2
  refine ⟨Z, hZ, fun V _ g r σV xV hg hZg hr hσ hxV => ?_⟩
  obtain ⟨W, _, _, ⟨MV⟩⟩ := lieModel_exists S G V xV
  obtain ⟨ρV, hρV, -⟩ := lieModel_exists_unique_act S G V xV W MV O act.act act.hom act.one act.mul act.add
  obtain ⟨jV, hjV, hsV, hspV, -⟩ := lie_lift r hxV M MV
  have hxK : xK = spMap g ≫ xV := by
    rw [hx, hxV, ← hr, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨b, hb, hsb, -, hinj⟩ := lie_lift g hxK MV MK
  have hd : spMap (dualMap f) = spMap (dualMap g) ≫ spMap (dualMap r) := by
    rw [← Spec.map_comp, ← hr]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    show dualMap (g.comp r) a = dualMap g (dualMap r a)
    ext <;> simp [dualMap]
  obtain ⟨u', e1, e2, e3⟩ := H V g W b (fun i => jV (s i)) ρV σV hg hZg (hinj hg) hsb
    (fun i => MK.inj (Over.OverMorphism.ext (by rw [hb, hjV, hjK, hd, Category.assoc])))
    (span_map r jV hsV hspV hs)
    (fun a e => MK.inj (Over.OverMorphism.ext (by
      rw [hρ a (b e), Over.comp_left, hb, hb, hρV a e, Over.comp_left, Category.assoc]))) hσ
  refine ⟨fun i => MV.pt (u' i), (LieEigFrame.isEigFrame_pt_iff S V G xV W MV O act ρV σV n u' hρV).2 ⟨e2, e3⟩,
    fun i => ?_⟩
  rw [← hb, e1]

theorem frame_transfer {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (x : Sp R ⟶ S) (hx : x = x' ≫ f) (σ : 𝓞 E →+* R) (n : ℕ) :
    (∀ v' : Fin n → (epsAt x' ⟶ t'.G), IsEigFrame t'.act x' σ v' → ∃ v : Fin n → (epsAt x ⟶ t.G),
      IsEigFrame t.act x σ v ∧ ∀ i, (v' i).left ≫ m.φ = (v i).left) ∧
    ∀ v : Fin n → (epsAt x ⟶ t.G), IsEigFrame t.act x σ v → ∃ v' : Fin n → (epsAt x' ⟶ t'.G),
      IsEigFrame t'.act x' σ v' ∧ ∀ i, (v' i).left ≫ m.φ = (v i).left := by
  subst hx
  obtain ⟨V, _, _, ⟨M'⟩⟩ := lieModel_exists S' t'.G R x'
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap E H S S' t' t f m R x' V M'
  obtain ⟨ρ, hρ', -⟩ := lieModel_exists_unique_act S' t'.G R x' V M' _ t'.act.act t'.act.hom t'.act.one t'.act.mul
    t'.act.add
  have hρ : M.IsActOf t.act.act ρ := fun a e => Over.OverMorphism.ext (by
    rw [Over.comp_left, hM, hM, hρ' a e, Over.comp_left, Category.assoc, Category.assoc, m.act])
  have key : ∀ u : Fin n → V, IsEigFrame t'.act x' σ (fun i => M'.pt (u i)) ↔
      IsEigFrame t.act (x' ≫ f) σ (fun i => M.pt (u i)) := fun u =>
    (LieEigFrame.isEigFrame_pt_iff _ _ _ _ _ M' _ t'.act ρ σ n u hρ').trans
      (LieEigFrame.isEigFrame_pt_iff _ _ _ _ _ M _ t.act ρ σ n u hρ).symm
  refine ⟨fun v h => ?_, fun v h => ?_⟩
  · choose u hu using fun i => M'.onto (v i) (h.1 i).1
    obtain rfl : (fun k => M'.pt (u k)) = v := funext hu
    exact ⟨_, (key u).1 h, fun i => (hM _).symm⟩
  · choose u hu using fun i => M.onto (v i) (h.1 i).1
    obtain rfl : (fun k => M.pt (u k)) = v := funext hu
    exact ⟨_, (key u).2 h, fun i => (hM _).symm⟩

theorem exists_sab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (f : S' ⟶ S)
    (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m₁⟩⟩

theorem exists_point {X : Scheme.{0}} {F : Type} [Field F] (s : X ⟶ Sp F) [LocallyOfFiniteType s] (U : Set X)
    (hU : IsOpen U) (hne : U.Nonempty) : ∃ (L : Type) (_ : Field L) (β : F →+* L) (y : Sp L ⟶ X),
      β.Finite ∧ y ≫ s = spMap β ∧ Set.range y ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx hU
  replace hW : IsAffineOpen W := hW
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hW.fromSpec ≫ s)
  have hft : ψ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map ψ) := by
      rw [hψ]
      exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ inferInstance ‹_›
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hr : Set.range hW.fromSpec = (W : Set X) := hW.range_fromSpec
  obtain ⟨q, -⟩ : x ∈ Set.range hW.fromSpec := hr ▸ hxW
  haveI : Nontrivial Γ(X, W) := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, W)
  letI := Ideal.Quotient.field m
  refine ⟨Γ(X, W) ⧸ m, inferInstance, (Ideal.Quotient.mk m).comp ψ.hom,
    spMap (Ideal.Quotient.mk m) ≫ hW.fromSpec, ?_, ?_, ?_⟩
  · exact RingHom.finite_iff_finiteType_of_isJacobsonRing.2
      ((RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hft)
  · rw [Category.assoc, ← hψ]
    exact (Spec.map_comp _ _).symm
  · rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hWU (hr ▸ ⟨_, rfl⟩)

theorem exists_framed {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (β : c.F →+* K) (y : Sp K ⟶ Xo.XF c)
      (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w := by
  haveI := c.fin
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  haveI := Xo.univ.t.semi.smooth
  obtain ⟨L, _, β, y, hfin, hy, hyU⟩ :=
    exists_point (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) U hU hne
  let k := AlgebraicClosure L
  let βk : c.F →+* k := (algebraMap L k).comp β
  have hxs : (spMap (algebraMap L k) ≫ under y) ≫ Xo.s =
      spMap (βk.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc y, hy, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have hdet := (Xo.univ.geom k _ _ hxs).1
  have h0 : tauIn c τ H.rt = (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ := Subtype.ext hτ
  have h1 : tauIn c (ComplexEmbedding.conjugate τ) H.rt ≠ (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ := by
    intro h
    have h' : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := congrArg Subtype.val h
    rw [hτ] at h'
    obtain ⟨a, ha⟩ := Complex.conj_eq_iff_real.1 h'
    have h2 := H.sqrt_neg_disc_sq
    rw [ha] at h2
    have h3 : a ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [sq_nonneg a]
  obtain ⟨v, hv⟩ : ∃ v : Fin D.p → (epsAt (spMap (algebraMap L k) ≫ under y) ⟶ Xo.univ.t.G),
      IsEigFrame Xo.univ.t.act _ (βk.comp (tauIn c τ)) v :=
    (hdet (βk.comp (tauIn c τ))).1 (congrArg βk h0)
  obtain ⟨w, hw⟩ : ∃ w : Fin D.q → (epsAt (spMap (algebraMap L k) ≫ under y) ⟶ Xo.univ.t.G),
      IsEigFrame Xo.univ.t.act _ (βk.comp (tauIn c (ComplexEmbedding.conjugate τ))) w :=
    (hdet (βk.comp (tauIn c (ComplexEmbedding.conjugate τ)))).2 fun h => h1 (βk.injective h)
  obtain ⟨Z₁, hZ₁, H₁⟩ := frame_descend (algebraMap L k) (under y) _ rfl _ _ v hv
  obtain ⟨Z₂, hZ₂, H₂⟩ := frame_descend (algebraMap L k) (under y) _ rfl _ _ w hw
  let K := IntermediateField.adjoin L (Z₁ ∪ Z₂)
  haveI : Finite (Z₁ ∪ Z₂ : Set k) := (hZ₁.union hZ₂).to_subtype
  haveI : FiniteDimensional L K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let βK : c.F →+* K := (algebraMap L K).comp β
  have hβK : βK.Finite := (RingHom.finite_algebraMap.2 inferInstance).comp hfin
  haveI : CharZero K := βK.charZero_iff βK.injective |>.1 inferInstance
  haveI : NumberField c.F := { }
  haveI : NumberField K := by
    letI := βK.toAlgebra
    haveI : Module.Finite c.F K := hβK
    exact NumberField.of_module_finite c.F K
  have hZ : Z₁ ∪ Z₂ ⊆ Set.range (algebraMap K k) := fun z hz => ⟨⟨z, IntermediateField.subset_adjoin _ _ hz⟩, rfl⟩
  obtain ⟨v', hv', -⟩ := H₁ K (algebraMap K k) (algebraMap L K) (βK.comp (tauIn c τ))
    (under (spMap (algebraMap L K) ≫ y)) (algebraMap K k).injective (Set.subset_union_left.trans hZ) rfl rfl
    (Category.assoc _ _ _)
  obtain ⟨w', hw', -⟩ := H₂ K (algebraMap K k) (algebraMap L K) (βK.comp (tauIn c (ComplexEmbedding.conjugate τ)))
    (under (spMap (algebraMap L K) ≫ y)) (algebraMap K k).injective (Set.subset_union_right.trans hZ) rfl rfl
    (Category.assoc _ _ _)
  refine ⟨K, inferInstance, inferInstance, βK, spMap (algebraMap L K) ≫ y, v', w', ?_, ?_, hv', hw'⟩
  · rw [Category.assoc, hy, ← Spec.map_comp]
    rfl
  · rintro _ ⟨p, rfl⟩
    exact hyU ⟨spMap (algebraMap L K) p, (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem exists_denom {K : Type} [Field K] [NumberField K] (Z : Set K) (hZ : Z.Finite) :
    ∃ n : ℕ, 0 < n ∧ ∀ z ∈ Z, ∃ a : 𝓞 K, (a : K) = n * z := by
  obtain ⟨y, hy, H⟩ := exists_integral_multiples ℤ ℚ hZ.toFinset
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun z hz => ?_⟩
  have h := H z (hZ.mem_toFinset.2 hz)
  rcases Int.natAbs_eq y with e | e
  · refine ⟨⟨y • z, h⟩, ?_⟩
    show y • z = _
    rw [zsmul_eq_mul]
    nth_rewrite 1 [e]
    simp
  · refine ⟨⟨-(y • z), h.neg⟩, ?_⟩
    show -(y • z) = _
    rw [zsmul_eq_mul]
    nth_rewrite 1 [e]
    simp

theorem intFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {K R : Type} [Field K] [CommRing R] {y : Sp K ⟶ Xo.XF c} {tK : SAB H (Sp K)}
    (m : SABMap tK Xo.univ.t (under y)) {T : SAB H (Sp R)} (f : R →+* K) (m₀ : SABMap tK T (spMap f))
    (σ : 𝓞 E →+* K) {n : ℕ} (v : Vecs y n) (hv : IsEigFrame Xo.univ.t.act (under y) σ v) :
    ∃ Z : Set K, Z.Finite ∧ ∀ (V : Type) [CommRing V] [Algebra V K] (r : R →+* V) (σV : 𝓞 E →+* V)
      (TV : SAB H (Sp V)) (mV : SABMap TV T (spMap r)) (m' : SABMap tK TV (spMap (algebraMap V K))),
      Function.Injective (algebraMap V K) → Z ⊆ Set.range (algebraMap V K) → (algebraMap V K).comp r = f →
      (algebraMap V K).comp σV = σ → m₀.φ = m'.φ ≫ mV.φ → IsIntFrame m m' σ v := by
  haveI := T.semi.smooth
  obtain ⟨vK, hvK, eK⟩ := (frame_transfer m (𝟙 _) (under y) (Category.id_comp _).symm σ n).2 v hv
  obtain ⟨vT, hvT, eT⟩ := (frame_transfer m₀ (𝟙 _) (spMap f) (Category.id_comp _).symm σ n).1 vK hvK
  obtain ⟨Z, hZ, HZ⟩ := frame_descend f (𝟙 _) (spMap f) (Category.comp_id _).symm T.act σ vT hvT
  refine ⟨Z, hZ, fun V _ _ r σV TV mV m' hg hZg hr hσ hm => ?_⟩
  obtain ⟨v', hv', e'⟩ := HZ V (algebraMap V K) r σV (spMap r) hg hZg hr hσ (Category.comp_id _).symm
  obtain ⟨vV, hvV, eV⟩ := (frame_transfer mV (𝟙 _) (spMap r) (Category.id_comp _).symm σV n).2 v' hv'
  refine ⟨σV, vV, hσ, hvV, fun a => ⟨(vK a).left, eK a, ?_⟩⟩
  have hp : IsPullback mV.φ TV.G.hom T.G.hom (spMap r) := mV.cart.1
  have hq : IsPullback m'.φ tK.G.hom TV.G.hom (spMap (algebraMap V K)) := m'.cart.1
  apply hp.hom_ext
  · rw [Category.assoc, ← hm, eT, e', Category.assoc, eV]
  · have a₁ : (vK a).left ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) ≫ 𝟙 _ := Over.w (vK a)
    have a₂ : (vV a).left ≫ TV.G.hom = spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _ := Over.w (vV a)
    rw [Category.assoc, hq.w, ← Category.assoc, a₁, Category.assoc, Category.assoc, a₂, Category.comp_id,
      Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    show algebraMap K (DualNumber K) (algebraMap V K z) = dualMap (algebraMap V K) (algebraMap V (DualNumber V) z)
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' S'' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} (g : S'' ⟶ S') {h : S'' ⟶ S} (e : h = g ≫ f)
    (m : SABMap t' t f) (n : SABMap t'' t h) : ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n

end GlobalTheory.CompanionTheory.Ar.Flat.LinePointFrame

namespace GlobalTheory.CompanionTheory.Ar.Flat

open LinePointFrame in

theorem line_function_norm_zero_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsOpen U → U.Nonempty → IsLineFn U τ φ → ∃ n : ℕ, 0 < n ∧ ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ), ¬ (p : ℕ) ∣ n → HasFinNorm U τ φ p κ t → t = 0 := by
  intro E _ _ _ H D l Xo c U τ φ hτ hU hne hφ
  haveI := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨K, _, _, β, y, v, w, hfr⟩ := exists_framed Xo c U τ hτ hU hne
  obtain ⟨tK, ⟨m⟩⟩ := LinePointFrame.exists_sab (under y) Xo.univ.t
  have hprop : IsProper tK.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  obtain ⟨n₀, hn₀, T, f, hf, ⟨m₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.Flat.abelianTriple_spreads_out E H K tK hprop
  obtain ⟨Z₁, hZ₁, H₁⟩ := intFrame m f m₀ _ v hfr.2.2.1
  obtain ⟨Z₂, hZ₂, H₂⟩ := intFrame m f m₀ _ w hfr.2.2.2
  have hφ0 : φ K y v w ≠ 0 := hφ.ne K β y v w hfr
  obtain ⟨n, hn, Hn⟩ := exists_denom (Z₁ ∪ Z₂ ∪ {φ K y v w, (φ K y v w)⁻¹, (n₀ : K)⁻¹})
    ((hZ₁.union hZ₂).union (Set.toFinite _))
  refine ⟨n, hn, fun p κ t hp ht => ?_⟩
  obtain ⟨j, hj⟩ := PositivityTheory.Xgf.exists_extension_embedding_alg_closed c.F K ℂ_[p] β κ
  obtain ⟨V, hV, hjV, hOV, hnV⟩ := GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding K p j
  have hle : ∀ z ∈ Z₁ ∪ Z₂ ∪ {φ K y v w, (φ K y v w)⁻¹, (n₀ : K)⁻¹}, ‖j z‖ ≤ 1 := fun z hz => by
    obtain ⟨a, ha⟩ := Hn z hz
    have := (hjV _).2 (hOV a)
    rwa [ha, map_mul, norm_mul, hnV n hp, _root_.one_mul] at this
  have hrange : ∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range := fun a =>
    (hjV a).trans ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩
  have hn₀K : (n₀ : K) ≠ 0 := fun h => hn₀ (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hfV : ∀ x, f x ∈ V.toSubring := fun x => by
    obtain ⟨k, a, hx⟩ := IsLocalization.Away.surj n₀ x
    have h1 := congrArg f hx
    rw [map_mul, map_pow, hf, hf] at h1
    have h2 : f x = (a : K) * ((n₀ : K)⁻¹) ^ k := by
      rw [← h1, inv_pow, mul_inv_cancel_right₀ (pow_ne_zero k hn₀K)]
    rw [h2]
    exact mul_mem (hOV a) (pow_mem ((hjV _).1 (hle _ (by simp))) k)
  have hσV : ∀ (σ : 𝓞 E →+* K) (x : 𝓞 E), σ x ∈ V.toSubring := fun σ x =>
    hOV ⟨σ x, (RingOfIntegers.isIntegral x).map σ.toIntAlgHom⟩
  let r : Localization.Away n₀ →+* V := f.codRestrict V.toSubring hfV
  obtain ⟨TV, ⟨mV⟩⟩ := LinePointFrame.exists_sab (spMap r) T
  obtain ⟨m', hm'⟩ := exists_cancel (spMap (algebraMap V K)) (h := spMap f) (by rw [← Spec.map_comp]; rfl) mV m₀
  have key := ht V K j β y v w TV tK m m' hrange hj hfr
    (H₁ V r (RingHom.codRestrict (β.comp (tauIn c τ)) V.toSubring (hσV _)) TV mV m' Subtype.val_injective
      (fun z hz => (hrange z).1 (hle z (Or.inl (Or.inl hz)))) rfl rfl hm')
    (H₂ V r (RingHom.codRestrict (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) V.toSubring (hσV _)) TV mV m' Subtype.val_injective
      (fun z hz => (hrange z).1 (hle z (Or.inl (Or.inr hz)))) rfl rfl hm')
  have a₁ := hle (φ K y v w) (by simp)
  have a₂ := hle (φ K y v w)⁻¹ (by simp)
  have a₃ : 0 < ‖j (φ K y v w)‖ := norm_pos_iff.2 ((map_ne_zero j).2 hφ0)
  rw [map_inv₀, norm_inv, inv_le_one₀ a₃] at a₂
  rw [← key, le_antisymm a₁ a₂, Real.log_one]

end GlobalTheory.CompanionTheory.Ar.Flat
