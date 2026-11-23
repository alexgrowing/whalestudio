import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.FlagCarriesEigenframe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPointRelationFieldExt
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

namespace UpperTheory.ChartsTransportCombination

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

private theorem tan_of_push {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
    {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x') (h : IsTanAtG t (x' ≫ f) (w ≫ m.φ)) :
    IsTanAtG t' x' w := by
  obtain ⟨v, hv⟩ := (GlobalTheory.LieMet.pushE m x' rfl).surjective (GlobalTheory.LieMet.tanOf h)
  have e : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ m.φ = w ≫ m.φ :=
    congrArg (fun z => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv z).left) hv
  have e' : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w :=
    m.cart.1.hom_ext e ((GlobalTheory.LieMet.isTan_tv v).1.trans hw.symm)
  exact e' ▸ GlobalTheory.LieMet.isTan_tv v

private theorem transp_comb {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O₁ O₂ : Type} [CommRing O₁] [CommRing O₂]
    {β₁ : O₁ →+* c.F} {β₂ : O₂ →+* c.F} {Z₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₁}
    {Z₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₂} {R : Type} [CommRing R] {y : Sp R ⟶ Xo.XF c} {n : ℕ}
    {v₁ : Fin n → (Sp (DualNumber R) ⟶ Z₁.t.G.left)} {v₂ : Fin n → (Sp (DualNumber R) ⟶ Z₂.t.G.left)}
    {u₁ : Sp (DualNumber R) ⟶ Z₁.t.G.left} {u₂ : Sp (DualNumber R) ⟶ Z₂.t.G.left}
    (hv : ∀ i, Transp Z₁ Z₂ y (v₁ i) (v₂ i)) (hu : Transp Z₁ Z₂ y u₁ u₂)
    (tv : ∀ i, IsTanAtG Z₂.t (y ≫ Z₂.j) (v₂ i)) (tu : IsTanAtG Z₂.t (y ≫ Z₂.j) u₂) {cf : Fin n → R}
    (h : IsCombAtG Z₂.t (y ≫ Z₂.j) v₂ cf u₂) : IsCombAtG Z₁.t (y ≫ Z₁.j) v₁ cf u₁ := by
  choose a₁ a₂ h1 h2 h3 h4 h5 using hv
  obtain ⟨b₁, b₂, k1, k2, k3, rfl, rfl⟩ := hu
  obtain rfl : (fun i => a₁ i ≫ Z₁.m.φ) = v₁ := funext h4
  obtain rfl : (fun i => a₂ i ≫ Z₂.m.φ) = v₂ := funext h5
  have ta₂ : ∀ i, IsTanAtG Z₂.oF.t y (a₂ i) := fun i => tan_of_push Z₂.m (h2 i) (tv i)
  have tb₂ : IsTanAtG Z₂.oF.t y b₂ := tan_of_push Z₂.m k2 tu
  have ta₁ : ∀ i, IsTanAtG Z₁.oF.t y (a₁ i) := fun i => tan_of_push Z₁.m0.toSABMap (h1 i) (by
    rw [h3 i]; exact GlobalTheory.LieMet.isTan_push Z₂.m0.toSABMap y rfl (ta₂ i))
  have tb₁ : IsTanAtG Z₁.oF.t y b₁ := tan_of_push Z₁.m0.toSABMap k1 (by
    rw [k3]; exact GlobalTheory.LieMet.isTan_push Z₂.m0.toSABMap y rfl tb₂)
  have c₂ := (Pull.comb_push Z₂.m rfl ta₂ tb₂ cf).1 h
  have c₀ := (Pull.comb_push Z₂.m0.toSABMap rfl ta₂ tb₂ cf).2 c₂
  rw [← k3, ← funext h3] at c₀
  exact (Pull.comb_push Z₁.m rfl ta₁ tb₁ cf).2 ((Pull.comb_push Z₁.m0.toSABMap rfl ta₁ tb₁ cf).1 c₀)

private theorem comp_eq_of_tri {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ}
    {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) {K : Type} [Field K] {i j : U.Comp}
    {q : Sp K ⟶ (Φ.C i).Y.X} {q' : Sp K ⟶ (Φ.C j).Y.X} (hq : q' ≫ (Φ.C j).π = q ≫ (Φ.C i).π) {f f' : c.F →+* K}
    {x x' : Sp K ⟶ Z.X} {g : EigFrame Z f x} {g' : EigFrame Z f' x'} (hg : (Φ.C i).Carries q g)
    (hg' : (Φ.C j).Carries q' g') (h : ∀ τ, Pull.Tri Z.t x (g.v τ) (g'.v τ)) : i = j := by
  obtain ⟨a1, a2, a3⟩ := (UpperTheory.flag_carries_eigenframe (Φ.C i) K q).2 f x g hg
  obtain ⟨b1, b2, -⟩ := (UpperTheory.flag_carries_eigenframe (Φ.C j) K q').2 f' x' g' hg'
  rw [reassoc_of% hq] at b1 b2
  obtain rfl : x' = x := b1.trans a1.symm
  obtain rfl : f' = f := congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _)
    (a₂ := CommRingCat.ofHom _) (b2.symm.trans a2))
  have I : ∀ (g : EigFrame Z f' x') τ, Pull.Ind Z.t x' (g.v τ) := fun g τ =>
    Pull.frame_ind (f := f') (u := g.v) ⟨fun τ i => ⟨g.tan τ i, g.eig τ i⟩, g.basis⟩ τ
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  choose cf c1 c2 using h
  have c3 : ∀ τ i, cf τ i i ≠ 0 := fun τ i =>
    (Pull.Tri.diag (I g τ) (I g' τ) (fun i => ⟨_, c1 τ i, c2 τ i⟩) (c2 τ i)).1
  have hc : (Φ.C i).Carries q g' := (a3 f' x' g').2 ⟨fun τ i => Units.mk0 _ (c3 τ i), g.tri_refl.1, rfl,
    fun τ i => ⟨cf τ i, rfl, c1 τ i, by simpa only [h1, Category.id_comp] using c2 τ i⟩⟩
  let ν : K →+* AlgebraicClosure K := algebraMap _ _
  have hx : (spMap ν ≫ q ≫ (Φ.C i).π) ≫ genι Z = spMap ν ≫ x' := by rw [a1]; simp only [Category.assoc]
  obtain ⟨g₁, hg₁⟩ := g'.exists_isMap ν (φ' := ν.comp f') rfl hx
  have hs : (spMap ν ≫ q ≫ (Φ.C i).π) ≫ genStr Z = spMap (ν.comp f') := by
    rw [Category.assoc, Category.assoc, a2, ← Spec.map_comp]; rfl
  exact congrArg Sigma.fst ((Φ.lifts _ _ _ hs g₁).unique (y₁ := ⟨i, spMap ν ≫ q⟩) (y₂ := ⟨j, spMap ν ≫ q'⟩)
    ⟨Category.assoc _ _ _, GlobalTheory.GalCarryBC.carries_map _ ν hc hg₁ rfl hx⟩
    ⟨by rw [← hq]; exact Category.assoc _ _ _, GlobalTheory.GalCarryBC.carries_map _ ν hg' hg₁ rfl hx⟩)

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

private theorem comp_eq_of_charts (Z : LocM.Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) {O : Type} [CommRing O]
    {β : O →+* i₀.c.F} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F]
    {e : F ≃+* i₀.c.F} {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U)
    {i j : U.Comp} {K : Type} [Field K] {w : Sp K ⟶ Z.X} {a a' : Fin Z.m} {ψ : Γ(Z.X, (Z.U a).1) →+* K}
    {ψ' : Γ(Z.X, (Z.U a').1) →+* K} (hψ : spMap ψ ≫ Z.chart a = w) (hψ' : spMap ψ' ≫ Z.chart a' = w)
    {τ τ' : (Y Z.i).X ⟶ (Y i₀).X} {mu : SABMap (Y Z.i).t (Y i₀).t τ} {mu' : SABMap (Y Z.i).t (Y i₀).t τ'}
    (hT : LocM.IsTrans i₀ Z.i τ mu) (hT' : LocM.IsTrans i₀ Z.i τ' mu') {y y' : Sp K ⟶ (Xo i₀.l).XF i₀.c}
    (e1 : (w ≫ Z.π) ≫ τ = y ≫ (Y i₀).j) (e1' : (w ≫ Z.π) ≫ τ' = y' ≫ (Y i₀).j)
    {q : Sp K ⟶ (Φ.C i).Y.X} {q' : Sp K ⟶ (Φ.C j).Y.X} (y2 : y ≫ T.jQ = q ≫ (Φ.C i).π)
    (y2' : y' ≫ T.jQ = q' ≫ (Φ.C j).π) {f f' : i₀.c.F →+* K}
    {g : EigFrame T f (q ≫ (Φ.C i).π ≫ genι T)} {g' : EigFrame T f' (q' ≫ (Φ.C j).π ≫ genι T)}
    (tr : ∀ σ k, Transp T (Y i₀) y (g.v σ k) ((Z.fr a).bc ψ σ k ≫ mu.φ))
    (tr' : ∀ σ k, Transp T (Y i₀) y' (g'.v σ k) ((Z.fr a').bc ψ' σ k ≫ mu'.φ))
    (cg : (Φ.C i).Carries q g) (cg' : (Φ.C j).Carries q' g') : i = j := by
  obtain ⟨rfl, hmu⟩ := GlobalTheory.T.transition_unique_and_points E H Dw Xo p W Y _ _ _ _ _ _ Z.le hT hT'
  have := (Y i₀).jQ_open
  have := mono_spMap_subtype (i₀.c.V W)
  have hm : Mono (Y i₀).j := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]; infer_instance
  obtain rfl : y' = y := (cancel_mono (Y i₀).j).1 (e1'.symm.trans e1)
  have F := Pull.chart_frame Z hψ
  have F' := Pull.chart_frame Z hψ'
  obtain ⟨y₀, hy₀⟩ := Pull.exists_open_lift Z hψ'
  have e3 : ∀ σ i, (Z.fr a').bc ψ' σ i ≫ mu'.φ = (Z.fr a').bc ψ' σ i ≫ mu.φ := fun σ i =>
    (hmu _ y₀ _ _ _ ((F'.1 σ i).1.1.trans (by rw [hy₀]))).symm
  refine comp_eq_of_tri Φ (y2'.symm.trans y2) cg cg' fun σ k => ?_
  obtain ⟨cf, c1, c2⟩ := Pull.chart_tri Z hty hψ hψ' σ k
  refine ⟨cf, c1, ?_⟩
  have t' := tr' σ k
  rw [e3] at t'
  have := transp_comb (tr σ) t' (fun i => GlobalTheory.LieMet.isTan_push mu _ e1 (F.1 σ i).1)
    (GlobalTheory.LieMet.isTan_push mu _ e1 (F'.1 σ k).1)
    ((Pull.comb_push mu e1 (fun i => (F.1 σ i).1) (F'.1 σ k).1 cf).2 c2)
  have e4 : y' ≫ T.j = q ≫ (Φ.C i).π ≫ genι T := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, reassoc_of% y2]
  rwa [e4] at this

private theorem sq₁ {A B C D F G M : Scheme.{0}} {η : A ⟶ B} {ι : B ⟶ C} {s : A ⟶ C} (h : η ≫ ι = s) {y : B ⟶ M}
    {j : M ⟶ G} {c : C ⟶ D} {π : D ⟶ F} {τ : F ⟶ G} (hy : y ≫ j = ι ≫ c ≫ π ≫ τ) :
    ((s ≫ c) ≫ π) ≫ τ = (η ≫ y) ≫ j := by
  rw [Category.assoc η, hy, ← h]; simp only [Category.assoc]

private theorem sq₂ {A B C D M : Scheme.{0}} (η : A ⟶ B) {y : B ⟶ M} {j : M ⟶ D} {h : B ⟶ C} {π : C ⟶ D}
    (hy : y ≫ j = h ≫ π) : (η ≫ y) ≫ j = (η ≫ h) ≫ π := by
  rw [Category.assoc, hy, Category.assoc]

private theorem link_unique (Z : LocM.Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ)
    [IsDiscreteValuationRing (Z.i.c.V W)] (C : (nmodel Z).Comp) {O : Type} [CommRing O]
    {β : O →+* i₀.c.F} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {F : Type} [Field F] [NumberField F]
    {e : F ≃+* i₀.c.F} {σ : i₀.c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf (Xo i₀.l) i₀.c σ N} (Φ : FlagTor T e U)
    {i j : U.Comp} {b : 𝓞 F →+* Z.i.c.V W} (μ : Match (Φ.C i).Y b ((nmodel Z).comp C))
    (μ' : Match (Φ.C j).Y b ((nmodel Z).comp C)) (h : Link Z C (Φ.C i) μ) (h' : Link Z C (Φ.C j) μ') : i = j := by
  obtain ⟨a, τ, mu, y, ψ, f, g, -, hT, y1, y2, hψ, tr, cg⟩ := h
  obtain ⟨a', τ', mu', y', ψ', f', g', -, hT', y1', y2', hψ', tr', cg'⟩ := h'
  exact comp_eq_of_charts Z hty Φ hψ hψ' hT hT' (sq₁ (μ.U.fromSpecStalkOfMem_ι _ μ.mem) y1)
    (sq₁ (μ'.U.fromSpecStalkOfMem_ι _ μ'.mem) y1') (sq₂ _ y2) (sq₂ _ y2') tr tr' cg cg'

end UpperTheory.ChartsTransportCombination

theorem UpperTheory.admissible_point_charts :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), (∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) → ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)] (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W), (∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x) → (∀ x : 𝓞 D.what₂.LL, ((b x : z.Z.i.c.V W) : z.Z.i.c.F) = ε (x : D.what₂.LL)) → ∀ (C : (nmodel z.Z).Comp) (c c' : s.Comp) (μ : Match (fl.C c).Y b ((nmodel z.Z).comp C)) (μ' : Match (fl.C c').Y b ((nmodel z.Z).comp C)), Link z.Z C (fl.C c) μ → Link z.Z C (fl.C c') μ' → c = c' := by
  intro D A N j S κ s fl _ p hp W hW z _ ε b _ _ C c c' μ μ' h h'
  exact UpperTheory.ChartsTransportCombination.link_unique z.Z z.full C fl μ μ' h h'
