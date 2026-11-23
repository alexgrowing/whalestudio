import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

section SlopeTestRemainingChoices

private theorem sp_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem sp_dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (dualMap (ψ.comp φ)) = spMap (dualMap ψ) ≫ spMap (dualMap φ) := by
  rw [← sp_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [dualMap]

private theorem sp_inj {S T : Type} [CommRing S] [CommRing T] {φ ψ : S →+* T} (h : spMap φ = spMap ψ) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

private theorem sp_stalk {G : Scheme.{0}} [IsIntegral G] (z : G) :
    spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ G.fromSpecStalk z = G.fromSpecStalk (genericPoint G) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec G).specializes trivial)

private theorem exists_germ {G Z : Scheme.{0}} (j : G ⟶ Z) {U : Z.Opens} (hU : IsAffineOpen U) (z : G) (hz : j z ∈ U) :
    ∃ α : Γ(Z, U) →+* G.presheaf.stalk z, spMap α ≫ hU.fromSpec = G.fromSpecStalk z ≫ j := by
  refine ⟨(j.stalkMap z).hom.comp (Z.presheaf.germ U (j z) hz).hom, ?_⟩
  rw [sp_comp, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hU.fromSpecStalk_eq_fromSpecStalk hz]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

private theorem isTan_of_comb {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hu : ∀ l, IsTanAtG t x (u l)) {cf : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x u cf w) : IsTanAtG t x w := by
  have h' := (GlobalTheory.LieMet.isComb_iff (fun l => GlobalTheory.LieMet.tanOf (hu l)) cf _).2 rfl
  have e := ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h).symm.trans
    ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h')
  rw [e]
  exact GlobalTheory.LieMet.isTan_tv _

private theorem core {X : Scheme.{0}} {t : SAB H X} {R S K B L : Type} [CommRing R] [CommRing S] [CommRing K]
    [CommRing B] [CommRing L] {x : Sp R ⟶ X} {y : Sp B ⟶ X} (α : R →+* S) (io : S →+* K) (s : B →+* S) (κ : B →+* L)
    (φ : L →+* K) (hc : io.comp s = φ.comp κ) (hy : spMap s ≫ y = spMap α ≫ x) {g m : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t x e)
    {f : Fin m → (Sp (DualNumber B) ⟶ t.G.left)} (hf : ∀ i, IsTanAtG t y (f i))
    {u : Fin m → (Sp (DualNumber L) ⟶ t.G.left)} (T : Matrix (Fin m) (Fin m) L)
    (hu : ∀ i, IsCombAtG t (spMap κ ≫ y) (fun k => spMap (dualMap κ) ≫ f k) (fun k => T k i) (u i)) :
    ∃ a : Fin m → Fin g → S,
      (∀ i, IsCombAtG t (spMap α ≫ x) (fun k => spMap (dualMap α) ≫ e k) (a i) (spMap (dualMap s) ≫ f i)) ∧
      ∀ i, IsCombAtG t (spMap (io.comp α) ≫ x) (fun k => spMap (dualMap (io.comp α)) ≫ e k)
        (fun k => ∑ l, io (a l k) * φ (T l i)) (spMap (dualMap φ) ≫ u i) := by
  choose a ha using fun i => (he.2 S α _ (GlobalTheory.LieMet.isTan_map s hy (hf i))).exists
  refine ⟨a, ha, fun i => ?_⟩
  have h1 := fun l => GlobalTheory.LatDRFree.comb_map t io (ha l)
  have h2 := GlobalTheory.LatDRFree.comb_map t φ (hu i)
  have e1 : spMap φ ≫ spMap κ ≫ y = spMap (io.comp α) ≫ x := by
    rw [← Category.assoc, ← sp_comp, ← hc, sp_comp, sp_comp, Category.assoc, Category.assoc, hy]
  simp only [← Category.assoc, ← sp_dual_comp] at h1
  rw [← sp_comp] at h1
  rw [e1] at h2
  simp only [← Category.assoc, ← sp_dual_comp, ← hc] at h2
  exact tanLinG _ (fun k => GlobalTheory.LieMet.isTan_map (io.comp α) rfl (he.1 k)) _ (Matrix.of fun k l => io (a l k))
    (fun l => φ (T l i)) _ h1 h2

end SlopeTestRemainingChoices

theorem UpperTheory.local_frames_over_cover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : (∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))) (d : Y.X → Fin m → Y.Fnˣ) (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn), (∀ y i, IsTanAtG t (stalkPt Y y ≫ ρ) (f y i)) → TriOf t ρ u₀ f d T → ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)), IsTanBasis t (R := Γ(V.X, U)) (hU.fromSpec ≫ ρ') e → ∀ (n : ℕ) (h : Fin n → Fin g → Γ(V.X, U)), ∃ P : Matrix (Fin n) (Fin m) V.G.functionField, ChartCo t V ρ' hU e h f T P := by
  intro E _ _ _ H X t F _ _ Y V ρ' ρ hρ m u₀ f d T hf hT U hU g e he n h
  by_cases h0 : ∃ z : V.G, V.j z ∈ U
  swap
  · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ h0⟩
  obtain ⟨z₀, hz₀⟩ := h0
  obtain ⟨α₁, hα₁⟩ := exists_germ V.j hU z₀ hz₀
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : Γ(V.X, U) →+* V.G.functionField,
      spMap α₀ ≫ hU.fromSpec = V.G.fromSpecStalk (genericPoint V.G) ≫ V.j :=
    ⟨(algebraMap (V.G.presheaf.stalk z₀) V.G.functionField).comp α₁, by
      rw [sp_comp, Category.assoc, hα₁, ← Category.assoc, sp_stalk]⟩
  have key : ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z)
      (a : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧
      (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp α = α₀ ∧
      (∀ i, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun k => spMap (dualMap α) ≫ e k) (a i)
        (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) i)) ∧
      ∀ i, IsCombAtG t (spMap α₀ ≫ hU.fromSpec ≫ ρ') (fun k => spMap (dualMap α₀) ≫ e k)
        (fun k => ∑ l, algebraMap (V.G.presheaf.stalk z) V.G.functionField (a l k) * V.φ (T (V.π z) l i))
        (spMap (dualMap V.φ) ≫ u₀ i) := by
    intro z hz
    obtain ⟨α, hα⟩ := exists_germ V.j hU z hz
    have e0 : (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp α = α₀ := by
      apply sp_inj
      rw [← cancel_mono hU.fromSpec, sp_comp, Category.assoc, hα, ← Category.assoc, sp_stalk, hα₀]
    have hs : spMap (V.π.stalkMap z).hom ≫ Y.X.fromSpecStalk (V.π z) = V.G.fromSpecStalk z ≫ V.π :=
      Scheme.SpecMap_stalkMap_fromSpecStalk V.π
    have hc : (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom =
        V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField) := by
      apply sp_inj
      rw [← cancel_mono (Y.X.fromSpecStalk (V.π z)), sp_comp, sp_comp, Category.assoc, Category.assoc, hs, sp_stalk,
        ← Category.assoc, sp_stalk, V.φ_spec]
    have hy : spMap (V.π.stalkMap z).hom ≫ stalkPt Y (V.π z) ≫ ρ = spMap α ≫ hU.fromSpec ≫ ρ' := by
      rw [stalkPt, ← Category.assoc, hs, ← Category.assoc, hα, Category.assoc, Category.assoc, hρ]
    have hg : spMap (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField) ≫ stalkPt Y (V.π z) ≫ ρ =
        genericPt Y ≫ ρ := by
      rw [stalkPt, genericPt, ← Category.assoc, sp_stalk]
    obtain ⟨a, ha, hb⟩ := core α (algebraMap (V.G.presheaf.stalk z) V.G.functionField) (V.π.stalkMap z).hom
      (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField) V.φ hc hy he (hf (V.π z)) (u := u₀) (T (V.π z))
      (fun i => by rw [hg]; exact ((hT (V.π z)).2 i).2)
    rw [e0] at hb
    exact ⟨α, a, hα, e0, ha, hb⟩
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Fin m → Fin g → V.G.functionField, ∀ i, IsCombAtG t (spMap α₀ ≫ hU.fromSpec ≫ ρ')
      (fun k => spMap (dualMap α₀) ≫ e k) (A₀ i) (spMap (dualMap V.φ) ≫ u₀ i) := by
    obtain ⟨α, a, -, -, -, hb⟩ := key z₀ hz₀
    exact ⟨_, hb⟩
  refine ⟨Matrix.of fun j i => ∑ k, α₀ (h j k) * A₀ i k, fun z hz => ?_⟩
  obtain ⟨α, a, hα, e0, ha, hb⟩ := key z hz
  refine ⟨α, a, hα, ha, ?_⟩
  have hA : ∀ i, A₀ i = fun k => ∑ l, algebraMap (V.G.presheaf.stalk z) V.G.functionField (a l k) *
      V.φ (T (V.π z) l i) := fun i =>
    (he.2 _ α₀ _ (isTan_of_comb (fun k => GlobalTheory.LieMet.isTan_map α₀ rfl (he.1 k)) (hA₀ i))).unique (hA₀ i) (hb i)
  have hdet : IsUnit ((T (V.π z)).map V.φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_of_upperTriangular (hT (V.π z)).1]
    refine IsUnit.map _ (IsUnit.prod_iff.2 fun i _ => ?_)
    rw [((hT (V.π z)).2 i).1]
    exact Units.isUnit _
  have hP : (Matrix.of fun j i => ∑ k, α₀ (h j k) * A₀ i k : Matrix (Fin n) (Fin m) V.G.functionField) =
      (Matrix.of fun j i => algebraMap (V.G.presheaf.stalk z) V.G.functionField (∑ k, α (h j k) * a i k)) *
        (T (V.π z)).map V.φ := by
    ext j i
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, hA, map_sum, map_mul, ← e0, RingHom.comp_apply,
      Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    exact Finset.sum_comm
  intro j i
  rw [RootFrame.locM, hP, Matrix.mul_nonsing_inv_cancel_right _ _ hdet, Matrix.of_apply]
