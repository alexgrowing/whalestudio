import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Cap
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_mono {V W : X.Opens} (h : V ≤ W) (T : Thick (smFun X q))
    (hT : InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) V T) :
    InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) W T :=
  fun x hx => h (hT hx)

theorem coe_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    ((capO U i : X.Opens) : Set X) = ⋂ k, (U (i k) : Set X) := by
  have h : capO U i = Finset.univ.inf fun k => U (i k) := by
    rw [Finset.inf_univ_eq_iInf]; rfl
  rw [h, TopologicalSpace.Opens.coe_finset_inf]
  ext x
  simp [Finset.inf_eq_iInf]

theorem inU_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (smFun X q)) :
    InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (capO U i) T ↔
      ∀ k, InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U (i k)) T := by
  constructor
  · exact fun h k => inU_mono q (capO_le U i k) T h
  · intro h x hx
    have : (pt T x) ∈ ((capO U i : X.Opens) : Set X) := by
      rw [coe_capO]
      exact Set.mem_iInter.2 fun k => h k hx
    exact this

variable (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι)

theorem kc_of_ks (T : Thick (smFun X q)) (h : KS q (a + 1) {capO U.U i} T) : KC q U a T := by
  obtain ⟨h1, V, rfl, h2⟩ := h
  exact ⟨h1, U.U (i 0), ⟨_, rfl⟩, inU_mono q (capO_le U.U i 0) T h2⟩

theorem ks_of_cap (T : (KC q U a).FullSubcategory) (h : capT (Vk q U a) i T) : KS q (a + 1) {capO U.U i} T.obj :=
  ⟨T.property.1, _, rfl, (inU_capO q U.U i T.obj).2 h⟩

def capG : (KS q (a + 1) {capO U.U i}).FullSubcategory ⥤ (capT (Vk q U a) i).FullSubcategory :=
  (capT (Vk q U a) i).lift ((KC q U a).lift (KS q (a + 1) {capO U.U i}).ι fun T => kc_of_ks q U a n i _ T.property)
    fun T => by
      obtain ⟨h1, V, rfl, h2⟩ := T.property
      exact (inU_capO q U.U i T.obj).1 h2

def capH : (capT (Vk q U a) i).FullSubcategory ⥤ (KS q (a + 1) {capO U.U i}).FullSubcategory :=
  (KS q (a + 1) {capO U.U i}).lift ((capT (Vk q U a) i).ι ⋙ (KC q U a).ι) fun T => ks_of_cap q U a n i T.obj T.property

def capE : (KS q (a + 1) {capO U.U i}).FullSubcategory ≌ (capT (Vk q U a) i).FullSubcategory :=
  CategoryTheory.Equivalence.mk (capG q U a n i) (capH q U a n i)
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl))

def capM : CH.Mor ((capT (Vk q U a) i).ι ⋙ Fk q U a) ((KS q (a + 1) {capO U.U i}).ι ⋙ HT.grT (smFun X q) a) (RingHom.id K) where
  G := capG q U a n i
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem capM_bij (r : ℕ) : Function.Bijective ((capM q U a n i).pull r) := by
  haveI : (capM q U a n i).G.IsLeftAdjoint := (capE q U a n i).isLeftAdjoint_functor
  exact CrystallineSemistableComparison.P.adj_mor (capM q U a n i) (fun _ => Function.bijective_id) r

end Cap
end GlobalTheory.CompanionTheory.OmGlobTerm

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Nat
variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

theorem ks_pull (u : X ⟶ Y) (hu : u ≫ p = q) {V : X.Opens} {W : Y.Opens} (h : V ≤ u ⁻¹ᵁ W) (s a : ℕ) (T : Thick (smFun X q))
    (hT : KS q s {V} T) : KS p s {W} ((pullM u hu a).G.obj T) := by
  obtain ⟨h1, V', rfl, h2⟩ := hT
  exact ⟨h1, W, rfl, fun x hx => h (h2 hx)⟩

theorem capM_res (U : Cov q) (a m n : ℕ) (i : Fin (n + 1) → U.ι) (θ : Fin (m + 1) → Fin (n + 1))
    (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a) :
    (capM q U a n i).pull a ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
      (resU (HT.grT (smFun X q) a) (U := KS q (a + 1) {capO U.U (i ∘ θ)}) (V := KS q (a + 1) {capO U.U i}) (by
        rintro T ⟨h1, V', rfl, h2⟩
        exact ⟨h1, _, rfl, inU_mono q (capO_comp U.U i θ) T h2⟩)).pull a ((capM q U a m (i ∘ θ)).pull a x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem capM_pull (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
    (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T)) (n : ℕ) (i : Fin (n + 1) → U.ι)
    (hG' : ∀ T, capT (Vk q U a) i T →
      capT (Vk p W a) (τ ∘ i) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
    (h : ∀ T, KS q (a + 1) {capO U.U i} T → KS p (a + 1) {capO W.U (τ ∘ i)} ((pullM u hu a).G.obj T))
    (x : HU (Fk p W a) (capT (Vk p W a) (τ ∘ i)) a) :
    (capM q U a n i).pull a ((morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
        (U' := capT (Vk q U a) i) hG').pull a x) =
      (morU (pullM u hu a) (U := KS p (a + 1) {capO W.U (τ ∘ i)}) (U' := KS q (a + 1) {capO U.U i}) h).pull a
        ((capM p W a n (τ ∘ i)).pull a x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Nat
end GlobalTheory.CompanionTheory.OmGlobTerm

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Id
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def idT (hu : 𝟙 X ≫ q = q) (T : Thick (smFun X q)) : T ⟶ (smMor (𝟙 X) hu).functor.obj T :=
  mkH (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := (smMor (𝟙 X) hu).functor.obj T) (RingHom.id _) (fun _ => rfl) ⟨Ideal.map_le_iff_le_comap.2 (fun x hx => hx), fun x hx => rfl⟩ (fun x hx => hx) (by
    have e : CommRingCat.ofHom (Ideal.quotientMap ((smMor (𝟙 X) hu).functor.obj T).J (RingHom.id T.B) (fun x hx => hx)) = 𝟙 (CommRingCat.of (T.B ⧸ T.J)) := by
      refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl))
    refine Eq.trans (congrArg (fun f => (ConcreteCategory.hom ((nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map f)) T.y) e) ?_
    refine Eq.trans (congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _)) ((nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map_id _)) T.y) ?_
    exact Subtype.ext (Prod.ext rfl (Category.comp_id _).symm))

theorem morU_id (hu : 𝟙 X ≫ q = q) (a : ℕ) (Q Q' : ObjectProperty (Thick (smFun X q)))
    (h : ∀ T, Q' T → Q ((pullM (𝟙 X) hu a).G.obj T)) (hle : Q' ≤ Q) (n : ℕ) (x) :
    (morU (pullM (𝟙 X) hu a) (U := Q) (U' := Q') h).pull n x = (resU (HT.grT (smFun X q) a) hle).pull n x := by
  symm
  refine CrystallineSemistableComparison.P.prism (resU (HT.grT (smFun X q) a) hle) (morU (pullM (𝟙 X) hu a) (U := Q) (U' := Q') h)
    { app := fun T => ObjectProperty.homMk (idT hu T.obj)
      naturality := fun T T' f => ?_ } ?_ n x
  · refine ObjectProperty.hom_ext _ ?_
    exact hom_ext (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) rfl
  · intro T x
    obtain ⟨y, hy, rfl⟩ := HT.sq_surj _ _ x
    rfl

end Id
end GlobalTheory.CompanionTheory.OmGlobTerm
