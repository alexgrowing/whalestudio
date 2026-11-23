import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodgeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgLie

section Modules

theorem mem_of_mem_iSup {Ω E I : Type} [Field Ω] [AddCommGroup E] [Module Ω E] (A : Subring Ω)
    (W : I → Submodule Ω E) (hW : iSupIndep W) (N : I → Submodule A E) (hN : ∀ s, ∀ x ∈ N s, x ∈ W s)
    {e : E} (s₀ : I) (he : e ∈ ⨆ s, N s) (hs : e ∈ W s₀) : e ∈ N s₀ := by
  classical
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp N e).1 he
  have hsum : (f.sum fun _ x => x) - f s₀ = ∑ i ∈ f.support.erase s₀, f i := by
    by_cases h0 : s₀ ∈ f.support
    · rw [Finsupp.sum, ← Finset.add_sum_erase _ _ h0]
      abel
    · rw [Finsupp.sum, Finset.erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0, sub_zero]
  have h1 : (f.sum fun _ x => x) - f s₀ ∈ W s₀ := sub_mem hs (hN _ _ (hf s₀))
  have h2 : (f.sum fun _ x => x) - f s₀ ∈ ⨆ (k) (_ : k ≠ s₀), W k := by
    rw [hsum]
    refine Submodule.sum_mem _ fun k hk => ?_
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hk) (hN _ _ (hf k)))
  have h3 := (Submodule.disjoint_def.1 (hW s₀)) _ h1 h2
  rw [sub_eq_zero.1 h3]
  exact hf s₀

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (e : E) : e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

end Modules

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

theorem not_inFibre_push {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀}
    {i : Ω₀ →+* Ω} (hξ : IsCptGen ξ) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i) (q : Cpt ξ) {r : ℕ}
    (hq : ¬ InFibre ξ r q) : ¬ InFibre ξ₀ r (pushCpt hd q) := by
  intro hf
  apply hf
  obtain ⟨h0, -, s, hs⟩ : unitAt ξ q (r : Ω) := not_not.1 hq
  have hmul : (r : X.presheaf.stalk q.1) * s = 1 := hξ.inj q (by
    rw [map_mul, map_one, map_natCast, hs]
    exact mul_inv_cancel₀ h0)
  have hu : IsUnit (r : X.presheaf.stalk q.1) := IsUnit.of_mul_eq_one _ hmul
  have hu₀ : IsUnit (r : X₀.presheaf.stalk (h q.1)) :=
    isUnit_of_map_unit (h.stalkMap q.1).hom _ (by rwa [map_natCast])
  have h0' : (r : Ω₀) ≠ 0 := fun e => h0 (by rw [← map_natCast i, e, map_zero])
  refine ⟨h0', ⟨_, map_natCast (genMap ξ₀ (pushCpt hd q)) r⟩, ?_⟩
  obtain ⟨u, hu'⟩ := hu₀
  refine ⟨(u⁻¹ : (X₀.presheaf.stalk (h q.1))ˣ).val, ?_⟩
  have e1 : genMap ξ₀ (pushCpt hd q) u.val = (r : Ω₀) := (congrArg _ hu').trans (map_natCast _ r)
  exact (map_units_inv (genMap ξ₀ (pushCpt hd q)) u).trans (congrArg Inv.inv e1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_inj_of_pull {S' S : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) {ξ : Spec (CommRingCat.of Ω) ⟶ S'} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G' ξ V) {e e' : V}
    (h : (M.pt e).left ≫ φ = (M.pt e').left ≫ φ) : e = e' :=
  M.inj (Over.OverMorphism.ext (hG.1.hom_ext h ((Over.w _).trans (Over.w _).symm)))

theorem exists_value_up {t : SAB H X₀} {t' : SAB H X} {f : X ⟶ X₀} (m : SABMap t' t f)
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {i : Ω₀ →+* Ω}
    (hall : ∀ q : X, genPt ξ ⤳ q) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) {V V' : Type} [AddCommGroup V] [Module Ω₀ V]
    [AddCommGroup V'] [Module Ω V'] {M : LieModel t.G ξ₀ V} {M' : LieModel t'.G ξ V'} {j : V →+ V'}
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) {e : V} {v₀ : epsAt (z ≫ f) ⟶ t.G} (hv : M.ValAt (z ≫ f) e v₀) :
    ∃ v : epsAt z ⟶ t'.G, M'.ValAt z (j e) v ∧ v₀.left = v.left ≫ m.φ := by
  obtain ⟨h₀, w, hw, hwz⟩ := hv
  have hp : genPt ξ₀ ⤳ f (centre z) := h₀
  have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap (centre z)).hom) ≫ X₀.fromSpecStalk (f (centre z)) =
      X.fromSpecStalk (centre z) ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hρ' : (genMap ξ ⟨centre z, hall _⟩).comp (f.stalkMap (centre z)).hom = i.comp (genMap ξ₀ ⟨f (centre z), hp⟩) :=
    RingHom.ext (RegAtDom.genMap_stalkMap hd _ (hall _) hp)
  have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨centre z, hall _⟩
  obtain ⟨u, hu, huφ⟩ := LiePull.ext_up (A := X₀.presheaf.stalk (f (centre z))) (A' := X.presheaf.stalk (centre z))
    (g := genMap ξ₀ ⟨f (centre z), hp⟩) (g' := genMap ξ ⟨centre z, hall _⟩) (ρ := (f.stalkMap (centre z)).hom)
    (x := X₀.fromSpecStalk (f (centre z))) (x' := X.fromSpecStalk (centre z)) (M := M) (M' := M') (j := j) m.cart hj hρ
    hρ' hx' hw
  have hc : Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ X.fromSpecStalk (centre z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  refine ⟨LieCarrier.epsHom _ _ z hc ≫ u, ⟨hall _, u, hu, rfl⟩, ?_⟩
  have e1 : (LieCarrier.epsHom _ _ z hc ≫ u).left =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ u.left := rfl
  have e2 : (Scheme.stalkClosedPointTo (z ≫ f)).hom =
      (Scheme.stalkClosedPointTo z).hom.comp (f.stalkMap (centre z)).hom := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  have e4 : spMap (dualMap (Scheme.stalkClosedPointTo (z ≫ f)).hom) =
      spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ spMap (dualMap (f.stalkMap (centre z)).hom) := by
    rw [e2]
    exact (congrArg spMap (LiePull.dualMap_comp (f.stalkMap (centre z)).hom (Scheme.stalkClosedPointTo z).hom).symm).trans
      (spMap_comp' _ _)
  have e3 : (LieCarrier.epsHom _ _ z hc ≫ u).left ≫ m.φ = spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫
      spMap (dualMap (f.stalkMap (centre z)).hom) ≫ w.left :=
    (congrArg (· ≫ m.φ) e1).trans ((Category.assoc _ _ _).trans
      (congrArg (spMap (dualMap (Scheme.stalkClosedPointTo z).hom) ≫ ·) huφ))
  exact hwz.trans (((congrArg (· ≫ w.left) e4).trans (Category.assoc _ _ _)).trans e3.symm)

end Points

section Main

theorem lie_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl hβ hcov hfl
  obtain ⟨-, hf, hcst⟩ := hcov
  obtain ⟨m₀, hφ⟩ := exists_sabMap 𝔐₀ 𝔐 h hf
  obtain ⟨j, hpt, hsemi, hind, -, hpull⟩ := GlobalTheory.T.lie_model_dominant_hodge E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ Ω₀ Ω 𝔐₀.ξ 𝔐.ξ i 𝔐₀.Li 𝔐.Li 𝔐₀.M 𝔐.M
    𝔐₀.tie.gen 𝔐.tie.gen hd
  have hact : ∀ a e, 𝔐.ρ a (j e) = j (𝔐₀.ρ a e) := fun a e => pt_inj_of_pull m₀.cart 𝔐.M (by
    have e1 := congrArg CommaMorphism.left (𝔐.act a (j e))
    have e2 := congrArg CommaMorphism.left (𝔐₀.act a e)
    have e3 := m₀.act a
    rw [hpt]
    refine (congrArg (· ≫ m₀.φ) e1).trans ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine (congrArg (_ ≫ ·) e3).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (𝔐₀.t.act.act a).left) (hpt e)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (spMap (dualMap i) ≫ ·) e2.symm)
  have hemb : ∀ s, 𝔐.emb s = i.comp (𝔐₀.emb s) := fun s => by
    simp only [HodgeCpt.emb, hcst, RingHom.comp_assoc]
  have heig : ∀ s e, e ∈ 𝔐₀.Vgen s → j e ∈ 𝔐.Vgen s := fun s e he => by
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [hact, (mem_eigSp_iff _ _ _).1 he a, hsemi, hemb]
    rfl
  refine ⟨j, hsemi, hind, fun s a => ?_, fun q hq s => ?_, fun z r b Γ hΓ => ?_⟩
  · refine pt_inj_of_pull 𝔐.m.cart 𝔐.M ?_
    have e1 : (𝔐.M.pt (j (Fl₀.b s a))).left ≫ 𝔐.m.φ =
        spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ := by
      rw [hφ, ← Category.assoc, hpt, Category.assoc]
    exact e1.trans (hfl s a).symm
  · have hq₀ : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐₀.ξ r (pushCpt hd q) :=
      fun r hr => not_inFibre_push 𝔐.tie.gen hd q (hq r hr)
    obtain ⟨hV, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y 𝔐 hβ q hq
    obtain ⟨hV₀, -, hlat₀⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ hβ (pushCpt hd q) hq₀
    obtain ⟨-, -, -, -, -, -, hindep, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
    rw [hV s, hV₀ s]
    let N : (CMType H ⊕ CMType H) → Submodule (regAt 𝔐.ξ q) 𝔐.Li := fun s' =>
      Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.dR s' (pushCpt hd q) : Set 𝔐₀.Li))
    have hle : ∀ s', N s' ≤ 𝔐.dR s' q := fun s' => by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨e, he, rfl⟩
      refine ⟨?_, heig s' e he.2⟩
      rw [hpull]
      exact Submodule.subset_span ⟨hd.specializes q, e, he.1, rfl⟩
    have htop : 𝔐.M.lat q ≤ ⨆ s', N s' := by
      rw [hpull]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ ⨆ s', 𝔐₀.dR s' (pushCpt hd q) := hlat₀ ▸ he
      refine Submodule.iSup_induction _ (motive := fun x => j x ∈ ⨆ s', N s') he' (fun s' x hx => ?_) ?_ ?_
      · exact Submodule.mem_iSup_of_mem s' (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro x x' hx hx'
        rw [map_add]
        exact Submodule.add_mem _ hx hx'
    refine le_antisymm (fun e he => ?_) (hle s)
    exact mem_of_mem_iSup _ 𝔐.Vgen hindep N (fun s' x hx => (hle s' hx).2) s (htop he.1) he.2
  · obtain ⟨v₀, hv₀, hIP⟩ := hΓ
    choose v hv hvφ using fun k => exists_value_up m₀ 𝔐.all hd hpt z (hv₀ k)
    exact ⟨v, hv, fun p q => (GlobalTheory.T.hodge_inner_product_map_iff E H 𝔐₀.X 𝔐₀.t 𝔐.X 𝔐.t h m₀ z (v p) (v q) (v₀ p) (v₀ q) (Γ p q) (hvφ p) (hvφ q)).2 (hIP p q)⟩

end Main

end GlobalTheory.CompanionTheory.Ar.ChgLie
