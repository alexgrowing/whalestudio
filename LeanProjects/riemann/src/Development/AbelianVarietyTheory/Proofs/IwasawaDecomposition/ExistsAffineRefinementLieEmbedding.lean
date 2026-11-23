import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImageStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem LeftInv.change {S : Type} [CommRing S] {M n m : ℕ} {D C : Fin m → Fin M → S} (h : LeftInv D C)
    {U : Fin n → Fin M → S} (a : Fin m → Fin n → S) (b : Fin n → Fin m → S) (hU : ∀ z, U z = ∑ j, b z j • C j)
    (hab : ∀ z z', ∑ j, a j z * b z' j = if z = z' then 1 else 0) :
    LeftInv (fun z => ∑ j, a j z • D j) U := by
  intro z z'
  have e : ∑ r, (∑ j, a j z • D j) r * U z' r = ∑ j, ∑ j', a j z * b z' j' * ∑ r, D j r * C j' r := by
    simp only [hU z', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun r _ => by ring
  have h' : ∀ j j', ∑ r, D j r * C j' r = if j = j' then 1 else 0 := fun j j' => by convert h j j'
  rw [e]
  simp only [h', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  convert hab z z'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {L : FinLB X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd t L M}

theorem IsLieEmb.exists_leftInv (h : IsLieEmb t L aff crd) (i : Fin L.n) {R : Type} [CommRing R]
    (φ : Γ(X, L.U i) →+* R) {x : Sp R ⟶ X} (hx : spMap φ ≫ (aff i).fromSpec = x) {n : ℕ} {u : Fin n → Tn t R}
    (hu : ∀ j, IsTanAtG t x (u j)) (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → R, IsCombAtG t x u a w) :
    ∃ D : Fin n → Fin (M + 1) → R, LeftInv D fun z => crd i R φ (u z) := by
  obtain ⟨m, v, D, ⟨hv, hs⟩, hD⟩ := h.split i
  have hv' : ∀ j, IsTanAtG t x (spMap (dualMap φ) ≫ v j) := fun j => hx ▸ GlobalTheory.FactorDepth.isTanAtG_map t φ (hv j)
  have hC : ∀ j, crd i R φ (spMap (dualMap φ) ≫ v j) = φ ∘ crd i _ (RingHom.id _) (v j) := fun j =>
    h.nat i _ R (RingHom.id _) φ (v j) (by simpa [spMap] using hv j)
  choose a ha using fun j => (hb _ (hv' j)).exists
  choose b hb' using fun z => (hs R φ (u z) (hx ▸ hu z)).exists
  have ha' := fun j => (h.comb_iff i φ hx hu (hv' j) _).1 (ha j)
  have hb'' := fun z => (h.comb_iff i φ hx hv' (hu z) _).1 (hx ▸ hb' z)
  refine ⟨_, (hD.map φ).change a b (fun z => by simpa only [hC] using hb'' z) fun z z' => ?_⟩
  have e := (hb _ (hu z')).unique ((h.comb_iff i φ hx hu (hu z') fun z => ∑ j, a j z * b z' j).2 ?_)
    ((h.comb_iff i φ hx hu (hu z') fun z => if z = z' then 1 else 0).2 (by simp))
  · exact congrFun e z
  · rw [hb'' z']
    simp only [ha', Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem IsLieEmb.exists_leftInv_let (h : IsLieEmb t L aff crd) (i : Fin L.n) {R : Type} [CommRing R]
    (φ : Γ(X, L.U i) →+* R) {x : Sp R ⟶ X} (hx : spMap φ ≫ (aff i).fromSpec = x) {Dw : Datum H} {e : Vecs Dw t R}
    {n : ℕ} (en : Fin n ≃ Let Dw.mult) (hu : ∀ τ j, IsTanAtG t x (e τ j))
    (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → R, IsCombAtG t x (fun i => e (en i).1 (en i).2) a w) :
    ∃ D : Let Dw.mult → Fin (M + 1) → R, LeftInv D fun z => crd i R φ (e z.1 z.2) := by
  obtain ⟨D, hD⟩ := h.exists_leftInv i φ hx (fun i => hu (en i).1 (en i).2) hb
  refine ⟨fun z => D (en.symm z), fun z z' => ?_⟩
  obtain ⟨y, rfl⟩ := en.surjective z
  obtain ⟨y', rfl⟩ := en.surjective z'
  have := hD y y'
  simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  convert this

theorem tan_of_frame {Dw : Datum H} {l : Level H} {c : Coeff l} {R : Type} [CommRing R] {α : c.F →+* R} {x : Sp R ⟶ X}
    {e : Vecs Dw t R} (he : GlobalTheory.LocM.IsFrame t ((RingHom.id R).comp α) (spMap (RingHom.id R) ≫ x) (e.bc (RingHom.id R))) (τ) (j) :
    IsTanAtG t x (e τ j) := by
  have h1 : dualMap (RingHom.id R) = RingHom.id _ := RingHom.ext fun y => TrivSqZeroExt.inl_fst_add_inr_snd_eq y
  simpa [Vecs.bc, h1, spMap] using (he.1 τ j).1

theorem IsLieEmb.inBlock (h : IsLieEmb t L aff crd) {Dw : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k]
    {R R' : Type} [CommRing R] [CommRing R'] {i i' : Fin L.n} (ρ : Γ(X, L.U i) →+* R) (ρ' : Γ(X, L.U i') →+* R')
    {x : Sp R ⟶ X} {x' : Sp R' ⟶ X} (hx : spMap ρ ≫ (aff i).fromSpec = x) (hx' : spMap ρ' ≫ (aff i').fromSpec = x')
    {e : Vecs Dw t R} {e' : Vecs Dw t R'} (ht : ∀ τ j, IsTanAtG t x (e τ j)) (ht' : ∀ τ j, IsTanAtG t x' (e' τ j))
    (φ : R →+* k) (φ' : R' →+* k) (hφ : spMap φ ≫ x = spMap φ' ≫ x') {α : c.F →+* k}
    (he : GlobalTheory.LocM.IsFrame t α (spMap φ ≫ x) (e.bc φ)) (he' : GlobalTheory.LocM.IsFrame t α (spMap φ' ≫ x') (e'.bc φ')) :
    InBlock (m := Dw.mult) (fun z => φ ∘ crd i R ρ (e z.1 z.2)) (fun z => φ' ∘ crd i' R' ρ' (e' z.1 z.2)) := by
  rintro ⟨τ, j⟩
  subst hx hx'
  have e1 : spMap (φ.comp ρ) ≫ (aff i).fromSpec = spMap φ ≫ spMap ρ ≫ (aff i).fromSpec := by
    rw [spMap_comp, Category.assoc]
  have e2 : spMap (φ'.comp ρ') ≫ (aff i').fromSpec = spMap φ' ≫ spMap ρ' ≫ (aff i').fromSpec := by
    rw [spMap_comp, Category.assoc]
  have hw := (he'.1 τ j).1
  obtain ⟨a, ha, -⟩ := he.2 τ (e'.bc φ' τ j) (hφ ▸ hw) (he'.1 τ j).2
  have h1 := (h.comb_iff i (φ.comp ρ) e1 (fun j => (he.1 τ j).1) (hφ ▸ hw) a).1 ha
  have h2 := h.trans i' i k (φ'.comp ρ') (φ.comp ρ) (e'.bc φ' τ j) (by rw [e1, e2, hφ]) (e2 ▸ hw)
  have h3 := h.nat i' R' k ρ' φ' (e' τ j) (ht' τ j)
  have h4 := fun j => h.nat i R k ρ φ (e τ j) (ht τ j)
  show φ' ∘ crd i' R' ρ' (e' τ j) ∈ _
  rw [← h3]
  refine h2 ▸ Submodule.smul_mem _ _ ?_
  rw [h1]
  exact Submodule.sum_mem _ fun j' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j', (h4 j').symm⟩)

theorem noetherianSpace_model {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}
    {W : ValuationSubring ℂ} (Y : Model Xo c (c.V W).subtype) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    TopologicalSpace.NoetherianSpace Y.X := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsDiscreteValuationRing (c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  have := projProper _ _ _ Y.proj
  have := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : AlgebraicGeometry.IsNoetherian Y.X := {}
  infer_instance

theorem exists_isFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (L : FinLB Y.X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd Y.t L M), IsLieEmb Y.t L aff crd → ∃ (n : ℕ) (V : Fin n → Y.X.affineOpens) (ι : Fin n → Fin L.n) (ρ : ∀ b, Γ(Y.X, L.U (ι b)) →+* Γ(Y.X, (V b).1)) (α : ∀ b, c.F →+* Γ(Y.X, (V b).1)) (e : ∀ b, Vecs Dw Y.t Γ(Y.X, (V b).1)) (D : ∀ b, Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V b).1)), IsFrameCover Y L aff crd V ι ρ α e D := by
  intro E _ _ _ H Dw l Xo c p W Y hp hW L aff M crd h
  have := noetherianSpace_model Y hp hW
  obtain ⟨-, hloc⟩ := GlobalTheory.T.exists_affine_eigenframe_near_image E H Dw l Xo c p W Y hp hW
  have hcov : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 ((L.isLB.cover).symm ▸ (TopologicalSpace.Opens.mem_top x))
  choose ι hι using hcov
  choose V α e n en hxV hVU hVj hs hfr hbas using fun x : Set.range Y.j => hloc x.1 (L.U (ι x.1)) (hι x.1) x.2
  obtain ⟨T, hT⟩ := (TopologicalSpace.NoetherianSpace.isCompact (Set.range Y.j)).elim_finite_subcover
    (fun x => ((V x).1 : Set Y.X)) (fun x => (V x).1.2) fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩
  have hρ : ∀ x, ∃ ρ : Γ(Y.X, L.U (ι x.1)) →+* Γ(Y.X, (V x).1),
      spMap ρ ≫ (aff (ι x.1)).fromSpec = (V x).2.fromSpec := fun x =>
    ⟨(Y.X.presheaf.map (homOfLE (hVU x)).op).hom, (aff (ι x.1)).map_fromSpec (V x).2 _⟩
  choose ρ hρ using hρ
  have htan : ∀ x τ j, IsTanAtG Y.t (V x).2.fromSpec (e x τ j) := fun x => tan_of_frame (hfr x _ (RingHom.id _))
  have hD : ∀ x, ∃ D : Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V x).1),
      LeftInv D fun z => crd (ι x.1) _ (ρ x) (e x z.1 z.2) := fun x =>
    h.exists_leftInv_let (ι x.1) (ρ x) (hρ x) (en x) (htan x) (hbas x)
  choose D hD using hD
  obtain ⟨f, hf⟩ : ∃ f : Fin T.card → Set.range Y.j, ∀ x ∈ T, ∃ b, f b = x :=
    ⟨fun b => (T.equivFin.symm b).1, fun x hx => ⟨T.equivFin ⟨x, hx⟩, by simp⟩⟩
  refine ⟨T.card, fun b => V (f b), fun b => ι (f b).1, fun b => ρ (f b), fun b => α (f b), fun b => e (f b),
    fun b => D (f b), ?_, fun b => hρ _, fun b => hfr _, fun b => hs _, fun b => hD _,
    fun k _ b b' φ φ' hφ => ?_⟩
  · refine (Set.iUnion_subset fun b => hVj _).antisymm fun y hy => ?_
    obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨b, rfl⟩ := hf x hx
    exact Set.mem_iUnion.2 ⟨b, hy'⟩
  · have hα : φ.comp (α (f b)) = φ'.comp (α (f b')) := by
      have e1 : spMap (φ.comp ((α (f b)).comp (c.V W).subtype)) =
          spMap (φ'.comp ((α (f b')).comp (c.V W).subtype)) := by
        rw [spMap_comp _ φ, spMap_comp _ φ', ← hs, ← hs, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ Y.s) hφ
      have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
      exact IsLocalization.ringHom_ext (nonZeroDivisors (c.V W)) e2
    exact h.inBlock (ρ _) (ρ _) (hρ _) (hρ _) (htan _) (htan _) φ φ' hφ (hfr _ k φ) (hα ▸ hfr _ k φ')

end GlobalTheory.FlagEmb
