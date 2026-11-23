import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.Xgn.GermHodgeLattice

section Alg

variable {R Ω : Type} [CommRing R] [Field Ω] {d : ℕ}

theorem mem_stdLat (A : Subring Ω) (T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω))
    (y : (Fin d → Ω) × (Fin d → Ω)) :
    y ∈ stdLat A T ↔ ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ y = T y₀ := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y h => exact h
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact ⟨a + b, fun i => ⟨A.add_mem (ha i).1 (hb i).1, A.add_mem (ha i).2 (hb i).2⟩, (map_add T a b).symm⟩
  | smul c a _ ha =>
    obtain ⟨a, ha, rfl⟩ := ha
    exact ⟨(c : Ω) • a, fun i => ⟨A.mul_mem c.2 (ha i).1, A.mul_mem c.2 (ha i).2⟩, (map_smul T (c : Ω) a).symm⟩

theorem sum_cols (P : Matrix (Fin d) (Fin d) Ω) (u : Fin d → Ω) :
    ∑ l, u l • P.mulVec (Pi.single l 1) = P.mulVec u := by
  simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_sum]
  congr 1
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_span_cols (A : Subring Ω) (P : Matrix (Fin d) (Fin d) Ω) (e : Fin d → Ω) :
    e ∈ Submodule.span A (Set.range fun l => P.mulVec (Pi.single l 1)) ↔
      ∃ u : Fin d → Ω, (∀ i, u i ∈ A) ∧ e = P.mulVec u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, sum_cols P fun i => c i⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => ⟨u i, hu i⟩, sum_cols P u⟩

theorem decomp (y : (Fin d → R) × (Fin d → R)) :
    y = ∑ i, y.1 i • ((Pi.single i 1, 0) : (Fin d → R) × (Fin d → R)) +
      ∑ i, y.2 i • ((0, Pi.single i 1) : (Fin d → R) × (Fin d → R)) := by
  ext i <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem single_mem (A : Subring Ω) (i j : Fin d) : (Pi.single i 1 : Fin d → Ω) j ∈ A := by
  rw [Pi.single_apply]
  split_ifs
  exacts [A.one_mem, A.zero_mem]

theorem span_stdLat (A : Subring Ω) (T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω))
    (hT : Function.Surjective T) : Submodule.span Ω (stdLat A T : Set ((Fin d → Ω) × (Fin d → Ω))) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨y, rfl⟩ := hT y
  rw [decomp y, map_add, map_sum, map_sum]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_) <;>
    rw [map_smul] <;> refine Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ?_))
  · exact ⟨_, fun j => ⟨single_mem A i j, A.zero_mem⟩, rfl⟩
  · exact ⟨_, fun j => ⟨A.zero_mem, single_mem A i j⟩, rfl⟩

def mp (f : R →+* Ω) (y : (Fin d → R) × (Fin d → R)) : (Fin d → Ω) × (Fin d → Ω) :=
  (fun i => f (y.1 i), fun i => f (y.2 i))

theorem mp_sum (f : R →+* Ω) {J : Type} [Fintype J] (c : J → R) (w : J → (Fin d → R) × (Fin d → R)) :
    mp f (∑ i, c i • w i) = ∑ i, f (c i) • mp f (w i) := by
  ext j <;> simp [mp, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

theorem exists_finite (f : R →+* Ω) {J : Type} [Fintype J] (w : J → (Fin d → R) × (Fin d → R))
    (hw : Submodule.span R (Set.range w) = ⊤) :
    ∃ s : Set R, s.Finite ∧ ∀ A : Subring Ω, (∀ r ∈ s, f r ∈ A) →
      ∀ T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω),
        stdLat A T = Submodule.span A (Set.range fun i => T (mp f (w i))) := by
  choose c hc using fun y => (Submodule.mem_span_range_iff_exists_fun R).1 (hw.ge (Submodule.mem_top (x := y)))
  refine ⟨Set.range (fun k : Fin d × J => c (Pi.single k.1 1, 0) k.2) ∪
    Set.range (fun k : Fin d × J => c (0, Pi.single k.1 1) k.2) ∪
    Set.range (fun k : Fin d × J => (w k.2).1 k.1) ∪ Set.range (fun k : Fin d × J => (w k.2).2 k.1),
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _),
    fun A hA T => le_antisymm ?_ ?_⟩
  · have key : ∀ y, (∀ k, f (c y k) ∈ A) → T (mp f y) ∈ Submodule.span A (Set.range fun i => T (mp f (w i))) := by
      intro y hy
      rw [← hc y, mp_sum, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem _ (⟨_, hy k⟩ : A) (Submodule.subset_span ⟨k, rfl⟩)
    rw [stdLat, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [decomp y, map_add, map_sum, map_sum]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ => ?_) <;>
      rw [map_smul]
    · refine Submodule.smul_mem _ (⟨_, (hy i).1⟩ : A) ?_
      convert key (Pi.single i 1, 0) fun k => hA _ (Or.inl (Or.inl (Or.inl ⟨(i, k), rfl⟩))) using 2
      ext j <;> simp [mp, Pi.single_apply, apply_ite f]
    · refine Submodule.smul_mem _ (⟨_, (hy i).2⟩ : A) ?_
      convert key (0, Pi.single i 1) fun k => hA _ (Or.inl (Or.inl (Or.inr ⟨(i, k), rfl⟩))) using 2
      ext j <;> simp [mp, Pi.single_apply, apply_ite f]
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨_, fun i => ⟨hA _ (Or.inl (Or.inr ⟨(i, k), rfl⟩)), hA _ (Or.inr ⟨(i, k), rfl⟩)⟩, rfl⟩

theorem card_eq [Nontrivial R] {J : Type} [Fintype J] (w : J → (Fin d → R) × (Fin d → R))
    (h : LinearIndependent R w) (hw : Submodule.span R (Set.range w) = ⊤) : Fintype.card J = d + d := by
  rw [← Module.finrank_eq_card_basis (Module.Basis.mk h hw.ge)]
  simp

theorem rhoH_mp {O : Type} [CommRing O] [StarRing O] (f : R →+* Ω) {B : Germ.FB R d O} {B₂ : Germ.FB Ω d O}
    (h : IsMapOf f B B₂) (a : O) (y : (Fin d → R) × (Fin d → R)) : rhoH B₂ a (mp f y) = mp f (rhoH B a y) := by
  have h1 := (GlobalTheory.T.formal_data_base_change R Ω f d O B B₂ h).1
  have hv : ∀ (N : Matrix (Fin d) (Fin d) R) (v : Fin d → R) (i : Fin d),
      (N.map f).mulVec (fun j => f (v j)) i = f (N.mulVec v i) := fun N v i => (RingHom.map_mulVec _ _ _ _).symm
  rw [rhoH_apply, rhoH_apply, (h1 a).1, (h1 a).2, (h1 (star a)).1, ← Matrix.transpose_map, ← Matrix.transpose_map]
  ext i
  · exact hv _ _ i
  · simp only [mp, Pi.sub_apply, map_sub, hv]

def dd (Ω : Type) [Field Ω] (d : ℕ) : ((Fin d → Ω) × (Fin d → Ω)) ≃ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
  (LinearEquiv.refl Ω _).prodCongr (dotProductEquiv Ω (Fin d))

theorem dd_apply (y : (Fin d → Ω) × (Fin d → Ω)) : dd Ω d y = (y.1, dotProductBilin Ω Ω y.2) := by
  refine Prod.ext rfl (LinearMap.ext fun v => ?_)
  simp [dd]

theorem fst_stdLat (A : Subring Ω) (φ ψ : Germ.Pt Ω 1 d) (lam : Germ.PS Ω 2 d) (e : Fin d → Ω) :
    (∃ y ∈ stdLat A (transH φ ψ lam), y.1 = e) ↔
      e ∈ Submodule.span A (Set.range fun l => (lin φ 1).mulVec (Pi.single l 1)) := by
  rw [mem_span_cols]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (mem_stdLat _ _ _).1 hy
    exact ⟨z.1, fun i => (hz i).1, by rw [transH_apply]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, (mem_stdLat _ _ _).2 ⟨(u, 0), fun i => ⟨hu i, A.zero_mem⟩, rfl⟩, by rw [transH_apply]⟩

theorem inr_stdLat (A : Subring Ω) (φ ψ : Germ.Pt Ω 1 d) (lam : Germ.PS Ω 2 d) (h1 : lin φ 1 * lin ψ 1 = 1)
    (h2 : lin ψ 1 * lin φ 1 = 1) (w : Fin d → Ω) :
    (0, w) ∈ stdLat A (transH φ ψ lam) ↔
      ∀ e ∈ Submodule.span A (Set.range fun l => (lin φ 1).mulVec (Pi.single l 1)), w ⬝ᵥ e ∈ A := by
  rw [mem_stdLat]
  constructor
  · rintro ⟨y, hy, e⟩ v hv
    obtain ⟨u, hu, rfl⟩ := (mem_span_cols _ _ _).1 hv
    rw [transH_apply] at e
    obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e
    have h0 : y.1 = 0 := by
      have := congrArg (lin ψ 1).mulVec e1
      simpa [Matrix.mulVec_mulVec, h2] using this.symm
    simp only [h0, Matrix.mulVec_zero, add_zero] at e2
    rw [e2, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    exact A.sum_mem fun i _ => A.mul_mem (hy i).2 (hu i)
  · intro h
    refine ⟨(0, (lin φ 1).transpose.mulVec w), fun i => ⟨A.zero_mem, ?_⟩, ?_⟩
    · convert h _ (Submodule.subset_span ⟨i, rfl⟩) using 1
      rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_single, _root_.mul_one]
    · rw [transH_apply]
      simp [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, h1]

end Alg

section Geo

open Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem comp_prod_ofFn {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G)), f ≫ (List.ofFn u).prod = (List.ofFn fun l => f ≫ u l).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.comp_one f
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul,
      comp_prod_ofFn f (fun l => u l.succ)]

variable (t : SAB H X0)

theorem pt_sum {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) :
    ∀ {m : ℕ} (c : Fin m → V), (List.ofFn fun l => M.pt (c l)).prod = M.pt (∑ l, c l)
  | 0, c => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    have h := M.add 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | m + 1, c => by
    rw [List.ofFn_succ, List.prod_cons, pt_sum M (fun l => c l.succ), Fin.sum_univ_succ, M.add]

theorem comb_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0} {x' : Sp R' ⟶ X0}
    (hx : Spec.map (CommRingCat.ofHom f) ≫ x = x') {V : Type} [AddCommGroup V] [Module R' V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x' V) {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v cf w) (b : Fin m → V)
    (hb : ∀ l, (M.pt (b l)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap f)) ≫ v l) :
    (M.pt (∑ l, f (cf l) • b l)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap f)) ≫ w := by
  obtain ⟨u, hu, hw⟩ := h
  have e : ∀ l, M.pt (f (cf l) • b l) = LieCarrier.epsHom f x x' hx ≫ u l := fun l => by
    refine Over.OverMorphism.ext ?_
    change _ = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap f)) ≫ (u l).left
    rw [M.smul, hb, hu]
    have : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (f (cf l)))) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap f)) =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap f)) ≫
          Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (cf l))) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        LieCarrier.dualMap_epsMul]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ v l) this).trans (Category.assoc _ _ _))
  rw [← pt_sum, ← hw]
  simp only [e]
  exact (congrArg CommaMorphism.left (comp_prod_ofFn (LieCarrier.epsHom f x x' hx) u)).symm

variable [StarRing (𝓞 E)] {t} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X0} {d : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}

theorem lat_eq (S : GermSys t ξ M) (p : Cpt ξ) :
    M.lat p = Submodule.span (regAt ξ p) (Set.range fun l => (lin (S.φ p) 1).mulVec (Pi.single l 1)) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro e ⟨v, hv, he⟩
    obtain ⟨a, ha, -⟩ := (S.g p).basis v.left ⟨Over.w v, hv⟩
    have h := comb_map t (genMap ξ p) (LieCarrier.genMap_fromSpecStalk p) M ha _ (S.dir p)
    rw [M.inj (Over.OverMorphism.ext (he.trans h.symm))]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ (⟨_, a l, rfl⟩ : regAt ξ p) (Submodule.subset_span ⟨l, rfl⟩)
  · rintro _ ⟨l, rfl⟩
    exact ⟨Over.homMk ((S.g p).tg l) ((S.g p).tan l).1, ((S.g p).tan l).2, S.dir p l⟩

theorem exists_open {ξ : Sp Ω ⟶ X0} (p : Cpt ξ) (s : Set (X0.presheaf.stalk p.1)) (hs : s.Finite) :
    ∃ U : X0.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ r ∈ s, genMap ξ p r ∈ regAt ξ q := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ h => h.elim⟩
  | @insert a s _ _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    obtain ⟨V, hV, h'⟩ := exists_open_mem_regAt ξ p _ ⟨a, rfl⟩
    refine ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq r hr => ?_⟩
    rcases hr with rfl | hr
    exacts [h' q hq.2, h q hq.1 r hr]

end Geo

end PositivityTheory.Xgn.GermHodgeLattice
