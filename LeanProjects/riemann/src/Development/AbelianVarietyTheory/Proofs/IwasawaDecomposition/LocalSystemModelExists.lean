import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEmbeddingProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineRefinementLieEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesAgreeOnLieEmbeddingChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendingLetterChainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoverNormalProjectiveChartsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartTransitionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartSectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartValuesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.DR

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_comp_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    {Z : Scheme.{0}} (h : Sp A ⟶ Z) : spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by
  rw [← Category.assoc, sp_comp]

theorem sp_id {A : Type} [CommRing A] {Z : Scheme.{0}} (h : Sp A ⟶ Z) : spMap (RingHom.id A) ≫ h = h :=
  (congrArg (· ≫ h) (Spec.map_id _)).trans (Category.id_comp _)

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem dual_id {A : Type} [CommRing A] : dualMap (RingHom.id A) = RingHom.id _ := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem pt_congr {R A : Type} [CommRing R] [CommRing A] {N : ℕ} {c c' : R →+* A} {v v' : Fin (N + 1) → A} {h h'}
    (e : c = c') (e' : v = v') : pt c v h = pt c' v' h' := by
  subst e e'
  rfl

theorem exists_ringEquiv {A : Type} [CommRing A] {Z : Scheme.{0}} (κ : Sp A ⟶ Z) [IsOpenImmersion κ] :
    ∃ θ : A ≃+* Γ(Z, κ.opensRange), spMap θ.toRingHom ≫ κ = (isAffineOpen_opensRange κ).fromSpec := by
  let e := IsOpenImmersion.isoOfRangeEq (isAffineOpen_opensRange κ).fromSpec κ
    (isAffineOpen_opensRange κ).range_fromSpec
  let e' : CommRingCat.of A ≅ Γ(Z, κ.opensRange) := (Scheme.Spec.preimageIso (X := .op _) (Y := .op _) e).unop
  refine ⟨e'.commRingCatIsoToRingEquiv, ?_⟩
  have : spMap e'.commRingCatIsoToRingEquiv.toRingHom = e.hom := Scheme.Spec.map_preimage e.hom
  rw [this]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem exists_factor {k : Type} [Field k] {X : Scheme.{0}} (x : Sp k ⟶ X) (U : X.affineOpens)
    (h : x (IsLocalRing.closedPoint k) ∈ U.1) : ∃ ψ : Γ(X, U.1) →+* k, spMap ψ ≫ U.2.fromSpec = x := by
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hr : Set.range x ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q (IsLocalRing.closedPoint k)]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift U.2.fromSpec x hr)).hom, ?_⟩
  exact (congrArg (· ≫ _) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac U.2.fromSpec x hr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem bc_bc {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (u : Vecs Dw t A) : (u.bc f).bc g = u.bc (g.comp f) := by
  funext τ i
  simp only [Vecs.bc]
  rw [sp_comp_assoc, dual_comp]

theorem bc_id {X : Scheme.{0}} {t : SAB H X} {A : Type} [CommRing A] (u : Vecs Dw t A) : u.bc (RingHom.id A) = u := by
  funext τ i
  simp only [Vecs.bc]
  rw [dual_id, sp_id]

theorem map_cell {T : Type} {m : T → ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (x : CellVar m → S)
    (τ : T) (i j : Fin (m τ)) : φ (cell x τ i j) = cell (φ ∘ x) τ i j := by
  unfold cell
  split_ifs <;> simp

section Cover

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {L : FinLB Y.X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd Y.t L M} {B : Type}
  {V : B → Y.X.affineOpens} {ι : B → Fin L.n} {ρ : ∀ b, Γ(Y.X, L.U (ι b)) →+* Γ(Y.X, (V b).1)}
  {α : ∀ b, c.F →+* Γ(Y.X, (V b).1)} {e : ∀ b, Vecs Dw Y.t Γ(Y.X, (V b).1)}
  {D : ∀ b, Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V b).1)}

theorem crd_bc (hE : IsLieEmb Y.t L aff crd) (hF : IsFrameCover Y L aff crd V ι ρ α e D) (b : B) {R : Type} [CommRing R]
    (φ : Γ(Y.X, (V b).1) →+* R) (z : Let Dw.mult) :
    crd (ι b) R (φ.comp (ρ b)) ((e b).bc φ z.1 z.2) = φ ∘ crd (ι b) _ (ρ b) (e b z.1 z.2) := by
  refine hE.nat _ _ _ _ _ _ ?_
  have := ((hF.frame b _ (RingHom.id _)).1 z.1 z.2).1
  rwa [bc_id, sp_id, ← hF.res b] at this

theorem exists_cellFrame (hE : IsLieEmb Y.t L aff crd) (hF : IsFrameCover Y L aff crd V ι ρ α e D) (b : B)
    (w : Pm Dw.mult) {R₀ : Type} [CommRing R₀] (φ₀ : Γ(Y.X, (V b).1) →+* R₀) (x : CellVar Dw.mult → R₀) :
    ∃ u : Vecs Dw Y.t R₀, ∀ (R : Type) [CommRing R] (φ : R₀ →+* R),
      IsFrame Y.t (φ.comp (φ₀.comp (α b))) (spMap φ ≫ spMap φ₀ ≫ (V b).2.fromSpec) (u.bc φ) ∧
      ∀ z : Let Dw.mult, crd (ι b) R (φ.comp (φ₀.comp (ρ b))) (u.bc φ z.1 z.2) =
        cellVec (fun z => (φ.comp φ₀) ∘ crd (ι b) _ (ρ b) (e b z.1 z.2)) w (φ ∘ x) z := by
  choose u hu hu' using fun τ j => exists_comb Y.t (fun i => ((hF.frame b R₀ φ₀).1 τ (w τ i)).1) fun i => cell x τ i j
  refine ⟨u, fun R _ φ => ?_⟩
  have hc : ∀ τ j, IsCombAtG Y.t (spMap (φ.comp φ₀) ≫ (V b).2.fromSpec) (fun i => (e b).bc (φ.comp φ₀) τ (w τ i))
      (fun i => cell (φ ∘ x) τ i j) (Vecs.bc φ u τ j) := fun τ j => by
    have := GlobalTheory.LatDRFree.comb_map Y.t φ (hu' τ j)
    rw [sp_comp_assoc] at this
    simp only [map_cell] at this
    rw [← bc_bc]
    exact this
  have hf := hF.frame b R (φ.comp φ₀)
  refine ⟨?_, fun z => ?_⟩
  · rw [sp_comp_assoc]
    exact (GlobalTheory.T.tangent_combination_eigen_action E H Dw l c Y.X Y.t R _).2 _ _ _ w _ hf hc
  · have hx : spMap ((φ.comp φ₀).comp (ρ b)) ≫ (aff (ι b)).fromSpec = spMap (φ.comp φ₀) ≫ (V b).2.fromSpec := by
      rw [← sp_comp_assoc, hF.res]
    have ht := fun i => (hf.1 z.1 (w z.1 i)).1
    refine ((hE.comb_iff _ _ hx ht (comb_tan Y.t ht (hc z.1 z.2)) _).1 (hc z.1 z.2)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg _ (crd_bc hE hF b (φ.comp φ₀) ⟨z.1, w z.1 i⟩)

theorem exists_cell [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (hβ : β = algebraMap O c.F)
    (hE : IsLieEmb Y.t L aff crd) (hF : IsFrameCover Y L aff crd V ι ρ α e D)
    {k : Type} [Field k] (f : c.F →+* k) (y : Sp k ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap f)
    (u : Vecs Dw Y.t k) (hu : IsFrame Y.t f (y ≫ Y.j) u) :
    ∃ (b : B) (w : Pm Dw.mult) (ψ : Γ(Y.X, (V b).1) →+* k) (x : CellVar Dw.mult → k) (d : Let Dw.mult → k),
      spMap ψ ≫ (V b).2.fromSpec = y ≫ Y.j ∧ ψ.comp (α b) = f ∧
      Tri (cellVec (fun z => ψ ∘ crd (ι b) _ (ρ b) (e b z.1 z.2)) w x)
        (fun z => crd (ι b) k (ψ.comp (ρ b)) (u z.1 z.2)) d := by
  have h1 : (y ≫ Y.j) (IsLocalRing.closedPoint k) ∈ ⋃ b, ((V b).1 : Set Y.X) := by
    rw [hF.cover]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 h1
  obtain ⟨ψ, hψ⟩ := exists_factor (y ≫ Y.j) (V b) hb
  have h2 : ψ.comp (α b) = f := by
    have e1 : spMap ((ψ.comp (α b)).comp β) = spMap (f.comp β) := by
      rw [RingHom.comp_assoc, ← sp_comp, ← hF.isCover.ovr b, ← Category.assoc, hψ, ← sp_comp, ← hy, Model.j]
      simp only [Category.assoc]
      rw [pullback.condition, ← Y.jQ_over]
      simp only [Category.assoc]
    have e2 : (ψ.comp (α b)).comp β = f.comp β := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) ?_
    rw [← hβ]
    exact e2
  have hx : spMap (ψ.comp (ρ b)) ≫ (aff (ι b)).fromSpec = y ≫ Y.j := by rw [← sp_comp_assoc, hF.res, hψ]
  have hf := hF.frame b k ψ
  rw [hψ] at hf
  have t1 := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw l c Y.X Y.t L aff M crd hE (ι b) k _ _ _ _ _ _ hx hf hu).2.2 h2
  have t2 := (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw l c Y.X Y.t L aff M crd hE (ι b) k _ _ _ _ _ _ hx hu hu).2.1
  simp only [crd_bc hE hF b ψ] at t1
  obtain ⟨w, x, d, -, -, h⟩ := GlobalTheory.T.exists_integral_flagCell_of_valuedField _ _ k ⊤ M _ _ t1 t2
  exact ⟨b, w, ψ, x, d, hψ, h2, h⟩

end Cover

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem dvr_place {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsDiscreteValuationRing (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

set_option maxHeartbeats 800000 in

theorem exists_tied (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (i : Idx H p) (hd : i₀.l.Dvd i.l)
    (hle : i₀.c.F ≤ i.c.F) :
    ∃ (Z : Mdl Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M)
      (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1))
      (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Z.i = i ∧ Comparison₂ Z.toPre L aff crd ι ρ g := by
  classical
  have := dvr_place i.c hp.ne_zero hW
  have : IsProper (Y i).s := projProper _ _ _ (Y i).proj
  have : IsLocallyNoetherian (Y i).X := LocallyOfFiniteType.isLocallyNoetherian (Y i).s
  have : IsReduced (Y i).X := by
    have : ∀ x : (Y i).X, _root_.IsReduced ((Y i).X.presheaf.stalk x) := fun x => by
      have := ((Y i).normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, aff, M, crd, hE⟩ := GlobalTheory.T.exists_lie_embedding_projective E H _ _ (Y i).s (Y i).t (Y i).proj
  obtain ⟨n, V, ι, ρ, α, e, D, hF⟩ := GlobalTheory.T.exists_affine_refinement_lie_embedding E H Dw _ _ _ p W (Y i) hp hW L aff M crd hE
  obtain ⟨N, I, π, g, κ, hπ, hM⟩ := GlobalTheory.T.isCover_normal_projective_charts (i.c.V W) i.c.F _ (Y i).s _ Dw.mult M _ V α _ D (Y i).proj (Y i).normal
    hF.isCover
  have hop := hM.opn
  let eqv := (Fintype.equivFin (Fin n × Pm Dw.mult)).symm
  choose θ hθ using fun a => exists_ringEquiv (κ (eqv a).1 (eqv a).2)
  let φ₀ : ∀ a, Γ((Y i).X, (V (eqv a).1).1) →+* Γ(I.subscheme, (κ (eqv a).1 (eqv a).2).opensRange) :=
    fun a => (θ a).toRingHom.comp MvPolynomial.C
  choose fr hfr using fun a => exists_cellFrame hE hF (eqv a).1 (eqv a).2 (φ₀ a) fun v => θ a (MvPolynomial.X v)
  let Z : Pre Y i₀ := ⟨i, hd, hle, N, I, π, fun τ => Finset.range (Dw.mult τ + 1), _,
    fun a => ⟨(κ (eqv a).1 (eqv a).2).opensRange, isAffineOpen_opensRange _⟩, fun a => (φ₀ a).comp (α _), fr⟩
  have hch : ∀ a, Z.chart a = spMap (θ a).toRingHom ≫ κ (eqv a).1 (eqv a).2 := fun a => (hθ a).symm
  have hb : ∀ a, Z.chart a ≫ Z.π = spMap (φ₀ a) ≫ (V (eqv a).1).2.fromSpec := fun a => by
    rw [hch, Category.assoc]
    erw [hM.base]
    exact sp_comp_assoc _ _ _
  have hopn : Z.opn = π ⁻¹' ⋃ b, ((V b).1 : Set (Y i).X) := by rw [hF.cover]; rfl
  have hcov : ⋃ a, ((Z.U a).1 : Set Z.X) = Z.opn := by
    rw [hopn, ← hM.cover]
    ext z
    simp only [Set.mem_iUnion]
    refine ⟨fun ⟨a, h⟩ => ⟨_, _, h⟩, fun ⟨b, w, h⟩ => ?_⟩
    obtain ⟨a, ha⟩ := eqv.surjective (b, w)
    obtain rfl : b = (eqv a).1 := by rw [ha]
    obtain rfl : w = (eqv a).2 := by rw [ha]
    exact ⟨a, h⟩
  have halg : ∀ a, Z.chart a ≫ Z.π ≫ (Y Z.i).s = spMap ((Z.alg a).comp (Z.i.c.V W).subtype) := fun a => by
    rw [← Category.assoc, hb, Category.assoc]
    erw [hF.isCover.ovr]
    exact sp_comp _ _
  have hfr' : ∀ a (R : Type) [CommRing R] (φ : Γ(Z.X, (Z.U a).1) →+* R),
      IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) := fun a R _ φ => by
    rw [hb]
    exact (hfr a R φ).1
  have hres : ∀ a, spMap ((φ₀ a).comp (ρ (eqv a).1)) ≫ (aff (ι (eqv a).1)).fromSpec = Z.chart a ≫ Z.π := fun a => by
    rw [hb, ← sp_comp_assoc, hF.res]
  have hT : Comparison₂ Z L aff crd (fun a => ι (eqv a).1) (fun a => (φ₀ a).comp (ρ _)) g := by
    refine ⟨hE, rfl, hres, hcov, halg, hfr', fun a en => ?_, fun k _ z z' hz => hM.inj k z z' ?_⟩
    · obtain ⟨hu, h⟩ := hM.plk (eqv a).1 (eqv a).2 en
      have e1 : (θ a).toRingHom ∘ plk (uvec (fun z => crd (ι (eqv a).1) _ (ρ _) (e (eqv a).1 z.1 z.2)) (eqv a).2) en.2.1 =
          plk (fun z : Let Dw.mult => crd (ι (eqv a).1) _ ((φ₀ a).comp (ρ _)) (fr a z.1 z.2)) en.2.1 := by
        rw [map_plk]
        congr 1
        funext z
        have := (hfr a _ (RingHom.id _)).2 z
        rw [bc_id] at this
        exact (map_cellVec _ _ _ _ _).trans this.symm
      refine ⟨e1 ▸ span_range_comp_eq_top _ hu _, ?_⟩
      rw [hch, Category.assoc]
      exact (congrArg (spMap (θ a).toRingHom ≫ ·) h).trans ((spMap_pt _ _ _ _).trans (pt_congr rfl e1))
    · rintro _ ⟨q, rfl⟩
      have := hz ⟨q, rfl⟩
      rw [hopn] at this
      rw [Scheme.Hom.comp_apply]
      exact this
  refine ⟨⟨Z, hπ, GlobalTheory.IsNormalScheme.of_pred hM.normal, (congrArg (fun f => Flat f) hπ).mp hM.flat, hopn ▸ hM.dense, hcov, fun a => ?_, fun a => ?_, fun a => ?_,
    GlobalTheory.T.pre_model_chart_compatible E H Dw Xo p W Y i₀ Z L aff M crd _ _ g hT, fun k _ f y hy u hu => ?_⟩, L, aff, M, crd, _, _, g, rfl, hT⟩
  · exact (congrArg (Z.chart a ≫ ·) hπ.symm).trans (halg a)
  · have := (GlobalTheory.T.smooth_base_and_normal_coordinate_ring (Y i).X _ Dw.mult (V (eqv a).1) (Y i).normal).1
    have : IsIso (spMap (θ a).toRingHom) := inferInstanceAs (IsIso (Spec.map (θ a).toCommRingCatIso.hom))
    have e1 : Z.chart a ≫ π = spMap (θ a).toRingHom ≫ cbase Dw.mult (V (eqv a).1) := by
      rw [hch, Category.assoc]
      erw [hM.base]
    rw [e1]
    infer_instance
  · have := hfr' a _ (RingHom.id _)
    rwa [bc_id, sp_id] at this
  · refine existsUnique_of_exists_of_unique ?_ fun w w' h h' =>
      GlobalTheory.T.pre_model_chart_transition E H Dw Xo p W Y i₀ Z L aff M crd _ _ g hT k w w' u (h.1.trans h'.1.symm) h.2 h'.2
    obtain ⟨b, w, ψ, x, d, hψ, hf, htri⟩ := exists_cell rfl hE hF f y hy u hu
    obtain ⟨a, ha⟩ := eqv.surjective (b, w)
    obtain rfl : b = (eqv a).1 := by rw [ha]
    obtain rfl : w = (eqv a).2 := by rw [ha]
    let φ : Γ(Z.X, (Z.U a).1) →+* k := (MvPolynomial.eval₂Hom ψ x).comp (θ a).symm.toRingHom
    have h0 : φ.comp (φ₀ a) = ψ := RingHom.ext fun r =>
      (congrArg (MvPolynomial.eval₂Hom ψ x) ((θ a).symm_apply_apply _)).trans (MvPolynomial.eval₂Hom_C _ _ _)
    have h1 : (φ ∘ fun v => θ a (MvPolynomial.X v)) = x := funext fun v =>
      (congrArg (MvPolynomial.eval₂Hom ψ x) ((θ a).symm_apply_apply _)).trans (MvPolynomial.eval₂Hom_X' _ _ _)
    have h2 : (spMap φ ≫ Z.chart a) ≫ Z.π = y ≫ (Y i).j := by
      rw [Category.assoc, hb]
      exact (sp_comp_assoc _ _ _).trans ((congrArg (spMap · ≫ _) h0).trans hψ)
    have h3 : φ.comp (Z.alg a) = f := by rw [← hf, ← h0]; rfl
    have h4 := hfr' a k φ
    rw [← Category.assoc, h2] at h4
    refine ⟨spMap φ ≫ Z.chart a, h2, a, φ, rfl, ?_, ?_⟩
    · rw [h2, h3]
      exact hu
    · rw [h2]
      have hx : spMap (ψ.comp (ρ _)) ≫ (aff (ι (eqv a).1)).fromSpec = y ≫ (Y i).j := by
        rw [← sp_comp_assoc, hF.res]
        exact hψ
      refine (GlobalTheory.T.frames_agree_on_lie_embedding_chart E H Dw _ _ _ _ L aff M crd hE _ k _ _ _ _ _ _ hx h4 hu).1.2 ⟨d, ?_⟩
      have h5 := funext (hfr a k φ).2
      rw [h1, ← RingHom.comp_assoc, h0] at h5
      rw [← h5] at htri
      exact htri

end GlobalTheory.FlagEmb.DR

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.Cartier in

theorem GlobalTheory.FlagEmb.DR.exists_lineModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ i : Idx H p, i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z false st x) := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW _ i hd hle st x hx
  obtain ⟨Z, L, aff, M, crd, ι, ρ, g, hi, hT⟩ := GlobalTheory.FlagEmb.DR.exists_tied (Y := Y) hp hW i hd hle
  obtain ⟨n, u, k, hu, h₀, h₁, rfl, hln⟩ := GlobalTheory.T.exists_descending_letter_chain E H Dw st x hx
  obtain ⟨L', ix, q₀, q₁, r, hL⟩ := GlobalTheory.T.pre_model_chart_frame E H Dw Xo p W Y i₀ Z.toPre L aff M crd ι ρ g hT ⟨k, _, h₀⟩ ⟨k + 1, _, h₁⟩ rfl
  refine ⟨Z, hi, hT.ty, ⟨L', r, hL.trans,
    GlobalTheory.T.pre_model_chart_section E H Dw Xo p W Y i₀ Z.toPre L aff M crd ι ρ g hT n u k h₀ h₁ L' ix q₀ q₁ r hL, fun y a j φ h h' => ?_⟩⟩
  rw [hln]
  exact GlobalTheory.T.pre_model_chart_values E H Dw Xo p W Y i₀ Z.toPre L aff M crd ι ρ g hT n u k h₀ h₁ L' ix q₀ q₁ r hL hu _ y.z a j φ h h'
