import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Flags

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  {ty ty' : (E →+* ℂ) → Finset ℕ}

attribute [local instance] Over.cartesianMonoidalCategory

theorem comb_bc (φ : R →+* S) {x : Sp R ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', Formalism.L2.Pj.dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem comb_push_iff {f : X' ⟶ X} (mu : SABMap t' t f) {x : Sp R ⟶ X'} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t'.G.left)} (hv : ∀ i, IsTanAtG t' x (v i)) (cf : Fin m → R)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : IsTanAtG t' x w) :
    IsCombAtG t (x ≫ f) (fun i => v i ≫ mu.φ) cf (w ≫ mu.φ) ↔ IsCombAtG t' x v cf w := by
  refine (isComb_iff (fun i => pushE mu x rfl (tanOf (hv i))) cf (pushE mu x rfl (tanOf hw))).trans
    (Iff.trans ?_ (isComb_iff (fun i => tanOf (hv i)) cf (tanOf hw)).symm)
  rw [← (pushE mu x rfl).injective.eq_iff, map_sum]
  simp only [map_smul]

theorem Vecs.bc_bc (φ : R →+* S) (ψ : S →+* T) (u : Vecs Dw t R) : (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  have e : (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := RingHom.ext fun z => by ext <;> simp [dualMap]
  simp only [Vecs.bc]
  rw [← Category.assoc, spMap_comp', e]

theorem SameFlag.refl {x : Sp R ⟶ X} {u : Vecs Dw t R} (hu : ∀ τ i, IsTanAtG t x (u τ i)) : SameFlag ty t x u u :=
  fun τ _ _ i hi => ⟨Pi.single i 1, fun _ hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _,
    GlobalTheory.ShFam.isCombAtG_single t x (hu τ) i⟩

theorem SameFlag.mono {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (h : SameFlag ty t x u u') (hle : ∀ σ, ty' σ ⊆ ty σ) :
    SameFlag ty' t x u u' := fun τ k hk => h τ k (hle τ hk)

theorem SameFlag.trans {x : Sp R ⟶ X} {u u' u'' : Vecs Dw t R} (hu : ∀ τ i, IsTanAtG t x (u τ i))
    (hall : ∀ τ i, ∃ cf, IsCombAtG t x (u τ) cf (u' τ i))
    (h : SameFlag ty t x u u') (h' : SameFlag ty t x u' u'') : SameFlag ty t x u u'' := by
  intro τ k hk i hi
  obtain ⟨c, hc, hc'⟩ := h' τ k hk i hi
  have : ∀ j : Fin (Dw.mult τ), ∃ cf : Fin (Dw.mult τ) → R, ((j : ℕ) < k → ∀ j' : Fin (Dw.mult τ), k ≤ (j' : ℕ) → cf j' = 0) ∧
      IsCombAtG t x (u τ) cf (u' τ j) := fun j => by
    by_cases hj : (j : ℕ) < k
    · obtain ⟨a, ha, ha'⟩ := h τ k hk j hj
      exact ⟨a, fun _ => ha, ha'⟩
    · obtain ⟨a, ha⟩ := hall τ j
      exact ⟨a, fun h => absurd h hj, ha⟩
  choose A hA hA' using this
  refine ⟨(Matrix.of fun j' j => A j j').mulVec c, fun j' hj' => ?_, tanLinG _ (hu τ) _ _ _ _ hA' hc'⟩
  show ∑ j, A j j' * c j = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : (j : ℕ) < k
  · simp [hA j hj j' hj']
  · simp [hc j (not_lt.1 hj)]

theorem SameFlag.push {f : X' ⟶ X} (mu : SABMap t' t f) {x : Sp R ⟶ X'} {u u' : Vecs Dw t' R}
    (hu : ∀ τ i, IsTanAtG t' x (u τ i)) (hu' : ∀ τ i, IsTanAtG t' x (u' τ i)) (h : SameFlag ty t' x u u') :
    SameFlag (Dw := Dw) ty t (x ≫ f) (fun σ i => u σ i ≫ mu.φ) (fun σ i => u' σ i ≫ mu.φ) := fun τ k hk i hi =>
  (h τ k hk i hi).imp fun cf hcf => ⟨hcf.1, (comb_push_iff mu (hu τ) cf (hu' τ i)).2 hcf.2⟩

theorem IsFrame.push {l l' : Level H} {c : Coeff l} {c' : Coeff l'} (hc : c.F ≤ c'.F) {f : X' ⟶ X} (mu : SABMap t' t f)
    {g : c'.F →+* R} {x : Sp R ⟶ X'} {u : Vecs Dw t' R} (h : IsFrame t' g x u) :
    IsFrame (Dw := Dw) t (g.comp (IntermediateField.inclusion hc).toRingHom) (x ≫ f) (fun σ i => u σ i ≫ mu.φ) := by
  have e : ∀ τ a, g.comp (IntermediateField.inclusion hc).toRingHom (embK c τ a) = g (embK c' τ a) := fun _ _ => rfl
  refine ⟨fun τ i => ⟨isTan_push mu x rfl (h.1 τ i).1, fun a => ?_⟩, fun τ w hw he => ?_⟩
  · rw [e, Category.assoc, ← mu.act, ← Category.assoc, (h.1 τ i).2 a, Category.assoc]
  · obtain ⟨v, hv⟩ := (pushE mu x rfl).surjective (tanOf hw)
    obtain rfl : (tv v).left ≫ mu.φ = w := congrArg (fun z => (tv z).left) hv
    simp only [comb_push_iff mu (fun i => (h.1 τ i).1) _ (isTan_tv v)]
    refine h.2 τ _ (isTan_tv v) fun a => mu.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, mu.act, ← Category.assoc, he a, e, Category.assoc]
    · rw [Category.assoc, Over.w, Category.assoc, (isTan_tv v).1, ← Category.assoc, spMap_comp']
      congr 2
      ext r <;> simp [epsMul]

theorem IsFrame.exists_comb {l : Level H} {c : Coeff l} {g : c.F →+* R} {x : Sp R ⟶ X} {u u' : Vecs Dw t R}
    (h : IsFrame t g x u) (h' : IsFrame t g x u') (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    ∃! cf, IsCombAtG t x (u τ) cf (u' τ i) := h.2 τ _ (h'.1 τ i).1 (h'.1 τ i).2

end Flags

theorem isDiscreteValuationRing_V {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : IsDiscreteValuationRing (c.V W) := by
  refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero ?_).1
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp.ne_zero
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem coeff_ext {l : Level H} {c : Coeff l} {W : ValuationSubring ℂ} {R : Type} [CommRing R] {f g : c.F →+* R}
    (h : spMap (f.comp (c.V W).subtype) = spMap (g.comp (c.V W).subtype)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (c.V W)) (congrArg CommRingCat.Hom.hom (Spec.map_injective h))

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem Mdl.affineOpenChart_comp_structure_eq_spMap (Z : Mdl Y i₀) {R : Type} [CommRing R] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* R) :
    spMap φ ≫ Z.chart a ≫ Z.s = spMap ((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) := by
  rw [Z.alg_s, spMap_comp', RingHom.comp_assoc]

theorem Mdl.alg_eq (Z : Mdl Y i₀) {R : Type} [CommRing R] {a a' : Fin Z.m} {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {φ' : Γ(Z.X, (Z.U a').1) →+* R} (h : spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a') :
    φ.comp (Z.alg a) = φ'.comp (Z.alg a') :=
  coeff_ext (W := W) (by rw [← Z.affineOpenChart_comp_structure_eq_spMap, ← Z.affineOpenChart_comp_structure_eq_spMap, reassoc_of% h])

theorem Mdl.exists_chart_fac (Z : Mdl Y i₀) {R : Type} [CommRing R] (w : Sp R ⟶ Z.X) (a : Fin Z.m)
    (h : Set.range w ⊆ (Z.U a).1) : ∃ φ : Γ(Z.X, (Z.U a).1) →+* R, spMap φ ≫ Z.chart a = w := by
  have := (Z.U a).2.isOpenImmersion_fromSpec
  have h' : Set.range w ⊆ Set.range (Z.U a).2.fromSpec := by rwa [(Z.U a).2.range_fromSpec]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (Z.U a).2.fromSpec w h')).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem Mdl.exists_chart (Z : Mdl Y i₀) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (h : Set.range w ⊆ Z.opn) :
    ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k), spMap φ ≫ Z.chart a = w := by
  have h0 := h ⟨IsLocalRing.closedPoint k, rfl⟩
  rw [← Z.cover] at h0
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 h0
  refine ⟨a, Z.exists_chart_fac w a ?_⟩
  rintro _ ⟨x, rfl⟩
  rwa [Subsingleton.elim x (IsLocalRing.closedPoint k)]

theorem exists_isTrans_id (i : Idx H p) :
    ∃ mu : SABMap (Y i).t (Y i).t (𝟙 _), mu.φ = 𝟙 _ ∧ IsTrans (Y := Y) i i (𝟙 _) mu := by
  obtain ⟨mu, hmu⟩ := GlobalTheory.ObjMaps.exists_sab_id (Y i).t
  have e : spMap (RingHom.id (i.c.V W)) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id (i.c.V W))) := by rw [e]; infer_instance
  have hM : i.l.M / i.l.M = 1 := Nat.div_self (by have := i.l.three_le; omega)
  refine ⟨mu, hmu, RingHom.id _, inv (pullback.fst _ _), 𝟙 _, fun _ => rfl, IsIso.inv_hom_id _, ?_, inferInstance,
    by simp, fun a => ?_, fun a => ?_⟩
  · rw [IsIso.inv_comp_eq, pullback.condition]
    exact ((congrArg (_ ≫ ·) e).trans (Category.comp_id _)).symm
  · rw [hM, pow_one, hmu, Category.comp_id, Category.id_comp]
  · rw [Nat.div_self i.l.A_pos, pow_one, hmu, Category.comp_id, Category.id_comp]

theorem exists_isTrans (h : N2 Y) {i i₂ : Idx H p} (hl : i.l.Dvd i₂.l) (hc : i.c.F ≤ i₂.c.F) :
    ∃ (τ : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ), IsTrans i i₂ τ mu := by
  obtain ⟨-, π, hπ, -⟩ := h
  let b : i.c.V W →+* i₂.c.V W :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i₂.c.V W) fun x => x.2
  obtain ⟨π', mu, r, h⟩ := hπ i i₂ hl hc b fun _ => rfl
  exact ⟨_, mu, b, π', r, fun _ => rfl, h⟩

end GlobalTheory.LocM
