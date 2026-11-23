import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransitionUniqueAndPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTangentOfUniqueIntegralLiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentFamilyOfUniqueLiftPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUniqueStatement
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DominatesLiftUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Val

variable {F : Type} [Field F] {X Y : Scheme.{0}}

theorem valF_appLE {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_mul {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a * b) = valF x U a * valF x U b := by
  simp only [valF, dif_pos h, map_mul]

theorem valF_mul_inv {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valF x U a.val * valF x U (a⁻¹).val = 1 := by
  rw [← valF_mul h, a.mul_inv]
  simp only [valF, dif_pos h, map_one]

theorem valF_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* F) (s : Γ(X, V)) :
    valF (spMap χ ≫ hV.fromSpec) V s = χ s := by
  have h0 : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V := fun q _ => h0 (Set.mem_univ (spMap χ q))
  rw [valF, dif_pos h]
  have e : (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom = CommRingCat.ofHom χ := by
    have e1 : hV.fromSpec.appLE V ⊤ h0 = (Scheme.ΓSpecIso Γ(X, V)).inv := by
      rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg _ ((Spec Γ(X, V)).presheaf.map_id _)).trans (Category.comp_id _)
    rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h0 le_rfl, e1, Category.assoc, Iso.inv_comp_eq]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  exact congrArg (fun g => g.hom s) e

theorem exists_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] (w : Sp R ⟶ X)
    (h : ⊤ ≤ w ⁻¹ᵁ V) : ∃ χ : Γ(X, V) →+* R, spMap χ ≫ hV.fromSpec = w := by
  have h' : Set.range w ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hV.range_fromSpec]
    exact h (Set.mem_univ q)
  exact ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec w h')).hom,
    (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩

theorem le_of_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] {w : Sp R ⟶ X}
    {χ : Γ(X, V) →+* R} (h : spMap χ ≫ hV.fromSpec = w) : ⊤ ≤ w ⁻¹ᵁ V := fun q _ =>
  h ▸ hV.fromSpec_preimage_self.ge (Set.mem_univ (spMap χ q))

theorem mono_fromSpec {V : X.Opens} (hV : IsAffineOpen V) : Mono hV.fromSpec := inferInstance

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Frames

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}

theorem eig_iff {R : Type} [CommRing R] {x : Sp R ⟶ X} (v : TanM x t.G) (a : 𝓞 E) (s : R) :
    (tv v).left ≫ (t.act.act a).left = spMap (epsMul s) ≫ (tv v).left ↔ actR t.act a v = s • v :=
  ⟨fun h => tan_ext h, fun h => congrArg (fun z => (tv z).left) h⟩

theorem frame_ind {k : Type} [Field k] {f : c.F →+* k} {x : Sp k ⟶ X} {u : Vecs Dw t k}
    (h : GlobalTheory.LocM.IsFrame t f x u) (τ : E →+* ℂ) : Ind t x (u τ) := by
  refine ⟨fun i => (h.1 τ i).1, fun cf cf' w h1 h2 => ?_⟩
  obtain ⟨U, hU⟩ := exists_tan fun i => (h.1 τ i).1
  have e := (comb_iff U cf w).1 (hU ▸ h1)
  refine (h.2 τ w (e ▸ isTan_tv _) fun a => ?_).unique h1 h2
  rw [e, eig_iff, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, (eig_iff (U i) a _).1 (congrFun hU i ▸ (h.1 τ i).2 a)]

variable {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)

include hx

theorem comb_push {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t'.G.left)} (hu : ∀ i, IsTanAtG t' x' (u i))
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : IsTanAtG t' x' w) (cf : Fin m → R) :
    IsCombAtG t x (fun i => u i ≫ mu.φ) cf (w ≫ mu.φ) ↔ IsCombAtG t' x' u cf w := by
  refine (GlobalTheory.LieMet.isComb_iff (fun i => pushE mu x' hx (tanOf (hu i))) cf (pushE mu x' hx (tanOf hw))).trans
    (Iff.trans ?_ (GlobalTheory.LieMet.isComb_iff (fun i => tanOf (hu i)) cf (tanOf hw)).symm)
  simp only [← map_smul, ← map_sum, EmbeddingLike.apply_eq_iff_eq]

theorem frame_push {f' : c'.F →+* R} {f : c.F →+* R} (hf : ∀ τ a, f (embK c τ a) = f' (embK c' τ a))
    {u : Vecs Dw t' R} (h : GlobalTheory.LocM.IsFrame t' f' x' u) : GlobalTheory.LocM.IsFrame (Dw := Dw) t f x fun τ i => u τ i ≫ mu.φ := by
  refine ⟨fun τ i => ⟨isTan_push mu x' hx (h.1 τ i).1, fun a => ?_⟩, fun τ w hw he => ?_⟩
  · rw [Category.assoc, ← mu.act, ← Category.assoc, (h.1 τ i).2, hf, Category.assoc]
  · obtain ⟨v, hv⟩ := (pushE mu x' hx).surjective (tanOf hw)
    obtain rfl : (tv v).left ≫ mu.φ = w := congrArg (fun z => (tv z).left) hv
    refine (existsUnique_congr fun cf => comb_push mu hx (fun i => (h.1 τ i).1) (isTan_tv v) cf).2
      (h.2 τ _ (isTan_tv v) fun a => (eig_iff v a _).2 ((pushE mu x' hx).injective ?_))
    rw [pushE_act, map_smul, ← hf]
    exact (eig_iff _ a _).1 (he a)

end Frames

section Steps

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l} {p : ℕ}

theorem lnStep_push {g : X' ⟶ X} (mu : SABMap t' t g) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (b : Bool) (xO : Sp ↥(intO C) ⟶ X')
    (hO : ∀ y : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ xO ≫ g → y = xO ≫ g)
    {u : Vecs Dw t' C} (hu : ∀ τ i, IsTanAtG t' (spMap (intO C).subtype ≫ xO) (u τ i)) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) :
    lnStep t' (spMap (intO C).subtype ≫ xO) u p b st =
      lnStep (Dw := Dw) t (spMap (intO C).subtype ≫ xO ≫ g) (fun τ i => u τ i ≫ mu.φ) p b st := by
  have key := fun {m : ℕ} {v : Fin m → (Sp (DualNumber C) ⟶ t'.G.left)} =>
    grNorm_push (v := v) mu (Category.assoc _ _ _) (GlobalTheory.T.isTangent_of_unique_integral_lift E H X X' t t' g mu C p b xO hO)
  rcases st with ⟨τ, k⟩ | k
  · simp only [lnStep, key (hu τ)]
  · simp only [lnStep, key (v := fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) fun i => hu _ _]

theorem lnStep_tri (hB : HTBoundSt) (hp : p.Prime) (C : Formalism.MainNotions.DIV.Cons.SCF p) (b : Bool) (xO : Sp ↥(intO ↥C.S) ⟶ X)
    (hO : ∀ y : Sp ↥(intO ↥C.S) ⟶ X, spMap (intO ↥C.S).subtype ≫ y = spMap (intO ↥C.S).subtype ≫ xO → y = xO)
    {f : c.F →+* ↥C.S} {u u' : Vecs Dw t ↥C.S} (hu : GlobalTheory.LocM.IsFrame t f (spMap (intO ↥C.S).subtype ≫ xO) u)
    (hu' : GlobalTheory.LocM.IsFrame t f (spMap (intO ↥C.S).subtype ≫ xO) u')
    (h : ∀ τ, Tri t (spMap (intO ↥C.S).subtype ≫ xO) (u τ) (u' τ)) {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}
    (hx : letterOf Dw st = some x) {cf : Fin (Dw.mult x.1) → ↥C.S}
    (hc : IsCombAtG t (spMap (intO ↥C.S).subtype ≫ xO) (u x.1) cf (u' x.1 x.2)) :
    lnStep t (spMap (intO ↥C.S).subtype ≫ xO) u' p b st =
      Real.log ‖cf x.2‖ + lnStep t (spMap (intO ↥C.S).subtype ≫ xO) u p b st := by
  obtain ⟨h0, h1⟩ := (h x.1).diag (frame_ind hu _) (frame_ind hu' _) hc
  have pos := GlobalTheory.T.tangent_family_of_unique_lift_prime hB E H X t p C b xO hp hO
  rcases st with ⟨τ, k⟩ | k
  · by_cases hk : k < Dw.mult τ
    · simp only [letterOf, dif_pos hk, Option.some.injEq] at hx
      subst hx
      simp only [lnStep, dif_pos hk]
      rw [(h τ).grNorm_eq (frame_ind hu _) (frame_ind hu' _) _ hc, Real.log_mul (norm_ne_zero_iff.2 h0)
        (pos _ _ (frame_ind hu τ).1 (frame_ind hu τ).2 _).ne', add_sub_assoc]
    · simp [letterOf, hk] at hx
  · obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hx
    obtain ⟨i1, c1⟩ := GlobalTheory.T.frame_combination_coeff_unique E H Dw l c X t _ f _ u hu
    have I1 : Ind t _ _ := ⟨fun i => (hu.1 _ _).1, i1⟩
    have I2 : Ind t _ _ := ⟨fun i => (hu'.1 _ _).1, (GlobalTheory.T.frame_combination_coeff_unique E H Dw l c X t _ f _ u' hu').1⟩
    have T : Tri t _ (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
        (fun i => u' ((letters Dw).get i).1 ((letters Dw).get i).2) := fun j => by
      obtain ⟨d, d1, d2⟩ := h ((letters Dw).get j).1 ((letters Dw).get j).2
      obtain ⟨e, e1, -, e2⟩ := c1 j d _ d1 d2
      exact ⟨e, e1, e2⟩
    obtain ⟨e, -, e1, e2⟩ := c1 ⟨k, hk⟩ cf _ h1 hc
    simp only [lnStep, dif_pos hk]
    rw [T.grNorm_eq I1 I2 _ e2, e1]
    exact Real.log_mul (norm_ne_zero_iff.2 h0) (pos _ _ I1.1 I1.2 _).ne'

end Steps

section Models

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem chart_frame (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    GlobalTheory.LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (w ≫ Z.π) ((Z.fr a).bc φ) := by
  rw [← h, Category.assoc]
  exact GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)

theorem affineOpenChart_comp_structure_eq_spMap (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    w ≫ Z.π ≫ (Y Z.i).s = spMap (φ.comp (Z.alg a)) ≫ spMap (Z.i.c.V W).subtype := by
  rw [Z.π_s, ← h, Category.assoc, Z.alg_s, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, RingHom.comp_assoc]

theorem range_opn (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) : Set.range w ⊆ Z.opn := by
  rintro _ ⟨q, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, le_of_fromSpec (Z.U a).2 h (Set.mem_univ q)⟩

theorem exists_open_lift (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    ∃ y : Sp R ⟶ (Xo Z.i.l).XF Z.i.c, y ≫ (Y Z.i).j = w ≫ Z.π := by
  have := (Y Z.i).jQ_open
  let q : Sp R ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) _ ((Category.assoc _ _ _).trans (affineOpenChart_comp_structure_eq_spMap Z h))
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z h ⟨z, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  exact ⟨IsOpenImmersion.lift _ q hr, by rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, IsOpenImmersion.lift_fac_assoc, hq]⟩

theorem tri_of_sameFlag {X : Scheme.{0}} {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {u u' : Vecs Dw t k}
    {ty : (E →+* ℂ) → Finset ℕ} (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ ty τ) (h : SameFlag ty t x u u') (τ : E →+* ℂ) :
    Tri t x (u τ) (u' τ) := fun j => h τ (j + 1) (hty τ _ j.2) j (Nat.lt_succ_self _)

theorem chart_tri (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) {k : Type} [Field k] {a a' : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} {φ' : Γ(Z.X, (Z.U a').1) →+* k} {w : Sp k ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w)
    (h' : spMap φ' ≫ Z.chart a' = w) (τ : E →+* ℂ) :
    Tri (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ τ) ((Z.fr a').bc φ' τ) := by
  have := tri_of_sameFlag hty (Z.glue k a a' φ φ' (h.trans h'.symm)) τ
  rwa [← Category.assoc, h] at this

theorem isReduced_model (Z : Mdl Y i₀) : IsReduced Z.X :=
  have := Z.normal
  inferInstance

theorem isSeparated_base (i : Idx H p) : (Y i).X.IsSeparated := by
  have := projProper _ _ _ (Y i).proj
  exact ⟨by rw [← terminal.comp_from (Y i).s]; infer_instance⟩

theorem ext_unique (i : Idx H p) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ (Y i).X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have := isSeparated_base (Y := Y) i
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem exists_trans (h : N2 Y) {i i₂ : Idx H p} (hl : i.l.Dvd i₂.l) (hc : i.c.F ≤ i₂.c.F) :
    ∃ τ mu, IsTrans (Y := Y) i i₂ τ mu := by
  obtain ⟨-, π, hπ, -⟩ := h
  let b : i.c.V W →+* i₂.c.V W :=
    ((IntermediateField.inclusion hc).toRingHom.comp (i.c.V W).subtype).codRestrict (i₂.c.V W) fun x => x.2
  obtain ⟨π', mu, r, h⟩ := hπ i i₂ hl hc b fun _ => rfl
  exact ⟨_, mu, b, π', r, fun _ => rfl, h⟩

variable {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)

include hf hT

theorem map_π : f ≫ Z.π = Z'.π ≫ τ := by
  have := isReduced_model Z'
  have := (isSeparated_base (Y := Y) Z.i).1
  refine ext_of_fromSpecResidueField_eq _ _ (terminal.from _) _ Z'.dense (fun x hx => ?_) (terminal.hom_ext _ _)
  obtain ⟨τ', mu', u, h1, h2, -⟩ := hf.2 (Z'.X.residueField x) (Z'.X.fromSpecResidueField x) (by
    rw [Scheme.range_fromSpecResidueField]; simpa using hx)
  rw [(GlobalTheory.T.transition_unique_and_points E H Dw Xo p W Y _ _ _ _ _ _ hf.1.2.1 hT h1).1, ← Category.assoc]
  exact h2

theorem alg_eq {R : Type} [CommRing R] {a : Fin Z.m} {a' : Fin Z'.m} {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {φ' : Γ(Z'.X, (Z'.U a').1) →+* R} {w : Sp R ⟶ Z'.X} (h' : spMap φ' ≫ Z'.chart a' = w)
    (h : spMap φ ≫ Z.chart a = w ≫ f) :
    φ.comp (Z.alg a) = (φ'.comp (Z'.alg a')).comp (IntermediateField.inclusion hf.1.2.1).toRingHom := by
  have e0 := map_π hf hT
  obtain ⟨b, π', -, hb, h₁, h₂, -⟩ := hT
  have e : τ ≫ (Y Z.i).s = (Y Z'.i).s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  have := mono_spMap_subtype (Z.i.c.V W)
  refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
  rw [← cancel_mono (spMap (Z.i.c.V W).subtype), ← affineOpenChart_comp_structure_eq_spMap Z h, Category.assoc, reassoc_of% e0, e,
    reassoc_of% affineOpenChart_comp_structure_eq_spMap Z' h', ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp]
  congr 1
  ext x
  exact congrArg (φ'.comp (Z'.alg a')) (Subtype.ext (hb x))

theorem push_frame {R : Type} [CommRing R] {a : Fin Z.m} {a' : Fin Z'.m} {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {φ' : Γ(Z'.X, (Z'.U a').1) →+* R} {w : Sp R ⟶ Z'.X} (h' : spMap φ' ≫ Z'.chart a' = w)
    (h : spMap φ ≫ Z.chart a = w ≫ f) :
    GlobalTheory.LocM.IsFrame (Dw := Dw) (Y Z.i).t (φ.comp (Z.alg a)) ((w ≫ f) ≫ Z.π)
      fun σ i => (Z'.fr a').bc φ' σ i ≫ mu.φ :=
  frame_push mu (by rw [Category.assoc, Category.assoc, map_π hf hT]) (fun σ x => by rw [alg_eq hf hT h' h]; rfl)
    (chart_frame Z' h')

theorem exists_chart {k : Type} [Field k] {w : Sp k ⟶ Z'.X} (hw : Set.range w ⊆ Z'.opn) :
    ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k), spMap φ ≫ Z.chart a = w ≫ f := by
  obtain ⟨-, -, -, -, -, -, a, φ, h, -⟩ := hf.2 k w hw
  exact ⟨a, φ, h⟩

theorem push_tri (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) {k : Type} [Field k] {a : Fin Z.m} {a' : Fin Z'.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} {φ' : Γ(Z'.X, (Z'.U a').1) →+* k} {w : Sp k ⟶ Z'.X}
    (h' : spMap φ' ≫ Z'.chart a' = w) (h : spMap φ ≫ Z.chart a = w ≫ f) (σ : E →+* ℂ) :
    Tri (Y Z.i).t ((w ≫ f) ≫ Z.π) ((Z.fr a).bc φ σ) fun i => (Z'.fr a').bc φ' σ i ≫ mu.φ := by
  have hty' : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z'.ty τ := fun τ n hn => hf.1.2.2 τ (hty τ n hn)
  obtain ⟨τ', mu', u, h1, -, ⟨a₁', φ₁', k1', F', S'⟩, a₁, φ₁, k1, F, S⟩ := hf.2 k w (range_opn Z' h')
  obtain ⟨y, hy⟩ := exists_open_lift Z' h'
  have e : (fun σ i => u σ i ≫ mu'.φ) = fun σ i => u σ i ≫ mu.φ := funext fun σ => funext fun i =>
    (GlobalTheory.T.transition_unique_and_points E H Dw Xo p W Y _ _ _ _ _ _ hf.1.2.1 h1 hT).2 k y _ _ _ ((F'.1 σ i).1.1.trans (by rw [hy]))
  rw [e] at F S
  have t1 := ((tri_of_sameFlag hty' S' σ).symm (frame_ind (chart_frame Z' k1') σ) (frame_ind F' σ)).1.trans
    (frame_ind F' σ).1 (frame_ind (chart_frame Z' k1') σ).1 (chart_tri Z' hty' k1' h' σ)
  refine ((chart_tri Z hty h k1 σ).trans (frame_ind (chart_frame Z h) σ).1 (frame_ind (chart_frame Z k1) σ).1
    (tri_of_sameFlag hty S σ)).trans (frame_ind (chart_frame Z h) σ).1 (frame_ind F σ).1 fun j => ?_
  obtain ⟨cf, c1, c2⟩ := t1 j
  exact ⟨cf, c1, (comb_push mu (by rw [Category.assoc, Category.assoc, map_π hf hT]) (frame_ind F' σ).1
    ((frame_ind (chart_frame Z' h') σ).1 j) cf).2 c2⟩

end Models

section Bundle

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def pb (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) : Γ(X, U)ˣ →* Γ(Y, V)ˣ := Units.map (f.appLE U V e).hom.toMonoidHom

theorem res_pb {U U' : X.Opens} {V V' : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') (h : U' ≤ U) (h' : V' ≤ V)
    (a : Γ(X, U)ˣ) : res h' (pb f U V e a) = pb f U' V' e' (res h a) :=
  Units.ext (congrArg (fun q => q.hom a.val)
    ((Scheme.Hom.appLE_map f e (homOfLE h').op).trans (Scheme.Hom.map_appLE f e' (homOfLE h).op).symm))

def pullLB (L : FinLB X) : FinLB Y where
  n := L.n
  U i := f ⁻¹ᵁ L.U i
  g i k := pb f _ _ le_rfl (L.g i k)
  isLB :=
    { cover := by
        have := congrArg (f ⁻¹ᵁ ·) L.isLB.cover
        simpa [Scheme.Hom.preimage_iSup] using this
      g_self := fun i => (res_pb f _ le_rfl _ _ _).trans ((congrArg _ (L.isLB.g_self i)).trans (map_one _))
      cocycle := fun i j k => by
        have := congrArg (pb f _ (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j ⊓ f ⁻¹ᵁ L.U k) le_rfl) (L.isLB.cocycle i j k)
        rw [map_mul] at this
        exact (congrArg₂ (· * ·) (res_pb f _ _ _ _ _) (res_pb f _ _ _ _ _)).trans
          (this.trans (res_pb f _ _ _ _ _).symm) }

end Bundle

section Main

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

def Rel (f : Z'.X ⟶ Z.X) (mu : SABMap (Y Z'.i).t (Y Z.i).t τ) (M : LineModel Z b st x) (a' : Fin Z'.m) (i : Fin M.L.n)
    (k : Type) [Field k] (w : Sp k ⟶ Z'.X) (s : k) : Prop :=
  ∀ (φ' : Γ(Z'.X, (Z'.U a').1) →+* k) (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) (cf : Fin (Dw.mult x.1) → k),
    spMap φ' ≫ Z'.chart a' = w → spMap φ ≫ Z.chart a = w ≫ f →
    IsCombAtG (Y Z.i).t ((w ≫ f) ≫ Z.π) ((Z.fr a).bc φ x.1) cf ((Z'.fr a').bc φ' x.1 x.2 ≫ mu.φ) →
    s * valF (w ≫ f) _ (M.r a i).val = cf x.2

variable (hf : IsMap Z' Z f) {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)
  (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) (M : LineModel Z b st x)

theorem val_ne {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m} {φ : Γ(Z.X, (Z.U a).1) →+* k}
    (h : spMap φ ≫ Z.chart a = w) {i : Fin M.L.n} (hi : ⊤ ≤ w ⁻¹ᵁ M.L.U i) : valF w _ (M.r a i).val ≠ 0 :=
  left_ne_zero_of_mul_eq_one (valF_mul_inv (U := (Z.U a).1 ⊓ M.L.U i)
    (fun q hq => ⟨le_of_fromSpec (Z.U a).2 h hq, hi hq⟩) _)

include hf hT hty

theorem exists_coeff {k : Type} [Field k] {w : Sp k ⟶ Z'.X} {a' : Fin Z'.m} {φ' : Γ(Z'.X, (Z'.U a').1) →+* k}
    (h' : spMap φ' ≫ Z'.chart a' = w) {a : Fin Z.m} {φ : Γ(Z.X, (Z.U a).1) →+* k} (h : spMap φ ≫ Z.chart a = w ≫ f) :
    ∃ cf : Fin (Dw.mult x.1) → k, cf x.2 ≠ 0 ∧
      IsCombAtG (Y Z.i).t ((w ≫ f) ≫ Z.π) ((Z.fr a).bc φ x.1) cf ((Z'.fr a').bc φ' x.1 x.2 ≫ mu.φ) := by
  obtain ⟨cf, -, hc⟩ := push_tri hf hT hty h' h x.1 x.2
  exact ⟨cf, ((push_tri hf hT hty h' h x.1).diag (frame_ind (chart_frame Z h) _) (frame_ind (push_frame hf hT h' h) _)
    hc).1, hc⟩

theorem rel_of_one {k : Type} [Field k] {w : Sp k ⟶ Z'.X} {a' : Fin Z'.m} {φ' : Γ(Z'.X, (Z'.U a').1) →+* k}
    (h' : spMap φ' ≫ Z'.chart a' = w) {a : Fin Z.m} {φ : Γ(Z.X, (Z.U a).1) →+* k} (h : spMap φ ≫ Z.chart a = w ≫ f)
    {i : Fin M.L.n} (hi : ⊤ ≤ (w ≫ f) ⁻¹ᵁ M.L.U i) {cf : Fin (Dw.mult x.1) → k}
    (hc : IsCombAtG (Y Z.i).t ((w ≫ f) ≫ Z.π) ((Z.fr a).bc φ x.1) cf ((Z'.fr a').bc φ' x.1 x.2 ≫ mu.φ)) {s : k}
    (hs : s * valF (w ≫ f) _ (M.r a i).val = cf x.2) : Rel f mu M a' i k w s := by
  intro φ₂' a₂ φ₂ c₂ k' k₂ hc₂
  have : Mono (Z'.chart a') := mono_fromSpec (Z'.U a').2
  obtain rfl : φ₂' = φ' := congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _)
    (a₂ := CommRingCat.ofHom _) ((cancel_mono (Z'.chart a')).1 (k'.trans h'.symm)))
  have T := chart_tri Z hty k₂ h x.1
  obtain ⟨d, d1, d2⟩ := T x.2
  have e := M.chart k a₂ a i φ₂ φ d (k₂.trans h.symm) (k₂ ▸ hi) d1 (by rwa [← Category.assoc, k₂])
  rw [k₂] at e
  rw [e, ← _root_.mul_assoc, hs]
  exact (T.diag_mul (frame_ind (chart_frame Z k₂) _) (frame_ind (chart_frame Z h) _).1
    ((push_tri hf hT hty h' h x.1).diag (frame_ind (chart_frame Z h) _) (frame_ind (push_frame hf hT h' h) _) hc).2
    hc d2 hc₂).symm

theorem exists_unit (a' : Fin Z'.m) (i : Fin M.L.n) : ∃ s : Γ(Z'.X, (Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i)ˣ,
    ∀ (k : Type) [Field k] (w : Sp k ⟶ Z'.X), ⊤ ≤ w ⁻¹ᵁ ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i) →
      Rel f mu M a' i k w (valF w _ s.val) := by
  have := isReduced_model Z'
  have ex : ∀ (k : Type) [Field k] (w : Sp k ⟶ Z'.X), ⊤ ≤ w ⁻¹ᵁ ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i) →
      ∃ r c : k, r ≠ 0 ∧ c ≠ 0 ∧ ∀ s, Rel f mu M a' i k w s → s * r = c := fun k _ w hw => by
    obtain ⟨φ', h'⟩ := exists_fromSpec (Z'.U a').2 w fun q hq => (hw hq).1
    obtain ⟨a, φ, h⟩ := exists_chart hf hT (range_opn Z' h')
    obtain ⟨cf, c0, hc⟩ := exists_coeff (x := x) hf hT hty h' h
    exact ⟨_, _, val_ne M h fun q hq => (hw hq).2, c0, fun s hs => hs φ' a φ cf h' h hc⟩
  refine GlobalTheory.T.exists_unit_section_of_local_values _ _ (Rel f mu M a' i) (fun k _ w s s' hw h h' => ?_) (fun k _ w hw h => ?_) fun z hz => ?_
  · obtain ⟨r, c, r0, -, e⟩ := ex k w hw
    exact mul_right_cancel₀ r0 ((e s h).trans (e s' h').symm)
  · obtain ⟨r, c, -, c0, e⟩ := ex k w hw
    exact c0 ((e 0 h).symm.trans (zero_mul _))
  obtain ⟨a, φ₀, h₀⟩ := exists_chart hf hT (k := Z'.X.residueField z) (w := Z'.X.fromSpecResidueField z) (by
    rw [Scheme.range_fromSpecResidueField, ← Z'.cover, Set.singleton_subset_iff]
    exact Set.mem_iUnion.2 ⟨a', hz.1⟩)
  have hza : z ∈ f ⁻¹ᵁ (Z.U a).1 := by
    have := le_of_fromSpec (Z.U a).2 h₀ (Set.mem_univ (IsLocalRing.closedPoint (Z'.X.residueField z)))
    exact (congrArg (fun q => f q ∈ (Z.U a).1) (Scheme.fromSpecResidueField_apply z _)).mp this
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z'.X) (x := z)
    (U := ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i) ⊓ f ⁻¹ᵁ (Z.U a).1) ⟨hz, hza⟩
  have l₁ : V ≤ (Z'.U a').1 := fun q hq => (hle hq).1.1
  have l₂ : V ≤ f ⁻¹ᵁ (Z.U a).1 := fun q hq => (hle hq).2
  have l₃ : V ≤ f ⁻¹ᵁ ((Z.U a).1 ⊓ M.L.U i) := fun q hq => ⟨(hle hq).2, (hle hq).1.2⟩
  let ψ' : Γ(Z'.X, (Z'.U a').1) →+* Γ(Z'.X, V) := (Z'.X.presheaf.map (homOfLE l₁).op).hom
  let ψ : Γ(Z.X, (Z.U a).1) →+* Γ(Z'.X, V) := (f.appLE _ V l₂).hom
  have e' : spMap ψ' ≫ Z'.chart a' = hV.fromSpec := (Z'.U a').2.map_fromSpec hV _
  have e : spMap ψ ≫ Z.chart a = hV.fromSpec ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f (Z.U a).2 hV l₂
  obtain ⟨c, hc, -⟩ := (chart_frame Z e).2 x.1 _ ((push_frame hf hT e' e).1 x.1 x.2).1
    ((push_frame hf hT e' e).1 x.1 x.2).2
  refine ⟨V, c x.2 * (f.appLE _ V l₃).hom (M.r a i)⁻¹.val, hzV, fun q hq => (hle hq).1, fun k _ w hw => ?_⟩
  obtain ⟨χ, hχ⟩ := exists_fromSpec hV w hw
  have bc : ∀ {X : Scheme.{0}} {t : SAB H X} {A : Type} [CommRing A] (ρ : A →+* Γ(Z'.X, V)) (u : Vecs Dw t A) σ j,
      u.bc (χ.comp ρ) σ j = spMap (dualMap χ) ≫ u.bc ρ σ j := fun ρ u σ j => by
    rw [Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
    congr 2
    ext z <;> simp [dualMap]
  have hc' := GlobalTheory.LatDRFree.comb_map _ χ hc
  refine rel_of_one hf hT hty M (φ' := χ.comp ψ') (a := a) (φ := χ.comp ψ) (cf := fun j => χ (c j)) ?_ ?_
    (fun q hq => (l₃ (hw hq)).2) ?_ ?_
  · rw [← ModelRelProbe.spMap_comp, Category.assoc, e', hχ]
  · rw [← ModelRelProbe.spMap_comp, Category.assoc, e, ← Category.assoc, hχ]
  · rw [bc, funext (bc ψ _ x.1), ← hχ]
    simpa only [Category.assoc] using hc'
  · have v := valF_mul_inv (x := w ≫ f) (fun q hq => l₃ (hw hq)) (M.r a i)
    have v' : valF w V (c x.2) = χ (c x.2) := hχ ▸ valF_fromSpec hV χ _
    rw [valF_mul hw, valF_appLE f _ l₃ hw, v']
    linear_combination χ (c x.2) * v

omit hty in
theorem exists_pt (y : Z'.Pt) : ∃ P : PointsOfFlagModel.PtC (Y Z.i) y.C, (y.z ≫ f) ≫ Z.π = P.yt := by
  have e0 := map_π hf hT
  obtain ⟨b, π', r, hb, h⟩ := hT
  have := mono_spMap_subtype (Z.i.c.V W)
  have hσ : (IntermediateField.inclusion hf.1.2.1).toRingHom.comp (Z.i.c.V W).subtype = (Z'.i.c.V W).subtype.comp b :=
    RingHom.ext fun x => Subtype.ext (hb x).symm
  obtain ⟨e1, r, e2, e3⟩ := ModelRelProbe.transition_over (Y Z.i) (Y Z'.i) b τ ⟨π', mu, r, h⟩ _ hσ
  refine ⟨⟨y.P.alg.comp b, y.P.fK.comp (IntermediateField.inclusion hf.1.2.1).toRingHom, ?_, y.P.y ≫ r, ?_, y.P.yt ≫ τ,
    ?_, ?_⟩, ?_⟩
  · rw [← RingHom.comp_assoc, y.P.compat, RingHom.comp_assoc, RingHom.comp_assoc, hσ]
  · rw [Category.assoc, e3, reassoc_of% y.P.y_over, ModelRelProbe.spMap_comp]
  · rw [Category.assoc, e1, reassoc_of% y.P.yt_over, ModelRelProbe.spMap_comp]
  · rw [reassoc_of% y.P.ext, e2, Category.assoc]
  · rw [Category.assoc, e0, reassoc_of% y.z_π]

include M in
theorem nonempty_pull (hB : HTBoundSt) (hp : p.Prime) (hx : letterOf Dw st = some x) :
    Nonempty (LineModel Z' b st x) := by
  choose s hs using exists_unit hf hT hty M
  have inv : ∀ {k : Type} [Field k] {w : Sp k ⟶ Z'.X} {a' i}, ⊤ ≤ w ⁻¹ᵁ ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i) →
      valF w _ (s a' i)⁻¹.val = (valF w _ (s a' i).val)⁻¹ ∧ valF w _ (s a' i).val ≠ 0 := fun h =>
    ⟨eq_inv_of_mul_eq_one_right (valF_mul_inv h _), left_ne_zero_of_mul_eq_one (valF_mul_inv h _)⟩
  refine ⟨⟨pullLB f M.L, fun a' i => (s a' i)⁻¹, fun k _ w a' i i' hw => ?_,
    fun k _ a' a₂ i φ' φ₂ cf he hi hcf hc => ?_, fun y a' i φ' h' hi => ?_⟩⟩
  · have w₁ : ⊤ ≤ w ⁻¹ᵁ ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i) := fun q hq => ⟨(hw hq).1, (hw hq).2.1⟩
    have w₂ : ⊤ ≤ w ⁻¹ᵁ ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i') := fun q hq => ⟨(hw hq).1, (hw hq).2.2⟩
    obtain ⟨φ', h'⟩ := exists_fromSpec (Z'.U a').2 w fun q hq => (hw hq).1
    obtain ⟨a, φ, h⟩ := exists_chart hf hT (range_opn Z' h')
    obtain ⟨cf, -, hc⟩ := exists_coeff (x := x) hf hT hty h' h
    have e := (hs a' i k w w₁ φ' a φ cf h' h hc).trans (hs a' i' k w w₂ φ' a φ cf h' h hc).symm
    rw [M.trans k (w ≫ f) a i i' fun q hq => ⟨le_of_fromSpec (Z.U a).2 h hq, (hw hq).2⟩, ← _root_.mul_assoc] at e
    replace e := mul_right_cancel₀ (val_ne M h fun q hq => (hw hq).2.1) e
    have g : valF w _ ((pullLB f M.L).g i i').val = valF (w ≫ f) _ (M.L.g i i').val :=
      valF_appLE (x := w) (U := f ⁻¹ᵁ M.L.U i ⊓ f ⁻¹ᵁ M.L.U i') f _ le_rfl (fun q hq => (hw hq).2) _
    have n := (inv w₁).2
    refine (inv w₂).1.trans (Eq.trans ?_ (congrArg₂ (· * ·) g (inv w₁).1).symm)
    rw [e] at n ⊢
    have := right_ne_zero_of_mul n
    have := left_ne_zero_of_mul n
    field_simp
  · have w₁ : ⊤ ≤ (spMap φ' ≫ Z'.chart a') ⁻¹ᵁ ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i) := fun q hq =>
      ⟨le_of_fromSpec (Z'.U a').2 rfl hq, hi hq⟩
    have w₂ : ⊤ ≤ (spMap φ' ≫ Z'.chart a') ⁻¹ᵁ ((Z'.U a₂).1 ⊓ f ⁻¹ᵁ M.L.U i) := fun q hq =>
      ⟨le_of_fromSpec (Z'.U a₂).2 he.symm hq, hi hq⟩
    obtain ⟨a, φ, h⟩ := exists_chart hf hT (range_opn Z' (φ := φ') rfl)
    obtain ⟨c₁, -, hc₁⟩ := exists_coeff (x := x) hf hT hty rfl h
    obtain ⟨c₂, -, hc₂⟩ := exists_coeff (x := x) hf hT hty he.symm h
    have e := (push_tri hf hT hty rfl h x.1).diag_mul (frame_ind (chart_frame Z h) _)
      (frame_ind (push_frame hf hT rfl h) _).1 hcf ((comb_push mu
        (by rw [Category.assoc _ f, map_π hf hT, Category.assoc]) (frame_ind (chart_frame Z' rfl) _).1
        ((frame_ind (chart_frame Z' he.symm) _).1 x.2) cf).2 (by rwa [Category.assoc])) hc₁ hc₂
    rw [← hs a' i k _ w₁ φ' a φ c₁ rfl h hc₁, ← hs a₂ i k _ w₂ φ₂ a φ c₂ he.symm h hc₂, ← _root_.mul_assoc] at e
    replace e := mul_right_cancel₀ (val_ne M h hi) e
    have n := (inv w₂).2
    refine (inv w₁).1.trans (Eq.trans ?_ (congrArg (· * cf x.2) (inv w₂).1).symm)
    rw [e] at n ⊢
    have := right_ne_zero_of_mul n
    have := left_ne_zero_of_mul n
    field_simp
  · have hi' : ⊤ ≤ (y.gen ≫ f) ⁻¹ᵁ M.L.U i := fun q _ => hi (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
    have w₁ : ⊤ ≤ y.gen ⁻¹ᵁ ((Z'.U a').1 ⊓ f ⁻¹ᵁ M.L.U i) := fun q hq => ⟨le_of_fromSpec (Z'.U a').2 h' hq, hi' hq⟩
    obtain ⟨a, φ, h⟩ := exists_chart hf hT (range_opn Z' h')
    obtain ⟨c, c0, hc⟩ := exists_coeff (x := x) hf hT hty h' h
    obtain ⟨P, hP⟩ := exists_pt hf hT y
    have N := M.norm ⟨y.C, P, y.z ≫ f, hP⟩ a i φ (h.trans (Category.assoc _ _ _)) hi
    have g₀ : Mdl.Pt.gen (Z := Z) ⟨y.C, P, y.z ≫ f, hP⟩ = y.gen ≫ f := (Category.assoc _ _ _).symm
    have g₁ : y.gen ≫ Z'.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z'.π := Category.assoc _ _ _
    have g₂ : (y.gen ≫ f) ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ (y.z ≫ Z'.π) ≫ τ := by
      rw [Category.assoc, map_π hf hT, reassoc_of% g₁, Category.assoc]
    have F := chart_frame Z h
    have F' := push_frame hf hT h' h
    have T := push_tri hf hT hty h' h
    have e := hs a' i _ _ w₁ φ' a φ c h' h hc
    rw [g₀] at N
    rw [g₂] at N F F' T hc
    rw [g₁, lnStep_push mu b _ (ext_unique _ _) (fun σ j => g₁ ▸ ((chart_frame Z' h').1 σ j).1),
      lnStep_tri hB hp y.C b _ (ext_unique _ _) F F' T hx hc, ← e, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 (inv w₁).2) (norm_ne_zero_iff.2 (val_ne M h hi'))]
    have v := congrArg (fun z => Real.log ‖z‖) (inv w₁).1
    simp only [norm_inv, Real.log_inv] at v
    exact (congrArg (· + _) v).trans (by linarith)

end Main

theorem lineModel_pull : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (Z Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), IsMap Z' Z f → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ b st x, letterOf Dw st = some x → Nonempty (LineModel Z b st x) → Nonempty (LineModel Z' b st x) := by
  intro hB E _ _ _ H Dw Xo p W Y i₀ hp _ hN Z Z' f hf hty b st x hx ⟨M⟩
  obtain ⟨τ, mu, hT⟩ := exists_trans hN.1 hf.1.1 hf.1.2.1
  exact nonempty_pull hf hT hty M hB hp hx

end GlobalTheory.ShFam.Pad.Pull
