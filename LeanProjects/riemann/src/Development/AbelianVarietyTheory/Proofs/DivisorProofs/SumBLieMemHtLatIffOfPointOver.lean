import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomExtOfGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionMap

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
open GlobalTheory.KernelNoTorsion
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.IndepPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}

theorem corr_nilp {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] {x : specO O R ⟶ P.Gt}
    {y : specO O R ⟶ P.G} (h : Corr P x y) (φ : R →ₐ[O] R') (hR : IsNilpotent (p : R')) :
    P.cmp R' hR (ptMap φ ≫ x) = ptMap φ ≫ y := by
  obtain ⟨m, hm⟩ := id hR
  let ψ : (R ⧸ Ideal.span {(p : R) ^ m}) →ₐ[O] R' := Ideal.Quotient.liftₐ _ φ fun c hc => by
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    simp [hm]
  have e : ptMap φ = ptMap ψ ≫ ptMap (redR p O R m) := by
    rw [TangentPow.ptMap_comp_ptMap]
    rfl
  rw [e, Category.assoc, Category.assoc, h, P.cmp_nat _ _ (nilpR m)]

def ptsHom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) :
    (T ⟶ A) →* (T ⟶ B) :=
  MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y _

variable (p) in

def tateIso {A B : Out.PolAV (Sp C)} (α : A.A ≅ B.A) [IsMonHom α.hom] : TateA A p ≃ₗ[ℤ_[p]] TateA B p :=
  LinearEquiv.ofLinearMap (Tate.map p (ptsHom α.hom _)) (Tate.map p (ptsHom α.inv _))
    (LinearMap.ext fun t => Tate.ext fun n => by
      change (t.lev n ≫ α.inv) ≫ α.hom = t.lev n
      simp)
    (LinearMap.ext fun t => Tate.ext fun n => by
      change (t.lev n ≫ α.hom) ≫ α.inv = t.lev n
      simp)

theorem lev_tateIso {A B : Out.PolAV (Sp C)} (α : A.A ≅ B.A) [IsMonHom α.hom] (t : TateA A p) (n : ℕ) :
    (tateIso p α t).lev n = t.lev n ≫ α.hom := rfl

variable [IsAlgClosed C] [CharZero C]

theorem weil_iso {A B : Out.PolAV (Sp C)} (α : A.A ≅ B.A) [IsMonHom α.hom] (hL : LBIso A.L (B.L.pull α.hom.left))
    {k : ℕ} (hk : 1 ≤ k) {z s : ChTor.Pts A.A} (hz : z ^ k = 1) (hs : s ^ k = 1) :
    weil B k (z ≫ α.hom) (s ≫ α.hom) = weil A k z s := by
  have hl : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨w, hw⟩ := hL
  have h1 : (z ≫ α.hom) ^ k = 1 := by rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  have h2 : (s ≫ α.hom) ^ k = 1 := by rw [← MonObj.pow_comp, hs, MonObj.one_comp]
  exact (weilIs_iff hk hz hs _).1 ((GlobalTheory.weilIs_iso_iff hl.globalFns hl.cube A B α w hw k z s hz hs _).1
    ((weilIs_iff hk h1 h2 _).2 rfl))

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]

omit [Algebra ℤ_[p] O] in

theorem weilChar_tateIso (α : P.A.A ≅ P'.A.A) [IsMonHom α.hom] (hL : LBIso P.A.L (P'.A.L.pull α.hom.left))
    (g : P.G ⟶ P'.G) (hgen : α.hom.left ≫ P'.gen = P.gen ≫ g.left) (t : P.T) {n : ℕ}
    {d : torsion P.Gt (p ^ n) ⟶ torsion P'.Gt (p ^ n)}
    (hd : ∀ (R : Type) [CommRing R] [Algebra O R] (hR : IsNilpotent (p : R)) (w : specO O R ⟶ torsion P.Gt (p ^ n)),
      P'.cmp R hR (w ≫ d ≫ torsion.ι P'.Gt (p ^ n)) = P.cmp R hR (w ≫ torsion.ι P.Gt (p ^ n)) ≫ g) :
    (P.weilChar t).χ n = d ≫ (P'.weilChar (tateIso p α t)).χ n := P.char_ext fun w => by
  have e1 : P'.toG ((w ≫ d) ≫ torsion.ι P'.Gt (p ^ n)) = P.toG (w ≫ torsion.ι P.Gt (p ^ n)) ≫ g :=
    P.hom_ext_red fun m => by
      rw [Point.red_toG, ← Category.assoc _ (P.toG _), Point.red_toG, ← Category.assoc _ w, ← hd]
      simp only [Category.assoc]
  have e2 : P.toA (w ≫ torsion.ι P.Gt (p ^ n)) ≫ α.hom = P'.toA ((w ≫ d) ≫ torsion.ι P'.Gt (p ^ n)) := by
    rw [Point.eq_toA_iff, e1, Over.comp_left, Over.comp_left, Category.assoc, hgen, ← Category.assoc,
      (P.eq_toA_iff _ _).1 rfl, Category.assoc]
  rw [← Category.assoc, P.isWeilChar_weilChar, P'.isWeilChar_weilChar, ← e2, lev_tateIso]
  exact congrArg Units.val (weil_iso α hL (one_le_ppow p n) (P.toA_pow w) (t.lev_pow n)).symm

theorem al₀_tateIso (α : P.A.A ≅ P'.A.A) [IsMonHom α.hom] (hL : LBIso P.A.L (P'.A.L.pull α.hom.left))
    (g : P.G ⟶ P'.G) (hg : IsMonHom g) (hgen : α.hom.left ≫ P'.gen = P.gen ≫ g.left)
    {x : LieG P.Gt} {x' : LieG P'.Gt} {y : specO O (DualNumber O) ⟶ P.G} (hx : Corr P x.1 y)
    (hx' : Corr P' x'.1 (y ≫ g)) (t : P.T) : (P'.al₀ (tateIso p α t)).1 x' = (P.al₀ t).1 x := by
  have key : ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R], (p : R) ^ n = 0 →
      algebraMap O R ((dlogTv (P'.weilChar (tateIso p α t))).1 x') =
        algebraMap O R ((dlogTv (P.weilChar t)).1 x) := fun n R _ _ hR => by
    obtain ⟨d, hd⟩ := GlobalTheory.RaynaudTorsionMap.exists_torsion_map p C v O Λ P P' g hg (p ^ n) (one_le_ppow p n)
    have hn : IsNilpotent (p : DualNumber R) := ⟨n, by
      rw [← map_natCast (algebraMap R (DualNumber R)), ← map_pow, hR, map_zero]⟩
    have hw : _ = ptMap (dualBC (Algebra.ofId O R)) ≫ x.1 := HodgeTateImage.lift_ι hR x
    have h1 := isAl_dlogTv (P.weilChar t) n _ hR x _ hw
    have h2 := isAl_dlogTv (P'.weilChar (tateIso p α t)) n _ hR x' (HodgeTateImage.lift hR x ≫ d)
      ((P'.cmp _ hn).injective (by
        rw [Category.assoc, hd, hw, corr_nilp hx, corr_nilp hx', Category.assoc]))
    rw [Category.assoc, ← weilChar_tateIso α hL g hgen t hd, h1] at h2
    simpa [Algebra.algebraMap_eq_smul_one] using (congrArg TrivSqZeroExt.snd h2).symm
  exact HodgeTateImage.eq_of_forall (p := p) fun n => key n _ (HodgeTateImage.pow_quot n)

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (e : P.T ≃ₗ[ℤ_[p]] P'.T)

theorem exists_bLie_eq (he : ∀ s t, weilT P'.A p (e s) (e t) = weilT P.A p s t) :
    ∃ u : ℤ_[p], ∀ (x : LieG P.Gt) (x' : LieG P'.Gt), (∀ t, (P'.al₀ (e t)).1 x' = (P.al₀ t).1 x) →
      P'.bLie x' = u • e.toLinearMap.baseChange C (P.bLie x) := by
  let u : ℤ_[p] := P.eps.equiv.symm (P'.eps.equiv 1)
  have h1 : ∀ s t, pairT P.A P.eps s t = u * pairT P'.A P'.eps (e s) (e t) := fun s t => by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
    change P.eps.equiv.symm (weilT P.A p s t) =
      P.eps.equiv.symm (P'.eps.equiv (P'.eps.equiv.symm (weilT P'.A p (e s) (e t))))
    rw [LinearEquiv.apply_symm_apply, he]
  have h2 : ∀ (w : P.V) (t : P.T), P.pairV w (1 ⊗ₜ t) =
      P'.pairV (u • e.toLinearMap.baseChange C w) (1 ⊗ₜ e t) := fun w t => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, smul_add, LinearMap.add_apply, ha, hb]
    | tmul c s =>
      rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', Point.pairV_tmul, Point.pairV_tmul, h1, mul_comm u,
        mul_smul, smul_mul_assoc]
      rfl
  refine ⟨u, fun x x' h => P'.eq_of_pairV fun t => ?_⟩
  obtain ⟨t, rfl⟩ := e.surjective t
  rw [← h2, Point.pairV_bLie, Point.pairV_bLie, h]

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem map_latT_le : P.latT.map ((e.toLinearMap.baseChange C).restrictScalars O) ≤ P'.latT := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | tmul c t => exact ⟨c ⊗ₜ e t, by rw [Point.inclT_tmul, Point.inclT_tmul]; rfl⟩

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C] in

theorem isEquivariant_baseChange (ha : ∀ a t, e (P.actT a t) = P'.actT a (e t)) :
    IsEquivariant P.actV P'.actV (e.toLinearMap.baseChange C) := fun a x => by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c t => exact congrArg (c ⊗ₜ ·) (ha a t)

omit [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem exists_corr {Y S : Scheme.{0}} {ψ : P.A.A.left ⟶ Y} {ψ' : P'.A.A.left ⟶ Y} {s : Y ⟶ S} {y : Sp C ⟶ S}
    (hψ : IsPullback ψ' P'.A.A.hom s y) (α : P.A.A ⟶ P'.A.A) (hα : α.left ≫ ψ' = ψ) (g : P.G ⟶ P'.G)
    (hgen : α.left ≫ P'.gen = P.gen ≫ g.left) {x : LieG P.Gt} {x' : LieG P'.Gt} {u : Sp (DualNumber C) ⟶ Y}
    (h : LieTie P ψ x u) (h' : LieTie P' ψ' x' u) : ∃ y, Corr P x.1 y ∧ Corr P' x'.1 (y ≫ g) := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  have e1 : w.left ≫ α.left = w'.left := hψ.hom_ext (by rw [Category.assoc, hα, h2, h2'])
    ((Over.w (w ≫ α)).trans (Over.w w').symm)
  have : IsSchemeTheoreticallyDominant (spMap (dualMap (algebraMap O C))) :=
    (schemeDominant_specMap_iff _).2 fun a b hab => TrivSqZeroExt.ext
      (P.integers.hom_inj (by simpa [dualMap] using congrArg TrivSqZeroExt.fst hab))
      (P.integers.hom_inj (by simpa [dualMap, Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd hab))
  have := P'.semi.separated
  have e2 : xG.1 ≫ g = xG'.1 := Over.OverMorphism.ext (ext_of_schDom P'.G.hom
    ((Over.w (xG.1 ≫ g)).trans (Over.w xG'.1).symm) _ (by
      rw [← h3', ← e1, Over.comp_left, ← Category.assoc, ← h3, Category.assoc, Category.assoc, hgen]))
  exact ⟨xG.1, h1, e2 ▸ h1'⟩

end GlobalTheory.CompHt.IndepPoint

namespace GlobalTheory.CompHt

open IndepPoint

theorem sum_bLie_mem_htLat_of_pointOver {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}
    [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C]
    [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] {T : CDVR} {x₀ : Sp T.Fr ⟶ Xo.X} {k : T.Fr →+* C}
    {kO kO' : T.V →+* O} {P P' : Point p v O (𝓞 E)} {ψ : P.A.A.left ⟶ Xo.univ.t.G.left}
    {ψ' : P'.A.A.left ⟶ Xo.univ.t.G.left} (h : PointOver P x₀ k kO ψ) (h' : PointOver P' x₀ k kO' ψ')
    (τ : E →+* ℂ) {n : ℕ} {u : Fin n → (Sp (DualNumber C) ⟶ Xo.univ.t.G.left)} {x : Fin n → LieG P.Gt}
    {x' : Fin n → LieG P'.Gt} (hx : ∀ j, LieTie P ψ (x j) (u j)) (hx' : ∀ j, LieTie P' ψ' (x' j) (u j))
    (a : Fin n → C) (ha : ∑ j, a j • P.bLie (x j) ∈ htLat c P τ) : ∑ j, a j • P'.bLie (x' j) ∈ htLat c P' τ := by
  classical
  obtain ⟨α, g, hα, hg, h1, h2, h3, h4⟩ := GlobalTheory.CompHt.pointOver_iso E H Dw l Xo p C v O T x₀ k kO kO' P P' ψ ψ' h h'
  let e : P.T ≃ₗ[ℤ_[p]] P'.T := tateIso p α
  obtain ⟨r, hr⟩ := exists_bLie_eq e fun s t => Tate.ext fun m =>
    weil_iso α h4 (one_le_ppow p m) (s.lev_pow m) (t.lev_pow m)
  have hb : ∀ j, P'.bLie (x' j) = r • e.toLinearMap.baseChange C (P.bLie (x j)) := fun j => hr _ _ fun t => by
    obtain ⟨y, hy, hy'⟩ := exists_corr h'.isGrpPullback.1 α.hom h1 g h2 (hx j) (hx' j)
    exact al₀_tateIso α h4 g hg h2 hy hy' t
  have he := isEquivariant_baseChange e fun b t => Tate.ext fun m => by
    change (t.lev m ≫ P.oA.act b) ≫ α.hom = (t.lev m ≫ α.hom) ≫ P'.oA.act b
    rw [Category.assoc, Category.assoc, h3]
  have hs : ∑ j, a j • P'.bLie (x' j) =
      algebraMap ℤ_[p] O r • e.toLinearMap.baseChange C (∑ j, a j • P.bLie (x j)) := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb, map_smul, smul_comm, ← algebraMap_smul C (algebraMap ℤ_[p] O r), ← IsScalarTower.algebraMap_apply,
      algebraMap_smul]
  rw [hs]
  refine Submodule.smul_mem _ _ ?_
  unfold htLat at ha ⊢
  split_ifs at ha ⊢
  · refine eigQuotLat_mono _ _ _ (map_latT_le e) ?_
    rw [← map_eigQuotLat _ _ he]
    exact Submodule.mem_map_of_mem ha
  · obtain ⟨ha1, ha2⟩ := (mem_eigSubLat _).1 ha
    refine (mem_eigSubLat _).2 ⟨map_latT_le e (Submodule.mem_map_of_mem ha1), mem_eigenSub.2 fun b => ?_⟩
    rw [← he, mem_eigenSub.1 ha2 b, map_smul]

theorem sum_bLie_mem_htLat_iff_of_pointOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (x₀ : Sp T.Fr ⟶ Xo.X) (k : T.Fr →+* C) (kO kO' : T.V →+* O) (P P' : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (ψ' : P'.A.A.left ⟶ Xo.univ.t.G.left), PointOver P x₀ k kO ψ → PointOver P' x₀ k kO' ψ' → ∀ (τ : E →+* ℂ) (n : ℕ) (u : Fin n → (Sp (DualNumber C) ⟶ Xo.univ.t.G.left)) (x : Fin n → LieG P.Gt) (x' : Fin n → LieG P'.Gt), (∀ j, LieTie P ψ (x j) (u j)) → (∀ j, LieTie P' ψ' (x' j) (u j)) → ∀ a : Fin n → C, ∑ j, a j • P.bLie (x j) ∈ htLat c P τ ↔ ∑ j, a j • P'.bLie (x' j) ∈ htLat c P' τ := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T x₀ k kO kO' P P' ψ ψ' h h' τ n u x x' hx hx' a
  exact ⟨sum_bLie_mem_htLat_of_pointOver h h' τ hx hx' a, sum_bLie_mem_htLat_of_pointOver h' h τ hx' hx a⟩

end GlobalTheory.CompHt
