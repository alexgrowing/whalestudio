import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieLocBasis
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap eigLat IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

theorem finrank_range_idem' {V k : Type} [CommRing V] [IsLocalRing V] [CommRing k] [IsLocalRing k] [CharZero k]
    (f : V →+* k) {n : ℕ} (e : Module.End V (Fin n → V)) (e' : Module.End k (Fin n → k)) (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (h : ∀ c, e' (f ∘ c) = f ∘ e c) :
    Module.finrank V (LinearMap.range e) = Module.finrank k (LinearMap.range e') := by
  classical
  have tr : ∀ {R : Type} [CommRing R] [IsLocalRing R] (e : Module.End R (Fin n → R)), IsIdempotentElem e →
      ∑ i, e (Pi.single i 1) i = (Module.finrank R (LinearMap.range e) : R) := fun {R} _ _ e he => by
    have := Formalism.L2.Pj.LocFrM.range_free e he
    have k1 : IsIdempotentElem (1 - e) := he.one_sub
    have kr : LinearMap.ker e = LinearMap.range (1 - e) := by
      ext v
      refine ⟨fun hv => ⟨v, by simp [LinearMap.mem_ker.1 hv]⟩, ?_⟩
      rintro ⟨w, rfl⟩
      simpa [sub_eq_zero] using (LinearMap.congr_fun he.eq w).symm
    have : Module.Free R (LinearMap.ker e) := kr ▸ Formalism.L2.Pj.LocFrM.range_free _ k1
    have : Module.Finite R (LinearMap.ker e) := kr ▸ Module.Finite.range _
    rw [← (LinearMap.IsIdempotentElem.isProj_range e he).trace, LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin n))]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  refine Nat.cast_injective (R := k) ?_
  rw [← tr e' he', ← map_natCast f, ← tr e he, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i 1 : Fin n → k) = f ∘ Pi.single i 1 from funext fun j => by
    by_cases hj : j = i <;> simp [hj, Pi.single_apply], h]
  rfl

theorem exists_generisation {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (hU : IsOpen U) (hd : Dense U) (y : X) : ∃ g ∈ U, g ⤳ y := by
  have hC := irreducibleComponent_mem_irreducibleComponents y
  have hg := (isIrreducible_irreducibleComponent (x := y)).isGenericPoint_genericPoint isClosed_irreducibleComponent
  obtain ⟨o, ho, hne, hle⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨p, hp, hpU⟩ := hd.inter_open_nonempty o ho hne
  exact ⟨_, (hg.mem_open_set_iff hU).2 ⟨p, hle hp, hpU⟩, hg.specializes mem_irreducibleComponent⟩

theorem exists_stalk_factor {Y : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ Y) (y : Y)
    (h : x (IsLocalRing.closedPoint R) ⤳ y) :
    ∃ ψ : Y.presheaf.stalk y →+* R, spMap ψ ≫ Y.fromSpecStalk y = x := by
  refine ⟨(Y.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of R) x).hom, ?_⟩
  show Spec.map (Y.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of R) x) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}

instance actHom (a : 𝓞 E) : IsMonHom (t.act.act a) := t.act.hom a

section Chart

variable {L : Type} [CommRing L] {x : Sp L ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G}

theorem vec_inj (hx : IsUnivChart _ n xc) {c₁ c₂ : Fin n → L} (h : vec t x xc c₁ = vec t x xc c₂) : c₁ = c₂ :=
  ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (push_ext h)

theorem vec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    vec t x xc (tmap hx ((Over.pullback x).map (t.act.act a)) cc) = vec t x xc cc ≫ (t.act.act a).left := by
  show (tvec (x := xc) (tmap hx _ cc)).left ≫ _ = ((tvec (x := xc) cc).left ≫ _) ≫ _
  rw [ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, Over.comp_left, Category.assoc, Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

theorem vec_smul (hx : IsUnivChart _ n xc) (s : L) (cc : Fin n → L) :
    vec t x xc (s • cc) = spMap (epsMul s) ≫ vec t x xc cc := by
  show (tvec (x := xc) (s • cc)).left ≫ _ = _
  rw [ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx]
  exact Category.assoc _ _ _

theorem vec_eig_iff (hx : IsUnivChart _ n xc) (χ : 𝓞 E → L) (cc : Fin n → L) :
    (∀ a, vec t x xc cc ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ vec t x xc cc) ↔
      cc ∈ eigLat hx (fun a => (Over.pullback x).map (t.act.act a)) χ := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
  refine forall_congr' fun a => ?_
  rw [← vec_tmap hx, ← vec_smul hx]
  exact ⟨vec_inj hx, fun h => by rw [h]⟩

def rho (hx : IsUnivChart _ n xc) : 𝓞 E →+* Module.End L (Fin n → L) :=
  have add : ∀ a b, tmap hx ((Over.pullback x).map (t.act.act (a + b))) =
      tmap hx ((Over.pullback x).map (t.act.act a)) + tmap hx ((Over.pullback x).map (t.act.act b)) :=
    fun a b => LinearMap.ext fun cc => ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (by
      rw [LinearMap.add_apply, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx,
        ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, t.act.add, Functor.map_mul,
        MonObj.comp_mul])
  { toFun := fun a => tmap hx ((Over.pullback x).map (t.act.act a))
    map_one' := LinearMap.ext fun cc => vec_inj hx (by rw [vec_tmap, t.act.one]; exact Category.comp_id _)
    map_mul' := fun a b => LinearMap.ext fun cc => vec_inj hx (by
      rw [Module.End.mul_apply, vec_tmap, vec_tmap, vec_tmap, mul_comm a b, t.act.mul, Category.assoc]; rfl)
    map_zero' := by
      have := add 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    map_add' := add }

end Chart

variable (t) in
theorem exists_chart {L : Type} [CommRing L] [IsLocalRing L] (x : Sp L ⟶ X) :
    ∃ (n : ℕ) (xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G),
      IsUnivChart _ n xc := by
  have : Smooth ((Over.pullback x).obj t.G).hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom _)
    infer_instance
  exact ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj t.G)

variable {l : Level H} (c : Coeff l)

abbrev eig {L : Type} [CommRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc)
    (τ : E →+* ℂ) : Submodule L (Fin n → L) :=
  eigLat hx (fun a => (Over.pullback x).map (t.act.act a)) fun a => φ (embK c τ a)

theorem eig_bc {L : Type} [CommRing L] [IsLocalRing L] (φ : c.F →+* L) {x : Sp L ⟶ X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj t.G} (hx : IsUnivChart _ n xc)
    {k : Type} [CommRing k] [IsLocalRing k] (ψ : L →+* k) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback (spMap ψ ≫ x)).obj t.G)
      (hx' : IsUnivChart _ n xc'), ∀ τ, Module.Free k (eig c (ψ.comp φ) hx' τ) ∧
        Module.Finite k (eig c (ψ.comp φ) hx' τ) ∧
        Module.finrank L (eig c φ hx τ) = Module.finrank k (eig c (ψ.comp φ) hx' τ) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ (τ : E →+* ℂ) {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ X}
      {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj t.G}
      (hx : IsUnivChart _ n xc), IsIdempotentElem (proj (rho hx) (embK c) α τ) ∧
        LinearMap.range (proj (rho hx) (embK c) α τ) = eig c (algebraMap c.F R) hx τ :=
    fun τ {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) (proj (rho hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx) (embK c τ) m → proj (rho hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rho hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨LinearMap.ext fun m => e₂ _ (e₁ m), Submodule.ext fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun ⟨m', h⟩ => h ▸ e₁ m', fun h => ⟨m, e₂ m h⟩⟩
  letI : Algebra c.F L := φ.toAlgebra
  letI : Algebra L k := ψ.toAlgebra
  letI : Algebra c.F k := (ψ.comp φ).toAlgebra
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (algebraMap L k ∘ cc) = algebraMap L k ∘ rho hx a cc :=
    fun a cc => vec_inj hx' (by
      show vec t _ xc' (tmap hx' _ _) = vec t _ xc' (_ ∘ tmap hx _ _)
      rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
  have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rho hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  refine ⟨xc', hx', fun τ => ?_⟩
  have r := finrank_range_idem' (algebraMap L k) _ _ (key τ hx).1 (key τ hx').1 (pr _)
  have fr := Formalism.L2.Pj.LocFrM.range_free _ (key τ hx').1
  have fi : Module.Finite k (LinearMap.range (proj (rho hx') (embK c) α τ)) := Module.Finite.range _
  rw [(key τ hx').2] at r fr fi
  rw [(key τ hx).2] at r
  exact ⟨fr, fi, r⟩

variable {Dw : Datum H} {Xo : Moduli Dw l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem finrank_geom (Z : Model Xo c β) {k : Type} [Field k] [IsAlgClosed k] (φ : c.F →+* k) (z : Sp k ⟶ Xo.XF c)
    (hz : z ≫ pullback.snd _ _ = spMap φ) {x : Sp k ⟶ Z.X} (hzx : z ≫ Z.jQ ≫ pullback.fst _ _ = x) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G} (hx : IsUnivChart _ n xc)
    (τ : E →+* ℂ) : Module.finrank k (eig c φ hx τ) = Dw.mult τ := by
  let gam : KA l →+* k := φ.comp (IntermediateField.inclusion c.le).toRingHom
  have hgam : z ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap gam := by
    rw [pullback.condition, ← Category.assoc, hz]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hd := (Z.oF.geom k z gam hgam).1
  let τ' : 𝓞 E →+* k := φ.comp (embK c τ)
  have key : ∀ N, LieMult Z.oF.t.act z τ' N → Module.finrank k (eig c φ hx τ) = N :=
    fun N h => ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult Z.m.cart hzx hx Z.oF.t.act
      Z.t.act.act Z.m.act _ (fun a => rfl) τ' h
  have hinj : Function.Injective φ := RingHom.injective _
  have e0 : τ' H.rt = gam (baseKA l).ρ ↔ τ (H.rt : E) = H.rt0 := by
    constructor
    · intro h
      have h' := @hinj (embK c τ H.rt) (IntermediateField.inclusion c.le (baseKA l).ρ) h
      exact congrArg (fun z : c.F => (z : ℂ)) h'
    · intro h
      have h' : embK c τ H.rt = IntermediateField.inclusion c.le (baseKA l).ρ := Subtype.ext h
      exact congrArg φ h'
  unfold Datum.mult
  split_ifs with h
  · exact key _ ((hd τ').1 (e0.2 h))
  · exact key _ ((hd τ').2 (fun h' => h (e0.1 h')))

theorem eigFrame_of_basis (Z : Model Xo c β) {R : Type} [CommRing R] (φ : c.F →+* R) {x : Sp R ⟶ Z.X} {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G} (hx : IsUnivChart _ n xc)
    (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ)) : Nonempty (EigFrame Z φ x) := by
  refine ⟨⟨fun τ i => vec Z.t x xc (B τ i), fun τ i => vec_tan hx _, fun τ i => (vec_eig_iff hx _ _).2 (B τ i).2,
    fun τ w hw he => ?_⟩⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx w hw
  let v : eig c φ hx τ := ⟨cc, (vec_eig_iff hx _ _).1 he⟩
  have k : ∀ a, IsCombAtG Z.t x (fun i => vec Z.t x xc (B τ i)) a (vec Z.t x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end GlobalTheory.ShFam.EigLoc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.EigLoc in

theorem GlobalTheory.ShFam.EigLoc.exists_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] [IsLocalRing R] (φ : c.F →+* R) (x : Sp R ⟶ gen Z), x ≫ genStr Z = spMap φ → Nonempty (EigFrame Z φ (x ≫ genι Z)) := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ _ φ x hφ
  have : IsProper Z.s := projProper O Z.X Z.s Z.proj
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  let y : gen Z := x (IsLocalRing.closedPoint R)
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_generisation Z.jQ.isOpenEmbedding.isOpen_range Z.jQ_dense y
  let L : Type := (gen Z).presheaf.stalk y
  let xL : Sp L ⟶ gen Z := (gen Z).fromSpecStalk y
  let φL : c.F →+* L := (Spec.preimage (xL ≫ genStr Z)).hom
  have hφL : spMap φL = xL ≫ genStr Z := Spec.map_preimage _
  have hov : ∀ {S : Type} [CommRing S] (ψ : L →+* S), (spMap ψ ≫ xL) ≫ genStr Z = spMap (ψ.comp φL) := fun ψ => by
    rw [Category.assoc, ← hφL]
    exact (Spec.map_comp _ _).symm
  let k : Type := AlgebraicClosure ((Xo.XF c).residueField p)
  let z : Sp k ⟶ Xo.XF c := spMap (algebraMap ((Xo.XF c).residueField p) k) ≫ (Xo.XF c).fromSpecResidueField p
  have hz : (z ≫ Z.jQ) (IsLocalRing.closedPoint k) = Z.jQ p := by
    refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ ?_)
    exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨ψk, hψk⟩ := exists_stalk_factor (z ≫ Z.jQ) y (hz ▸ hp)
  obtain ⟨ψ, hψ⟩ := exists_stalk_factor x y specializes_rfl
  change spMap ψk ≫ xL = _ at hψk
  change spMap ψ ≫ xL = _ at hψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (xL ≫ genι Z)
  obtain ⟨xk, hxk, hk⟩ := eig_bc c φL hx ψk
  obtain ⟨xR, hxR, hR⟩ := eig_bc c φL hx ψ
  have hzs : z ≫ pullback.snd _ _ = spMap (ψk.comp φL) := by
    rw [← hov, hψk, Category.assoc z, Z.jQ_over]
  have rk : ∀ τ, Module.finrank R (eig c (ψ.comp φL) hxR τ) = Dw.mult τ := fun τ =>
    (hR τ).2.2.symm.trans ((hk τ).2.2.trans (finrank_geom c Z _ z hzs
      (by rw [← Category.assoc, ← hψk, Category.assoc]) hxk τ))
  have e : φ = ψ.comp φL := spMap_inj (by rw [← hφ, ← hov, hψ])
  rw [e, ← hψ, Category.assoc]
  exact eigFrame_of_basis c Z _ hxR fun τ =>
    have := (hR τ).1
    have := (hR τ).2.1
    Module.finBasisOfFinrankEq R _ (rk τ)
