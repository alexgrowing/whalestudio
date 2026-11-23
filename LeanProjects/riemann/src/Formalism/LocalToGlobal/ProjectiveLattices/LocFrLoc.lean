import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecV
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB
import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecLocFrM
import Formalism.LocalToGlobal.ProjectiveLattices.LocFrGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)

private theorem free_range_idem_lemma {V : Type} [CommRing V] [IsLocalRing V] {n : ℕ}
    (g : Module.End V (Fin n → V)) (hg : IsIdempotentElem g) : Module.Free V (LinearMap.range g) := by
  haveI : Module.Projective V (LinearMap.range g) :=
    Module.Projective.of_split (LinearMap.range g).subtype g.rangeRestrict
      (LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
        obtain ⟨y, rfl⟩ := hx
        exact LinearMap.congr_fun hg y))
  exact Module.free_of_flat_of_isLocalRing

theorem finrank_range_idem {V k : Type} [CommRing V] [IsLocalRing V] [Field k] [CharZero k] (f : V →+* k) {n : ℕ}
    (e : Module.End V (Fin n → V)) (e' : Module.End k (Fin n → k)) (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (h : ∀ c, e' (f ∘ c) = f ∘ e c) : Module.finrank V (LinearMap.range e) = Module.finrank k (LinearMap.range e') := by
  classical

  have hker : LinearMap.ker e = LinearMap.range (1 - e) := by
    ext x
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      rw [LinearMap.mem_ker] at hx
      simp [hx]
    · rintro ⟨y, rfl⟩
      have h2 := LinearMap.congr_fun he y
      simp only [Module.End.mul_apply] at h2
      simp [h2]
  haveI := free_range_idem_lemma e he
  haveI : Module.Free V (LinearMap.ker e) := by
    rw [hker]; exact free_range_idem_lemma (1 - e) he.one_sub
  haveI : Module.Finite V (LinearMap.ker e) := by
    rw [hker]; infer_instance
  have hP : LinearMap.IsProj (LinearMap.range e) e :=
    ⟨fun x => LinearMap.mem_range_self e x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun he y⟩
  have hP' : LinearMap.IsProj (LinearMap.range e') e' :=
    ⟨fun x => LinearMap.mem_range_self e' x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun he' y⟩

  have hs : ∀ i : Fin n, (f ∘ Pi.single i (1 : V)) = Pi.single i (1 : k) := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have htr : f (LinearMap.trace V _ e) = LinearMap.trace k _ e' := by
    rw [LinearMap.trace_eq_matrix_trace V (Pi.basisFun V (Fin n)),
      LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n))]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (h (Pi.single i 1)) i
    rw [hs i] at this
    exact this.symm
  have h1 := hP.trace
  have h2 := hP'.trace
  apply Nat.cast_injective (R := k)
  rw [← h2, ← htr, h1, map_natCast]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gsvVec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gsvVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gsvVec x xc cc ≫ (Xo.univ.t.act.act a).left := by
  unfold gsvVec
  rw [ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, Over.comp_left, Category.assoc, Category.assoc]
  congr 1
  all_goals first
    | rfl
    | (simp; done)
    | (simp [Over.pullback]; done)
    | (simp [Over.pullback, pullback.map]; done)
    | (erw [pullback.lift_fst]; done)
    | (erw [pullback.lift_fst]; rfl)

theorem gsv_bc [IsLocalRing L] {L' : Type} [CommRing L'] [Algebra L L'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L') (JetR L' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap L L') ≫ x)).obj Xo.univ.t.G) (hx' : IsUnivChart _ n xc'),
      (∀ cc : Fin n → L, gsvVec (spMap (algebraMap L L') ≫ x) xc' (algebraMap L L' ∘ cc) =
        spMap (dualMap (algebraMap L L')) ≫ gsvVec x xc cc) ∧
      ∀ (a : 𝓞 E) (cc : Fin n → L),
        tmap hx' ((Over.pullback (spMap (algebraMap L L') ≫ x)).map (Xo.univ.t.act.act a)) (algebraMap L L' ∘ cc) =
          algebraMap L L' ∘ tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := L) (R' := L') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB L L'))
    (isGrpPullback_pullback Xo.univ.t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback Xo.univ.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB L L' ≫ x))
  have hv : ∀ cc : Fin n → L, gsvVec (spMap (algebraMap L L') ≫ x) (fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc) =
      spMap (dualMap (algebraMap L L')) ≫ gsvVec x xc cc := by
    intro cc
    have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left =
        (tvec (x := x₁) (algebraMap L L' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap L L' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  have hx' := gfp_chart_iso e hx₁
  refine ⟨fun m => x₁ m ≫ e.hom, hx', hv, fun a cc => gsv_inj hx' ?_⟩
  rw [gsvVec_tmap hx', hv, hv, gsvVec_tmap hx, Category.assoc]

def rhoT (hx : IsUnivChart _ n xc) : 𝓞 E →+* Module.End L (Fin n → L) :=
  have add : ∀ a b, tmap hx ((Over.pullback x).map (Xo.univ.t.act.act (a + b))) =
      tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) + tmap hx ((Over.pullback x).map (Xo.univ.t.act.act b)) :=
    fun a b => LinearMap.ext fun cc => ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (by
      rw [LinearMap.add_apply, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx,
        ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_tmap hx, Xo.univ.t.act.add, Functor.map_mul,
        MonObj.comp_mul])
  { toFun := fun a => tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a))
    map_one' := LinearMap.ext fun cc => gsv_inj hx (by rw [gsvVec_tmap, Xo.univ.t.act.one]; exact Category.comp_id _)
    map_mul' := fun a b => LinearMap.ext fun cc => gsv_inj hx (by
      rw [Module.End.mul_apply, gsvVec_tmap, gsvVec_tmap, gsvVec_tmap, mul_comm a b, Xo.univ.t.act.mul, Category.assoc]; rfl)
    map_zero' := by
      have := add 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    map_add' := add }

theorem exists_eig_basis [IsLocalRing L] [Algebra c.F L] (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) :
    Nonempty (Module.Basis (Fin (Dw.mult τ)) L
      (eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F L (embK c τ a))) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  have key : ∀ {R : Type} [CommRing R] [Algebra c.F R] {x : Sp R ⟶ Xo.X}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (JetR R (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
      (hx : IsUnivChart _ n xc), IsIdempotentElem (proj (rhoT hx) (embK c) α τ) ∧ LinearMap.range (proj (rhoT hx) (embK c) α τ) =
        eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F R (embK c τ a) :=
    fun {R} _ _ {x xc} hx => by
      have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rhoT hx) (embK c τ) (proj (rhoT hx) (embK c) α τ m) := fun m =>
        eig_of_alpha _ _ α hN τ (proj_eig_alpha _ _ α hinj f hf hfs τ m)
      have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rhoT hx) (embK c τ) m → proj (rhoT hx) (embK c) α τ m = m := fun m hm => by
        have := proj_sum_eig (rhoT hx) (embK c) α hinj (Pi.single τ m) (fun τ' => by
          by_cases h : τ' = τ
          · subst h; rwa [Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
        rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
      refine ⟨LinearMap.ext fun m => e₂ _ (e₁ m), Submodule.ext fun m => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
      exact ⟨fun ⟨m', h⟩ => h ▸ e₁ m', fun h => ⟨m, e₂ m h⟩⟩
  let k := IsLocalRing.ResidueField L
  letI : Algebra c.F k := ((algebraMap L k).comp (algebraMap c.F L)).toAlgebra
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  obtain ⟨xc', hx', -, htm⟩ := gsv_bc (L' := k) hx
  have hx0' : (spMap (algebraMap L k) ≫ x) ≫ Xo.s = sOf c k := by
    rw [Category.assoc, hx0]
    exact (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp _ _).symm
  have pw : ∀ (j : ℕ) cc, (rhoT hx' α ^ j) (algebraMap L k ∘ cc) = algebraMap L k ∘ (rhoT hx α ^ j) cc := fun j => by
    induction j with
    | zero => exact fun _ => rfl
    | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
  have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rhoT hx' α) (Q.map (algebraMap c.F k)) (algebraMap L k ∘ cc) =
      algebraMap L k ∘ Polynomial.aeval (rhoT hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
    induction Q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
      funext j; simp
    | monomial j a =>
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      funext i
      exact (map_mul (algebraMap L k) _ _).symm
  have r := finrank_range_idem (algebraMap L k) _ _ (key hx).1 (key hx').1 (pr _)
  have := Formalism.L2.Pj.LocFrM.range_free _ (key hx).1
  rw [(key hx').2] at r
  rw [← (key hx).2]
  exact ⟨Module.finBasisOfFinrankEq L _ (r.trans (gfp_finrank hx0' hx' τ))⟩

theorem exists_frPt_local (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) [IsLocalRing L] [Algebra c.F L] (x : Sp L ⟶ Xo.X)
    (hx0 : x ≫ Xo.s = sOf c L) : ∃ y : FrPt Xo c L, y.x = x := by
  have := Xo.univ.t.semi.smooth
  have : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  have B := fun τ => (exists_eig_basis (c := c) hx0 hx τ).some
  obtain ⟨t', ⟨m⟩⟩ := exists_sab x Xo.univ.t
  obtain ⟨β, hβ⟩ := globalSections_rank_one_obj hT Xo.univ m
  obtain ⟨s, hs⟩ := locFrGen_of x m β hβ
  refine ⟨⟨x, hx0, fun τ i => gsvVec x xc (B τ i), fun τ i => gsv_tan hx _, fun τ i => (gsv_eig_iff hx τ _).2 (B τ i).2,
    fun τ w hw he => ?_, s, hs⟩, rfl⟩
  obtain ⟨cc, rfl⟩ := gsv_exists hx w hw
  let v : eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) fun a => algebraMap c.F L (embK c τ a) :=
    ⟨cc, (gsv_eig_iff hx τ _).1 he⟩
  have k : ∀ a, IsCombAt x (fun i => gsvVec x xc (B τ i)) a (gsvVec x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [gsv_comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

end Formalism.L2.Pj
