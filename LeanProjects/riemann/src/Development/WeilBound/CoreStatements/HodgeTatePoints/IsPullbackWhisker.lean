import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1PointPowerExpand
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.WeilBound.CoreStatements.HodgeTatePoints.CdLocal
import Development.WeilBound.CoreStatements.HodgeTatePoints.CdUniv
import Development.WeilBound.CoreStatements.HodgeTatePoints.CbFrob
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

theorem spMap_cp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem comp_listProd {X0 : Scheme.{0}} {G T T' : Over X0} [GrpObj G] (ρ : T' ⟶ T) (l : List (T ⟶ G)) :
    ρ ≫ l.prod = (l.map (ρ ≫ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [MonObj.comp_mul, ih]

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S₂ : Type} [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0)

theorem comb_iff {V : Type} [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) {n : ℕ} (b : Fin n → V)
    (a : Fin n → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x (fun l => (M.pt (b l)).left) a w ↔ (M.pt (∑ i, a i • b i)).left = w := by
  have h0 : M.pt 0 = 1 := by
    have := M.add 0 0
    rw [add_zero] at this
    simpa using this
  let φ : Multiplicative V →* (tEpsG x ⟶ t.G) :=
    { toFun := fun v => M.pt v.toAdd, map_one' := h0, map_mul' := fun u v => M.add _ _ }
  have hs : M.pt (∑ i, a i • b i) = (List.ofFn fun i => M.pt (a i • b i)).prod := by
    have := map_prod φ (fun i => Multiplicative.ofAdd (a i • b i)) Finset.univ
    rw [List.prod_ofFn]
    rw [← ofAdd_sum] at this
    exact this
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => M.pt (a i • b i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [hs, this]
  · rintro rfl
    exact ⟨fun i => M.pt (a i • b i), fun i => M.smul _ _, by rw [hs]⟩

def epsBC : tEpsG (spMap f ≫ x) ⟶ tEpsG x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    change spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp]
    congr 2
    ext s <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl])

theorem comb_bc {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin n → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap f ≫ x) (fun i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v i) (fun i => f (a i))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => epsBC f x ≫ u i, fun i => ?_, ?_⟩
  · change spMap _ ≫ (u i).left = _
    rw [hu, ← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp]
    congr 2
    refine RingHom.ext fun s => ?_
    ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, mul_comm]
  · have := comp_listProd (epsBC f x) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact (congrArg (fun q => q.left) this).symm

theorem tan_bc {v : Sp (DualNumber S) ⟶ t.G.left} (h : IsTanAtG t x v) :
    IsTanAtG t (spMap f ≫ x) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1]
    exact Over.w (epsBC f x)
  · have e : spMap (TrivSqZeroExt.fstHom S₂ S₂ S₂).toRingHom ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) =
        spMap f ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [spMap_cp, spMap_cp]
      congr 1
      refine RingHom.ext fun s => ?_
      simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    rw [← Category.assoc, e, Category.assoc, h.2]
    exact congrArg (fun q => q.left)
      (MonObj.comp_one (M := t.G) (Over.homMk (spMap f) rfl : Over.mk (spMap f ≫ x) ⟶ Over.mk x))

theorem basis_bc {n : ℕ} {tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (ht : ∀ l, IsTanAtG t x (tg l))
    (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x tg a w) (w : Sp (DualNumber S₂) ⟶ t.G.left)
    (hw : IsTanAtG t (spMap f ≫ x) w) :
    ∃! a : Fin n → S₂, IsCombAtG t (spMap f ≫ x) (fun i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ tg i) a w := by
  letI : Algebra S S₂ := f.toAlgebra
  obtain ⟨V, _, _, ⟨M⟩⟩ := GlobalTheory.T.exists_lie_model X0 t.G S x
  obtain ⟨V', _, _, ⟨M'⟩⟩ := GlobalTheory.T.exists_lie_model X0 t.G S₂ (spMap f ≫ x)
  obtain ⟨j, hj, -, hbs⟩ := PositivityTheory.HtPt.Htat.lie_bc X0 t.G S S₂ x V V' M M'
  choose b hb' using fun l => M.onto (Over.homMk (tg l) (ht l).1) (ht l).2
  have htg : tg = fun l => (M.pt (b l)).left := funext fun l => by rw [hb']; rfl
  have hu : ∀ v : V, ∃! a : Fin n → S, ∑ i, a i • b i = v := fun v => by
    obtain ⟨a, ha, hau⟩ := hb (M.pt v).left ⟨Over.w (M.pt v), M.tan v⟩
    rw [htg, comb_iff] at ha
    refine ⟨a, M.inj (Over.OverMorphism.ext ha), fun a' ha' => hau a' ?_⟩
    beta_reduce
    rw [htg, comb_iff, ha']
  have hli : LinearIndependent S b := Fintype.linearIndependent_iff.2 fun a ha i =>
    congrFun ((hu 0).unique (y₁ := a) (y₂ := 0) ha (by simp)) i
  have hsp : ⊤ ≤ Submodule.span S (Set.range b) := fun v _ => by
    obtain ⟨a, rfl, -⟩ := hu v
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨hli', hsp'⟩ := hbs t.semi.smooth n (Module.Basis.mk hli hsp)
  simp only [Module.Basis.mk_apply] at hli' hsp'
  have htg' : (fun i => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ tg i) = fun l => (M'.pt (j (b l))).left :=
    funext fun l => by rw [hj, htg]
  obtain ⟨v, hv⟩ := M'.onto (Over.homMk w hw.1) hw.2
  have hvw : (M'.pt v).left = w := by rw [hv]; rfl
  let B := Module.Basis.mk hli' hsp'.ge
  have hB : ∀ i, j (b i) = B i := fun i => by simp [B]
  refine ⟨B.equivFun v, ?_, fun a ha => ?_⟩
  · beta_reduce
    rw [htg', comb_iff]
    simp only [hB, Module.Basis.sum_equivFun, hvw]
  · rw [htg', comb_iff, ← hvw] at ha
    have := M'.inj (Over.OverMorphism.ext ha)
    simp only [hB] at this
    rw [← this, ← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

def cO (κ : Type) (m : ℕ) : overAt (spMap f ≫ x) (Jet S₂ κ m) ⟶ overAt x (Jet S κ m) :=
  Over.homMk (spMap (jetCoef f κ m)) (by
    change spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap f ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp, jetCoef_alg])

theorem sq_of {κ κ' : Type} {m m' : ℕ} (α : Jet S κ m →ₐ[S] Jet S κ' m') (β : Jet S₂ κ m →ₐ[S₂] Jet S₂ κ' m')
    (h : (jetCoef f κ' m').comp (α : Jet S κ m →+* Jet S κ' m') =
      (β : Jet S₂ κ m →+* Jet S₂ κ' m').comp (jetCoef f κ m)) :
    homAt (spMap f ≫ x) β ≫ cO f x κ m = cO f x κ' m' ≫ homAt x α := by
  apply Over.OverMorphism.ext
  change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [spMap_cp, spMap_cp, h]

theorem sq_subst {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (φ' : κ → MvPolynomial κ' S₂)
    (h : ∀ i, φ' i = MvPolynomial.map f (φ i)) :
    homAt (spMap f ≫ x) (jetSubstP m φ') ≫ cO f x κ m = cO f x κ' m ≫ homAt x (jetSubstP m φ) := by
  obtain rfl : φ' = _ := funext h
  exact sq_of f x _ _ (jetCoef_substP f m φ)

variable {d : ℕ} (y : ∀ m, jOG x d m 1 ⟶ t.G)

def yBC (m : ℕ) : jOG (spMap f ≫ x) d m 1 ⟶ t.G := cO f x _ m ≫ y m

theorem jpt_bc {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t (spMap f ≫ x) d (yBC t f x y) m i = cO f x _ m ≫ jptG t x d y m i := by
  rw [jptG, jptG, yBC, ← Category.assoc, sq_of f x _ _ (jetCoef_copy f d m n i), Category.assoc]

theorem chart_bc {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {tg : Fin d → (Sp (DualNumber S) ⟶ t.G.left)} (h : IsChartG t x d F act tg (fun l j => if l = j then 1 else 0) y) :
    IsChartG t (spMap f ≫ x) d (fun i => MvPowerSeries.map f (F i)) (fun a i => MvPowerSeries.map f (act a i))
      (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ tg l) (fun l j => if l = j then 1 else 0) (yBC t f x y) where
  zero m := by
    let ρ : overAt (spMap f ≫ x) S₂ ⟶ overAt x S := Over.homMk (spMap f) (by
      change spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap f ≫ x
      rw [spMap_alg_self, spMap_alg_self, Category.id_comp, Category.id_comp])
    have e : homAt (spMap f ≫ x) (jetAug : Jet S₂ (Fin 1 × Fin d) m →ₐ[S₂] S₂) ≫ cO f x _ m =
        ρ ≫ homAt x (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
      apply Over.OverMorphism.ext
      change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [spMap_cp, spMap_cp, jetCoef_aug]
    rw [yBC, ← Category.assoc, e, Category.assoc, h.zero, MonObj.comp_one]
  trunc m := by
    rw [yBC, yBC, ← Category.assoc, sq_of f x _ _ (jetCoef_trunc f _ m).symm, Category.assoc, h.trunc]
  law m := by
    rw [jpt_bc, jpt_bc, ← MonObj.comp_mul, ← h.law, yBC, ← Category.assoc,
      sq_subst f x m (fun p : Fin 1 × Fin d => psTrunc m (F p.2)) _ (fun i => psTrunc_map f m _), Category.assoc]
  act m a := by
    rw [yBC, Category.assoc, h.act, ← Category.assoc (homAt _ _),
      sq_subst f x m (fun p : Fin 1 × Fin d => psTrunc m (act a p.2)) _ (fun i => psTrunc_map f m _), Category.assoc]
  tan l := by
    have := comb_bc t f x (h.tan l)
    convert this using 2 with j j
    · change spMap _ ≫ spMap _ ≫ (y 1).left = spMap _ ≫ spMap _ ≫ (y 1).left
      rw [← Category.assoc, ← Category.assoc, spMap_cp, spMap_cp]
      congr 2
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        change (MvPolynomial.aeval _) (MvPolynomial.map f (MvPolynomial.C r)) =
          GlobalTheory.CompanionTheory.Ar.dualMap f ((MvPolynomial.aeval _) (MvPolynomial.C r))
        ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      · intro i
        change (MvPolynomial.aeval _) (MvPolynomial.map f (MvPolynomial.X i)) =
          GlobalTheory.CompanionTheory.Ar.dualMap f ((MvPolynomial.aeval _) (MvPolynomial.X i))
        rw [MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        split_ifs
        · ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]
        · simp
    · split_ifs <;> simp
  basis v := ⟨v, fun j => by simp, fun a ha => funext fun j => by simpa using ha j⟩

end

end PositivityTheory.HtPt.Ce

end
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open MvPolynomial (X C)

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S₂ : Type} [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0)
variable {d : ℕ} (y : ∀ m, jOG x d m 1 ⟶ t.G)

theorem psum_pre {T T' : Over X0} (h : T' ⟶ T) {n : ℕ} (a : Fin n → (T ⟶ t.G)) (I : Finset (Fin n)) :
    psum t.G (fun k => h ≫ a k) I = h ≫ psum t.G a I := foldr_padd_pre h a _

theorem cφ_bc (m : ℕ) (I : ULift (Finset (Fin 2))) :
    cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2), jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)] I =
      (cO f x _ m).left ≫ cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)] I := by
  rw [cφG, cφG, ← Over.comp_left, ← psum_pre]
  congr 2
  funext k
  fin_cases k <;> exact jpt_bc t f x y m _

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ (hJ.mem φ r) _))

def uBC {κ : Type} {m : ℕ} (u : (Jet S κ m)ˣ) : (Jet S₂ κ m)ˣ := Units.map (jetCoef f κ m : Jet S κ m →* Jet S₂ κ m) u

theorem uBC_inv {κ : Type} {m : ℕ} (u : (Jet S κ m)ˣ) : (uBC f u)⁻¹ = uBC f u⁻¹ := (map_inv _ _).symm

theorem gm_unit_bc {Z : Scheme.{0}} {κ : Type} {m : ℕ} (u : (Jet S κ m)ˣ) (r : Z ⟶ Sp (Jet S₂ κ m)) (z : Z) :
    gm r z ⊤ (unitΓ (uBC f u)) =
      gm (r ≫ (cO f x κ m).left) z ⊤ (unitΓ u) := by
  rw [← gm_pull r (cO f x κ m).left z ⊤ trivial]
  congr 1
  apply Units.ext
  exact (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (jetCoef f κ m))))

theorem coef_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (F : MvPowerSeries κ S) :
    jetCoef f κ m (psJet m F) = psJet m (MvPowerSeries.map f F) := by
  rw [psJet, psJet, jetCoef_mk, psTrunc_map]

theorem psIn_map {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (F : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map f F) = MvPolynomial.map f (psIn d m r F) := by
  rw [psIn, psIn, psTrunc_map, MvPolynomial.map_rename]

variable (e : ∀ m, FrTyG t x d y m) (e₂ : ∀ m, FrTyG t (spMap f ≫ x) d (yBC t f x y) m)

def FrBC : Prop := ∀ (m : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet S₂ (Fin 2 × Fin d) m)) (z : Z) (J), Good t.PP.L z J →
  val (L := t.PP.L) (φ := cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2),
    jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)]) (ε := cε 2) (e₂ m) r z J =
  val (L := t.PP.L) (φ := cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)]) (ε := cε 2) (e m)
    (r ≫ (cO f x _ m).left) z J

theorem exists_frBC (he : ∀ m, (e m).IsGen) :
    ∃ e₂ : ∀ m, FrTyG t (spMap f ≫ x) d (yBC t f x y) m, (∀ m, (e₂ m).IsGen) ∧ FrBC t f x y e e₂ := by
  have := fun m => exists_gen t.PP.isLB
    (φ' := cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2),
      jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)]) (ε' := cε 2)
    (fun U _ h => Finset.prod_congr rfl fun k _ => by rw [cφ_bc])
    (LB.pullGen t.PP.L (cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)]) (cε 2) (e m) (cO f x _ m).left)
    (DVR.pullGen_isGen_of_isGen _ _ _ (he m) _)
  choose e₂ h1 h2 using this
  exact ⟨e₂, h1, fun m Z r z J hJ => (h2 m Z r z J hJ).trans (val_pull hJ _ _ _)⟩

variable {t f x y e e₂}

theorem FrBC.pull (h : FrBC t f x y e e₂) {m m' : ℕ} {κ : Type} (α : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S κ m')
    (β : Jet S₂ (Fin 2 × Fin d) m →ₐ[S₂] Jet S₂ κ m')
    (hs : homAt (spMap f ≫ x) β ≫ cO f x _ m = cO f x κ m' ≫ homAt x α)
    {Z : Scheme.{0}} (r : Z ⟶ Sp (Jet S₂ κ m')) {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (LB.pullGen t.PP.L (cφG t ![jptG t (spMap f ≫ x) d (yBC t f x y) m (0 : Fin 2),
      jptG t (spMap f ≫ x) d (yBC t f x y) m (1 : Fin 2)]) (cε 2) (e₂ m) (homAt (spMap f ≫ x) β).left) r z J =
    val (LB.pullGen t.PP.L (cφG t ![jptG t x d y m (0 : Fin 2), jptG t x d y m (1 : Fin 2)]) (cε 2) (e m)
      (homAt x α).left) (r ≫ (cO f x κ m').left) z J := by
  refine (val_pull hJ _ _ _).trans ((h m Z _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hs]

theorem FrBC.pe (h : FrBC t f x y e e₂) {m n : ℕ} (a b : Fin d → MvPolynomial (Fin n × Fin d) S)
    (a' b' : Fin d → MvPolynomial (Fin n × Fin d) S₂) (ha : ∀ j, a' j = MvPolynomial.map f (a j))
    (hb : ∀ j, b' j = MvPolynomial.map f (b j))
    {Z : Scheme.{0}} (r : Z ⟶ Sp (Jet S₂ (Fin n × Fin d) m)) {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (peG t (spMap f ≫ x) d (yBC t f x y) e₂ m ![a', b']) r z J =
      val (peG t x d y e m ![a, b]) (r ≫ (cO f x _ m).left) z J :=
  h.pull _ _ (sq_subst f x m _ _ fun ⟨i, j⟩ => by fin_cases i; exacts [ha j, hb j]) r hJ

theorem val_pull_eq {Y Y₁ Y₂ Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h₁ : Y₁ ⟶ Y) (h₂ : Y₂ ⟶ Y) (c : Y₂ ⟶ Y₁) (hc : h₂ = c ≫ h₁) (r : Z ⟶ Y₂)
    {z : Z} {J} (hJ : Good t.PP.L z J) :
    val (LB.pullGen t.PP.L φ ε g h₂) r z J = val (LB.pullGen t.PP.L φ ε g h₁) (r ≫ c) z J := by
  rw [val_pull hJ, val_pull hJ, hc, Category.assoc]

theorem FrBC.frame (h : FrBC t f x y e e₂) (hg : ∀ m, (e₂ m).IsGen)
    {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (hf : IsFrameG t x d y F act ph1 ph2 sy ad e) :
    IsFrameG t (spMap f ≫ x) d (yBC t f x y) (fun i => MvPowerSeries.map f (F i))
      (fun a i => MvPowerSeries.map f (act a i)) (MvPowerSeries.map f ph1) (MvPowerSeries.map f ph2)
      (MvPowerSeries.map f sy) (fun a => MvPowerSeries.map f (ad a)) e₂ where
  gen := hg
  ph1 m := by
    obtain ⟨u, hu, hc⟩ := hf.ph1 m
    refine ⟨uBC f u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    refine (val_pull_eq _ _ _ (cO f x _ m).left ?_ _ hJ).trans ((val_corr hJ hc _).trans ?_)
    · rw [← Over.comp_left, comp_lift, comp_lift, jpt_bc, jpt_bc, jpt_bc]
    · rw [val_scale t _ _ _ hJ, val_scale t _ _ _ hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
        val_inv, val_inv, gm_unit_bc f x,
        h.pe _ _ _ _ (fun j => psIn_map f m _ _) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ]
  ph2 m := by
    obtain ⟨u, hu, hc⟩ := hf.ph2 m
    refine ⟨uBC f u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    refine (val_pull_eq _ _ _ (cO f x _ m).left ?_ _ hJ).trans ((val_corr hJ hc _).trans ?_)
    · rw [← Over.comp_left, comp_lift, comp_lift, jpt_bc, jpt_bc, jpt_bc]
    · rw [val_scale t _ _ _ hJ, val_scale t _ _ _ hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
        val_inv, val_inv, gm_unit_bc f x,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => psIn_map f m _ _) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ]
  sy m := by
    obtain ⟨u, hu, hc⟩ := hf.sy m
    refine ⟨uBC f u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    refine (h m _ _ z J hJ).trans ((val_corr hJ hc _).trans ?_)
    rw [val_scale t _ _ _ hJ, val_scale t _ _ _ hJ, uBC_inv, gm_unit_bc f x,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ]
  ad a := by
    obtain ⟨wL, hw, hm⟩ := hf.ad a
    refine ⟨wL, hw, fun m => ?_⟩
    obtain ⟨u, hu, hc⟩ := hm m
    refine ⟨uBC f u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    have hv := val_corr hJ hc (𝟙 _ ≫ (cO f x _ m).left)
    rw [val_mul hJ, val_scale t _ _ _ hJ] at hv
    rw [val_mul hJ, val_scale t _ _ _ hJ, gm_unit_bc f x,
      h.pe _ _ _ _ (fun j => psIn_map f m _ _) (fun j => (MvPolynomial.map_X f _).symm) _ hJ,
      h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => psIn_map f m _ _) _ hJ, ← hv,
      val_pull_eq _ (lift (jptG t x d y m (0 : Fin 2)) (jptG t x d y m (1 : Fin 2))).left _ (cO f x _ m).left
        (by rw [← Over.comp_left, comp_lift, jpt_bc, jpt_bc]) _ hJ]

theorem FrBC.trunc (h : FrBC t f x y e e₂) (hf : FrTrunc t x d y e) : FrTrunc t (spMap f ≫ x) d (yBC t f x y) e₂ :=
  fun m => corr_of_val t.PP.isLB fun z J hJ =>
    (h.pull _ _ (sq_of f x _ _ (jetCoef_trunc f _ m).symm) _ hJ).trans
      ((val_corr hJ (hf m) _).trans (h m _ _ z J hJ).symm)

theorem FrBC.axes (h : FrBC t f x y e e₂) (hf : FrAxes t x d y e) : FrAxes t (spMap f ≫ x) d (yBC t f x y) e₂ :=
  fun m => ⟨corr_of_val t.PP.isLB fun z J hJ =>
    (h.pe _ _ _ _ (fun _ => (map_zero _).symm) (fun _ => (MvPolynomial.map_X f _).symm) _ hJ).trans
      ((val_corr hJ (hf m).1 _).trans ((val_one _).trans (val_one _).symm)),
    corr_of_val t.PP.isLB fun z J hJ =>
    (h.pe _ _ _ _ (fun _ => (MvPolynomial.map_X f _).symm) (fun _ => (map_zero _).symm) _ hJ).trans
      ((val_corr hJ (hf m).2 _).trans ((val_one _).trans (val_one _).symm))⟩

end

theorem germ_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S S₂ : Type) [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), ∃ g₂ : GermAt t (spMap f ≫ x) d, IsMapOf f g.B g₂.B ∧ ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
  intro E _ _ _ H _ _ X0 t S S₂ _ _ f x d g
  obtain ⟨e₂, h1, h2⟩ := exists_frBC t f x g.x g.e g.frame.gen
  exact ⟨⟨FBMap.mapFB f g.B, yBC t f x g.x, e₂, fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l,
    chart_bc t f x g.x g.chart, fun l => tan_bc t f x (g.tan l), basis_bc t f x g.tan g.basis,
    h2.frame h1 g.frame, h2.trunc g.trunc, h2.axes g.axes⟩,
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩, fun _ => rfl⟩

end PositivityTheory.HtPt.Ce

end
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

theorem toFirst_eq (k : Type) [CommRing k] (p : ℕ) (hp : 1 ≤ p) : toFirst k p hp = trTo k Unit hp := rfl

theorem C_mul_X_eq_zero {k : Type} [CommRing k] (c : k)
    (h : (Ideal.Quotient.mk (orig k Unit ^ (1 + 1)) (MvPolynomial.C c * MvPolynomial.X ())) = 0) : c = 0 := by
  have := congrArg (fun a => TrivSqZeroExt.snd ((jetTan () : Jet k Unit (0 + 1) →ₐ[k] DualNumber k) a)) h
  have e : (jetTan () : Jet k Unit (0 + 1) →ₐ[k] DualNumber k)
      (Ideal.Quotient.mk _ (MvPolynomial.C c * MvPolynomial.X ())) =
      MvPolynomial.aeval (fun i : Unit => if i = () then (DualNumber.eps : DualNumber k) else 0)
        (MvPolynomial.C c * MvPolynomial.X ()) := rfl
  simp only [e, map_zero] at this
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

theorem pt_of_vec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) = 1 ∧ ((hw g.B p).mulVec (fun i => w i ^ p) = 0 → (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1) ∧ (homAt x (toFirst k p hp) ≫ (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) = 1 → w = 0) := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ hp x d g w
  set χ : Jet k (Fin 1 × Fin d) p →ₐ[k] Jet k Unit p :=
    jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X () with hχ
  have hX : ∀ q, χ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      Ideal.Quotient.mk _ (MvPolynomial.C (w q.2) * MvPolynomial.X ()) := fun q => by
    rw [hχ, substP_X]
    simp
  have h0 : ∀ q, (jetAug : Jet k Unit p →ₐ[k] k) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0 := fun q => by
    rw [hX, aug_mk]
    simp
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · rw [← Category.assoc, homAt_comp]
    exact x_zero g _ h0
  · obtain ⟨ψ, h1, h2⟩ := pow_coord g p (by omega) (PositivityTheory.HtPt.Cb.mulp_V k p d _ g.B) χ
    rw [h1]
    refine x_zero g _ fun q => ?_
    have hq := congrFun h q.2
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hq
    have : ∀ j, algebraMap k (Jet k Unit p) (hw g.B p q.2 j) *
        χ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) ^ p =
        algebraMap k (Jet k Unit p) (hw g.B p q.2 j * w j ^ p) * Ideal.Quotient.mk _ (MvPolynomial.X ()) ^ p := by
      intro j
      rw [hX, map_mul, map_mul, map_pow, mul_pow, _root_.mul_assoc]
      rfl
    rw [h2, Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_mul, ← map_sum, hq, map_zero, zero_mul]
  · obtain ⟨χ', a1, a2⟩ := exists_low hp χ h0
    rw [toFirst_eq, ← Category.assoc, homAt_comp, ← a2, ← homAt_comp, Category.assoc, x_trTo] at h
    obtain ⟨χ₀, -, hu⟩ := (PositivityTheory.HtPt.Cd.germ_univ E H hstar X0 t k x d g).2 Unit 1 1 (MonObj.comp_one _)
    have e1 := hu χ' ⟨a1, h.symm⟩
    have e2 := hu ((Algebra.ofId k _).comp jetAug) ⟨fun q => by
      rw [AlgHom.comp_apply, aug_mk]; simp, (x_zero g _ fun q => by rw [AlgHom.comp_apply, aug_mk]; simp).symm⟩
    funext j
    have e3 := congrArg (fun φ => φ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) a2
    simp only [AlgHom.comp_apply, trTo_mk, hX] at e3
    rw [e1, ← e2, AlgHom.comp_apply, aug_mk] at e3
    exact C_mul_X_eq_zero _ (by rw [← e3]; simp)

theorem pow_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (x : Sp k ⟶ X0) (y y₂ : overAt x (Jet k Unit p) ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y₂ = 1 → homAt x (toFirst k p hp) ≫ y = homAt x (toFirst k p hp) ≫ y₂ → y ^ p = y₂ ^ p := by
  intro E _ _ _ H _ hstar X0 t hP k _ p _ _ hp x y y₂ hy hy₂ h
  obtain ⟨d, ⟨g⟩⟩ := PositivityTheory.HtPt.Cd.germ_local E H hstar X0 t hP k x
  obtain ⟨χ, ⟨a0, rfl⟩, -⟩ := (PositivityTheory.HtPt.Cd.germ_univ E H hstar X0 t k x d g).2 Unit p y hy
  obtain ⟨χ₂, ⟨b0, rfl⟩, -⟩ := (PositivityTheory.HtPt.Cd.germ_univ E H hstar X0 t k x d g).2 Unit p y₂ hy₂
  obtain ⟨χ', a1, a2⟩ := exists_low hp χ a0
  obtain ⟨χ₂', b1, b2⟩ := exists_low hp χ₂ b0
  rw [toFirst_eq, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp, ← a2, ← b2, ← homAt_comp, ← homAt_comp,
    Category.assoc, Category.assoc, x_trTo] at h
  obtain ⟨χ₀, -, hu⟩ := (PositivityTheory.HtPt.Cd.germ_univ E H hstar X0 t k x d g).2 Unit 1 (homAt x χ' ≫ g.x 1) (by
    rw [← Category.assoc, homAt_comp]
    exact x_zero g _ a1)
  have e : χ' = χ₂' := (hu χ' ⟨a1, rfl⟩).trans (hu χ₂' ⟨b1, h⟩).symm
  have e' : (trTo k Unit hp).comp χ = (trTo k Unit hp).comp χ₂ := by rw [← a2, ← b2, e]
  obtain ⟨ψ, h1, h2⟩ := pow_coord g p (by omega) (PositivityTheory.HtPt.Cb.mulp_V k p d _ g.B) χ
  obtain ⟨ψ₂, h3, h4⟩ := pow_coord g p (by omega) (PositivityTheory.HtPt.Cb.mulp_V k p d _ g.B) χ₂
  have : ψ = ψ₂ := jet_hom_ext fun q => by
    rw [h2, h4]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_eq_of_first p hp (χ _) (χ₂ _) (AlgHom.congr_fun e' _)]
  rw [h1, h3, this]

theorem tanpf_inj_of (hC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k), alpha g.B p (fun i => w i ^ p) = 0 → ∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G))), c.IsGen) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p := by
  intro E _ _ _ H _ hstar X0 t k _ _ p hpp _ x d g hT
  have hp : 1 ≤ p := hpp.out.one_le
  rw [ConjInj, injective_iff_map_eq_zero]
  intro u hu
  choose w hw' using fun i => IsAlgClosed.exists_pow_nat_eq (u i) (n := p) hp
  obtain rfl : u = fun i => w i ^ p := funext fun i => (hw' i).symm
  obtain ⟨h1, h2, h3⟩ := pt_of_vec E H hstar X0 t k p hp x d g w
  have hwv : (hw g.B p).mulVec (fun i => w i ^ p) = 0 := by
    have := congrArg Prod.fst hu
    rwa [alpha_apply] at this
  have := h3 (hT hp _ h1 (h2 hwv) (hC E H hstar X0 t k p hp x d g w hu))
  funext i
  simp [this, show p ≠ 0 by omega]

end PositivityTheory.HtPt.Ce

end
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TorusModel

theorem mem_orig_pow_iff {k κ : Type} [CommRing k] (n : ℕ) (P : MvPolynomial κ k) :
    P ∈ orig k κ ^ n ↔ ∀ e : κ →₀ ℕ, e.degree < n → P.coeff e = 0 :=
  MvPolynomial.mem_pow_idealOfVars_iff' n P

theorem first_eq_zero {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (a : Jet k Unit p)
    (h : a ^ p = 0) : trTo k Unit hp a = 0 := by
  have h0 : (jetAug : Jet k Unit p →ₐ[k] k) a = 0 := by
    have := congrArg (jetAug : Jet k Unit p →ₐ[k] k) h
    rw [map_pow, map_zero] at this
    exact pow_eq_zero_iff (by omega) |>.1 this
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [aug_mk] at h0
  have e : trTo k Unit hp (Ideal.Quotient.mk _ P) = trTo k Unit hp
      (Ideal.Quotient.mk _ (MvPolynomial.monomial (Finsupp.single () 1) (P.coeff (Finsupp.single () 1)))) := by
    rw [trTo_mk, trTo_mk, Ideal.Quotient.eq, mem_orig_pow_iff]
    intro e he
    have h1 : e = Finsupp.single () (e ()) := by ext; simp
    have h2 : e () < 2 := by rw [h1] at he; simpa using he
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial]
    split_ifs with h3
    · rw [h3, sub_self]
    · have : e () = 0 := by
        by_contra hh
        apply h3
        rw [h1, show e () = 1 by omega]
      rw [h1, this]
      simpa [MvPolynomial.constantCoeff_eq] using h0
  rw [pow_eq_of_first p hp _ _ e, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, mem_orig_pow_iff] at h
  have h4 := h (p • Finsupp.single () 1) (by simp)
  rw [MvPolynomial.monomial_pow, MvPolynomial.coeff_monomial, if_pos rfl, pow_eq_zero_iff (by omega)] at h4
  rw [e, h4]
  simp

theorem units_trTo_surj {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) :
    Function.Surjective (Units.map (trTo k Unit hp : Jet k Unit p →* Jet k Unit 1)) := by
  have hs : ∀ b : Jet k Unit 1, ∃ a, trTo k Unit hp a = b := fun b => by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨Ideal.Quotient.mk _ P, rfl⟩
  intro u
  obtain ⟨a, ha⟩ := hs u
  obtain ⟨b, hb⟩ := hs (u⁻¹ : (Jet k Unit 1)ˣ)
  have : IsNilpotent (a * b - 1) := ⟨p, by
    rw [pow_eq_of_first p hp (a * b - 1) 0 (by simp [ha, hb]), zero_pow (by omega)]⟩
  have hu : IsUnit a := isUnit_of_mul_isUnit_left (y := b) (by simpa using this.isUnit_add_one)
  exact ⟨hu.unit, Units.ext ha⟩

theorem torus_tan : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (y₁ : overAt (𝟙 (Sp k)) (Jet k Unit 1) ⟶ splitTorus (Sp k) X), homAt (𝟙 (Sp k)) (jetAug : Jet k Unit 1 →ₐ[k] k) ≫ y₁ = 1 → ∃ y : overAt (𝟙 (Sp k)) (Jet k Unit p) ⟶ splitTorus (Sp k) X, homAt (𝟙 (Sp k)) (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 ∧ homAt (𝟙 (Sp k)) (toFirst k p hp) ≫ y = y₁ ∧ (y ^ p = 1 → y₁ = 1) := by
  intro k _ p _ _ hp X _ _ _ y₁ h₁
  let u₁ : Multiplicative X →* (Jet k Unit 1)ˣ :=
    MonoidHom.toHomUnits { toFun := fun χ => charVal y₁ χ.toAdd, map_one' := charVal_zero _
                           map_mul' := fun a b => charVal_add _ _ _ }
  obtain ⟨v, hv⟩ := Module.projective_lifting_property
    (MonoidHom.toAdditive (Units.map (trTo k Unit hp : Jet k Unit p →* Jet k Unit 1))).toIntLinearMap
    (MonoidHom.toAdditiveRight u₁).toIntLinearMap (units_trTo_surj p hp)
  obtain ⟨y, hy⟩ := exists_charVal (X := X) (spMap (algebraMap k (Jet k Unit p)) ≫ 𝟙 (Sp k))
    (AddMonoidHom.toMultiplicativeLeft v.toAddMonoidHom)
  have e : homAt (𝟙 (Sp k)) (toFirst k p hp) ≫ y = y₁ := charVal_ext fun χ => by
    rw [charVal_comp (toFirst k p hp : Jet k Unit p →+* Jet k Unit 1) y _ rfl, hy]
    exact congrArg (fun q => (Additive.toMul q).val) (LinearMap.congr_fun hv χ)
  refine ⟨y, ?_, e, fun h => ?_⟩
  · have : (jetAug : Jet k Unit p →ₐ[k] k) = (jetAug : Jet k Unit 1 →ₐ[k] k).comp (toFirst k p hp) :=
      jet_hom_ext fun _ => rfl
    rw [this, ← homAt_comp, Category.assoc, e, h₁]
  · refine charVal_ext fun χ => ?_
    rw [← e, charVal_comp (toFirst k p hp : Jet k Unit p →+* Jet k Unit 1) y _ rfl, charVal_one]
    have hpw : ∀ n : ℕ, charVal (y ^ n) χ = charVal y χ ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero y, charVal_one]; exact (pow_zero _).symm
      | succ n ih => rw [pow_succ y n, pow_succ _ n, charVal_mul, ih]
    have h1 : charVal y χ ^ p = 1 := by rw [← hpw, h, charVal_one]
    have : Nontrivial (Jet k Unit p) := (jetAug : Jet k Unit p →ₐ[k] k).toRingHom.domain_nontrivial
    have : CharP (Jet k Unit p) p := charP_of_injective_algebraMap (algebraMap k _).injective p
    have h2 := first_eq_zero p hp (charVal y χ - 1) (by rw [sub_pow_char, h1, one_pow, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2

end PositivityTheory.HtPt.Ce

end
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out.TLinPf

section Fn

variable {X Y Z : Scheme.{0}}

def evA {R : CommRingCat.{0}} (y : Spec R ⟶ Y) : Γ(Y, ⊤) ⟶ R := y.appTop ≫ (Scheme.ΓSpecIso R).hom

theorem evA_comp {R : CommRingCat.{0}} (y : Spec R ⟶ Y) (h : Y ⟶ X) (f : Γ(X, ⊤)) :
    (evA (y ≫ h)).hom f = (evA y).hom (h.appTop.hom f) := by
  rw [evA, evA, Scheme.Hom.comp_appTop]
  rfl

theorem evA_map {R R' : CommRingCat.{0}} (g : R ⟶ R') (y : Spec R ⟶ Y) (f : Γ(Y, ⊤)) :
    (evA (Spec.map g ≫ y)).hom f = g.hom ((evA y).hom f) := by
  have : evA (Spec.map g ≫ y) = evA y ≫ g := by
    rw [evA, evA, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc, Scheme.ΓSpecIso_naturality]
  rw [this]
  rfl

theorem evA_inj {R : CommRingCat.{0}} {y : Spec R ⟶ Y} {y' : Spec R ⟶ X} {f : Γ(Y, ⊤)} {g : Γ(X, ⊤)}
    (h : (evA y).hom f = (evA y').hom g) : y.appTop.hom f = y'.appTop.hom g :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1 h

theorem evA_ext {f g : Γ(Y, ⊤)} (h : ∀ (R : CommRingCat.{0}) (y : Spec R ⟶ Y), (evA y).hom f = (evA y).hom g) :
    f = g :=
  Scheme.OpenCover.ext_elem f g Y.affineOpenCover.openCover fun i => evA_inj (h _ (Y.affineOpenCover.f i))

theorem exists_glob (a : ∀ (R : CommRingCat.{0}), (Spec R ⟶ Y) → R)
    (ha : ∀ (R R' : CommRingCat.{0}) (g : R ⟶ R') (y : Spec R ⟶ Y), a R' (Spec.map g ≫ y) = g.hom (a R y)) :
    ∃ f : Γ(Y, ⊤), ∀ (R : CommRingCat.{0}) (y : Spec R ⟶ Y), (evA y).hom f = a R y := by
  let m : ∀ (R : CommRingCat.{0}), (Spec R ⟶ Y) → (Spec R ⟶ A1) := fun R y =>
    mOf ((Scheme.ΓSpecIso R).inv.hom (a R y))
  have hm : ∀ (R R' : CommRingCat.{0}) (g : R ⟶ R') (y : Spec R ⟶ Y), Spec.map g ≫ m R y = m R' (Spec.map g ≫ y) := by
    intro R R' g y
    simp only [m]
    rw [comp_mOf, ha]
    congr 1
    exact (congrArg (fun q => q.hom (a R y)) (Scheme.ΓSpecIso_inv_naturality g)).symm
  have key : ∀ (Z : Scheme.{0}) (R R' : CommRingCat.{0}) (y : Spec R ⟶ Y) (y' : Spec R' ⟶ Y) (u : Z ⟶ Spec R)
      (u' : Z ⟶ Spec R'), u ≫ y = u' ≫ y' → u ≫ m R y = u' ≫ m R' y' := by
    intro Z R R' y y' u u' e
    refine Z.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
    have e1 : Z.affineOpenCover.openCover.f i ≫ u = Spec.map (Spec.preimage (Z.affineOpenCover.f i ≫ u)) :=
      (Spec.map_preimage _).symm
    have e2 : Z.affineOpenCover.openCover.f i ≫ u' = Spec.map (Spec.preimage (Z.affineOpenCover.f i ≫ u')) :=
      (Spec.map_preimage _).symm
    rw [← Category.assoc, ← Category.assoc, e1, e2]
    refine (hm _ _ _ _).trans (Eq.trans ?_ (hm _ _ _ _).symm)
    rw [Spec.map_preimage, Spec.map_preimage, Category.assoc, Category.assoc, e]
  let 𝒰 := Y.affineOpenCover
  let F : Y ⟶ A1 := 𝒰.openCover.glueMorphisms (fun i => m _ (𝒰.f i))
    fun i j => key _ _ _ _ _ _ _ pullback.condition
  have hF : ∀ (R : CommRingCat.{0}) (y : Spec R ⟶ Y), y ≫ F = m R y := by
    intro R y
    refine Scheme.Cover.hom_ext (𝒰.openCover.pullback₁ y) _ _ fun i => ?_
    change pullback.fst y (𝒰.openCover.f i) ≫ y ≫ F = pullback.fst y (𝒰.openCover.f i) ≫ m R y
    have hι : 𝒰.openCover.f i ≫ F = m _ (𝒰.f i) := Scheme.Cover.ι_glueMorphisms 𝒰.openCover _ _ i
    rw [pullback.condition_assoc, hι]
    exact key _ _ _ _ _ _ _ pullback.condition.symm
  refine ⟨fnOf F, fun R y => ?_⟩
  change (Scheme.ΓSpecIso R).hom.hom (y.appTop.hom (fnOf F)) = _
  rw [← fnOf_comp, hF, fnOf_mOf]
  exact Iso.inv_hom_id_apply _ _

variable (Q : X ⟶ Y) [Flat Q] [Surjective Q]

theorem appTop_inj : Function.Injective Q.appTop.hom := fun a b h => by
  have : Epi Q := Flat.epi_of_flat_of_surjective _
  apply mOf_inj
  rw [← cancel_epi Q, comp_mOf, comp_mOf, h]

theorem desc_top [QuasiCompact Q] (ρ : Γ(X, ⊤))
    (hρ : ∀ {Z : Scheme.{0}} (y1 y2 : Z ⟶ X), y1 ≫ Q = y2 ≫ Q → y1.appTop.hom ρ = y2.appTop.hom ρ) :
    ∃ v : Γ(Y, ⊤), Q.appTop.hom v = ρ := by
  refine ⟨fnOf (EffectiveEpi.desc Q (mOf ρ) fun g₁ g₂ h => by rw [comp_mOf, comp_mOf, hρ _ _ h]), ?_⟩
  rw [← fnOf_comp, EffectiveEpi.fac, fnOf_mOf]

omit [Flat Q] in
theorem surj_res (U : Y.Opens) : Surjective (Q ∣_ U) :=
  MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict Q U).flip inferInstance

set_option backward.isDefEq.respectTransparency false in
omit [Flat Q] [Surjective Q] in
theorem app_topIso (U : Y.Opens) :
    Q.app U ≫ (Q ⁻¹ᵁ U).topIso.inv = U.topIso.inv ≫ (Q ∣_ U).appTop := by
  rw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  exact (Scheme.Hom.map_appLE _ _ _).symm

theorem app_inj (U : Y.Opens) : Function.Injective (Q.app U).hom := fun a b h => by
  have := surj_res Q U
  apply (ConcreteCategory.bijective_of_isIso U.topIso.inv).1
  apply appTop_inj (Q ∣_ U)
  have e := fun c => congrArg (fun q => q.hom c) (app_topIso Q U)
  exact (e a).symm.trans ((congrArg (Q ⁻¹ᵁ U).topIso.inv.hom h).trans (e b))

theorem gs_topIso (U : X.Opens) (s : Γ(X, U)) (y : Z ⟶ U.toScheme) (z : Z) :
    gs y z ⊤ (U.topIso.inv.hom s) = gs (y ≫ U.ι) z U s := by
  have hz : U.ι (y z) ∈ U := (y z).2
  rw [← gs_pull y U.ι z U hz, ← gs_res y z (show ⊤ ≤ U.ι ⁻¹ᵁ U by simp) trivial]
  congr 1
  change _ = (U.ι.appLE U ⊤ (by simp)).hom s
  rw [Scheme.Opens.ι_appLE]
  rfl

theorem desc_sec [QuasiCompact Q] (U : Y.Opens) (s : Γ(X, Q ⁻¹ᵁ U))
    (h : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ X), r ≫ Q = r' ≫ Q → ∀ z, r z ∈ Q ⁻¹ᵁ U → gs r z _ s = gs r' z _ s) :
    ∃ v : Γ(Y, U), (Q.app U).hom v = s := by
  have := surj_res Q U
  obtain ⟨v, hv⟩ := desc_top (Q ∣_ U) ((Q ⁻¹ᵁ U).topIso.inv.hom s) fun {Z} y1 y2 e => fn_ext fun z _ => by
    have e1 := gs_pull (𝟙 Z) y1 z ⊤ trivial ((Q ⁻¹ᵁ U).topIso.inv.hom s)
    have e2 := gs_pull (𝟙 Z) y2 z ⊤ trivial ((Q ⁻¹ᵁ U).topIso.inv.hom s)
    rw [Category.id_comp, gs_topIso] at e1 e2
    refine e1.trans ((h Z _ _ ?_ z (y1 z).2).trans e2.symm)
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e]
  refine ⟨U.topIso.hom.hom v, (ConcreteCategory.bijective_of_isIso (Q ⁻¹ᵁ U).topIso.inv).1 ?_⟩
  refine (congrArg (fun q => q.hom (U.topIso.hom.hom v)) (app_topIso Q U)).trans ?_
  rw [← hv]
  exact congrArg (Q ∣_ U).appTop.hom (Iso.hom_inv_id_apply U.topIso v)

theorem desc_unit [QuasiCompact Q] (U : Y.Opens) (s : Γ(X, Q ⁻¹ᵁ U)ˣ)
    (h : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ X), r ≫ Q = r' ≫ Q → ∀ z, r z ∈ Q ⁻¹ᵁ U → gm r z _ s = gm r' z _ s) :
    ∃ v : Γ(Y, U)ˣ, pullU Q U v = s := by
  have hm : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ X), r ≫ Q = r' ≫ Q → ∀ z, r z ∈ Q ⁻¹ᵁ U → r' z ∈ Q ⁻¹ᵁ U := by
    intro Z r r' e z hz
    change (r' ≫ Q) z ∈ U
    rw [← e]
    exact hz
  obtain ⟨v, hv⟩ := desc_sec Q U s.val fun Z r r' e z hz => by
    rw [gs_unit _ _ _ hz, gs_unit _ _ _ (hm Z r r' e z hz), h Z r r' e z hz]
  obtain ⟨w, hw⟩ := desc_sec Q U (s⁻¹).val fun Z r r' e z hz => by
    rw [gs_unit _ _ _ hz, gs_unit _ _ _ (hm Z r r' e z hz), map_inv, map_inv, h Z r r' e z hz]
  have e : v * w = 1 := app_inj Q U (by rw [map_mul, hv, hw, map_one, Units.mul_inv])
  exact ⟨⟨v, w, e, by rw [mul_comm, e]⟩, Units.ext hv⟩

theorem unit_ext_flat {U : Y.Opens} {a b : Γ(Y, U)ˣ} (h : ∀ x, Q x ∈ U → gm Q x U a = gm Q x U b) : a = b := by
  have : pullU Q U a = pullU Q U b := unit_ext fun x hx => by
    rw [gm_pull (𝟙 X) Q x U hx, gm_pull (𝟙 X) Q x U hx, Category.id_comp]
    exact h x hx
  exact Units.ext (app_inj Q U (congrArg Units.val this))

end Fn

section Gen

variable {X Y P : Scheme.{0}} {K : Type} [Fintype K]

theorem good_exists {M : LB P} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ P => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem desc_gen (Q : X ⟶ Y) [Flat Q] [Surjective Q] [QuasiCompact Q] {M : LB P} (hM : M.IsLB) (ψ : K → (Y ⟶ P))
    (ε : K → ℤ) (c : LB.Gen (LB.LinComb M (fun k => Q ≫ ψ k) ε)) (hc : c.IsGen)
    (h : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ X), r ≫ Q = r' ≫ Q → ∀ z J, Good M z J → val c r z J = val c r' z J) :
    ∃ c' : LB.Gen (LB.LinComb M ψ ε), c'.IsGen := by
  have le : ∀ j, Q ⁻¹ᵁ LB.wchart M ψ j ≤ LB.wchart M (fun k => Q ≫ ψ k) j := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have := fun j => desc_unit Q (LB.wchart M ψ j) (res (le j) (c.s j)) fun Z r r' e z hz => by
    have hz' : r' z ∈ Q ⁻¹ᵁ LB.wchart M ψ j := by
      change (r' ≫ Q) z ∈ LB.wchart M ψ j
      rw [← e]
      exact hz
    obtain ⟨J, hJ⟩ := good_exists hM z
    refine (gm_res r z (le j) hz _).trans (Eq.trans ?_ (gm_res r' z (le j) hz' _).symm)
    refine (gen_trans hc r z (le j hz) (hJ.mem _ r)).trans
      (Eq.trans ?_ (gen_trans hc r' z (le j hz') (hJ.mem _ r')).symm)
    refine congrArg₂ (· * ·) ?_ (h Z r r' e z J hJ)
    have e' : ∀ k, r ≫ Q ≫ ψ k = r' ≫ Q ≫ ψ k := fun k => by rw [reassoc_of% e]
    have e2 : (fun k => J (r ≫ Q ≫ ψ k)) = fun k => J (r' ≫ Q ≫ ψ k) := funext fun k => by rw [e']
    exact (congrArg (trF (fun k => Q ≫ ψ k) ε r z j) e2).trans (by simp only [trF, e'])
  choose v hv using this
  have hv' : ∀ j x, Q x ∈ LB.wchart M ψ j → gm Q x _ (v j) = gm (𝟙 X) x _ (c.s j) := fun j x hx => by
    have := gm_pull (𝟙 X) Q x _ hx (v j)
    rw [Category.id_comp, hv] at this
    exact this.symm.trans (gm_res (𝟙 X) x (le j) hx _)
  refine ⟨⟨v⟩, fun i j => unit_ext_flat Q fun x hx => ?_⟩
  refine (gm_res _ _ _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb M ψ ε Q x i j hx.1 hx.2) (gm_res _ _ _ hx _))).symm)
  refine (hv' i x hx.1).trans ((gen_trans hc (𝟙 X) x (le i hx.1) (le j hx.2)).trans
    (congrArg₂ (· * ·) ?_ (hv' j x hx.2).symm))
  simp only [trF, Category.id_comp]

theorem unflat {X' : Scheme.{0}} (L : LB P) (F : X' ⟶ P) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb (L.pull F) φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), c'.IsGen := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤ LB.wchart (L.pull F) φ (fun k _ => j k) := fun j y hy =>
    Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (c.s fun k _ => j k)⟩, fun i j => unit_ext fun x hx => ?_⟩
  refine (gm_res _ _ _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L _ ε (𝟙 Y) x i j hx.1 hx.2) (gm_res _ _ _ hx _))).symm)
  refine (gm_res _ _ _ hx.1 _).trans ((gen_trans hc (𝟙 Y) x (le i hx.1) (le j hx.2)).trans
    (congrArg₂ (· * ·) ?_ (gm_res _ _ _ hx.2 _).symm))
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  refine (gm_linComb L (fun _ : PUnit => F) (fun _ => 1) (𝟙 Y ≫ φ k) x (fun _ => i k) (fun _ => j k)
    (Set.mem_iInter.1 (le i hx.1) k) (Set.mem_iInter.1 (le j hx.2) k)).trans ?_
  simp

theorem gm_gen {N : LB Y} {t : LB.Gen N} (ht : t.IsGen) (y : Y) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j) :
    gm (𝟙 Y) y _ (t.s i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y _ (t.s j) := by
  have hm : y ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  exact (gm_res _ y _ hm _).symm.trans ((congrArg (gm _ y _) (ht i j)).trans ((map_mul _ _ _).trans
    (congrArg (_ * ·) (gm_res _ y _ hm _))))

theorem alg_iso {U : Type} [CommGroup U] (b g w a : U) : b * g⁻¹ * w * (g * a) = b * (w * a) := by
  rw [mul_right_comm b, mul_assoc, inv_mul_cancel_left, mul_assoc]

theorem gen_of_lbIso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) (a : LB.Gen A)
    (ha : a.IsGen) : ∃ b : LB.Gen B, b.IsGen := by
  have hw' : ∀ y p p' q q', y ∈ B.U p → y ∈ B.U p' → y ∈ A.U q → y ∈ A.U q' →
      gm (𝟙 Y) y (B.U p ⊓ A.U q) (w.s (p, q)) * gm (𝟙 Y) y _ (a.s q) =
        gm (𝟙 Y) y _ (B.g p p') * (gm (𝟙 Y) y (B.U p' ⊓ A.U q') (w.s (p', q')) * gm (𝟙 Y) y _ (a.s q')) := by
    intro y p p' q q' hp hp' hq hq'
    have hm : y ∈ B.U p ⊓ A.U q ⊓ (B.U p' ⊓ A.U q') := ⟨⟨hp, hq⟩, hp', hq'⟩
    have e1 := (gm_gen hw y (p, q) (p', q') ⟨hp, hq⟩ ⟨hp', hq'⟩).trans (congrArg (· * _) ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_res _ y _ hm _) ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hm _))))))
    refine (congrArg₂ (· * ·) e1 (gm_gen ha y q q' hq hq')).trans ?_
    exact alg_iso _ _ _ _
  have := fun p => glue_unit (B.U p) (fun q => B.U p ⊓ A.U q) (fun _ => inf_le_left) (fun y hy => by
      obtain ⟨q, hq⟩ := exists_chart hA y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, hq⟩)
    (fun q => @id (Γ(Y, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) * res inf_le_right (a.s q)) (fun q q' y hy => by
      rw [map_mul, map_mul, gm_res _ _ _ hy.1, gm_res _ _ _ hy.2]
      refine (hw' y p p q q' hy.1.1 hy.1.1 hy.1.2 hy.2.2).trans ?_
      rw [gm_self hB (𝟙 Y) y hy.1.1, one_mul]
      rfl)
  choose b hb using this
  have hb' : ∀ y p q, y ∈ B.U p → y ∈ A.U q →
      gm (𝟙 Y) y _ (b p) = gm (𝟙 Y) y (B.U p ⊓ A.U q) (w.s (p, q)) * gm (𝟙 Y) y _ (a.s q) := fun y p q hp hq => by
    have hm : y ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
    rw [← gm_res (𝟙 Y) y inf_le_left hm, hb, map_mul, gm_res _ _ _ hm]
    rfl
  refine ⟨⟨b⟩, fun i j => unit_ext fun y hy => ?_⟩
  obtain ⟨q, hq⟩ := exists_chart hA y
  rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy]
  exact (hb' y i q hy.1 hq).trans ((hw' y i j q q hy.1 hy.2 hq hq).trans (congrArg (_ * ·) (hb' y j q hy.2 hq).symm))

end Gen

end PositivityTheory.HtPt.Ce

end
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusUnit
open AddMonoidAlgebra (single)
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def twist {R : Type} [CommRing R] (u : Multiplicative X →* R) : AddMonoidAlgebra R X →ₐ[R] AddMonoidAlgebra R X :=
  AddMonoidAlgebra.lift R (AddMonoidAlgebra R X) X
    { toFun := fun x => single x.toAdd (u x)
      map_one' := by simp [AddMonoidAlgebra.one_def]
      map_mul' := fun a b => by simp [AddMonoidAlgebra.single_mul_single] }

theorem twist_single {R : Type} [CommRing R] (u : Multiplicative X →* R) (x : X) (r : R) :
    twist u (single x r) = single x (r * u (Multiplicative.ofAdd x)) := by
  simp [twist]

theorem twist_coeff {R : Type} [CommRing R] (u : Multiplicative X →* R) (a : AddMonoidAlgebra R X) :
    (twist u a).coeff 0 = a.coeff 0 := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single x r =>
    rw [twist_single]
    by_cases h : x = 0
    · subst h
      simp
    · simp [Finsupp.single_apply, h]

theorem const_apply {R : CommRingCat.{0}} (r : R) : (const X R).hom r = single 0 r := by
  simp [const, AddMonoidAlgebra.coe_algebraMap]

theorem mem_span_of {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) (δ : Γ(Y.left, ⊤))
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤))
    (h0 : ∀ (R : CommRingCat.{0}) (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left), (evA y).hom δ = 0 →
      (value φ y).hom ρ = 1) : ∃ c, (value φ y).hom ρ = 1 + (evA y).hom δ * c := by
  let g : R ⟶ CommRingCat.of (R ⧸ Ideal.span {(evA y).hom δ}) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  have h1 := h0 _ (φ ≫ g) (Spec.map g ≫ y) (by
    rw [evA_map]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
  rw [← value_comp] at h1
  have h2 : (value φ y).hom ρ - 1 ∈ Ideal.span {(evA y).hom δ} := Ideal.Quotient.eq.1 h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h2
  exact ⟨c, by rw [← hc]; ring⟩

theorem value_eq {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left)
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) : (value φ y).hom ρ = (evA (prodPoint φ y)).hom ρ := rfl

theorem value_map {R R' : CommRingCat.{0}} (g : R ⟶ R') (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left)
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    (value (φ ≫ g) (Spec.map g ≫ y)).hom ρ = g.hom ((value φ y).hom ρ) := by
  rw [← value_comp]
  rfl

section

variable (a : (splitTorus S X ⊗ Y).left ⟶ Y.left) (δ : Γ(Y.left, ⊤)) (hδ : δ * δ = 0)
    (ha : ∀ (R : CommRingCat.{0}) (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left),
      (evA (prodPoint φ y ≫ a)).hom δ = (evA y).hom δ)
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤))
    (h0 : ∀ (R : CommRingCat.{0}) (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left), (evA y).hom δ = 0 →
      (value φ y).hom ρ = 1)
    (hc : ∀ (R : CommRingCat.{0}) (φ φ' ψ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left),
      (∀ x : X, ψ.hom (single x 1) = φ.hom (single x 1) * φ'.hom (single x 1)) →
      (value ψ y).hom ρ = (value φ (prodPoint φ' y ≫ a)).hom ρ * (value φ' y).hom ρ)

include hδ in
theorem evA_sq (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left) : (evA y).hom δ * (evA y).hom δ = 0 := by
  rw [← map_mul, hδ, map_zero]

include h0 in
theorem coeff_mem (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left) :
    ∃ c, ((expand (X := X) y).hom ρ - 1).coeff 0 = (evA y).hom δ * c := by
  obtain ⟨c, h⟩ := mem_span_of (fromInt X R) (Spec.map (const X R) ≫ y) δ ρ h0
  refine ⟨c.coeff 0, ?_⟩
  rw [expand, h, evA_map, add_sub_cancel_left, const_apply]
  exact AddMonoidAlgebra.coeff_single_zero_mul _ _ _

include hc in
theorem expand_mul (R : CommRingCat.{0}) (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    ∃ u : Multiplicative X →* R, twist u ((expand y).hom ρ) =
      (expand (prodPoint φ y ≫ a)).hom ρ * (const X R).hom ((value φ y).hom ρ) := by
  let u : Multiplicative X →* R := φ.hom.toMonoidHom.comp (AddMonoidAlgebra.of ZU.{0} X)
  let σ : grpAlg X R ⟶ grpAlg X R := CommRingCat.ofHom (twist u).toRingHom
  have hσ : const X R ≫ σ = const X R := CommRingCat.hom_ext (twist u).comp_algebraMap
  have h1 := hc _ (fromInt X R) (φ ≫ const X R) (fromInt X R ≫ σ) (Spec.map (const X R) ≫ y) fun x => by
    change twist u ((fromInt X R).hom (single x 1)) = _ * (const X R).hom (φ.hom (single x 1))
    rw [fromInt_single, twist_single, const_apply, AddMonoidAlgebra.single_mul_single, add_zero]
    rfl
  have h2 := value_map σ (fromInt X R) (Spec.map (const X R) ≫ y) ρ
  rw [← Category.assoc, ← Spec.map_comp, hσ] at h2
  rw [h2, value_map, ← map_prodPoint, Category.assoc] at h1
  exact ⟨u, h1⟩

include hδ ha h0 hc in
theorem coeff_cocycle (R : CommRingCat.{0}) (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    ((expand (X := X) y).hom ρ - 1).coeff 0 =
      ((expand (X := X) (prodPoint φ y ≫ a)).hom ρ - 1).coeff 0 + ((value φ y).hom ρ - 1) := by
  obtain ⟨u, h1⟩ := expand_mul a ρ hc R φ y
  obtain ⟨c, h3⟩ := mem_span_of (fromInt X R) (Spec.map (const X R) ≫ prodPoint φ y ≫ a) δ ρ h0
  obtain ⟨c', h4⟩ := mem_span_of φ y δ ρ h0
  have h5 : twist u ((expand y).hom ρ - 1) = ((expand (prodPoint φ y ≫ a)).hom ρ - 1) +
      (const X R).hom ((value φ y).hom ρ - 1) := by
    rw [map_sub, map_one, h1, expand, h3, h4, evA_map, ha, map_sub, map_add, map_mul, map_one]
    have := congrArg (const X R).hom (evA_sq δ hδ R y)
    rw [map_mul, map_zero] at this
    linear_combination c * (const X R).hom c' * this
  rw [← twist_coeff u, h5, const_apply]
  simp

include hδ ha h0 hc in
theorem cobound :
    ∃ u : Γ(Y.left, ⊤)ˣ, (snd (splitTorus S X) Y).left.appTop.hom u.val = a.appTop.hom u.val * ρ := by
  obtain ⟨f, hf⟩ := exists_glob (Y := Y.left) (fun R y => ((expand (X := X) y).hom ρ - 1).coeff 0) fun R R' g y => by
    rw [expand_map, ← AddMonoidAlgebra.coeff_mapRingHom, map_sub, map_one]
  have hf0 : ∀ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), ∃ c, (evA y).hom f = (evA y).hom δ * c := fun R y => by
    rw [hf]
    exact coeff_mem δ ρ h0 R y
  have hff : f * f = 0 := evA_ext fun R y => by
    obtain ⟨c, h⟩ := hf0 R y
    rw [map_mul, h, map_zero]
    linear_combination c * c * evA_sq δ hδ R y
  have key : ∀ (R : CommRingCat.{0}) (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left),
      (evA y).hom f = (evA (prodPoint φ y ≫ a)).hom f + ((value φ y).hom ρ - 1) := fun R φ y => by
    rw [hf, hf]
    exact coeff_cocycle a δ hδ ha ρ h0 hc R φ y
  have fin : (snd (splitTorus S X) Y).left.appTop.hom (1 + f) = a.appTop.hom (1 + f) * ρ := by
    refine evA_ext fun R p => ?_
    obtain ⟨φ, y, rfl⟩ : ∃ φ y, p = prodPoint φ y :=
      ⟨Spec.preimage (p ≫ (fst (splitTorus S X) Y).left ≫ Rosenlicht.torusFst S X), p ≫ (snd (splitTorus S X) Y).left,
        (isPullback_prod X Y).hom_ext (by rw [prodPoint_fst, Spec.map_preimage]) (by rw [prodPoint_snd])⟩
    obtain ⟨c, h3⟩ := hf0 R (prodPoint φ y ≫ a)
    obtain ⟨c', h4⟩ := mem_span_of φ y δ ρ h0
    rw [map_mul, ← evA_comp, ← evA_comp, prodPoint_snd, map_add, map_add, map_one, map_one, key R φ y, ← value_eq,
      h3, h4, ha]
    linear_combination (-c * c') * evA_sq δ hδ R y
  exact ⟨⟨1 + f, 1 - f, by linear_combination -hff, by linear_combination -hff⟩, fin⟩

end

end PositivityTheory.HtPt.Ce

end
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusUnit Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section Act

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  (i : splitTorus S X ⟶ G) (W : Over S)

def actW : splitTorus S X ⊗ (W ⊗ G) ⟶ W ⊗ G := lift (snd _ _ ≫ fst _ _) ((fst _ _ ≫ i) * (snd _ _ ≫ snd _ _))

theorem lift_actW {Z : Over S} (t : Z ⟶ splitTorus S X) (v : Z ⟶ W ⊗ G) :
    lift t v ≫ actW i W = lift (v ≫ fst _ _) ((t ≫ i) * (v ≫ snd _ _)) := by
  simp [actW, MonObj.comp_mul]

theorem actW_fst : actW i W ≫ fst _ _ = snd _ _ ≫ fst _ _ := lift_fst _ _

theorem actW_assoc [IsMonHom i] {Z : Over S} (t t' : Z ⟶ splitTorus S X) (v : Z ⟶ W ⊗ G) :
    lift (t * t') v ≫ actW i W = lift t (lift t' v ≫ actW i W) ≫ actW i W := by
  simp [lift_actW, MonObj.mul_comp, _root_.mul_assoc]

variable {i} {q : G ⟶ B} [IsMonHom q]

theorem actW_q (h : IsPullback i (toUnit _) q η[B]) : actW i W ≫ W ◁ q = snd _ _ ≫ W ◁ q := by
  have : i ≫ q = 1 := h.w
  ext
  · simp [actW]
  · simp [actW, MonObj.mul_comp, this]

theorem exists_kp (h : IsPullback i (toUnit _) q η[B]) {Z : Scheme.{0}} (r r' : Z ⟶ (W ⊗ G).left)
    (e : r ≫ (W ◁ q).left = r' ≫ (W ◁ q).left) :
    ∃ p : Z ⟶ (splitTorus S X ⊗ (W ⊗ G)).left, p ≫ (actW i W).left = r ∧ p ≫ (snd _ _ : _ ⟶ W ⊗ G).left = r' := by
  have hw : r ≫ (W ⊗ G).hom = r' ≫ (W ⊗ G).hom := by
    rw [← Over.w (W ◁ q), ← Category.assoc, e, Category.assoc]
  let z1 : Over.mk (r' ≫ (W ⊗ G).hom) ⟶ W ⊗ G := Over.homMk r hw
  let z2 : Over.mk (r' ≫ (W ⊗ G).hom) ⟶ W ⊗ G := Over.homMk r' rfl
  have hq : z1 ≫ W ◁ q = z2 ≫ W ◁ q := Over.OverMorphism.ext e
  have h1 : z1 ≫ fst _ _ = z2 ≫ fst _ _ := by simpa using congrArg (· ≫ fst _ _) hq
  have h2 : (z1 ≫ snd _ _) ≫ q = (z2 ≫ snd _ _) ≫ q := by simpa using congrArg (· ≫ snd _ _) hq
  have hinv : (z2 ≫ snd _ _)⁻¹ ≫ q = ((z2 ≫ snd _ _) ≫ q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hd : ((z1 ≫ snd _ _) * (z2 ≫ snd _ _)⁻¹) ≫ q = toUnit _ ≫ η[B] := by
    rw [MonObj.mul_comp, hinv, h2, mul_inv_cancel, Hom.one_def]
  have hτ := h.lift_fst _ (toUnit _) (hd.trans (by simp))
  have e1 : lift (h.lift _ (toUnit _) (hd.trans (by simp))) z2 ≫ actW i W = z1 := by
    rw [lift_actW, hτ, inv_mul_cancel_right, ← h1]
    ext <;> simp
  exact ⟨(lift _ z2).left, congrArg (·.left) e1, congrArg (·.left) (lift_snd _ z2)⟩

omit [GrpObj G] [GrpObj B] [IsMonHom q] in
theorem isPullback_whisker : IsPullback (snd W G).left (W ◁ q).left q.left (snd W B).left := by
  have : IsPullback (snd W G) (W ◁ q) q (snd W B) :=
    ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst) (fun s => by simp)
      (fun s => by ext <;> simp [s.condition]) fun s m h1 h2 => by ext <;> simp [← h1, ← h2]⟩⟩
  exact this.map (Over.forget S)

omit [GrpObj G] in
theorem prodPoint_eq {Y : Over S} {R : CommRingCat.{0}} {s : Spec R ⟶ S} (φ : torusRing ZU X ⟶ R)
    (v : Over.mk s ⟶ Y) : prodPoint φ v.left = (lift (torusPoint φ s) v).left := by
  refine (isPullback_prod X Y).hom_ext ?_ ?_
  · rw [prodPoint_fst, ← Category.assoc, ← Over.comp_left, lift_fst, torusPoint_fst]
  · rw [prodPoint_snd, ← Over.comp_left, lift_snd]

end Act

theorem evA_spec {A R : CommRingCat.{0}} (g : A ⟶ R) (a : A) :
    (evA (Spec.map g)).hom ((Scheme.ΓSpecIso A).inv.hom a) = g.hom a := by
  have := evA_map g (𝟙 _) ((Scheme.ΓSpecIso A).inv.hom a)
  rw [Category.comp_id] at this
  rw [this]
  congr 1
  simp [evA]

theorem gm_id_top {Y Z : Scheme.{0}} (p : Z ⟶ Y) (z : Z) (c : Γ(Y, ⊤)ˣ) :
    gm (𝟙 Z) z ⊤ (Units.map p.appTop.hom.toMonoidHom c) = gm p z ⊤ c := by
  rw [← gm_comp_top (𝟙 Z) p z c _ rfl, Category.id_comp]

abbrev T1 (k : Type) [Field k] : Over (Sp k) := overAt (𝟙 (Sp k)) (Jet k Unit 1)

theorem desc_first {k : Type} [Field k] {X : Type} [AddCommGroup X] {G B : Over (Sp k)} [GrpObj G] [GrpObj B]
    {i : splitTorus (Sp k) X ⟶ G} [IsMonHom i] {q : G ⟶ B} [IsMonHom q] [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (h : IsPullback i (toUnit _) q η[B]) {P : Scheme.{0}} {M : LB P} (hM : M.IsLB)
    {K : Type} [Fintype K] (ψ : K → ((T1 k ⊗ B).left ⟶ P)) (ε : K → ℤ)
    (s0 : G ⟶ overAt (𝟙 (Sp k)) k)
    (h0 : DVR.fsum (fun a => (lift (s0 ≫ homAt (𝟙 (Sp k)) (jetAug : Jet k Unit 1 →ₐ[k] k)) (𝟙 G)).left ≫
      (T1 k ◁ q).left ≫ ψ a) ε = 0)
    (c₀ : LB.Gen (LB.LinComb M (fun a => (T1 k ◁ q).left ≫ ψ a) ε)) (hc₀ : c₀.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb M ψ ε), c'.IsGen := by
  obtain ⟨z0, hz0⟩ : ∃ z0 : G ⟶ (T1 k) ⊗ G, z0 = lift (s0 ≫ homAt (𝟙 (Sp k)) (jetAug : Jet k Unit 1 →ₐ[k] k)) (𝟙 G) := ⟨_, rfl⟩
  rw [← hz0] at h0
  have hpb := isPullback_whisker (q := q) (T1 k)
  have : Flat ((T1 k) ◁ q).left := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have : Surjective ((T1 k) ◁ q).left := MorphismProperty.of_isPullback (P := @Surjective) hpb inferInstance
  have : QuasiCompact ((T1 k) ◁ q).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hpb inferInstance
  have hz : z0.left ≫ (snd (T1 k) G).left = 𝟙 _ := by rw [← Over.comp_left, hz0, lift_snd]; rfl
  obtain ⟨c, hc, hn⟩ := DVR.exists_normalized hM _ ε c₀ hc₀ (snd (T1 k) G).left z0.left hz h0
  have hn' : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good M z J → val c (r ≫ z0.left) z J = 1 := by
    intro Z r z J hJ
    rw [← val_pull hJ, val, hn _ (fun a b e => congrArg (fun u => J (r ≫ u)) e)]
    exact map_one _
  have haq : (actW i (T1 k)).left ≫ ((T1 k) ◁ q).left = (snd _ _ : _ ⟶ (T1 k) ⊗ G).left ≫ ((T1 k) ◁ q).left :=
    congrArg (·.left) (actW_q (T1 k) h)
  obtain ⟨ρ, hρ⟩ := exists_ratio hM (funext fun a => by rw [reassoc_of% haq])
    (LB.pullGen M _ ε c (actW i (T1 k)).left) (LB.pullGen M _ ε c (snd _ _ : _ ⟶ (T1 k) ⊗ G).left)
    (DVR.pullGen_isGen_of_isGen _ _ _ hc _) (DVR.pullGen_isGen_of_isGen _ _ _ hc _)
  have hρ' : ∀ (Z : Scheme.{0}) (p : Z ⟶ (splitTorus (Sp k) X ⊗ ((T1 k) ⊗ G)).left) (z : Z) (J), Good M z J →
      val c (p ≫ (actW i (T1 k)).left) z J = gm p z ⊤ ρ * val c (p ≫ (snd _ _ : _ ⟶ (T1 k) ⊗ G).left) z J := by
    intro Z p z J hJ
    rw [← val_pull hJ, ← val_pull hJ]
    exact hρ Z p z J hJ
  let δ0 : Jet k Unit 1 := Ideal.Quotient.mk _ (MvPolynomial.X ())
  let δ : Γ(((T1 k) ⊗ G).left, ⊤) :=
    (fst (T1 k) G).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Jet k Unit 1))).inv.hom δ0)
  have hδ0 : δ0 * δ0 = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
    exact Ideal.pow_mem_pow (X_mem_orig _) _
  have ha : ∀ (R : CommRingCat.{0}) (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ ((T1 k) ⊗ G).left),
      (evA (prodPoint φ y ≫ (actW i (T1 k)).left)).hom δ = (evA y).hom δ := by
    intro R φ y
    simp only [δ]
    rw [← evA_comp, ← evA_comp, Category.assoc, ← Over.comp_left, actW_fst, Over.comp_left, ← Category.assoc,
      prodPoint_snd]
  have hfac : ∀ (R : CommRingCat.{0}) (y : Spec R ⟶ ((T1 k) ⊗ G).left), (evA y).hom δ = 0 →
      y = (y ≫ (snd (T1 k) G).left) ≫ z0.left := by
    intro R y hy
    obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of (Jet k Unit 1) ⟶ R, y ≫ (fst (T1 k) G).left = Spec.map g :=
      ⟨Spec.preimage _, (Spec.map_preimage _).symm⟩
    simp only [δ] at hy
    rw [← evA_comp] at hy
    erw [hg, evA_spec] at hy
    apply Over.tensorObj_ext
    · have e1 : z0.left ≫ (fst (T1 k) G).left = G.hom ≫ spMap ((jetAug : Jet k Unit 1 →ₐ[k] k) : Jet k Unit 1 →+* k) := by
        rw [← Over.comp_left, hz0, lift_fst, ← Over.w s0]
        simp [homAt, spMap]
      have e2 : (snd (T1 k) G).left ≫ G.hom = (fst (T1 k) G).left ≫ (T1 k).hom := (Over.w _).trans (Over.w _).symm
      change y ≫ (fst (T1 k) G).left = ((y ≫ (snd (T1 k) G).left) ≫ z0.left) ≫ (fst (T1 k) G).left
      rw [Category.assoc, e1, Category.assoc, reassoc_of% e2, ← Category.assoc, hg]
      change Spec.map g = Spec.map g ≫ (spMap _ ≫ 𝟙 _) ≫ spMap _
      rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        change g.hom (algebraMap k _ r) = g.hom (algebraMap k _ (jetAug (algebraMap k (Jet k Unit 1) r)))
        rw [AlgHom.commutes]
        rfl
      · rintro ⟨⟩
        change g.hom δ0 = g.hom (algebraMap k _ (jetAug δ0))
        rw [hy, aug_mk]
        simp
    · change y ≫ (snd (T1 k) G).left = ((y ≫ (snd (T1 k) G).left) ≫ z0.left) ≫ (snd (T1 k) G).left
      rw [Category.assoc, hz, Category.comp_id]
  have hv : ∀ (R : CommRingCat.{0}) (y : Spec R ⟶ ((T1 k) ⊗ G).left), (evA y).hom δ = 0 → ∀ z J, Good M z J →
      val c y z J = 1 := fun R y hy z J hJ =>
    (congrArg (fun w => val c w z J) (hfac R y hy)).trans (hn' _ _ _ _ hJ)
  obtain ⟨u, hu⟩ := cobound (actW i (T1 k)).left δ (by simp only [δ]; rw [← map_mul, ← map_mul, hδ0, map_zero, map_zero])
    ha ρ.val (fun R φ y hy => by
      have : (prodPoint φ y).appTop.hom ρ.val = (prodPoint φ y).appTop.hom 1 :=
        appTop_eq_of_gm _ _ _ 1 fun z => by
          obtain ⟨J, hJ⟩ := good_exists hM z
          have e := hρ' _ (prodPoint φ y) z J hJ
          rw [prodPoint_snd, hv R _ ((ha R φ y).trans hy) z J hJ, hv R y hy z J hJ, _root_.mul_one] at e
          rw [← e, map_one]
      change (Scheme.ΓSpecIso R).hom.hom ((prodPoint φ y).appTop.hom ρ.val) = 1
      rw [this, map_one, map_one])
    (fun R φ φ' ψ' y hm => by
      have e0 : prodPoint ψ' y ≫ (actW i (T1 k)).left = prodPoint φ (prodPoint φ' y ≫ (actW i (T1 k)).left) ≫ (actW i (T1 k)).left := by
        let v : Over.mk (y ≫ ((T1 k) ⊗ G).hom) ⟶ (T1 k) ⊗ G := Over.homMk y rfl
        have a1 := prodPoint_eq ψ' v
        have a2 := prodPoint_eq φ' v
        have a3 := prodPoint_eq φ (lift (torusPoint φ' (y ≫ ((T1 k) ⊗ G).hom)) v ≫ actW i (T1 k))
        rw [Over.comp_left, ← a2] at a3
        rw [← torusPoint_mul φ φ' ψ' _ hm] at a1
        exact (congrArg (· ≫ (actW i (T1 k)).left) a1).trans ((congrArg (·.left) (actW_assoc i (T1 k) _ _ v)).trans
          (congrArg (· ≫ (actW i (T1 k)).left) a3).symm)
      have : Units.map (prodPoint ψ' y).appTop.hom.toMonoidHom ρ =
          Units.map (prodPoint φ (prodPoint φ' y ≫ (actW i (T1 k)).left)).appTop.hom.toMonoidHom ρ *
            Units.map (prodPoint φ' y).appTop.hom.toMonoidHom ρ := unit_ext fun z _ => by
        obtain ⟨J, hJ⟩ := good_exists hM z
        have e1 := hρ' _ (prodPoint ψ' y) z J hJ
        have e2 := hρ' _ (prodPoint φ (prodPoint φ' y ≫ (actW i (T1 k)).left)) z J hJ
        have e3 := hρ' _ (prodPoint φ' y) z J hJ
        rw [prodPoint_snd] at e1 e2 e3
        rw [e0, e2, e3, ← _root_.mul_assoc] at e1
        rw [map_mul, gm_id_top, gm_id_top, gm_id_top]
        exact (mul_right_cancel e1).symm
      exact (congrArg (fun a => (Scheme.ΓSpecIso R).hom.hom a.val) this).trans (map_mul _ _ _))
  refine desc_gen ((T1 k) ◁ q).left hM ψ ε (DVR.scaleGen u c) (DVR.scaleGen_isGen u c hc) fun Z r r' e z J hJ => ?_
  have hs : ∀ r : Z ⟶ ((T1 k) ⊗ G).left, val (DVR.scaleGen u c) r z J = gm r z ⊤ u * val c r z J := fun r =>
    (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ (hJ.mem _ r) _))
  obtain ⟨p, rfl, rfl⟩ := exists_kp (T1 k) h r r' e
  rw [hs, hs, hρ' _ _ _ _ hJ, ← _root_.mul_assoc,
    gm_comp_top p _ z u (Units.map (actW i (T1 k)).left.appTop.hom.toMonoidHom u) rfl,
    gm_comp_top p _ z u (Units.map (actW i (T1 k)).left.appTop.hom.toMonoidHom u * ρ) hu, map_mul]

theorem triv_descend : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (T : TorusExtension G) (M : LB T.B.left) (y : overAt (𝟙 (Sp k)) (Jet k Unit 1) ⟶ G), letI := T.grpB; M.IsLB → homAt (𝟙 (Sp k)) (jetAug : Jet k Unit 1 →ₐ[k] k) ≫ y = 1 → (∃ c : LB.Gen (Out.translDiff G (M.pull T.q.left) y), c.IsGen) → ∃ c : LB.Gen (Out.translDiff T.B M (y ≫ T.q)), c.IsGen := by
  intro k _ G _ T M y
  letI := T.grpB
  letI := T.addCommGroup
  intro hM hy ⟨c, hc⟩
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  obtain ⟨c₁, hc₁⟩ := unflat M T.q.left _ _ c hc
  let W := overAt (𝟙 (Sp k)) (Jet k Unit 1)
  let ψ : Fin 2 → ((W ⊗ T.B).left ⟶ T.B.left) :=
    ![(lift (fst W T.B ≫ y ≫ T.q) (snd W T.B) ≫ μ[T.B]).left, (snd W T.B).left]
  have e0 : W ◁ T.q ≫ lift (fst W T.B ≫ y ≫ T.q) (snd W T.B) ≫ μ[T.B] =
      (lift (fst W G ≫ y) (snd W G) ≫ μ[G]) ≫ T.q := by
    rw [← Hom.mul_def, ← Hom.mul_def, MonObj.comp_mul, MonObj.mul_comp]
    simp
  obtain ⟨c₂, hc₂, -⟩ := exists_gen hM (φ' := fun a => (W ◁ T.q).left ≫ ψ a) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun a _ => by
      congr 2
      fin_cases a
      · exact (congrArg (·.left) e0).symm
      · exact (congrArg (·.left) (whiskerLeft_snd W T.q)).symm) c₁ hc₁
  let s0 : G ⟶ overAt (𝟙 (Sp k)) k := Over.homMk G.hom (by simp [spMap])
  refine desc_first T.isKernel hM ψ ![1, -1] s0 ?_ c₂ hc₂
  have e1 : lift (s0 ≫ homAt (𝟙 (Sp k)) (jetAug : Jet k Unit 1 →ₐ[k] k)) (𝟙 G) ≫
      W ◁ T.q ≫ lift (fst W T.B ≫ y ≫ T.q) (snd W T.B) ≫ μ[T.B] =
      lift (s0 ≫ homAt (𝟙 (Sp k)) (jetAug : Jet k Unit 1 →ₐ[k] k)) (𝟙 G) ≫ W ◁ T.q ≫ snd W T.B := by
    rw [e0, ← Hom.mul_def, ← Category.assoc, MonObj.comp_mul, lift_fst_assoc, Category.assoc, hy, MonObj.comp_one,
      _root_.one_mul]
    simp
  have e2 := congrArg (·.left) e1
  rw [DVR.fsum, Fin.sum_univ_two]
  refine (congrArg₂ (· + ·) (congrArg (Finsupp.single · (1 : ℤ)) e2) rfl).trans ?_
  exact (Finsupp.single_add _ _ _).symm.trans (Finsupp.single_zero _)

end PositivityTheory.HtPt.Ce

end
end

section

noncomputable section
namespace PositivityTheory.HtPt.Ce
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section

variable {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] {k : Type} [Field k] {x : Sp k ⟶ X0} {G' : Over (Sp k)} [GrpObj G']
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)

def fibPt (A : Type) [CommRing A] [Algebra k A] : (overAt (𝟙 (Sp k)) A ⟶ G') →* (overAt x A ⟶ G) :=
  (preHom (Over.homMk (𝟙 _) (by simp) : overAt x A ⟶ Over.mk ((overAt (𝟙 (Sp k)) A).hom ≫ x))).comp (pushHom h _)

theorem fibPt_left {A : Type} [CommRing A] [Algebra k A] (y : overAt (𝟙 (Sp k)) A ⟶ G') :
    (fibPt h A y).left = y.left ≫ φ := Category.id_comp _

theorem fibPt_inj (A : Type) [CommRing A] [Algebra k A] : Function.Injective (fibPt h A) := fun a b e => by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · rw [← fibPt_left h, ← fibPt_left h, e]
  · rw [Over.w a, Over.w b]

theorem fibPt_surj (A : Type) [CommRing A] [Algebra k A] : Function.Surjective (fibPt h A) := fun y =>
  ⟨Over.homMk (h.1.lift y.left (spMap (algebraMap k A)) (Over.w y)) ((h.1.lift_snd _ _ _).trans (Category.comp_id _).symm),
    Over.OverMorphism.ext ((fibPt_left h _).trans (h.1.lift_fst _ _ _))⟩

theorem fibPt_nat {A B : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (α : A →ₐ[k] B)
    (y : overAt (𝟙 (Sp k)) A ⟶ G') : homAt x α ≫ fibPt h A y = fibPt h B (homAt (𝟙 (Sp k)) α ≫ y) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, fibPt_left, fibPt_left, Over.comp_left, Category.assoc]
  rfl

theorem gen_fib {A : Type} [CommRing A] [Algebra k A] (L : LB G.left) (y : overAt (𝟙 (Sp k)) A ⟶ G')
    (c : LB.Gen (Out.translDiff G L (fibPt h A y))) (hc : c.IsGen) :
    ∃ c' : LB.Gen (Out.translDiff G' (L.pull φ) y), c'.IsGen := by
  let W' := overAt (𝟙 (Sp k)) A
  let W := overAt x A
  let u : Over.mk ((W' ⊗ G').hom ≫ x) ⟶ W := Over.homMk (fst W' G').left (by
    rw [← Over.w (fst W' G')]
    simp [W, W'])
  let v : Over.mk ((W' ⊗ G').hom ≫ x) ⟶ G := pushPt h.1.w (snd W' G')
  refine ⟨_, Out.LBxP.isGen_pullAlong L φ (lift u v).left _ _ _ (fun a => ?_) c hc⟩
  fin_cases a
  · have e := h.2 (W' ⊗ G') (fst W' G' ≫ y) (snd W' G') (u ≫ fibPt h A y) v (by
      rw [Over.comp_left, fibPt_left, Over.comp_left, Category.assoc]; rfl) rfl
    refine e.symm.trans (congrArg (·.left) (?_ : _ = lift u v ≫ ((fst W G ≫ fibPt h A y) * snd W G)))
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  · exact (congrArg (·.left) (lift_snd u v)).symm

end

theorem geompf_tan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0), GeomPF t x → TanPF t x p := by
  intro E _ _ _ H _ hstar X0 t hP k _ p _ _ x ⟨T, M, hM, hK, w, hw⟩ hp y hy hyp ⟨c, hc⟩
  letI := T.grpB
  letI := T.addCommGroup
  have := T.q_hom
  have := T.i_hom
  have := T.free
  have := T.finite
  have h := isGrpPullback_pullback t.G x
  obtain ⟨y', rfl⟩ := fibPt_surj h _ y
  have ha : (jetAug : Jet k Unit p →ₐ[k] k) = (jetAug : Jet k Unit 1 →ₐ[k] k).comp (toFirst k p hp) :=
    jet_hom_ext fun _ => rfl
  have hy' : homAt (𝟙 (Sp k)) (jetAug : Jet k Unit 1 →ₐ[k] k) ≫ homAt (𝟙 (Sp k)) (toFirst k p hp) ≫ y' = 1 := by
    apply fibPt_inj h
    rw [← Category.assoc, homAt_comp, ← ha, ← fibPt_nat, hy, map_one]
  have hc1 : ∃ c : LB.Gen (Out.translDiff t.G t.PP.L (fibPt h _ (homAt (𝟙 (Sp k)) (toFirst k p hp) ≫ y'))),
      c.IsGen := by
    rw [← fibPt_nat]
    exact ⟨c, hc⟩
  obtain ⟨c₁, hc₁⟩ := hc1
  obtain ⟨c₂, hc₂⟩ := gen_fib h _ _ c₁ hc₁
  obtain ⟨c₃, hc₃⟩ := triv_descend k _ T M _ hM hy'
    (gen_of_lbIso (DVR.linComb_isLB _ (DVR.linComb_isLB _ t.PP.isLB _ _) _ _)
      (DVR.linComb_isLB _ (DVR.linComb_isLB _ hM _ _) _ _) (LB.linCombIso w _ _) (DVR.linCombIso_isGen w hw _ _) c₂ hc₂)
  have hq := hK _ _ _ fun _ => ⟨⊤, trivial, _, LB.isGen_genPull _ c₃ hc₃ _⟩
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁, τ₁ ≫ T.i = homAt (𝟙 (Sp k)) (toFirst k p hp) ≫ y' :=
    ⟨T.isKernel.lift _ (toUnit _) (hq.trans (by simp)), T.isKernel.lift_fst _ _ _⟩
  have hi : ∀ {Z : Over (Sp k)} (a : Z ⟶ splitTorus (Sp k) T.X), a ≫ T.i = 1 → a = 1 := fun a e =>
    T.isKernel.hom_ext (by rw [e, MonObj.one_comp]) (toUnit_unique _ _)
  obtain ⟨τ, h1, h2, h3⟩ := torus_tan k p hp T.X τ₁ (hi _ (by rw [Category.assoc, hτ₁, hy']))
  have h4 := pow_first E H hstar X0 t hP k p hp x (fibPt h _ (τ ≫ T.i)) (fibPt h _ y')
    (by rw [fibPt_nat, ← Category.assoc, h1, MonObj.one_comp, map_one]) hy
    (by rw [fibPt_nat, fibPt_nat, ← Category.assoc, h2, hτ₁])
  rw [hyp, ← map_pow, ← map_one (fibPt h _)] at h4
  have h5 := h3 (hi _ (by rw [MonObj.pow_comp]; exact fibPt_inj h _ h4))
  rw [fibPt_nat, ← hτ₁, h5, MonObj.one_comp, map_one]

end PositivityTheory.HtPt.Ce

end
end
