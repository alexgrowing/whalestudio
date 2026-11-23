import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrD
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section
namespace PositivityTheory.Xgn.GermSystem.Bc
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
    ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]
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
  obtain ⟨V, _, _, ⟨M⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G S x
  obtain ⟨V', _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G S₂ (spMap f ≫ x)
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

theorem gm_unit_bc {Z : Scheme.{0}} {κ : Type} {m : ℕ} (u : (Jet S κ m)ˣ) (r : Z ⟶ Sp (Jet S₂ κ m)) (z : Z) :
    gm r z ⊤ (unitΓ (Units.map (jetCoef f κ m).toMonoidHom u)) =
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
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
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
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
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
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
      corr_of_val t.PP.isLB fun z J hJ => ?_⟩
    refine (h m _ _ z J hJ).trans ((val_corr hJ hc _).trans ?_)
    rw [val_scale t _ _ _ hJ, val_scale t _ _ _ hJ, ← map_inv, gm_unit_bc f x,
        h.pe _ _ _ _ (fun j => (MvPolynomial.map_X f _).symm) (fun j => (MvPolynomial.map_X f _).symm) _ hJ]
  ad a := by
    obtain ⟨wL, hw, hm⟩ := hf.ad a
    refine ⟨wL, hw, fun m => ?_⟩
    obtain ⟨u, hu, hc⟩ := hm m
    refine ⟨Units.map (jetCoef f _ m).toMonoidHom u, by rw [← coef_psJet, ← hu]; rfl,
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

end PositivityTheory.Xgn.GermSystem.Bc
