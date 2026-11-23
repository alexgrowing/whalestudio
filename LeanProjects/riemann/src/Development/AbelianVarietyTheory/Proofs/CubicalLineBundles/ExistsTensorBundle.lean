import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.TensorBundle

open GlobalTheory.PrimNorm GlobalTheory.MulPull GlobalTheory.Serre

section Algebra

variable {O V W U I : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]
  [AddCommGroup U] [Fintype I]

def gramForm (β : V →+ V →+ U) (p : I → W →ₗ[O] V) (g : I → I → O) (x y : W) : U :=
  ∑ k : I × I, β (g k.1 k.2 • p k.1 x) (p k.2 y)

variable {β : V →+ V →+ U} {p : I → W →ₗ[O] V} {g : I → I → O} {br : O ≃+* O}

theorem gramForm_add_left (x y z : W) : gramForm β p g (x + y) z = gramForm β p g x z + gramForm β p g y z := by
  simp only [gramForm, map_add, smul_add, AddMonoidHom.add_apply, Finset.sum_add_distrib]

theorem gramForm_add_right (x y z : W) : gramForm β p g x (y + z) = gramForm β p g x y + gramForm β p g x z := by
  simp only [gramForm, map_add, Finset.sum_add_distrib]

theorem gramForm_zero (y : W) : gramForm β p g 0 y = 0 := by
  simp [gramForm]

theorem gramForm_adj (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (c : O) (x y : W) :
    gramForm β p g (c • x) y = gramForm β p g x (br c • y) := by
  simp only [gramForm, map_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_comm, ha]

theorem gramForm_comm (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) (x y : W) : gramForm β p g x y = gramForm β p g y x :=
  Fintype.sum_equiv (Equiv.prodComm I I) _ _ fun k => by
    rw [ha, hs, ← hg]
    rfl

theorem gramForm_polar (hs : ∀ x y, β x y = β y x) (ha : ∀ c x y, β (c • x) y = β x (br c • y))
    (hg : ∀ i j, g j i = br (g i j)) {w : O} (hw : w + br w = 1) (x y : W) :
    gramForm β p g (x + y) (w • (x + y)) + -gramForm β p g x (w • x) + -gramForm β p g y (w • y) +
      gramForm β p g 0 (w • 0) = gramForm β p g x y := by
  have e : gramForm β p g x y = gramForm β p g x (w • y) + gramForm β p g y (w • x) := by
    rw [gramForm_comm hs ha hg y, gramForm_adj ha, ← gramForm_add_right, ← add_smul, hw, one_smul]
  rw [e, gramForm_zero, smul_add, gramForm_add_left, gramForm_add_right, gramForm_add_right]
  abel

theorem gramForm_pure (ha : ∀ c x y, β (c • x) y = β x (br c • y)) (hb : ∀ c, br (br c) = c)
    {x y : W} {u v : V} {s s' : I → O} (hx : ∀ i, p i x = s i • u) (hy : ∀ i, p i y = s' i • v) :
    gramForm β p g x y = β ((∑ k : I × I, br (s' k.2) * (g k.1 k.2 * s k.1)) • u) v := by
  rw [Finset.sum_smul, map_sum, AddMonoidHom.finset_sum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [hx, hy, mul_smul (br _), ha (br _), hb, mul_smul]

theorem hermitian_expand {M : Type} [AddCommGroup M] [Module O M] (h : M →ₗ[O] M →+ O)
    (hh : ∀ x y, h y x = br (h x y)) (e : I → M) (s s' : I → O) :
    ∑ k : I × I, br (s' k.2) * (h (e k.1) (e k.2) * s k.1) = h (∑ i, s i • e i) (∑ i, s' i • e i) := by
  have sm : ∀ c x y, h x (c • y) = br c * h x y := fun c x y => by
    rw [hh (c • y) x, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, map_mul, ← hh]
  rw [map_sum h, AddMonoidHom.finset_sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sm, map_smul, AddMonoidHom.smul_apply, smul_eq_mul, mul_comm (s i)]

end Algebra

section Geometry

variable {S : Scheme.{0}} {O : Type} [CommRing O] {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A]
  [IsCommMonObj A] {L : LB G.left}

def lamForm (a : OAct O G) (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta G L), t.IsGen) (T : Over S) :
    Pts a T →+ Pts a T →+ Additive (PullClass L T.left) :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (diff₂ (ptCls L T) x.hom y.hom))
    fun y z => congrArg Additive.ofMul (diff₂_mul_right (diff₃_ptCls hL hT) x.hom y.hom z.hom))
    fun x y => AddMonoidHom.ext fun z => congrArg Additive.ofMul (diff₂_mul_left (diff₃_ptCls hL hT) x.hom y.hom z.hom)

variable {I : Type} [Fintype I]

def prodMap (f f' : I → (A ⟶ G)) (k : I × ULift.{0} (Finset (Fin 2))) : A.left ⟶ G.left :=
  (psum G ![f k.1, f' k.1] k.2.down).left

def prodExp (k : I × ULift.{0} (Finset (Fin 2))) : ℤ := (-1) ^ (2 - k.2.down.card)

def prodCls (L : LB G.left) (f f' : I → (A ⟶ G)) {Y : Scheme.{0}} (ψ : Y ⟶ A.left) : PullClass L Y :=
  ∏ k, cls L (ψ ≫ prodMap f f' k) ^ prodExp k

omit [GrpObj A] [IsCommMonObj A] in
theorem prodCls_left (f f' : I → (A ⟶ G)) {T : Over S} (x : T ⟶ A) :
    prodCls L f f' x.left = ∏ k, diff₂ (ptCls L T) (x ≫ f k) (x ≫ f' k) := by
  rw [prodCls, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun k _ => prod_square x (f k) (f' k) (cls L)

end Geometry

theorem exists_tensor_bundle : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type) [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (br : O ≃+* O) (w : O) (L : LB G.left) (h : M →ₗ[O] M →+ O), Module.Finite O M → Module.Projective O M → w + br w = 1 → (∀ c, br (br c) = c) → (∀ x y, h y x = br (h x y)) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ c, LamEq L (a.act c) (𝟙 G) L (𝟙 G) (a.act (br c))) →
  ∃ N : LB A.left, N.IsLB ∧ Out.Rigidified A N ∧ (∃ t : LB.Gen (Theta A N), t.IsGen) ∧ ∀ m m', LamEq N (t.tmul m) (t.tmul m') L (a.act (h m m')) (𝟙 G) := by
  intro S O _ G A _ _ _ _ a b M _ _ t br w L h _ _ hw hb hh hL hT ha
  obtain ⟨P⟩ := Summand.nonempty O M
  let c : Fin P.n → M →ₗ[O] O := fun i => LinearMap.proj i ∘ₗ P.incl
  let e : Fin P.n → M := fun i => P.proj (Pi.single i 1)
  have he : ∀ m, ∑ i, c i m • e i = m := fun m => by
    have : ∑ i, P.incl m i • (Pi.single i 1 : Fin P.n → O) = P.incl m := by
      ext j
      simp [Pi.single_apply]
    simp only [e, ← map_smul, ← map_sum]
    exact (congrArg P.proj this).trans congr($(P.proj_incl) m)
  let π : Fin P.n → (A ⟶ G) := fun i => t.mapLeft (IsTensor.self a) (c i)
  have hπ : ∀ i, IsLinearHom b a (π i) := fun i => t.isLinearHom_mapLeft _ _
  let g : Fin P.n → Fin P.n → O := fun i j => h (e i) (e j)
  let f : Fin P.n × Fin P.n → (A ⟶ G) := fun k => π k.1 ≫ a.act (g k.1 k.2)
  let f' : Fin P.n × Fin P.n → (A ⟶ G) := fun k => b.act w ≫ π k.2
  let B : ∀ T : Over S, Pts b T → Pts b T → Additive (PullClass L T.left) := fun T =>
    gramForm (lamForm a hL hT T) (fun i => Pts.post (hπ i) T) g
  have hs : ∀ (T : Over S) x y, lamForm a hL hT T x y = lamForm a hL hT T y x := fun T x y =>
    congrArg Additive.ofMul (diff₂_comm _ _)
  have hadj : ∀ (T : Over S) (r : O) x y, lamForm a hL hT T (r • x) y = lamForm a hL hT T x (br r • y) :=
    fun T r x y => by
      have := ha r
      unfold LamEq at this
      rw [Category.comp_id, Category.comp_id] at this
      exact congrArg Additive.ofMul (diff₂_ptCls_adj hL this x.hom y.hom)
  have hq : ∀ (T : Over S) (x : T ⟶ A), prodCls L f f' x.left = (B T (Pts.mk b x) (w • Pts.mk b x)).toMul :=
    fun T x => by
      rw [prodCls_left]
      refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (toMul_sum _ _).symm
      simp only [f, f', ← Category.assoc]
      rfl
  have h₂ : ∀ (T : Over S) (x y : T ⟶ A), diff₂ (fun q : T ⟶ A => prodCls L f f' q.left) x y =
      (B T (Pts.mk b x) (Pts.mk b y)).toMul := fun T x y => by
    simp only [diff₂, hq]
    exact congrArg Additive.toMul (gramForm_polar (hs T) (hadj T) (fun i j => hh _ _) hw (Pts.mk b x) (Pts.mk b y))
  refine ⟨LB.LinComb L (prodMap f f') prodExp, DVR.linComb_isLB _ hL _ _, ?_, ?_, fun m m' => ?_⟩
  · refine hasGen_nested (K' := PUnit) hL _ _ (fun _ => eSec A) (fun _ => 1) ?_
    rw [Fintype.prod_unique, zpow_one]
    refine (hq _ η[A]).trans ?_
    have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by simp [Hom.one_def]
    rw [e]
    exact congrArg Additive.toMul (gramForm_zero _)
  · refine hasGen_nested hL _ _ (thφ A (x3 A)) thε ((GlobalTheory.AbLaw.Cube.prod_theta (prodCls L f f')).trans
      ((prod_cub _ _ _ (prodCls L f f')).trans ?_))
    have e := diff₂_mul_left_eq (m := fun q : G3 A ⟶ A => prodCls L f f' q.left) (x3 A 0) (x3 A 1) (x3 A 2)
    rw [h₂, h₂, h₂, Pts.mk_mul] at e
    exact mul_eq_right.1 (e.symm.trans (congrArg Additive.toMul (gramForm_add_left _ _ _)))
  · refine lbIso_nested hL _ _ _ _ _ _ ((prod_square_id _ _ (prodCls L f f')).trans
      (Eq.trans ?_ (prod_square_id _ _ (cls L)).symm))
    have k : ∀ (u : G ⊗ G ⟶ G) (m : M) i,
        Pts.post (hπ i) _ (Pts.mk b (u ≫ t.tmul m)) = c i m • Pts.mk a u := fun u m i => Pts.ext (by
      simp only [Pts.hom_post, Pts.hom_mk, Pts.hom_smul, π, Category.assoc, IsTensor.tmul_mapLeft,
        IsTensor.self_tmul])
    rw [h₂, Category.comp_id]
    refine congrArg Additive.toMul ((gramForm_pure (hadj _) hb (k _ m) (k _ m')).trans ?_)
    rw [(hermitian_expand h hh e (fun i => c i m) fun i => c i m' :
      ∑ k : Fin P.n × Fin P.n, br (c k.2 m') * (g k.1 k.2 * c k.1 m) = _), he, he]
    rfl

end GlobalTheory.TensorBundle
