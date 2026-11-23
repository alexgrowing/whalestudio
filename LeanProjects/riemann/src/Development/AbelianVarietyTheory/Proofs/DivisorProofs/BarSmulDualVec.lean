import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply

set_option autoImplicit false

noncomputable section

open CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.GroupBplus (IsPropG TorsionMap dualVec EF_dualVec)
open GlobalTheory.RingChain
open GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.ChainPts.SysB.RingAct

section Unit

variable {p h o : ℕ} {A : Type} [CommRing A] {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie] [Module A Lie]
  [AddCommGroup Om] [Module A Om]

theorem smul_top_of_isUnit {X : Type} [AddCommGroup X] [Module A X] {u : A} (hu : IsUnit u) :
    u • (⊤ : Submodule A X) = ⊤ := by
  obtain ⟨u, rfl⟩ := hu
  refine eq_top_iff.2 fun x _ => (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(u⁻¹ : Aˣ) • x, trivial, ?_⟩
  rw [← Units.smul_def, smul_inv_smul]

theorem map_of_isUnit (C : RChain p A h o π γ Lie Om) (hp : IsUnit (p : A)) (hπ : π ∣ (p : A))
    (M : Matrix (Fin h) (Fin h) ℤ) (l : Lie → Lie) (m : Om → Om) : C.Map C (RingHom.id A) M l m := by
  have hb : baseOf π h = ⊤ := smul_top_of_isUnit (isUnit_of_dvd_unit hπ hp)
  have hq : ∀ n, Subsingleton (Qt (C.L n) (baseOf π h)) := fun n =>
    Submodule.Quotient.subsingleton_iff.2 (by rw [hb, Submodule.comap_top])
  haveI : Subsingleton (Lie ⧸ (p : A) • (⊤ : Submodule A Lie)) :=
    Submodule.Quotient.subsingleton_iff.2 (smul_top_of_isUnit hp)
  haveI : Subsingleton (Qt (C.L 0) (baseOf π h) ⧸ LinearMap.range C.j) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  exact ⟨fun n x _ => C.base_le n (hb ▸ trivial), fun _ _ _ _ _ => Subsingleton.elim _ _,
    fun _ _ _ _ _ => Subsingleton.elim _ _, fun _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _,
    fun _ _ _ _ _ _ _ => Subsingleton.elim _ _⟩

end Unit

section Groups

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G H : PDivGroup p O}

theorem char_ext {χ ψ : G.dual.Tate} (h : ∀ n, charElem χ n = charElem ψ n) : χ = ψ :=
  TateOver.ext (funext fun n => AlgHom.ext fun φ => by rw [← apply_charElem, ← apply_charElem, h])

variable (O' : Type) [CommRing O'] [Algebra O O']

def bcCharHom (G : PDivGroup p O) : G.dual.Tate →+ (G.baseChange O').dual.Tate :=
  AddMonoidHom.mk' (bcChar O') fun χ ψ => char_ext fun n => by
    rw [charElem_add, charElem_bcChar, charElem_bcChar, charElem_bcChar, charElem_add,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def bcTateHom (G : PDivGroup p O) : G.Tate →+ (G.baseChange O').Tate :=
  AddMonoidHom.mk' (bcTate O') fun x y => TateOver.ext_conv fun n =>
    (PDiv.toBaseChange_pts_bijective (R := O) O' (A := G.A n) O' fun _ => rfl).1 (by
      rw [TateOver.add_conv, map_mul]
      have k : ∀ z : G.Tate, (PDiv.toBaseChange O O' (G.A n)).pts O' (fun _ => rfl) ((bcTate O' z).conv n) =
          PDiv.ptsPush (G.A n) (Algebra.ofId O O') (z.conv n) := fun z =>
        WithConv.ofConv_injective (AlgHom.ext fun a => one_mul _)
      rw [k, k, k, TateOver.add_conv, map_mul])

theorem tateMap_bcChar (f : G ⟶ H) (χ : H.dual.Tate) :
    tateMap _ _ O' (dualHom _ _ (PDivGroup.baseChangeMap O' f)) (bcChar O' χ) = bcChar O' (tateMap _ _ O (dualHom G H f) χ) :=
  char_ext fun n => by
    rw [charElem_tateMap, charElem_bcChar, charElem_bcChar, charElem_tateMap]
    rfl

def toSelf (G : PDivGroup p O) : G.baseChange O ⟶ G := SemiHom.toHom (G.toBase O)

theorem tateMap_toSelf (χ : G.dual.Tate) : tateMap _ _ O (dualHom _ _ (toSelf G)) χ = bcChar O χ :=
  char_ext fun n => by
    rw [charElem_tateMap, charElem_bcChar]
    rfl

theorem toBase_omegaMap (f : G ⟶ H) (w : H.omega) :
    (G.toBase O').omega (omegaMap G H f w) = omegaMap _ _ (PDivGroup.baseChangeMap O' f) ((H.toBase O').omega w) :=
  SemiHom.omega_naturality _ _ f _ (fun _ _ => rfl) w

theorem polBC_adj (pol : G ≅ G.dual) (f g : G ⟶ G) (h : g ≫ pol.hom = pol.hom ≫ dualHom G G f) :
    PDivGroup.baseChangeMap O' g ≫ polBC pol O' = polBC pol O' ≫ dualHom _ _ (PDivGroup.baseChangeMap O' f) := by
  have h1 : (dualBaseChange O' G).hom ≫ PDivGroup.baseChangeMap O' (dualHom G G f) =
      dualHom _ _ (PDivGroup.baseChangeMap O' f) ≫ (dualBaseChange O' G).hom :=
    PDivGroup.hom_ext fun n => BialgHom.ext fun x => CartierDual.baseChange_map O' (f.app n) x
  have h2 : PDivGroup.baseChangeMap O' g ≫ PDivGroup.baseChangeMap O' pol.hom = PDivGroup.baseChangeMap O' pol.hom ≫ PDivGroup.baseChangeMap O' (dualHom G G f) :=
    ((baseChangeFunctor p O O').map_comp _ _).symm.trans
      ((congrArg (PDivGroup.baseChangeMap O') h).trans ((baseChangeFunctor p O O').map_comp _ _))
  rw [polBC, ← Category.assoc, h2, Category.assoc, Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, ← h1, Iso.inv_hom_id_assoc]

theorem omegaMap_polBC_bijective (pol : G ≅ G.dual) : Function.Bijective (omegaMap _ _ (polBC pol O')) := by
  let e : G.baseChange O' ≅ (G.baseChange O').dual := (baseChangeFunctor p O O').mapIso pol ≪≫ (dualBaseChange O' G).symm
  have he : polBC pol O' = e.hom := rfl
  rw [he]
  refine Function.bijective_iff_has_inverse.2 ⟨omegaMap _ _ e.inv, fun w => ?_, fun w => ?_⟩
  · rw [← LinearMap.comp_apply, ← omegaMap_comp, e.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← omegaMap_comp, e.hom_inv_id, omegaMap_id, LinearMap.id_apply]

end Groups

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a :=
  Subtype.ext (show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E) by
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

theorem smul_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) (i : Fin n) :
    a • b i = ∑ k, actMat b a k i • b k := by
  simp only [actMat_apply, Module.Basis.sum_repr]

theorem bar_smul_dualVec {n m : ℕ} (e : m = n) (b : Module.Basis (Fin n) ℤ Dw.La) (a : 𝓞 E) (j : Fin n) :
    H.bar a • dualVec (b.reindex (finCongr e.symm)) (Fin.cast e.symm j) =
      ∑ i, actMat b a j i • dualVec (b.reindex (finCongr e.symm)) (Fin.cast e.symm i) := by
  subst e
  have hf : ∀ y z : Dw.La, (∀ i, Dw.EF (b i) y = Dw.EF (b i) z) → y = z := fun y z h =>
    Dw.unimod.1 (b.ext fun i => neg_injective (by
      rw [LinearMap.IsAlt.neg Dw.alt, LinearMap.IsAlt.neg Dw.alt, h]))
  refine hf _ _ fun i => ?_
  rw [← Dw.adj, EF_dualVec, map_sum]
  simp [EF_dualVec, actMat_apply, Finsupp.single_apply]

end Lattice

theorem ringAct (hM : MapSt) : RingActSt := by
  intro E _ _ _ H Dw p _ D A _ t GG act pol θ ε τ hP n o e b π γ Lie Om _ _ _ _ cω pr C a l m m' hC hm hm' hl hπ
  by_cases hp : IsUnit (p : A)
  · exact map_of_isUnit C hp hπ _ _ _
  obtain ⟨S, _, -, -, hε, eL, eO, hL, hO, hOf⟩ := hC hp
  subst e
  have ht' : ∀ j : Fin GG.height, tateMap _ _ S.R (dualHom _ _ (PDivGroup.baseChangeMap S.R (act a : GG ⟶ GG)))
      (((ct hP rfl b).baseChange S.R hε).t' j) = ∑ i, actMat b a j i • ((ct hP rfl b).baseChange S.R hε).t' i := fun j => by
    have h1 := hP.adj (H.bar a)
    rw [bar_bar] at h1
    have h2 : tateMap _ _ A (dualHom GG GG (act a)) ((ct hP rfl b).t' j) = ∑ i, actMat b a j i • (ct hP rfl b).t' i := by
      change tateMap _ _ A (dualHom GG GG (act a)) (tateMap GG GG.dual A pol.hom (τ _)) =
        ∑ i, actMat b a j i • tateMap GG GG.dual A pol.hom (τ _)
      rw [← tateMap_comp, ← h1, tateMap_comp, ← hP.lin]
      erw [bar_smul_dualVec rfl b a j]
      simp only [map_sum, map_zsmul]
      rfl
    refine (tateMap_bcChar S.R _ _).trans ?_
    rw [h2]
    exact (map_sum (bcCharHom S.R GG) _ _).trans (Finset.sum_congr rfl fun i _ => map_zsmul (bcCharHom S.R GG) _ _)
  have ht : ∀ i : Fin GG.height, tateMap _ _ S.R (PDivGroup.baseChangeMap S.R (act a : GG ⟶ GG))
      (((ct hP rfl b).baseChange S.R hε).t i) = ∑ k, actMat b a k i • ((ct hP rfl b).baseChange S.R hε).t k := fun i => by
    have h0 : ∀ k, (ct hP rfl b).t k = τ (b k) := fun k => congrArg τ (by simp)
    change tateMap _ _ S.R _ (bcTate S.R _) = ∑ k, actMat b a k i • bcTateHom S.R GG ((ct hP rfl b).t k)
    rw [tateMap_bcTate, h0, ← hP.lin, smul_basis]
    change bcTateHom S.R GG _ = _
    simp only [map_sum, map_zsmul, h0]
  have hbij := omegaMap_polBC_bijective S.R pol
  refine (hM p D S S _ _ _ _ A A (RingHom.id A) _ o rfl rfl π π γ γ Lie Om Lie Om _ _ _ _ C C
    (toSelf _ ≫ PDivGroup.baseChangeMap S.R (act a : GG ⟶ GG)) (actMat b a) l m hOf hOf (fun _ => rfl) (fun _ => rfl)
    (fun j => ?_) (fun y j => ?_) fun w x hx => ?_).1
  · rw [dualHom_comp, tateMap_comp]
    erw [ht' j]
    simp only [map_sum, map_zsmul, tateMap_toSelf]
    rfl
  · have h1 : ∀ v, eL (1 ⊗ₜ l y) v = eL (1 ⊗ₜ y) (omegaMap _ _ (PDivGroup.baseChangeMap S.R (act a : GG ⟶ GG)) v) := fun v => by
      obtain ⟨v, rfl⟩ := hbij.2 v
      obtain ⟨v, rfl⟩ := eO.surjective v
      induction v with
      | zero => simp
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul r w =>
        rw [← mul_one r, ← smul_eq_mul, ← TensorProduct.smul_tmul']
        simp only [map_smul]
        rw [hO, hL, hl, ← hL, hm', toBase_omegaMap]
    rw [ConstTate.alDual_apply, h1, ← dlog_tateMap]
    erw [ht' j]
    simp [mv, Matrix.mulVec, dotProduct, map_sum, map_zsmul]
  · have h1 : eO (1 ⊗ₜ m w) = omegaDualMap _ _ (PDivGroup.baseChangeMap S.R (act a : GG ⟶ GG)) (eO (1 ⊗ₜ w)) := by
      have h2 := hP.adj (H.bar a)
      rw [bar_bar] at h2
      apply hbij.1
      rw [hO, hm, toBase_omegaMap, ← hO, omegaDualMap_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← omegaMap_comp, ← omegaMap_comp, polBC_adj S.R pol _ _ h2]
    rw [h1, ← map_smul, hx]
    simp only [ConstTate.al_apply, map_sum, map_smul, ← hodgeTate_tateMap, ht, map_zsmul, Finset.smul_sum, mv,
      Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul, Int.cast_smul_eq_zsmul]
    rfl

end GlobalTheory.ChainPts.SysB.RingAct

end
