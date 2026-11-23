import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.ConeZcls (ub ub_mul ub_nat ub_isUnit exists_unit_lift pt_map)

namespace CrystallineSemistableComparison.Pb.LX

attribute [local instance] MvPolynomial.gradedAlgebra

section Pts
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem inU_map_c {V : X.Opens} {T T' : Thick (smFun X q)} (f : T ⟶ T') (h : InU V T) : InU V T' := by
  intro x _
  have e := pt_map f
  have hx : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) x) ∈ pt T ⁻¹ᵁ V := h (Set.mem_univ _)
  change (pt T') x ∈ V
  rw [← e]
  exact hx

theorem inU_inf_left {V W : X.Opens} {T : Thick (smFun X q)} (h : InU (V ⊓ W) T) : InU V T :=
  inU_mono q inf_le_left h

theorem inU_inf_right {V W : X.Opens} {T : Thick (smFun X q)} (h : InU (V ⊓ W) T) : InU W T :=
  inU_mono q inf_le_right h

end Pts

variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {N : ℕ}
  (i : X ⟶ PSpace K N) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (s : ℕ)

theorem wK_tf {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : TF 1 s T := h.1

theorem wK_uy {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : InU (uy i y k) T := by
  obtain ⟨-, V, ⟨j, rfl⟩, hV⟩ := h
  exact inU_inf_left hV

theorem wK_wch {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : ∃ j, InU (wch i j) T := by
  obtain ⟨-, V, ⟨j, rfl⟩, hV⟩ := h
  exact ⟨j, inU_inf_right hV⟩

theorem wK_le_wU (k : Fin m) : wK q i y s k ≤ wU q i y s := fun _ h => ⟨k, h⟩

theorem wU_wch {T : Thick (smFun X q)} (h : wU q i y s T) : ∃ j, InU (wch i j) T := by
  obtain ⟨k, hk⟩ := h
  exact wK_wch i y s hk

def lj (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) : ChartR K N j →+* T.B ⧸ T.J :=
  liftA (pt T ≫ i) (X_mem K N j) one_pos h

theorem lj_spec (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    pt T ≫ i = Spec.map (CommRingCat.ofHom (lj i T j h)) ≫ chart K N j :=
  (liftA_spec (pt T ≫ i) (X_mem K N j) one_pos h).symm

def az (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ pullback i (chart K N j) :=
  pullback.lift (pt T) (Spec.map (CommRingCat.ofHom (lj i T j h))) (lj_spec i T j h)

theorem lj_comp {T T' : Thick (smFun X q)} (f : T ⟶ T') (j : Fin (N + 1)) (h : InU (wch i j) T) (h' : InU (wch i j) T') :
    lj i T' j h' = (Ideal.quotientMap T'.J f.φ f.hle).comp (lj i T j h) := by
  have e : pt T' ≫ i = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) ≫ (pt T ≫ i) := by
    rw [← Category.assoc, pt_map f]
  unfold lj
  have key := liftA_comp (Ideal.quotientMap T'.J f.φ f.hle) (pt T ≫ i) (X_mem K N j) one_pos h (e ▸ h')
  refine Eq.trans ?_ key
  congr 1

section O1
variable {D : E.LineData X}

def sO (hD : IsTautologicalLineAt D N i) (j : Fin (N + 1)) : pullback i (chart K N j) ⟶ D.Y := hD.2.choose j

theorem sO_f (hD : IsTautologicalLineAt D N i) (j : Fin (N + 1)) : sO i hD j ≫ D.f = pullback.fst _ _ :=
  hD.2.choose_spec.choose j

theorem sO_u (hD : IsTautologicalLineAt D N i) {V : Scheme.{0}} (j k : Fin (N + 1)) (a : V ⟶ pullback i (chart K N j))
    (b : V ⟶ pullback i (chart K N k)) (h : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _)
    (h' : (a ≫ sO i hD j) ≫ D.f = (b ≫ sO i hD k) ≫ D.f) :
    ((D.u (a ≫ sO i hD j) (b ≫ sO i hD k) h' : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
      (a ≫ pullback.snd _ _).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR K N j))).inv.hom (ratio K N j k)) :=
  hD.2.choose_spec.choose_spec V j k a b h

theorem ub_congr {A : Type} [CommRing A] {a a' b b' : Spec (CommRingCat.of A) ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : ub (D := D) a b h = ub (D := D) a' b' h' := by
  subst ha hb; rfl

theorem az_f (hD : IsTautologicalLineAt D N i) (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    (az i T j h ≫ sO i hD j) ≫ D.f = pt T := by
  rw [Category.assoc, sO_f]
  exact pullback.lift_fst _ _ _

theorem az_f' (hD : IsTautologicalLineAt D N i) (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    az i T j h ≫ sO i hD j ≫ D.f = pt T := by
  rw [sO_f]
  exact pullback.lift_fst _ _ _

def jc (c : (wU q i y s).FullSubcategory) : Fin (N + 1) := (wU_wch i y s c.property).choose

theorem hjc (c : (wU q i y s).FullSubcategory) : InU (wch i (jc i y s c)) c.obj := (wU_wch i y s c.property).choose_spec

def AU (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (c : (wU q i y s).FullSubcategory) : (c.obj.B ⧸ c.obj.J)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (c.obj.B ⧸ c.obj.J))).hom.hom.toMonoidHom
    (D.u (az i c.obj (jc i y s c) (hjc i y s c) ≫ sO i hD (jc i y s c)) (Λ.p c) ((az_f i hD _ _ _).trans (Λ.hp c).symm))

def μ (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory) : c.obj.B ⧸ c.obj.J :=
  lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) *
    (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J)

theorem μ_isUnit (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) : IsUnit (μ i y hy s hD Λ k c) :=
  (liftA_yx_isUnit (pt c.obj ≫ i) y hy _ k (hjc i y s c) hk).mul (Units.isUnit _)

def vv (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) : c.obj.Bˣ :=
  (exists_unit_lift c.obj _ (μ_isUnit i y hy s hD Λ k c hk)).choose

theorem vv_spec (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) :
    Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k c hk : c.obj.Bˣ) : c.obj.B) = μ i y hy s hD Λ k c :=
  (exists_unit_lift c.obj _ (μ_isUnit i y hy s hD Λ k c hk)).choose_spec

end O1

section E
variable {D : E.LineData X}

theorem gamma_specMap {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      ((Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ψ r := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((Spec.map (CommRingCat.ofHom ψ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom).hom _ = _
  rw [e]
  simp

theorem eps_mem (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) {c c' : (wU q i y s).FullSubcategory}
    (φ : c ⟶ c') (hk : InU (uy i y k) c.obj) (hk' : InU (uy i y k) c'.obj) :
    (((show c'.obj.Bˣ from Λ.w φ) ^ e * vv i y hy s hD Λ k c' hk' *
        (Units.map (show c.obj ⟶ c'.obj from (wU q i y s).ι.map φ).φ.toMonoidHom (vv i y hy s hD Λ k c hk))⁻¹ :
          c'.obj.Bˣ) : c'.obj.B) - 1 ∈ c'.obj.J := by
  set f : c.obj ⟶ c'.obj := (wU q i y s).ι.map φ with hf
  set Q := Ideal.quotientMap c'.obj.J f.φ f.hle with hQ
  have hj : InU (wch i (jc i y s c)) c.obj := hjc i y s c
  have hj' : InU (wch i (jc i y s c')) c'.obj := hjc i y s c'
  have hjT : InU (wch i (jc i y s c)) c'.obj := inU_map_c f hj
  have hpt : Spec.map (CommRingCat.ofHom Q) ≫ pt c.obj = pt c'.obj := pt_map f

  have h1 : (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [Category.assoc, Λ.hp, Λ.hp]; exact hpt
  have ew : Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) =
      ub (D := D) (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) (Λ.p c') h1 := Λ.hw φ h1

  have h2 : (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c))) ≫ D.f =
      (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) ≫ D.f := by
    simp only [Category.assoc, az_f']
    rw [Λ.hp]
    rfl
  have eA : Q (((AU i y s hD Λ c : (c.obj.B ⧸ c.obj.J)ˣ)) : c.obj.B ⧸ c.obj.J) =
      ub (D := D) (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c)))
        (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) h2 :=
    (ub_nat Q _ _ _ h2).symm

  have h3 : (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c))) ≫ D.f =
      (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f := by
    simp only [Category.assoc, az_f']
    exact hpt
  have h4 : (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [az_f, Λ.hp]
    rfl
  have hcoc : ub (D := D) _ _ h2 * ub (D := D) _ _ h1 = ub (D := D) _ _ h3 * ub (D := D) _ _ h4 := by
    rw [ub_mul, ub_mul]

  have h5 : (Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ pullback.fst _ _ = az i c'.obj _ hj' ≫ pullback.fst _ _ := by
    rw [Category.assoc]
    unfold az
    rw [pullback.lift_fst, pullback.lift_fst, hpt]
  have h3' : ((Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ sO i hD (jc i y s c)) ≫ D.f =
      (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f := by
    rw [Category.assoc]; exact h3
  have eR : ub (D := D) _ _ h3 = lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) := by
    rw [ub_congr (Category.assoc _ _ _).symm rfl h3 h3']
    unfold ub
    rw [sO_u i hD _ _ _ _ h5 h3']
    have e6 : (Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (lj i c'.obj _ hjT)) := by
      rw [Category.assoc]
      unfold az
      rw [pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun ψ => Spec.map (CommRingCat.ofHom ψ)) (lj_comp i f _ hj hjT).symm
    rw [e6]
    exact gamma_specMap _ _

  have hY : lj i c'.obj _ hjT (yx y hy (jc i y s c) k) =
      lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) ^ e :=
    liftA_yx_change (pt c'.obj ≫ i) y hy (jc i y s c) (jc i y s c') k hjT hj'
  have eY : Q (lj i c.obj _ hj (yx y hy (jc i y s c) k)) = lj i c'.obj _ hjT (yx y hy (jc i y s c) k) :=
    (RingHom.congr_fun (lj_comp i f _ hj hjT) _).symm

  have key : Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) ^ e * μ i y hy s hD Λ k c' =
      Q (μ i y hy s hD Λ k c) := by
    set U := Units.map Q.toMonoidHom (AU i y s hD Λ c) with hU
    have hUv : (U : c'.obj.B ⧸ c'.obj.J) = ub (D := D) _ _ h2 := eA
    set A' := AU i y s hD Λ c' with hA'
    have hA'v : (A' : c'.obj.B ⧸ c'.obj.J) = ub (D := D) _ _ h4 := rfl
    set W := Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) with hWdef
    set R := lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) with hR
    have hc : (U : c'.obj.B ⧸ c'.obj.J) * W = R * A' := by
      rw [hUv, hA'v, ew, ← eR]; exact hcoc
    have hW : W = ((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) * (R * A') := by
      rw [← hc, ← mul_assoc, Units.inv_mul, one_mul]
    have hQμ : Q (μ i y hy s hD Λ k c) = lj i c'.obj _ hjT (yx y hy (jc i y s c) k) *
        (((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J)) ^ e := by
      unfold μ
      rw [map_mul, eY, Units.val_pow_eq_pow_val, map_pow]
      rfl
    rw [hQμ]
    unfold μ
    rw [← hA', hY, hW, Units.val_pow_eq_pow_val]
    have hA : (A' : c'.obj.B ⧸ c'.obj.J) ^ e * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    calc (((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) * (R * A')) ^ e *
          (lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e)
        = lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * R ^ e * ((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e *
          ((A' : c'.obj.B ⧸ c'.obj.J) ^ e * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e) := by ring
      _ = _ := by rw [hA, mul_one]

  have hv := vv_spec i y hy s hD Λ k c hk
  have hv' := vv_spec i y hy s hD Λ k c' hk'
  have hfv : Ideal.Quotient.mk c'.obj.J
      ((Units.map f.φ.toMonoidHom (vv i y hy s hD Λ k c hk) : c'.obj.Bˣ) : c'.obj.B) = Q (μ i y hy s hD Λ k c) := by
    rw [← hv]; rfl
  have hinv : Ideal.Quotient.mk c'.obj.J
      (((Units.map f.φ.toMonoidHom (vv i y hy s hD Λ k c hk))⁻¹ : c'.obj.Bˣ) : c'.obj.B) * Q (μ i y hy s hD Λ k c) = 1 := by
    rw [← hfv, ← map_mul, Units.inv_mul, map_one]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, Units.val_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, map_mul, map_mul, map_pow, hv', key, mul_comm]
  exact hinv

end E

end CrystallineSemistableComparison.Pb.LX
